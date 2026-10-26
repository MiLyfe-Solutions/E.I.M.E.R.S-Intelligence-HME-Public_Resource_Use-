import V185TrunkScan23Chunk0946

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5606177 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 6]
def baseStart_5606177 : Nat := 118140960795 + 5606177 * 2 ^ 59
def prefixEnd_5606177 : Nat := 4983230072969 + 3 ^ 40 * 5606177 * 2
def baseEnd_5606177 : Nat := 959554478393672513468389

theorem tailTrace_5606177 : CollatzResearch.WordTrace tailWord_5606177 prefixEnd_5606177 959554478393672513468389 := by
  unfold tailWord_5606177
  simp only [CollatzResearch.WordTrace]
  refine ⟨204474073410785662649520785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136316048940523775099680523 204474073410785662649520785)
  ·
    refine ⟨153355555058089246987140589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204474073410785662649520785 153355555058089246987140589)
    ·
      refine ⟨57508333146783467620177721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153355555058089246987140589 57508333146783467620177721)
      ·
        refine ⟨43131249860087600715133291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57508333146783467620177721 43131249860087600715133291)
        ·
          refine ⟨64696874790131401072699937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43131249860087600715133291 64696874790131401072699937)
          ·
            refine ⟨48522656092598550804524953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64696874790131401072699937 48522656092598550804524953)
            ·
              refine ⟨36391992069448913103393715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48522656092598550804524953 36391992069448913103393715)
              ·
                refine ⟨54587988104173369655090573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36391992069448913103393715 54587988104173369655090573)
                ·
                  refine ⟨20470495539065013620658965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54587988104173369655090573 20470495539065013620658965)
                  ·
                    refine ⟨959554478393672513468389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20470495539065013620658965 959554478393672513468389)
                    ·
                      rfl

theorem cell23_5606177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_5606177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606177 prefixEnd_5606177 := by exact prefixLift 5606177
  have htrace : WordTrace (prefixWord ++ tailWord_5606177) baseStart_5606177 baseEnd_5606177 := by
    simpa [prefixWord, tailWord_5606177, baseEnd_5606177] using wordTrace_append hprefix tailTrace_5606177
  have hstable : (prefixWord ++ tailWord_5606177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606177).length < 2 ^ (prefixWord ++ tailWord_5606177).sum := by decide
  have hdescent : baseEnd_5606177 < baseStart_5606177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606187 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5]
def baseStart_5606187 : Nat := 118140960795 + 5606187 * 2 ^ 59
def prefixEnd_5606187 : Nat := 4983230072969 + 3 ^ 40 * 5606187 * 2
def baseEnd_5606187 : Nat := 2878668569987562501280121

theorem tailTrace_5606187 : CollatzResearch.WordTrace tailWord_5606187 prefixEnd_5606187 2878668569987562501280121 := by
  unfold tailWord_5606187
  simp only [CollatzResearch.WordTrace]
  refine ⟨204474438140749434357384815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136316292093832956238256543 204474438140749434357384815)
  ·
    refine ⟨306711657211124151536077223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204474438140749434357384815 306711657211124151536077223)
    ·
      refine ⟨460067485816686227304115835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306711657211124151536077223 460067485816686227304115835)
      ·
        refine ⟨690101228725029340956173753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460067485816686227304115835 690101228725029340956173753)
        ·
          refine ⟨517575921543772005717130315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690101228725029340956173753 517575921543772005717130315)
          ·
            refine ⟨776363882315658008575695473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517575921543772005717130315 776363882315658008575695473)
            ·
              refine ⟨582272911736743506431771605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776363882315658008575695473 582272911736743506431771605)
              ·
                refine ⟨13647021368829925931994647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 582272911736743506431771605 13647021368829925931994647)
                ·
                  refine ⟨20470532053244888897991971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13647021368829925931994647 20470532053244888897991971)
                  ·
                    refine ⟨30705798079867333346987957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20470532053244888897991971 30705798079867333346987957)
                    ·
                      refine ⟨2878668569987562501280121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30705798079867333346987957 2878668569987562501280121)
                      ·
                        rfl

theorem cell23_5606187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 5].length) (baseStart_5606187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606187 prefixEnd_5606187 := by exact prefixLift 5606187
  have htrace : WordTrace (prefixWord ++ tailWord_5606187) baseStart_5606187 baseEnd_5606187 := by
    simpa [prefixWord, tailWord_5606187, baseEnd_5606187] using wordTrace_append hprefix tailTrace_5606187
  have hstable : (prefixWord ++ tailWord_5606187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606187).length < 2 ^ (prefixWord ++ tailWord_5606187).sum := by decide
  have hdescent : baseEnd_5606187 < baseStart_5606187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606194 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_5606194 : Nat := 118140960795 + 5606194 * 2 ^ 59
def prefixEnd_5606194 : Nat := 4983230072969 + 3 ^ 40 * 5606194 * 2
def baseEnd_5606194 : Nat := 959557388117381324630863

theorem tailTrace_5606194 : CollatzResearch.WordTrace tailWord_5606194 prefixEnd_5606194 959557388117381324630863 := by
  unfold tailWord_5606194
  simp only [CollatzResearch.WordTrace]
  refine ⟨51118673362931018638222409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136316462301149383035259757 51118673362931018638222409)
  ·
    refine ⟨38339005022198263978666807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51118673362931018638222409 38339005022198263978666807)
    ·
      refine ⟨57508507533297395968000211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38339005022198263978666807 57508507533297395968000211)
      ·
        refine ⟨86262761299946093952000317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57508507533297395968000211 86262761299946093952000317)
        ·
          refine ⟨32348535487479785232000119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86262761299946093952000317 32348535487479785232000119)
          ·
            refine ⟨48522803231219677848000179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32348535487479785232000119 48522803231219677848000179)
            ·
              refine ⟨72784204846829516772000269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48522803231219677848000179 72784204846829516772000269)
              ·
                refine ⟨27294076817561068789500101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72784204846829516772000269 27294076817561068789500101)
                ·
                  refine ⟨5117639403292700398031269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27294076817561068789500101 5117639403292700398031269)
                  ·
                    refine ⟨959557388117381324630863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117639403292700398031269 959557388117381324630863)
                    ·
                      rfl

theorem cell23_5606194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_5606194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606194 prefixEnd_5606194 := by exact prefixLift 5606194
  have htrace : WordTrace (prefixWord ++ tailWord_5606194) baseStart_5606194 baseEnd_5606194 := by
    simpa [prefixWord, tailWord_5606194, baseEnd_5606194] using wordTrace_append hprefix tailTrace_5606194
  have hstable : (prefixWord ++ tailWord_5606194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606194).length < 2 ^ (prefixWord ++ tailWord_5606194).sum := by decide
  have hdescent : baseEnd_5606194 < baseStart_5606194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606195 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 1, 1, 3]
def baseStart_5606195 : Nat := 118140960795 + 5606195 * 2 ^ 59
def prefixEnd_5606195 : Nat := 4983230072969 + 3 ^ 40 * 5606195 * 2
def baseEnd_5606195 : Nat := 2878672677832798469980085

theorem tailTrace_5606195 : CollatzResearch.WordTrace tailWord_5606195 prefixEnd_5606195 2878672677832798469980085 := by
  unfold tailWord_5606195
  simp only [CollatzResearch.WordTrace]
  refine ⟨204474729924720451723676039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136316486616480301149117359 204474729924720451723676039)
  ·
    refine ⟨306712094887080677585514059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204474729924720451723676039 306712094887080677585514059)
    ·
      refine ⟨460068142330621016378271089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306712094887080677585514059 460068142330621016378271089)
      ·
        refine ⟨345051106747965762283703317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460068142330621016378271089 345051106747965762283703317)
        ·
          refine ⟨16174270628810895107048593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 345051106747965762283703317 16174270628810895107048593)
          ·
            refine ⟨12130702971608171330286445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174270628810895107048593 12130702971608171330286445)
            ·
              refine ⟨4549013614353064248857417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12130702971608171330286445 4549013614353064248857417)
              ·
                refine ⟨3411760210764798186643063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549013614353064248857417 3411760210764798186643063)
                ·
                  refine ⟨5117640316147197279964595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411760210764798186643063 5117640316147197279964595)
                  ·
                    refine ⟨7676460474220795919946893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117640316147197279964595 7676460474220795919946893)
                    ·
                      refine ⟨2878672677832798469980085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676460474220795919946893 2878672677832798469980085)
                      ·
                        rfl

theorem cell23_5606195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 1, 3].length) (baseStart_5606195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606195 prefixEnd_5606195 := by exact prefixLift 5606195
  have htrace : WordTrace (prefixWord ++ tailWord_5606195) baseStart_5606195 baseEnd_5606195 := by
    simpa [prefixWord, tailWord_5606195, baseEnd_5606195] using wordTrace_append hprefix tailTrace_5606195
  have hstable : (prefixWord ++ tailWord_5606195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606195).length < 2 ^ (prefixWord ++ tailWord_5606195).sum := by decide
  have hdescent : baseEnd_5606195 < baseStart_5606195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606204 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_5606204 : Nat := 118140960795 + 5606204 * 2 ^ 59
def prefixEnd_5606204 : Nat := 4983230072969 + 3 ^ 40 * 5606204 * 2
def baseEnd_5606204 : Nat := 2878677299158688934767543

theorem tailTrace_5606204 : CollatzResearch.WordTrace tailWord_5606204 prefixEnd_5606204 2878677299158688934767543 := by
  unfold tailWord_5606204
  simp only [CollatzResearch.WordTrace]
  refine ⟨102237529090843923130376833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136316705454458564173835777 102237529090843923130376833)
  ·
    refine ⟨76678146818132942347782625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102237529090843923130376833 76678146818132942347782625)
    ·
      refine ⟨57508610113599706760836969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76678146818132942347782625 57508610113599706760836969)
      ·
        refine ⟨43131457585199780070627727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57508610113599706760836969 43131457585199780070627727)
        ·
          refine ⟨64697186377799670105941591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43131457585199780070627727 64697186377799670105941591)
          ·
            refine ⟨97045779566699505158912387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64697186377799670105941591 97045779566699505158912387)
            ·
              refine ⟨145568669350049257738368581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97045779566699505158912387 145568669350049257738368581)
              ·
                refine ⟨27294125503134235825944109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145568669350049257738368581 27294125503134235825944109)
                ·
                  refine ⟨10235297063675338434729041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27294125503134235825944109 10235297063675338434729041)
                  ·
                    refine ⟨7676472797756503826046781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10235297063675338434729041 7676472797756503826046781)
                    ·
                      refine ⟨2878677299158688934767543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676472797756503826046781 2878677299158688934767543)
                      ·
                        rfl

theorem cell23_5606204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_5606204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606204 prefixEnd_5606204 := by exact prefixLift 5606204
  have htrace : WordTrace (prefixWord ++ tailWord_5606204) baseStart_5606204 baseEnd_5606204 := by
    simpa [prefixWord, tailWord_5606204, baseEnd_5606204] using wordTrace_append hprefix tailTrace_5606204
  have hstable : (prefixWord ++ tailWord_5606204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606204).length < 2 ^ (prefixWord ++ tailWord_5606204).sum := by decide
  have hdescent : baseEnd_5606204 < baseStart_5606204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606207 : List Nat := [1, 1, 2, 2, 5, 1, 1, 10]
def baseStart_5606207 : Nat := 118140960795 + 5606207 * 2 ^ 59
def prefixEnd_5606207 : Nat := 4983230072969 + 3 ^ 40 * 5606207 * 2
def baseEnd_5606207 : Nat := 106617734800024163815927

theorem tailTrace_5606207 : CollatzResearch.WordTrace tailWord_5606207 prefixEnd_5606207 106617734800024163815927 := by
  unfold tailWord_5606207
  simp only [CollatzResearch.WordTrace]
  refine ⟨204475167600676977773112875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136316778400451318515408583 204475167600676977773112875)
  ·
    refine ⟨306712751401015466659669313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204475167600676977773112875 306712751401015466659669313)
    ·
      refine ⟨230034563550761599994751985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306712751401015466659669313 230034563550761599994751985)
      ·
        refine ⟨172525922663071199996063989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230034563550761599994751985 172525922663071199996063989)
        ·
          refine ⟨16174305249662924999630999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172525922663071199996063989 16174305249662924999630999)
          ·
            refine ⟨24261457874494387499446499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16174305249662924999630999 24261457874494387499446499)
            ·
              refine ⟨36392186811741581249169749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24261457874494387499446499 36392186811741581249169749)
              ·
                refine ⟨106617734800024163815927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36392186811741581249169749 106617734800024163815927)
                ·
                  rfl

theorem cell23_5606207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 10].length) (baseStart_5606207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606207 prefixEnd_5606207 := by exact prefixLift 5606207
  have htrace : WordTrace (prefixWord ++ tailWord_5606207) baseStart_5606207 baseEnd_5606207 := by
    simpa [prefixWord, tailWord_5606207, baseEnd_5606207] using wordTrace_append hprefix tailTrace_5606207
  have hstable : (prefixWord ++ tailWord_5606207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606207).length < 2 ^ (prefixWord ++ tailWord_5606207).sum := by decide
  have hdescent : baseEnd_5606207 < baseStart_5606207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606234 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_5606234 : Nat := 118140960795 + 5606234 * 2 ^ 59
def prefixEnd_5606234 : Nat := 4983230072969 + 3 ^ 40 * 5606234 * 2
def baseEnd_5606234 : Nat := 2878692703578323817392405

theorem tailTrace_5606234 : CollatzResearch.WordTrace tailWord_5606234 prefixEnd_5606234 2878692703578323817392405 := by
  unfold tailWord_5606234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51119038092894790346086439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136317434914386107589563837 51119038092894790346086439)
  ·
    refine ⟨76678557139342185519129659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51119038092894790346086439 76678557139342185519129659)
    ·
      refine ⟨115017835709013278278694489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76678557139342185519129659 115017835709013278278694489)
      ·
        refine ⟨86263376781759958709020867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115017835709013278278694489 86263376781759958709020867)
        ·
          refine ⟨129395065172639938063531301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86263376781759958709020867 129395065172639938063531301)
          ·
            refine ⟨24261574719869988386912119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129395065172639938063531301 24261574719869988386912119)
            ·
              refine ⟨36392362079804982580368179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24261574719869988386912119 36392362079804982580368179)
              ·
                refine ⟨54588543119707473870552269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36392362079804982580368179 54588543119707473870552269)
                ·
                  refine ⟨20470703669890302701457101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54588543119707473870552269 20470703669890302701457101)
                  ·
                    refine ⟨7676513876208863513046413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20470703669890302701457101 7676513876208863513046413)
                    ·
                      refine ⟨2878692703578323817392405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676513876208863513046413 2878692703578323817392405)
                      ·
                        rfl

theorem cell23_5606234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_5606234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606234 prefixEnd_5606234 := by exact prefixLift 5606234
  have htrace : WordTrace (prefixWord ++ tailWord_5606234) baseStart_5606234 baseEnd_5606234 := by
    simpa [prefixWord, tailWord_5606234, baseEnd_5606234] using wordTrace_append hprefix tailTrace_5606234
  have hstable : (prefixWord ++ tailWord_5606234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606234).length < 2 ^ (prefixWord ++ tailWord_5606234).sum := by decide
  have hdescent : baseEnd_5606234 < baseStart_5606234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606251 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 3]
def baseStart_5606251 : Nat := 118140960795 + 5606251 * 2 ^ 59
def prefixEnd_5606251 : Nat := 4983230072969 + 3 ^ 40 * 5606251 * 2
def baseEnd_5606251 : Nat := 2878701432749450250879827

theorem tailTrace_5606251 : CollatzResearch.WordTrace tailWord_5606251 prefixEnd_5606251 2878701432749450250879827 := by
  unfold tailWord_5606251
  simp only [CollatzResearch.WordTrace]
  refine ⟨204476772412517573287714607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136317848275011715525143071 204476772412517573287714607)
  ·
    refine ⟨306715158618776359931571911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204476772412517573287714607 306715158618776359931571911)
    ·
      refine ⟨460072737928164539897357867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306715158618776359931571911 460072737928164539897357867)
      ·
        refine ⟨690109106892246809846036801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460072737928164539897357867 690109106892246809846036801)
        ·
          refine ⟨517581830169185107384527601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690109106892246809846036801 517581830169185107384527601)
          ·
            refine ⟨388186372626888830538395701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517581830169185107384527601 388186372626888830538395701)
            ·
              refine ⟨36392472433770827862974597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 388186372626888830538395701 36392472433770827862974597)
              ·
                refine ⟨6823588581332030224307737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36392472433770827862974597 6823588581332030224307737)
                ·
                  refine ⟨5117691435999022668230803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6823588581332030224307737 5117691435999022668230803)
                  ·
                    refine ⟨7676537153998534002346205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117691435999022668230803 7676537153998534002346205)
                    ·
                      refine ⟨2878701432749450250879827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676537153998534002346205 2878701432749450250879827)
                      ·
                        rfl

theorem cell23_5606251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 1, 3].length) (baseStart_5606251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606251 prefixEnd_5606251 := by exact prefixLift 5606251
  have htrace : WordTrace (prefixWord ++ tailWord_5606251) baseStart_5606251 baseEnd_5606251 := by
    simpa [prefixWord, tailWord_5606251, baseEnd_5606251] using wordTrace_append hprefix tailTrace_5606251
  have hstable : (prefixWord ++ tailWord_5606251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606251).length < 2 ^ (prefixWord ++ tailWord_5606251).sum := by decide
  have hdescent : baseEnd_5606251 < baseStart_5606251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606267 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 8]
def baseStart_5606267 : Nat := 118140960795 + 5606267 * 2 ^ 59
def prefixEnd_5606267 : Nat := 4983230072969 + 3 ^ 40 * 5606267 * 2
def baseEnd_5606267 : Nat := 959569882813307396093251

theorem tailTrace_5606267 : CollatzResearch.WordTrace tailWord_5606267 prefixEnd_5606267 959569882813307396093251 := by
  unfold tailWord_5606267
  simp only [CollatzResearch.WordTrace]
  refine ⟨204477355980459608020297055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136318237320306405346864703 204477355980459608020297055)
  ·
    refine ⟨306716033970689412030445583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204477355980459608020297055 306716033970689412030445583)
    ·
      refine ⟨460074050956034118045668375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306716033970689412030445583 460074050956034118045668375)
      ·
        refine ⟨690111076434051177068502563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460074050956034118045668375 690111076434051177068502563)
        ·
          refine ⟨1035166614651076765602753845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690111076434051177068502563 1035166614651076765602753845)
          ·
            refine ⟨97046870123538446775258173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1035166614651076765602753845 97046870123538446775258173)
            ·
              refine ⟨36392576296326917540721815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97046870123538446775258173 36392576296326917540721815)
              ·
                refine ⟨54588864444490376311082723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36392576296326917540721815 54588864444490376311082723)
                ·
                  refine ⟨81883296666735564466624085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54588864444490376311082723 81883296666735564466624085)
                  ·
                    refine ⟨959569882813307396093251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81883296666735564466624085 959569882813307396093251)
                    ·
                      rfl

theorem cell23_5606267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 8].length) (baseStart_5606267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606267 prefixEnd_5606267 := by exact prefixLift 5606267
  have htrace : WordTrace (prefixWord ++ tailWord_5606267) baseStart_5606267 baseEnd_5606267 := by
    simpa [prefixWord, tailWord_5606267, baseEnd_5606267] using wordTrace_append hprefix tailTrace_5606267
  have hstable : (prefixWord ++ tailWord_5606267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606267).length < 2 ^ (prefixWord ++ tailWord_5606267).sum := by decide
  have hdescent : baseEnd_5606267 < baseStart_5606267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606297 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 11]
def baseStart_5606297 : Nat := 118140960795 + 5606297 * 2 ^ 59
def prefixEnd_5606297 : Nat := 4983230072969 + 3 ^ 40 * 5606297 * 2
def baseEnd_5606297 : Nat := 319858339206617452322735

theorem tailTrace_5606297 : CollatzResearch.WordTrace tailWord_5606297 prefixEnd_5606297 319858339206617452322735 := by
  unfold tailWord_5606297
  simp only [CollatzResearch.WordTrace]
  refine ⟨204478450170350923143889145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136318966780233948762592763 204478450170350923143889145)
  ·
    refine ⟨153358837627763192357916859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204478450170350923143889145 153358837627763192357916859)
    ·
      refine ⟨230038256441644788536875289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153358837627763192357916859 230038256441644788536875289)
      ·
        refine ⟨172528692331233591402656467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230038256441644788536875289 172528692331233591402656467)
        ·
          refine ⟨258793038496850387103984701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172528692331233591402656467 258793038496850387103984701)
          ·
            refine ⟨97047389436318895163994263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258793038496850387103984701 97047389436318895163994263)
            ·
              refine ⟨145571084154478342745991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97047389436318895163994263 145571084154478342745991395)
              ·
                refine ⟨218356626231717514118987093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145571084154478342745991395 218356626231717514118987093)
                ·
                  refine ⟨319858339206617452322735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 218356626231717514118987093 319858339206617452322735)
                  ·
                    rfl

theorem cell23_5606297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 11].length) (baseStart_5606297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606297 prefixEnd_5606297 := by exact prefixLift 5606297
  have htrace : WordTrace (prefixWord ++ tailWord_5606297) baseStart_5606297 baseEnd_5606297 := by
    simpa [prefixWord, tailWord_5606297, baseEnd_5606297] using wordTrace_append hprefix tailTrace_5606297
  have hstable : (prefixWord ++ tailWord_5606297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606297).length < 2 ^ (prefixWord ++ tailWord_5606297).sum := by decide
  have hdescent : baseEnd_5606297 < baseStart_5606297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606304 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5606304 : Nat := 118140960795 + 5606304 * 2 ^ 59
def prefixEnd_5606304 : Nat := 4983230072969 + 3 ^ 40 * 5606304 * 2
def baseEnd_5606304 : Nat := 2878728647224138543517083

theorem tailTrace_5606304 : CollatzResearch.WordTrace tailWord_5606304 prefixEnd_5606304 2878728647224138543517083 := by
  unfold tailWord_5606304
  simp only [CollatzResearch.WordTrace]
  refine ⟨102239352740662781669696983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136319136987550375559595977 102239352740662781669696983)
  ·
    refine ⟨153359029110994172504545475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102239352740662781669696983 153359029110994172504545475)
    ·
      refine ⟨230038543666491258756818213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153359029110994172504545475 230038543666491258756818213)
      ·
        refine ⟨43132226937467111016903415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230038543666491258756818213 43132226937467111016903415)
        ·
          refine ⟨64698340406200666525355123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43132226937467111016903415 64698340406200666525355123)
          ·
            refine ⟨97047510609300999788032685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64698340406200666525355123 97047510609300999788032685)
            ·
              refine ⟨36392816478487874920512257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97047510609300999788032685 36392816478487874920512257)
              ·
                refine ⟨27294612358865906190384193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36392816478487874920512257 27294612358865906190384193)
                ·
                  refine ⟨20470959269149429642788145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27294612358865906190384193 20470959269149429642788145)
                  ·
                    refine ⟨15353219451862072232091109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20470959269149429642788145 15353219451862072232091109)
                    ·
                      refine ⟨2878728647224138543517083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15353219451862072232091109 2878728647224138543517083)
                      ·
                        rfl

theorem cell23_5606304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5606304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606304 prefixEnd_5606304 := by exact prefixLift 5606304
  have htrace : WordTrace (prefixWord ++ tailWord_5606304) baseStart_5606304 baseEnd_5606304 := by
    simpa [prefixWord, tailWord_5606304, baseEnd_5606304] using wordTrace_append hprefix tailTrace_5606304
  have hstable : (prefixWord ++ tailWord_5606304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606304).length < 2 ^ (prefixWord ++ tailWord_5606304).sum := by decide
  have hdescent : baseEnd_5606304 < baseStart_5606304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606308 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 4, 2, 2]
def baseStart_5606308 : Nat := 118140960795 + 5606308 * 2 ^ 59
def prefixEnd_5606308 : Nat := 4983230072969 + 3 ^ 40 * 5606308 * 2
def baseEnd_5606308 : Nat := 2878730701146756527867065

theorem tailTrace_5606308 : CollatzResearch.WordTrace tailWord_5606308 prefixEnd_5606308 2878730701146756527867065 := by
  unfold tailWord_5606308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102239425686655536011269789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136319234248874048015026385 102239425686655536011269789)
  ·
    refine ⟨38339784632495826004226171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102239425686655536011269789 38339784632495826004226171)
    ·
      refine ⟨57509676948743739006339257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38339784632495826004226171 57509676948743739006339257)
      ·
        refine ⟨43132257711557804254754443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57509676948743739006339257 43132257711557804254754443)
        ·
          refine ⟨64698386567336706382131665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43132257711557804254754443 64698386567336706382131665)
          ·
            refine ⟨48523789925502529786598749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64698386567336706382131665 48523789925502529786598749)
            ·
              refine ⟨18196421222063448669974531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48523789925502529786598749 18196421222063448669974531)
              ·
                refine ⟨27294631833095173004961797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18196421222063448669974531 27294631833095173004961797)
                ·
                  refine ⟨5117743468705344938430337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27294631833095173004961797 5117743468705344938430337)
                  ·
                    refine ⟨3838307601529008703822753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117743468705344938430337 3838307601529008703822753)
                    ·
                      refine ⟨2878730701146756527867065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838307601529008703822753 2878730701146756527867065)
                      ·
                        rfl

theorem cell23_5606308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_5606308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606308 prefixEnd_5606308 := by exact prefixLift 5606308
  have htrace : WordTrace (prefixWord ++ tailWord_5606308) baseStart_5606308 baseEnd_5606308 := by
    simpa [prefixWord, tailWord_5606308, baseEnd_5606308] using wordTrace_append hprefix tailTrace_5606308
  have hstable : (prefixWord ++ tailWord_5606308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606308).length < 2 ^ (prefixWord ++ tailWord_5606308).sum := by decide
  have hdescent : baseEnd_5606308 < baseStart_5606308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606361 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 2, 5]
def baseStart_5606361 : Nat := 118140960795 + 5606361 * 2 ^ 59
def prefixEnd_5606361 : Nat := 4983230072969 + 3 ^ 40 * 5606361 * 2
def baseEnd_5606361 : Nat := 959585971873814940168107

theorem tailTrace_5606361 : CollatzResearch.WordTrace tailWord_5606361 prefixEnd_5606361 959585971873814940168107 := by
  unfold tailWord_5606361
  simp only [CollatzResearch.WordTrace]
  refine ⟨204480784442119062074218937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136320522961412708049479291 204480784442119062074218937)
  ·
    refine ⟨153360588331589296555664203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204480784442119062074218937 153360588331589296555664203)
    ·
      refine ⟨230040882497383944833496305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153360588331589296555664203 230040882497383944833496305)
      ·
        refine ⟨172530661873037958625122229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230040882497383944833496305 172530661873037958625122229)
        ·
          refine ⟨16174749550597308621105209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172530661873037958625122229 16174749550597308621105209)
          ·
            refine ⟨12131062162947981465828907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174749550597308621105209 12131062162947981465828907)
            ·
              refine ⟨18196593244421972198743361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131062162947981465828907 18196593244421972198743361)
              ·
                refine ⟨13647444933316479149057521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18196593244421972198743361 13647444933316479149057521)
                ·
                  refine ⟨10235583699987359361793141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13647444933316479149057521 10235583699987359361793141)
                  ·
                    refine ⟨959585971873814940168107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10235583699987359361793141 959585971873814940168107)
                    ·
                      rfl

theorem cell23_5606361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_5606361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606361 prefixEnd_5606361 := by exact prefixLift 5606361
  have htrace : WordTrace (prefixWord ++ tailWord_5606361) baseStart_5606361 baseEnd_5606361 := by
    simpa [prefixWord, tailWord_5606361, baseEnd_5606361] using wordTrace_append hprefix tailTrace_5606361
  have hstable : (prefixWord ++ tailWord_5606361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606361).length < 2 ^ (prefixWord ++ tailWord_5606361).sum := by decide
  have hdescent : baseEnd_5606361 < baseStart_5606361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606365 : List Nat := [1, 4, 3, 1, 2, 2, 3, 2, 5]
def baseStart_5606365 : Nat := 118140960795 + 5606365 * 2 ^ 59
def prefixEnd_5606365 : Nat := 4983230072969 + 3 ^ 40 * 5606365 * 2
def baseEnd_5606365 : Nat := 319862218838229200539367

theorem tailTrace_5606365 : CollatzResearch.WordTrace tailWord_5606365 prefixEnd_5606365 319862218838229200539367 := by
  unfold tailWord_5606365
  simp only [CollatzResearch.WordTrace]
  refine ⟨204480930334104570757364549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136320620222736380504909699 204480930334104570757364549)
  ·
    refine ⟨38340174437644607017005853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204480930334104570757364549 38340174437644607017005853)
    ·
      refine ⟨14377565414116727631377195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38340174437644607017005853 14377565414116727631377195)
      ·
        refine ⟨21566348121175091447065793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14377565414116727631377195 21566348121175091447065793)
        ·
          refine ⟨16174761090881318585299345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21566348121175091447065793 16174761090881318585299345)
          ·
            refine ⟨12131070818160988938974509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16174761090881318585299345 12131070818160988938974509)
            ·
              refine ⟨4549151556810370852115441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12131070818160988938974509 4549151556810370852115441)
              ·
                refine ⟨3411863667607778139086581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549151556810370852115441 3411863667607778139086581)
                ·
                  refine ⟨319862218838229200539367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411863667607778139086581 319862218838229200539367)
                  ·
                    rfl

theorem cell23_5606365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_5606365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606365 prefixEnd_5606365 := by exact prefixLift 5606365
  have htrace : WordTrace (prefixWord ++ tailWord_5606365) baseStart_5606365 baseEnd_5606365 := by
    simpa [prefixWord, tailWord_5606365, baseEnd_5606365] using wordTrace_append hprefix tailTrace_5606365
  have hstable : (prefixWord ++ tailWord_5606365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606365).length < 2 ^ (prefixWord ++ tailWord_5606365).sum := by decide
  have hdescent : baseEnd_5606365 < baseStart_5606365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606394 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_5606394 : Nat := 118140960795 + 5606394 * 2 ^ 59
def prefixEnd_5606394 : Nat := 4983230072969 + 3 ^ 40 * 5606394 * 2
def baseEnd_5606394 : Nat := 2878774860483043191391669

theorem tailTrace_5606394 : CollatzResearch.WordTrace tailWord_5606394 prefixEnd_5606394 2878774860483043191391669 := by
  unfold tailWord_5606394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51120497012749877177542559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136321325367333005806780157 51120497012749877177542559)
  ·
    refine ⟨76680745519124815766313839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51120497012749877177542559 76680745519124815766313839)
    ·
      refine ⟨115021118278687223649470759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76680745519124815766313839 115021118278687223649470759)
      ·
        refine ⟨172531677418030835474206139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115021118278687223649470759 172531677418030835474206139)
        ·
          refine ⟨258797516127046253211309209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172531677418030835474206139 258797516127046253211309209)
          ·
            refine ⟨194098137095284689908481907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258797516127046253211309209 194098137095284689908481907)
            ·
              refine ⟨291147205642927034862722861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194098137095284689908481907 291147205642927034862722861)
              ·
                refine ⟨109180202116097638073521073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291147205642927034862722861 109180202116097638073521073)
                ·
                  refine ⟨81885151587073228555140805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109180202116097638073521073 81885151587073228555140805)
                  ·
                    refine ⟨15353465922576230354088901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81885151587073228555140805 15353465922576230354088901)
                    ·
                      refine ⟨2878774860483043191391669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15353465922576230354088901 2878774860483043191391669)
                      ·
                        rfl

theorem cell23_5606394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_5606394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606394 prefixEnd_5606394 := by exact prefixLift 5606394
  have htrace : WordTrace (prefixWord ++ tailWord_5606394) baseStart_5606394 baseEnd_5606394 := by
    simpa [prefixWord, tailWord_5606394, baseEnd_5606394] using wordTrace_append hprefix tailTrace_5606394
  have hstable : (prefixWord ++ tailWord_5606394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606394).length < 2 ^ (prefixWord ++ tailWord_5606394).sum := by decide
  have hdescent : baseEnd_5606394 < baseStart_5606394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606421 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 6]
def baseStart_5606421 : Nat := 118140960795 + 5606421 * 2 ^ 59
def prefixEnd_5606421 : Nat := 4983230072969 + 3 ^ 40 * 5606421 * 2
def baseEnd_5606421 : Nat := 319865413828968287306005

theorem tailTrace_5606421 : CollatzResearch.WordTrace tailWord_5606421 prefixEnd_5606421 319865413828968287306005 := by
  unfold tailWord_5606421
  simp only [CollatzResearch.WordTrace]
  refine ⟨204482972821901692321403117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136321981881267794880935411 204482972821901692321403117)
  ·
    refine ⟨76681114808213134620526169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204482972821901692321403117 76681114808213134620526169)
    ·
      refine ⟨57510836106159850965394627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76681114808213134620526169 57510836106159850965394627)
      ·
        refine ⟨86266254159239776448091941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57510836106159850965394627 86266254159239776448091941)
        ·
          refine ⟨16174922654857458084017239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86266254159239776448091941 16174922654857458084017239)
          ·
            refine ⟨24262383982286187126025859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16174922654857458084017239 24262383982286187126025859)
            ·
              refine ⟨36393575973429280689038789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24262383982286187126025859 36393575973429280689038789)
              ·
                refine ⟨6823795495017990129194773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36393575973429280689038789 6823795495017990129194773)
                ·
                  refine ⟨319865413828968287306005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6823795495017990129194773 319865413828968287306005)
                  ·
                    rfl

theorem cell23_5606421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_5606421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606421 prefixEnd_5606421 := by exact prefixLift 5606421
  have htrace : WordTrace (prefixWord ++ tailWord_5606421) baseStart_5606421 baseEnd_5606421 := by
    simpa [prefixWord, tailWord_5606421, baseEnd_5606421] using wordTrace_append hprefix tailTrace_5606421
  have hstable : (prefixWord ++ tailWord_5606421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606421).length < 2 ^ (prefixWord ++ tailWord_5606421).sum := by decide
  have hdescent : baseEnd_5606421 < baseStart_5606421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606425 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 1, 4]
def baseStart_5606425 : Nat := 118140960795 + 5606425 * 2 ^ 59
def prefixEnd_5606425 : Nat := 4983230072969 + 3 ^ 40 * 5606425 * 2
def baseEnd_5606425 : Nat := 959596926127777523368009

theorem tailTrace_5606425 : CollatzResearch.WordTrace tailWord_5606425 prefixEnd_5606425 959596926127777523368009 := by
  unfold tailWord_5606425
  simp only [CollatzResearch.WordTrace]
  refine ⟨204483118713887201004548729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136322079142591467336365819 204483118713887201004548729)
  ·
    refine ⟨153362339035415400753411547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204483118713887201004548729 153362339035415400753411547)
    ·
      refine ⟨230043508553123101130117321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153362339035415400753411547 230043508553123101130117321)
      ·
        refine ⟨172532631414842325847587991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230043508553123101130117321 172532631414842325847587991)
        ·
          refine ⟨258798947122263488771381987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172532631414842325847587991 258798947122263488771381987)
          ·
            refine ⟨388198420683395233157072981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258798947122263488771381987 388198420683395233157072981)
            ·
              refine ⟨4549200242383537888559449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 388198420683395233157072981 4549200242383537888559449)
              ·
                refine ⟨3411900181787653416419587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4549200242383537888559449 3411900181787653416419587)
                ·
                  refine ⟨5117850272681480124629381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411900181787653416419587 5117850272681480124629381)
                  ·
                    refine ⟨959596926127777523368009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117850272681480124629381 959596926127777523368009)
                    ·
                      rfl

theorem cell23_5606425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 4].length) (baseStart_5606425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606425 prefixEnd_5606425 := by exact prefixLift 5606425
  have htrace : WordTrace (prefixWord ++ tailWord_5606425) baseStart_5606425 baseEnd_5606425 := by
    simpa [prefixWord, tailWord_5606425, baseEnd_5606425] using wordTrace_append hprefix tailTrace_5606425
  have hstable : (prefixWord ++ tailWord_5606425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606425).length < 2 ^ (prefixWord ++ tailWord_5606425).sum := by decide
  have hdescent : baseEnd_5606425 < baseStart_5606425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606444 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5606444 : Nat := 118140960795 + 5606444 * 2 ^ 59
def prefixEnd_5606444 : Nat := 4983230072969 + 3 ^ 40 * 5606444 * 2
def baseEnd_5606444 : Nat := 2878800534515767995766439

theorem tailTrace_5606444 : CollatzResearch.WordTrace tailWord_5606444 prefixEnd_5606444 2878800534515767995766439 := by
  unfold tailWord_5606444
  simp only [CollatzResearch.WordTrace]
  refine ⟨102241905850409183624745193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136322541133878911499660257 102241905850409183624745193)
  ·
    refine ⟨76681429387806887718558895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102241905850409183624745193 76681429387806887718558895)
    ·
      refine ⟨115022144081710331577838343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76681429387806887718558895 115022144081710331577838343)
      ·
        refine ⟨172533216122565497366757515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115022144081710331577838343 172533216122565497366757515)
        ·
          refine ⟨258799824183848246050136273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172533216122565497366757515 258799824183848246050136273)
          ·
            refine ⟨194099868137886184537602205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258799824183848246050136273 194099868137886184537602205)
            ·
              refine ⟨72787450551707319201600827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194099868137886184537602205 72787450551707319201600827)
              ·
                refine ⟨109181175827560978802401241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72787450551707319201600827 109181175827560978802401241)
                ·
                  refine ⟨81885881870670734101800931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109181175827560978802401241 81885881870670734101800931)
                  ·
                    refine ⟨122828822806006101152701397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81885881870670734101800931 122828822806006101152701397)
                    ·
                      refine ⟨2878800534515767995766439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122828822806006101152701397 2878800534515767995766439)
                      ·
                        rfl

theorem cell23_5606444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5606444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606444 prefixEnd_5606444 := by exact prefixLift 5606444
  have htrace : WordTrace (prefixWord ++ tailWord_5606444) baseStart_5606444 baseEnd_5606444 := by
    simpa [prefixWord, tailWord_5606444, baseEnd_5606444] using wordTrace_append hprefix tailTrace_5606444
  have hstable : (prefixWord ++ tailWord_5606444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606444).length < 2 ^ (prefixWord ++ tailWord_5606444).sum := by decide
  have hdescent : baseEnd_5606444 < baseStart_5606444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606448 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_5606448 : Nat := 118140960795 + 5606448 * 2 ^ 59
def prefixEnd_5606448 : Nat := 4983230072969 + 3 ^ 40 * 5606448 * 2
def baseEnd_5606448 : Nat := 2878802588438385980116421

theorem tailTrace_5606448 : CollatzResearch.WordTrace tailWord_5606448 prefixEnd_5606448 2878802588438385980116421 := by
  unfold tailWord_5606448
  simp only [CollatzResearch.WordTrace]
  refine ⟨102241978796401937966317999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136322638395202583955090665 102241978796401937966317999)
  ·
    refine ⟨153362968194602906949476999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102241978796401937966317999 153362968194602906949476999)
    ·
      refine ⟨230044452291904360424215499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153362968194602906949476999 230044452291904360424215499)
      ·
        refine ⟨345066678437856540636323249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230044452291904360424215499 345066678437856540636323249)
        ·
          refine ⟨258800008828392405477242437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345066678437856540636323249 258800008828392405477242437)
          ·
            refine ⟨48525001655323576026982957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258800008828392405477242437 48525001655323576026982957)
            ·
              refine ⟨18196875620746341010118609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48525001655323576026982957 18196875620746341010118609)
              ·
                refine ⟨13647656715559755757588957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18196875620746341010118609 13647656715559755757588957)
                ·
                  refine ⟨5117871268334908409095859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13647656715559755757588957 5117871268334908409095859)
                  ·
                    refine ⟨7676806902502362613643789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117871268334908409095859 7676806902502362613643789)
                    ·
                      refine ⟨2878802588438385980116421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676806902502362613643789 2878802588438385980116421)
                      ·
                        rfl

theorem cell23_5606448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_5606448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606448 prefixEnd_5606448 := by exact prefixLift 5606448
  have htrace : WordTrace (prefixWord ++ tailWord_5606448) baseStart_5606448 baseEnd_5606448 := by
    simpa [prefixWord, tailWord_5606448, baseEnd_5606448] using wordTrace_append hprefix tailTrace_5606448
  have hstable : (prefixWord ++ tailWord_5606448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606448).length < 2 ^ (prefixWord ++ tailWord_5606448).sum := by decide
  have hdescent : baseEnd_5606448 < baseStart_5606448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606451 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 1, 5]
def baseStart_5606451 : Nat := 118140960795 + 5606451 * 2 ^ 59
def prefixEnd_5606451 : Nat := 4983230072969 + 3 ^ 40 * 5606451 * 2
def baseEnd_5606451 : Nat := 959601376293449822792969

theorem tailTrace_5606451 : CollatzResearch.WordTrace tailWord_5606451 prefixEnd_5606451 959601376293449822792969 := by
  unfold tailWord_5606451
  simp only [CollatzResearch.WordTrace]
  refine ⟨204484067011793007444995207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136322711341195338296663471 204484067011793007444995207)
  ·
    refine ⟨306726100517689511167492811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204484067011793007444995207 306726100517689511167492811)
    ·
      refine ⟨460089150776534266751239217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306726100517689511167492811 460089150776534266751239217)
      ·
        refine ⟨345066863082400700063429413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460089150776534266751239217 345066863082400700063429413)
        ·
          refine ⟨64700036827950131261893015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345066863082400700063429413 64700036827950131261893015)
          ·
            refine ⟨97050055241925196892839523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64700036827950131261893015 97050055241925196892839523)
            ·
              refine ⟨145575082862887795339259285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97050055241925196892839523 145575082862887795339259285)
              ·
                refine ⟨6823832009197865406527779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145575082862887795339259285 6823832009197865406527779)
                ·
                  refine ⟨10235748013796798109791669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823832009197865406527779 10235748013796798109791669)
                  ·
                    refine ⟨959601376293449822792969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10235748013796798109791669 959601376293449822792969)
                    ·
                      rfl

theorem cell23_5606451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 5].length) (baseStart_5606451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606451 prefixEnd_5606451 := by exact prefixLift 5606451
  have htrace : WordTrace (prefixWord ++ tailWord_5606451) baseStart_5606451 baseEnd_5606451 := by
    simpa [prefixWord, tailWord_5606451, baseEnd_5606451] using wordTrace_append hprefix tailTrace_5606451
  have hstable : (prefixWord ++ tailWord_5606451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606451).length < 2 ^ (prefixWord ++ tailWord_5606451).sum := by decide
  have hdescent : baseEnd_5606451 < baseStart_5606451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606452 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5606452 : Nat := 118140960795 + 5606452 * 2 ^ 59
def prefixEnd_5606452 : Nat := 4983230072969 + 3 ^ 40 * 5606452 * 2
def baseEnd_5606452 : Nat := 2878804642361003964466403

theorem tailTrace_5606452 : CollatzResearch.WordTrace tailWord_5606452 prefixEnd_5606452 2878804642361003964466403 := by
  unfold tailWord_5606452
  simp only [CollatzResearch.WordTrace]
  refine ⟨102242051742394692307890805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136322735656526256410521073 102242051742394692307890805)
  ·
    refine ⟨9585192350849502403864763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102242051742394692307890805 9585192350849502403864763)
    ·
      refine ⟨14377788526274253605797145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9585192350849502403864763 14377788526274253605797145)
      ·
        refine ⟨10783341394705690204347859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14377788526274253605797145 10783341394705690204347859)
        ·
          refine ⟨16175012092058535306521789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783341394705690204347859 16175012092058535306521789)
          ·
            refine ⟨6065629534521950739945671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16175012092058535306521789 6065629534521950739945671)
            ·
              refine ⟨9098444301782926109918507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065629534521950739945671 9098444301782926109918507)
              ·
                refine ⟨13647666452674389164877761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9098444301782926109918507 13647666452674389164877761)
                ·
                  refine ⟨10235749839505791873658321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13647666452674389164877761 10235749839505791873658321)
                  ·
                    refine ⟨7676812379629343905243741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10235749839505791873658321 7676812379629343905243741)
                    ·
                      refine ⟨2878804642361003964466403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676812379629343905243741 2878804642361003964466403)
                      ·
                        rfl

theorem cell23_5606452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5606452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606452 prefixEnd_5606452 := by exact prefixLift 5606452
  have htrace : WordTrace (prefixWord ++ tailWord_5606452) baseStart_5606452 baseEnd_5606452 := by
    simpa [prefixWord, tailWord_5606452, baseEnd_5606452] using wordTrace_append hprefix tailTrace_5606452
  have hstable : (prefixWord ++ tailWord_5606452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606452).length < 2 ^ (prefixWord ++ tailWord_5606452).sum := by decide
  have hdescent : baseEnd_5606452 < baseStart_5606452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606482 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_5606482 : Nat := 118140960795 + 5606482 * 2 ^ 59
def prefixEnd_5606482 : Nat := 4983230072969 + 3 ^ 40 * 5606482 * 2
def baseEnd_5606482 : Nat := 2878820046780638847091265

theorem tailTrace_5606482 : CollatzResearch.WordTrace tailWord_5606482 prefixEnd_5606482 2878820046780638847091265 := by
  unfold tailWord_5606482
  simp only [CollatzResearch.WordTrace]
  refine ⟨51121299418670174934843425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136323465116453799826249133 51121299418670174934843425)
  ·
    refine ⟨38340974564002631201132569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51121299418670174934843425 38340974564002631201132569)
    ·
      refine ⟨28755730923001973400849427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38340974564002631201132569 28755730923001973400849427)
      ·
        refine ⟨43133596384502960101274141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28755730923001973400849427 43133596384502960101274141)
        ·
          refine ⟨16175098644188610037977803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43133596384502960101274141 16175098644188610037977803)
          ·
            refine ⟨24262647966282915056966705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16175098644188610037977803 24262647966282915056966705)
            ·
              refine ⟨18196985974712186292725029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24262647966282915056966705 18196985974712186292725029)
              ·
                refine ⟨3411934870258534929885943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18196985974712186292725029 3411934870258534929885943)
                ·
                  refine ⟨5117902305387802394828915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411934870258534929885943 5117902305387802394828915)
                  ·
                    refine ⟨7676853458081703592243373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5117902305387802394828915 7676853458081703592243373)
                    ·
                      refine ⟨2878820046780638847091265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676853458081703592243373 2878820046780638847091265)
                      ·
                        rfl

theorem cell23_5606482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_5606482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606482 prefixEnd_5606482 := by exact prefixLift 5606482
  have htrace : WordTrace (prefixWord ++ tailWord_5606482) baseStart_5606482 baseEnd_5606482 := by
    simpa [prefixWord, tailWord_5606482, baseEnd_5606482] using wordTrace_append hprefix tailTrace_5606482
  have hstable : (prefixWord ++ tailWord_5606482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606482).length < 2 ^ (prefixWord ++ tailWord_5606482).sum := by decide
  have hdescent : baseEnd_5606482 < baseStart_5606482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606501 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_5606501 : Nat := 118140960795 + 5606501 * 2 ^ 59
def prefixEnd_5606501 : Nat := 4983230072969 + 3 ^ 40 * 5606501 * 2
def baseEnd_5606501 : Nat := 2878829802913074272753677

theorem tailTrace_5606501 : CollatzResearch.WordTrace tailWord_5606501 prefixEnd_5606501 2878829802913074272753677 := by
  unfold tailWord_5606501
  simp only [CollatzResearch.WordTrace]
  refine ⟨204485890661611865984315357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136323927107741243989543571 204485890661611865984315357)
  ·
    refine ⟨76682208998104449744118259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204485890661611865984315357 76682208998104449744118259)
    ·
      refine ⟨115023313497156674616177389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76682208998104449744118259 115023313497156674616177389)
      ·
        refine ⟨43133742561433752981066521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115023313497156674616177389 43133742561433752981066521)
        ·
          refine ⟨32350306921075314735799891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43133742561433752981066521 32350306921075314735799891)
          ·
            refine ⟨48525460381612972103699837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32350306921075314735799891 48525460381612972103699837)
            ·
              refine ⟨18197047643104864538887439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48525460381612972103699837 18197047643104864538887439)
              ·
                refine ⟨27295571464657296808331159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18197047643104864538887439 27295571464657296808331159)
                ·
                  refine ⟨40943357196985945212496739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27295571464657296808331159 40943357196985945212496739)
                  ·
                    refine ⟨61415035795478917818745109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40943357196985945212496739 61415035795478917818745109)
                    ·
                      refine ⟨2878829802913074272753677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61415035795478917818745109 2878829802913074272753677)
                      ·
                        rfl

theorem cell23_5606501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_5606501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606501 prefixEnd_5606501 := by exact prefixLift 5606501
  have htrace : WordTrace (prefixWord ++ tailWord_5606501) baseStart_5606501 baseEnd_5606501 := by
    simpa [prefixWord, tailWord_5606501, baseEnd_5606501] using wordTrace_append hprefix tailTrace_5606501
  have hstable : (prefixWord ++ tailWord_5606501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606501).length < 2 ^ (prefixWord ++ tailWord_5606501).sum := by decide
  have hdescent : baseEnd_5606501 < baseStart_5606501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606505 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 3, 2, 2]
def baseStart_5606505 : Nat := 118140960795 + 5606505 * 2 ^ 59
def prefixEnd_5606505 : Nat := 4983230072969 + 3 ^ 40 * 5606505 * 2
def baseEnd_5606505 : Nat := 2878831856835692257103659

theorem tailTrace_5606505 : CollatzResearch.WordTrace tailWord_5606505 prefixEnd_5606505 2878831856835692257103659 := by
  unfold tailWord_5606505
  simp only [CollatzResearch.WordTrace]
  refine ⟨204486036553597374667460969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136324024369064916444973979 204486036553597374667460969)
  ·
    refine ⟨153364527415198031000595727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204486036553597374667460969 153364527415198031000595727)
    ·
      refine ⟨230046791122797046500893591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153364527415198031000595727 230046791122797046500893591)
      ·
        refine ⟨345070186684195569751340387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230046791122797046500893591 345070186684195569751340387)
        ·
          refine ⟨517605280026293354627010581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345070186684195569751340387 517605280026293354627010581)
          ·
            refine ⟨24262747501232500998141121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 517605280026293354627010581 24262747501232500998141121)
            ·
              refine ⟨18197060625924375748605841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24262747501232500998141121 18197060625924375748605841)
              ·
                refine ⟨13647795469443281811454381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18197060625924375748605841 13647795469443281811454381)
                ·
                  refine ⟨5117923301041230679295393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13647795469443281811454381 5117923301041230679295393)
                  ·
                    refine ⟨3838442475780923009471545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117923301041230679295393 3838442475780923009471545)
                    ·
                      refine ⟨2878831856835692257103659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838442475780923009471545 2878831856835692257103659)
                      ·
                        rfl

theorem cell23_5606505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 2, 2].length) (baseStart_5606505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606505 prefixEnd_5606505 := by exact prefixLift 5606505
  have htrace : WordTrace (prefixWord ++ tailWord_5606505) baseStart_5606505 baseEnd_5606505 := by
    simpa [prefixWord, tailWord_5606505, baseEnd_5606505] using wordTrace_append hprefix tailTrace_5606505
  have hstable : (prefixWord ++ tailWord_5606505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606505).length < 2 ^ (prefixWord ++ tailWord_5606505).sum := by decide
  have hdescent : baseEnd_5606505 < baseStart_5606505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606518 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5606518 : Nat := 118140960795 + 5606518 * 2 ^ 59
def prefixEnd_5606518 : Nat := 4983230072969 + 3 ^ 40 * 5606518 * 2
def baseEnd_5606518 : Nat := 2878838532084200706241099

theorem tailTrace_5606518 : CollatzResearch.WordTrace tailWord_5606518 prefixEnd_5606518 2878838532084200706241099 := by
  unfold tailWord_5606518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780406918909392367980263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136324340468366851925122805 12780406918909392367980263)
  ·
    refine ⟨19170610378364088551970395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12780406918909392367980263 19170610378364088551970395)
    ·
      refine ⟨28755915567546132827955593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19170610378364088551970395 28755915567546132827955593)
      ·
        refine ⟨21566936675659599620966695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28755915567546132827955593 21566936675659599620966695)
        ·
          refine ⟨32350405013489399431450043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21566936675659599620966695 32350405013489399431450043)
          ·
            refine ⟨48525607520234099147175065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32350405013489399431450043 48525607520234099147175065)
            ·
              refine ⟨36394205640175574360381299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48525607520234099147175065 36394205640175574360381299)
              ·
                refine ⟨54591308460263361540571949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36394205640175574360381299 54591308460263361540571949)
                ·
                  refine ⟨20471740672598760577714481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54591308460263361540571949 20471740672598760577714481)
                  ·
                    refine ⟨15353805504449070433285861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20471740672598760577714481 15353805504449070433285861)
                    ·
                      refine ⟨2878838532084200706241099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15353805504449070433285861 2878838532084200706241099)
                      ·
                        rfl

theorem cell23_5606518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5606518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606518 prefixEnd_5606518 := by exact prefixLift 5606518
  have htrace : WordTrace (prefixWord ++ tailWord_5606518) baseStart_5606518 baseEnd_5606518 := by
    simpa [prefixWord, tailWord_5606518, baseEnd_5606518] using wordTrace_append hprefix tailTrace_5606518
  have hstable : (prefixWord ++ tailWord_5606518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606518).length < 2 ^ (prefixWord ++ tailWord_5606518).sum := by decide
  have hdescent : baseEnd_5606518 < baseStart_5606518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606526 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5606526 : Nat := 118140960795 + 5606526 * 2 ^ 59
def prefixEnd_5606526 : Nat := 4983230072969 + 3 ^ 40 * 5606526 * 2
def baseEnd_5606526 : Nat := 2878842639929436674941063

theorem tailTrace_5606526 : CollatzResearch.WordTrace tailWord_5606526 prefixEnd_5606526 2878842639929436674941063 := by
  unfold tailWord_5606526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25560850310815161906746929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136324534991014196835983621 25560850310815161906746929)
  ·
    refine ⟨19170637733111371430060197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25560850310815161906746929 19170637733111371430060197)
    ·
      refine ⟨3594494574958382143136287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19170637733111371430060197 3594494574958382143136287)
      ·
        refine ⟨5391741862437573214704431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594494574958382143136287 5391741862437573214704431)
        ·
          refine ⟨8087612793656359822056647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391741862437573214704431 8087612793656359822056647)
          ·
            refine ⟨12131419190484539733084971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8087612793656359822056647 12131419190484539733084971)
            ·
              refine ⟨18197128785726809599627457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131419190484539733084971 18197128785726809599627457)
              ·
                refine ⟨13647846589295107199720593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18197128785726809599627457 13647846589295107199720593)
                ·
                  refine ⟨10235884941971330399790445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13647846589295107199720593 10235884941971330399790445)
                  ·
                    refine ⟨3838456853239248899921417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10235884941971330399790445 3838456853239248899921417)
                    ·
                      refine ⟨2878842639929436674941063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838456853239248899921417 2878842639929436674941063)
                      ·
                        rfl

theorem cell23_5606526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5606526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606526 prefixEnd_5606526 := by exact prefixLift 5606526
  have htrace : WordTrace (prefixWord ++ tailWord_5606526) baseStart_5606526 baseEnd_5606526 := by
    simpa [prefixWord, tailWord_5606526, baseEnd_5606526] using wordTrace_append hprefix tailTrace_5606526
  have hstable : (prefixWord ++ tailWord_5606526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606526).length < 2 ^ (prefixWord ++ tailWord_5606526).sum := by decide
  have hdescent : baseEnd_5606526 < baseStart_5606526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606559 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5606559 : Nat := 118140960795 + 5606559 * 2 ^ 59
def prefixEnd_5606559 : Nat := 4983230072969 + 3 ^ 40 * 5606559 * 2
def baseEnd_5606559 : Nat := 2878859584791035045828411

theorem tailTrace_5606559 : CollatzResearch.WordTrace tailWord_5606559 prefixEnd_5606559 2878859584791035045828411 := by
  unfold tailWord_5606559
  simp only [CollatzResearch.WordTrace]
  refine ⟨204488006095401741889926731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136325337396934494593284487 204488006095401741889926731)
  ·
    refine ⟨306732009143102612834890097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204488006095401741889926731 306732009143102612834890097)
    ·
      refine ⟨230049006857326959626167573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306732009143102612834890097 230049006857326959626167573)
      ·
        refine ⟨10783547196437201232476605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 230049006857326959626167573 10783547196437201232476605)
        ·
          refine ⟨4043830198663950462178727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10783547196437201232476605 4043830198663950462178727)
          ·
            refine ⟨6065745297995925693268091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043830198663950462178727 6065745297995925693268091)
            ·
              refine ⟨9098617946993888539902137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065745297995925693268091 9098617946993888539902137)
              ·
                refine ⟨6823963460245416404926603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9098617946993888539902137 6823963460245416404926603)
                ·
                  refine ⟨10235945190368124607389905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823963460245416404926603 10235945190368124607389905)
                  ·
                    refine ⟨7676958892776093455542429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10235945190368124607389905 7676958892776093455542429)
                    ·
                      refine ⟨2878859584791035045828411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7676958892776093455542429 2878859584791035045828411)
                      ·
                        rfl

theorem cell23_5606559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5606559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606559 prefixEnd_5606559 := by exact prefixLift 5606559
  have htrace : WordTrace (prefixWord ++ tailWord_5606559) baseStart_5606559 baseEnd_5606559 := by
    simpa [prefixWord, tailWord_5606559, baseEnd_5606559] using wordTrace_append hprefix tailTrace_5606559
  have hstable : (prefixWord ++ tailWord_5606559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606559).length < 2 ^ (prefixWord ++ tailWord_5606559).sum := by decide
  have hdescent : baseEnd_5606559 < baseStart_5606559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606565 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_5606565 : Nat := 118140960795 + 5606565 * 2 ^ 59
def prefixEnd_5606565 : Nat := 4983230072969 + 3 ^ 40 * 5606565 * 2
def baseEnd_5606565 : Nat := 2878862665674962022353383

theorem tailTrace_5606565 : CollatzResearch.WordTrace tailWord_5606565 prefixEnd_5606565 2878862665674962022353383 := by
  unfold tailWord_5606565
  simp only [CollatzResearch.WordTrace]
  refine ⟨204488224933380004914645149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136325483288920003276430099 204488224933380004914645149)
  ·
    refine ⟨76683084350017501842991931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204488224933380004914645149 76683084350017501842991931)
    ·
      refine ⟨115024626525026252764487897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76683084350017501842991931 115024626525026252764487897)
      ·
        refine ⟨86268469893769689573365923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115024626525026252764487897 86268469893769689573365923)
        ·
          refine ⟨129402704840654534360048885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86268469893769689573365923 129402704840654534360048885)
          ·
            refine ⟨12131503578811362596254583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129402704840654534360048885 12131503578811362596254583)
            ·
              refine ⟨18197255368217043894381875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131503578811362596254583 18197255368217043894381875)
              ·
                refine ⟨27295883052325565841572813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18197255368217043894381875 27295883052325565841572813)
                ·
                  refine ⟨10235956144622087190589805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27295883052325565841572813 10235956144622087190589805)
                  ·
                    refine ⟨3838483554233282696471177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10235956144622087190589805 3838483554233282696471177)
                    ·
                      refine ⟨2878862665674962022353383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838483554233282696471177 2878862665674962022353383)
                      ·
                        rfl

theorem cell23_5606565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_5606565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606565 prefixEnd_5606565 := by exact prefixLift 5606565
  have htrace : WordTrace (prefixWord ++ tailWord_5606565) baseStart_5606565 baseEnd_5606565 := by
    simpa [prefixWord, tailWord_5606565, baseEnd_5606565] using wordTrace_append hprefix tailTrace_5606565
  have hstable : (prefixWord ++ tailWord_5606565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606565).length < 2 ^ (prefixWord ++ tailWord_5606565).sum := by decide
  have hdescent : baseEnd_5606565 < baseStart_5606565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606635 : List Nat := [1, 1, 1, 1, 2, 7, 2, 3, 5]
def baseStart_5606635 : Nat := 118140960795 + 5606635 * 2 ^ 59
def prefixEnd_5606635 : Nat := 4983230072969 + 3 ^ 40 * 5606635 * 2
def baseEnd_5606635 : Nat := 319877623257864083164229

theorem tailTrace_5606635 : CollatzResearch.WordTrace tailWord_5606635 prefixEnd_5606635 319877623257864083164229 := by
  unfold tailWord_5606635
  simp only [CollatzResearch.WordTrace]
  refine ⟨204490778043126406869693359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136327185362084271246462239 204490778043126406869693359)
  ·
    refine ⟨306736167064689610304540039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204490778043126406869693359 306736167064689610304540039)
    ·
      refine ⟨460104250597034415456810059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306736167064689610304540039 460104250597034415456810059)
      ·
        refine ⟨690156375895551623185215089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460104250597034415456810059 690156375895551623185215089)
        ·
          refine ⟨517617281921663717388911317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690156375895551623185215089 517617281921663717388911317)
          ·
            refine ⟨12131655045038993376302609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 517617281921663717388911317 12131655045038993376302609)
            ·
              refine ⟨9098741283779245032226957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12131655045038993376302609 9098741283779245032226957)
              ·
                refine ⟨3412027981417216887085109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9098741283779245032226957 3412027981417216887085109)
                ·
                  refine ⟨319877623257864083164229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412027981417216887085109 319877623257864083164229)
                  ·
                    rfl

theorem cell23_5606635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 3, 5].length) (baseStart_5606635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606635 prefixEnd_5606635 := by exact prefixLift 5606635
  have htrace : WordTrace (prefixWord ++ tailWord_5606635) baseStart_5606635 baseEnd_5606635 := by
    simpa [prefixWord, tailWord_5606635, baseEnd_5606635] using wordTrace_append hprefix tailTrace_5606635
  have hstable : (prefixWord ++ tailWord_5606635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606635).length < 2 ^ (prefixWord ++ tailWord_5606635).sum := by decide
  have hdescent : baseEnd_5606635 < baseStart_5606635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606668 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5606668 : Nat := 118140960795 + 5606668 * 2 ^ 59
def prefixEnd_5606668 : Nat := 4983230072969 + 3 ^ 40 * 5606668 * 2
def baseEnd_5606668 : Nat := 2878915554182375119365409

theorem tailTrace_5606668 : CollatzResearch.WordTrace tailWord_5606668 prefixEnd_5606668 2878915554182375119365409 := by
  unfold tailWord_5606668
  simp only [CollatzResearch.WordTrace]
  refine ⟨102245990826003426752822329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136327987768004569003763105 102245990826003426752822329)
  ·
    refine ⟨76684493119502570064616747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102245990826003426752822329 76684493119502570064616747)
    ·
      refine ⟨115026739679253855096925121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76684493119502570064616747 115026739679253855096925121)
      ·
        refine ⟨86270054759440391322693841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115026739679253855096925121 86270054759440391322693841)
        ·
          refine ⟨64702541069580293492020381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86270054759440391322693841 64702541069580293492020381)
          ·
            refine ⟨24263452901092610059507643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64702541069580293492020381 24263452901092610059507643)
            ·
              refine ⟨36395179351638915089261465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24263452901092610059507643 36395179351638915089261465)
              ·
                refine ⟨27296384513729186316946099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36395179351638915089261465 27296384513729186316946099)
                ·
                  refine ⟨40944576770593779475419149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27296384513729186316946099 40944576770593779475419149)
                  ·
                    refine ⟨15354216288972667303282181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40944576770593779475419149 15354216288972667303282181)
                    ·
                      refine ⟨2878915554182375119365409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15354216288972667303282181 2878915554182375119365409)
                      ·
                        rfl

theorem cell23_5606668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5606668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606668 prefixEnd_5606668 := by exact prefixLift 5606668
  have htrace : WordTrace (prefixWord ++ tailWord_5606668) baseStart_5606668 baseEnd_5606668 := by
    simpa [prefixWord, tailWord_5606668, baseEnd_5606668] using wordTrace_append hprefix tailTrace_5606668
  have hstable : (prefixWord ++ tailWord_5606668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606668).length < 2 ^ (prefixWord ++ tailWord_5606668).sum := by decide
  have hdescent : baseEnd_5606668 < baseStart_5606668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606685 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5606685 : Nat := 118140960795 + 5606685 * 2 ^ 59
def prefixEnd_5606685 : Nat := 4983230072969 + 3 ^ 40 * 5606685 * 2
def baseEnd_5606685 : Nat := 2878924283353501552852831

theorem tailTrace_5606685 : CollatzResearch.WordTrace tailWord_5606685 prefixEnd_5606685 2878924283353501552852831 := by
  unfold tailWord_5606685
  simp only [CollatzResearch.WordTrace]
  refine ⟨204492601692945265409013509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136328401128630176939342339 204492601692945265409013509)
  ·
    refine ⟨38342362817427237264190033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204492601692945265409013509 38342362817427237264190033)
    ·
      refine ⟨28756772113070427948142525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38342362817427237264190033 28756772113070427948142525)
      ·
        refine ⟨10783789542401410480553447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28756772113070427948142525 10783789542401410480553447)
        ·
          refine ⟨16175684313602115720830171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783789542401410480553447 16175684313602115720830171)
          ·
            refine ⟨24263526470403173581245257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16175684313602115720830171 24263526470403173581245257)
            ·
              refine ⟨18197644852802380185933943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24263526470403173581245257 18197644852802380185933943)
              ·
                refine ⟨27296467279203570278900915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18197644852802380185933943 27296467279203570278900915)
                ·
                  refine ⟨40944700918805355418351373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27296467279203570278900915 40944700918805355418351373)
                  ·
                    refine ⟨15354262844552008281881765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40944700918805355418351373 15354262844552008281881765)
                    ·
                      refine ⟨2878924283353501552852831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15354262844552008281881765 2878924283353501552852831)
                      ·
                        rfl

theorem cell23_5606685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5606685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606685 prefixEnd_5606685 := by exact prefixLift 5606685
  have htrace : WordTrace (prefixWord ++ tailWord_5606685) baseStart_5606685 baseEnd_5606685 := by
    simpa [prefixWord, tailWord_5606685, baseEnd_5606685] using wordTrace_append hprefix tailTrace_5606685
  have hstable : (prefixWord ++ tailWord_5606685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606685).length < 2 ^ (prefixWord ++ tailWord_5606685).sum := by decide
  have hdescent : baseEnd_5606685 < baseStart_5606685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606686 : List Nat := [4, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_5606686 : Nat := 118140960795 + 5606686 * 2 ^ 59
def prefixEnd_5606686 : Nat := 4983230072969 + 3 ^ 40 * 5606686 * 2
def baseEnd_5606686 : Nat := 319880532981572894326703

theorem tailTrace_5606686 : CollatzResearch.WordTrace tailWord_5606686 prefixEnd_5606686 319880532981572894326703 := by
  unfold tailWord_5606686
  simp only [CollatzResearch.WordTrace]
  refine ⟨25561579770742705322474989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136328425443961095053199941 25561579770742705322474989)
  ·
    refine ⟨9585592414028514495928121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25561579770742705322474989 9585592414028514495928121)
    ·
      refine ⟨7189194310521385871946091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9585592414028514495928121 7189194310521385871946091)
      ·
        refine ⟨10783791465782078807919137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189194310521385871946091 10783791465782078807919137)
        ·
          refine ⟨8087843599336559105939353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10783791465782078807919137 8087843599336559105939353)
          ·
            refine ⟨6065882699502419329454515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087843599336559105939353 6065882699502419329454515)
            ·
              refine ⟨9098824049253628994181773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065882699502419329454515 9098824049253628994181773)
              ·
                refine ⟨3412059018470110872818165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9098824049253628994181773 3412059018470110872818165)
                ·
                  refine ⟨319880532981572894326703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412059018470110872818165 319880532981572894326703)
                  ·
                    rfl

theorem cell23_5606686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_5606686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606686 prefixEnd_5606686 := by exact prefixLift 5606686
  have htrace : WordTrace (prefixWord ++ tailWord_5606686) baseStart_5606686 baseEnd_5606686 := by
    simpa [prefixWord, tailWord_5606686, baseEnd_5606686] using wordTrace_append hprefix tailTrace_5606686
  have hstable : (prefixWord ++ tailWord_5606686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606686).length < 2 ^ (prefixWord ++ tailWord_5606686).sum := by decide
  have hdescent : baseEnd_5606686 < baseStart_5606686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606705 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_5606705 : Nat := 118140960795 + 5606705 * 2 ^ 59
def prefixEnd_5606705 : Nat := 4983230072969 + 3 ^ 40 * 5606705 * 2
def baseEnd_5606705 : Nat := 2878934552966591474602739

theorem tailTrace_5606705 : CollatzResearch.WordTrace tailWord_5606705 prefixEnd_5606705 2878934552966591474602739 := by
  unfold tailWord_5606705
  simp only [CollatzResearch.WordTrace]
  refine ⟨204493331152872808824741569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136328887435248539216494379 204493331152872808824741569)
  ·
    refine ⟨153369998364654606618556177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204493331152872808824741569 153369998364654606618556177)
    ·
      refine ⟨115027498773490954963917133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153369998364654606618556177 115027498773490954963917133)
      ·
        refine ⟨43135312040059108111468925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115027498773490954963917133 43135312040059108111468925)
        ·
          refine ⟨16175742015022165541800847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43135312040059108111468925 16175742015022165541800847)
          ·
            refine ⟨24263613022533248312701271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16175742015022165541800847 24263613022533248312701271)
            ·
              refine ⟨36395419533799872469051907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24263613022533248312701271 36395419533799872469051907)
              ·
                refine ⟨54593129300699808703577861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36395419533799872469051907 54593129300699808703577861)
                ·
                  refine ⟨10236211743881214131920849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54593129300699808703577861 10236211743881214131920849)
                  ·
                    refine ⟨7677158807910910598940637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10236211743881214131920849 7677158807910910598940637)
                    ·
                      refine ⟨2878934552966591474602739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677158807910910598940637 2878934552966591474602739)
                      ·
                        rfl

theorem cell23_5606705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_5606705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606705 prefixEnd_5606705 := by exact prefixLift 5606705
  have htrace : WordTrace (prefixWord ++ tailWord_5606705) baseStart_5606705 baseEnd_5606705 := by
    simpa [prefixWord, tailWord_5606705, baseEnd_5606705] using wordTrace_append hprefix tailTrace_5606705
  have hstable : (prefixWord ++ tailWord_5606705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606705).length < 2 ^ (prefixWord ++ tailWord_5606705).sum := by decide
  have hdescent : baseEnd_5606705 < baseStart_5606705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606745 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 5, 2]
def baseStart_5606745 : Nat := 118140960795 + 5606745 * 2 ^ 59
def prefixEnd_5606745 : Nat := 4983230072969 + 3 ^ 40 * 5606745 * 2
def baseEnd_5606745 : Nat := 2878955092192771318102555

theorem tailTrace_5606745 : CollatzResearch.WordTrace tailWord_5606745 prefixEnd_5606745 2878955092192771318102555 := by
  unfold tailWord_5606745
  simp only [CollatzResearch.WordTrace]
  refine ⟨204494790072727895656197689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136329860048485263770798459 204494790072727895656197689)
  ·
    refine ⟨153371092554545921742148267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204494790072727895656197689 153371092554545921742148267)
    ·
      refine ⟨230056638831818882613222401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153371092554545921742148267 230056638831818882613222401)
      ·
        refine ⟨172542479123864161959916801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230056638831818882613222401 172542479123864161959916801)
        ·
          refine ⟨129406859342898121469937601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172542479123864161959916801 129406859342898121469937601)
          ·
            refine ⟨97055144507173591102453201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129406859342898121469937601 97055144507173591102453201)
            ·
              refine ⟨72791358380380193326839901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97055144507173591102453201 72791358380380193326839901)
              ·
                refine ⟨27296759392642572497564963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72791358380380193326839901 27296759392642572497564963)
                ·
                  refine ⟨40945139088963858746347445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27296759392642572497564963 40945139088963858746347445)
                  ·
                    refine ⟨3838606789590361757470073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40945139088963858746347445 3838606789590361757470073)
                    ·
                      refine ⟨2878955092192771318102555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838606789590361757470073 2878955092192771318102555)
                      ·
                        rfl

theorem cell23_5606745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 5, 2].length) (baseStart_5606745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606745 prefixEnd_5606745 := by exact prefixLift 5606745
  have htrace : WordTrace (prefixWord ++ tailWord_5606745) baseStart_5606745 baseEnd_5606745 := by
    simpa [prefixWord, tailWord_5606745, baseEnd_5606745] using wordTrace_append hprefix tailTrace_5606745
  have hstable : (prefixWord ++ tailWord_5606745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606745).length < 2 ^ (prefixWord ++ tailWord_5606745).sum := by decide
  have hdescent : baseEnd_5606745 < baseStart_5606745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606768 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_5606768 : Nat := 118140960795 + 5606768 * 2 ^ 59
def prefixEnd_5606768 : Nat := 4983230072969 + 3 ^ 40 * 5606768 * 2
def baseEnd_5606768 : Nat := 959655634082608242704983

theorem tailTrace_5606768 : CollatzResearch.WordTrace tailWord_5606768 prefixEnd_5606768 959655634082608242704983 := by
  unfold tailWord_5606768
  simp only [CollatzResearch.WordTrace]
  refine ⟨102247814475822285292142479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136330419301096380389523305 102247814475822285292142479)
  ·
    refine ⟨153371721713733427938213719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102247814475822285292142479 153371721713733427938213719)
    ·
      refine ⟨230057582570600141907320579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153371721713733427938213719 230057582570600141907320579)
      ·
        refine ⟨345086373855900212860980869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230057582570600141907320579 345086373855900212860980869)
        ·
          refine ⟨64703695097981289911433913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345086373855900212860980869 64703695097981289911433913)
          ·
            refine ⟨48527771323485967433575435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64703695097981289911433913 48527771323485967433575435)
            ·
              refine ⟨72791656985228951150363153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48527771323485967433575435 72791656985228951150363153)
              ·
                refine ⟨54593742738921713362772365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72791656985228951150363153 54593742738921713362772365)
                ·
                  refine ⟨20472653527095642511039637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54593742738921713362772365 20472653527095642511039637)
                  ·
                    refine ⟨959655634082608242704983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20472653527095642511039637 959655634082608242704983)
                    ·
                      rfl

theorem cell23_5606768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_5606768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606768 prefixEnd_5606768 := by exact prefixLift 5606768
  have htrace : WordTrace (prefixWord ++ tailWord_5606768) baseStart_5606768 baseEnd_5606768 := by
    simpa [prefixWord, tailWord_5606768, baseEnd_5606768] using wordTrace_append hprefix tailTrace_5606768
  have hstable : (prefixWord ++ tailWord_5606768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606768).length < 2 ^ (prefixWord ++ tailWord_5606768).sum := by decide
  have hdescent : baseEnd_5606768 < baseStart_5606768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606786 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5606786 : Nat := 118140960795 + 5606786 * 2 ^ 59
def prefixEnd_5606786 : Nat := 4983230072969 + 3 ^ 40 * 5606786 * 2
def baseEnd_5606786 : Nat := 2878976144899605657689867

theorem tailTrace_5606786 : CollatzResearch.WordTrace tailWord_5606786 prefixEnd_5606786 2878976144899605657689867 := by
  unfold tailWord_5606786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51124071366394839914610053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136330856977052906438960141 51124071366394839914610053)
  ·
    refine ⟨9585763381199032483989385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51124071366394839914610053 9585763381199032483989385)
    ·
      refine ⟨7189322535899274362992039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9585763381199032483989385 7189322535899274362992039)
      ·
        refine ⟨10783983803848911544488059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189322535899274362992039 10783983803848911544488059)
        ·
          refine ⟨16175975705773367316732089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10783983803848911544488059 16175975705773367316732089)
          ·
            refine ⟨12131981779330025487549067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16175975705773367316732089 12131981779330025487549067)
            ·
              refine ⟨18197972668995038231323601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12131981779330025487549067 18197972668995038231323601)
              ·
                refine ⟨13648479501746278673492701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18197972668995038231323601 13648479501746278673492701)
                ·
                  refine ⟨5118179813154854502559763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13648479501746278673492701 5118179813154854502559763)
                  ·
                    refine ⟨7677269719732281753839645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118179813154854502559763 7677269719732281753839645)
                    ·
                      refine ⟨2878976144899605657689867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677269719732281753839645 2878976144899605657689867)
                      ·
                        rfl

theorem cell23_5606786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5606786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606786 prefixEnd_5606786 := by exact prefixLift 5606786
  have htrace : WordTrace (prefixWord ++ tailWord_5606786) baseStart_5606786 baseEnd_5606786 := by
    simpa [prefixWord, tailWord_5606786, baseEnd_5606786] using wordTrace_append hprefix tailTrace_5606786
  have hstable : (prefixWord ++ tailWord_5606786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606786).length < 2 ^ (prefixWord ++ tailWord_5606786).sum := by decide
  have hdescent : baseEnd_5606786 < baseStart_5606786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606795 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3]
def baseStart_5606795 : Nat := 118140960795 + 5606795 * 2 ^ 59
def prefixEnd_5606795 : Nat := 4983230072969 + 3 ^ 40 * 5606795 * 2
def baseEnd_5606795 : Nat := 2878980766225496122477325

theorem tailTrace_5606795 : CollatzResearch.WordTrace tailWord_5606795 prefixEnd_5606795 2878980766225496122477325 := by
  unfold tailWord_5606795
  simp only [CollatzResearch.WordTrace]
  refine ⟨204496613722546754195517839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136331075815031169463678559 204496613722546754195517839)
  ·
    refine ⟨306744920583820131293276759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204496613722546754195517839 306744920583820131293276759)
    ·
      refine ⟨460117380875730196939915139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306744920583820131293276759 460117380875730196939915139)
      ·
        refine ⟨690176071313595295409872709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460117380875730196939915139 690176071313595295409872709)
        ·
          refine ⟨129408013371299117889351133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 690176071313595295409872709 129408013371299117889351133)
          ·
            refine ⟨48528005014237169208506675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129408013371299117889351133 48528005014237169208506675)
            ·
              refine ⟨72792007521355753812760013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48528005014237169208506675 72792007521355753812760013)
              ·
                refine ⟨27297002820508407679785005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72792007521355753812760013 27297002820508407679785005)
                ·
                  refine ⟨10236376057690652879919377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27297002820508407679785005 10236376057690652879919377)
                  ·
                    refine ⟨7677282043267989659939533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10236376057690652879919377 7677282043267989659939533)
                    ·
                      refine ⟨2878980766225496122477325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677282043267989659939533 2878980766225496122477325)
                      ·
                        rfl

theorem cell23_5606795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 3].length) (baseStart_5606795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606795 prefixEnd_5606795 := by exact prefixLift 5606795
  have htrace : WordTrace (prefixWord ++ tailWord_5606795) baseStart_5606795 baseEnd_5606795 := by
    simpa [prefixWord, tailWord_5606795, baseEnd_5606795] using wordTrace_append hprefix tailTrace_5606795
  have hstable : (prefixWord ++ tailWord_5606795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606795).length < 2 ^ (prefixWord ++ tailWord_5606795).sum := by decide
  have hdescent : baseEnd_5606795 < baseStart_5606795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606805 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_5606805 : Nat := 118140960795 + 5606805 * 2 ^ 59
def prefixEnd_5606805 : Nat := 4983230072969 + 3 ^ 40 * 5606805 * 2
def baseEnd_5606805 : Nat := 2878985901032041083352279

theorem tailTrace_5606805 : CollatzResearch.WordTrace tailWord_5606805 prefixEnd_5606805 2878985901032041083352279 := by
  unfold tailWord_5606805
  simp only [CollatzResearch.WordTrace]
  refine ⟨204496978452510525903381869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136331318968340350602254579 204496978452510525903381869)
  ·
    refine ⟨76686366919691447213768201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204496978452510525903381869 76686366919691447213768201)
    ·
      refine ⟨57514775189768585410326151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76686366919691447213768201 57514775189768585410326151)
      ·
        refine ⟨86272162784652878115489227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57514775189768585410326151 86272162784652878115489227)
        ·
          refine ⟨129408244176979317173233841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86272162784652878115489227 129408244176979317173233841)
          ·
            refine ⟨97056183132734487879925381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129408244176979317173233841 97056183132734487879925381)
            ·
              refine ⟨18198034337387716477486009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97056183132734487879925381 18198034337387716477486009)
              ·
                refine ⟨13648525753040787358114507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18198034337387716477486009 13648525753040787358114507)
                ·
                  refine ⟨20472788629561181037171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13648525753040787358114507 20472788629561181037171761)
                  ·
                    refine ⟨15354591472170885777878821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20472788629561181037171761 15354591472170885777878821)
                    ·
                      refine ⟨2878985901032041083352279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15354591472170885777878821 2878985901032041083352279)
                      ·
                        rfl

theorem cell23_5606805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_5606805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606805 prefixEnd_5606805 := by exact prefixLift 5606805
  have htrace : WordTrace (prefixWord ++ tailWord_5606805) baseStart_5606805 baseEnd_5606805 := by
    simpa [prefixWord, tailWord_5606805, baseEnd_5606805] using wordTrace_append hprefix tailTrace_5606805
  have hstable : (prefixWord ++ tailWord_5606805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606805).length < 2 ^ (prefixWord ++ tailWord_5606805).sum := by decide
  have hdescent : baseEnd_5606805 < baseStart_5606805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606809 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 1, 1, 4]
def baseStart_5606809 : Nat := 118140960795 + 5606809 * 2 ^ 59
def prefixEnd_5606809 : Nat := 4983230072969 + 3 ^ 40 * 5606809 * 2
def baseEnd_5606809 : Nat := 2878987954954659067702261

theorem tailTrace_5606809 : CollatzResearch.WordTrace tailWord_5606809 prefixEnd_5606809 2878987954954659067702261 := by
  unfold tailWord_5606809
  simp only [CollatzResearch.WordTrace]
  refine ⟨204497124344496034586527481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136331416229664023057684987 204497124344496034586527481)
  ·
    refine ⟨153372843258372025939895611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204497124344496034586527481 153372843258372025939895611)
    ·
      refine ⟨230059264887558038909843417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153372843258372025939895611 230059264887558038909843417)
      ·
        refine ⟨172544448665668529182382563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230059264887558038909843417 172544448665668529182382563)
        ·
          refine ⟨258816672998502793773573845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172544448665668529182382563 258816672998502793773573845)
          ·
            refine ⟨6066015773402409229068137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 258816672998502793773573845 6066015773402409229068137)
            ·
              refine ⟨4549511830051806921801103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6066015773402409229068137 4549511830051806921801103)
              ·
                refine ⟨6824267745077710382701655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4549511830051806921801103 6824267745077710382701655)
                ·
                  refine ⟨10236401617616565574052483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824267745077710382701655 10236401617616565574052483)
                  ·
                    refine ⟨15354602426424848361078725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10236401617616565574052483 15354602426424848361078725)
                    ·
                      refine ⟨2878987954954659067702261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15354602426424848361078725 2878987954954659067702261)
                      ·
                        rfl

theorem cell23_5606809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 1, 4].length) (baseStart_5606809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606809 prefixEnd_5606809 := by exact prefixLift 5606809
  have htrace : WordTrace (prefixWord ++ tailWord_5606809) baseStart_5606809 baseEnd_5606809 := by
    simpa [prefixWord, tailWord_5606809, baseEnd_5606809] using wordTrace_append hprefix tailTrace_5606809
  have hstable : (prefixWord ++ tailWord_5606809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606809).length < 2 ^ (prefixWord ++ tailWord_5606809).sum := by decide
  have hdescent : baseEnd_5606809 < baseStart_5606809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606828 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_5606828 : Nat := 118140960795 + 5606828 * 2 ^ 59
def prefixEnd_5606828 : Nat := 4983230072969 + 3 ^ 40 * 5606828 * 2
def baseEnd_5606828 : Nat := 959665903695698164454891

theorem tailTrace_5606828 : CollatzResearch.WordTrace tailWord_5606828 prefixEnd_5606828 959665903695698164454891 := by
  unfold tailWord_5606828
  simp only [CollatzResearch.WordTrace]
  refine ⟨102248908665713600415734569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136331878220951467220979425 102248908665713600415734569)
  ·
    refine ⟨76686681499285200311800927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102248908665713600415734569 76686681499285200311800927)
    ·
      refine ⟨115030022248927800467701391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76686681499285200311800927 115030022248927800467701391)
      ·
        refine ⟨172545033373391700701552087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115030022248927800467701391 172545033373391700701552087)
        ·
          refine ⟨258817550060087551052328131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172545033373391700701552087 258817550060087551052328131)
          ·
            refine ⟨388226325090131326578492197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258817550060087551052328131 388226325090131326578492197)
            ·
              refine ⟨72792435954399623733467287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 388226325090131326578492197 72792435954399623733467287)
              ·
                refine ⟨109188653931599435600200931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72792435954399623733467287 109188653931599435600200931)
                ·
                  refine ⟨163782980897399153400301397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109188653931599435600200931 163782980897399153400301397)
                  ·
                    refine ⟨959665903695698164454891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163782980897399153400301397 959665903695698164454891)
                    ·
                      rfl

theorem cell23_5606828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_5606828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606828 prefixEnd_5606828 := by exact prefixLift 5606828
  have htrace : WordTrace (prefixWord ++ tailWord_5606828) baseStart_5606828 baseEnd_5606828 := by
    simpa [prefixWord, tailWord_5606828, baseEnd_5606828] using wordTrace_append hprefix tailTrace_5606828
  have hstable : (prefixWord ++ tailWord_5606828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606828).length < 2 ^ (prefixWord ++ tailWord_5606828).sum := by decide
  have hdescent : baseEnd_5606828 < baseStart_5606828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606869 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_5606869 : Nat := 118140960795 + 5606869 * 2 ^ 59
def prefixEnd_5606869 : Nat := 4983230072969 + 3 ^ 40 * 5606869 * 2
def baseEnd_5606869 : Nat := 2879018763793928832951985

theorem tailTrace_5606869 : CollatzResearch.WordTrace tailWord_5606869 prefixEnd_5606869 2879018763793928832951985 := by
  unfold tailWord_5606869
  simp only [CollatzResearch.WordTrace]
  refine ⟨204499312724278664833711661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136332875149519109889141107 204499312724278664833711661)
  ·
    refine ⟨76687242271604499312641873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204499312724278664833711661 76687242271604499312641873)
    ·
      refine ⟨57515431703703374484481405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76687242271604499312641873 57515431703703374484481405)
      ·
        refine ⟨21568286888888765431680527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57515431703703374484481405 21568286888888765431680527)
        ·
          refine ⟨32352430333333148147520791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21568286888888765431680527 32352430333333148147520791)
          ·
            refine ⟨48528645499999722221281187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32352430333333148147520791 48528645499999722221281187)
            ·
              refine ⟨72792968249999583331921781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48528645499999722221281187 72792968249999583331921781)
              ·
                refine ⟨6824340773437460937367667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72792968249999583331921781 6824340773437460937367667)
                ·
                  refine ⟨10236511160156191406051501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824340773437460937367667 10236511160156191406051501)
                  ·
                    refine ⟨3838691685058571777269313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10236511160156191406051501 3838691685058571777269313)
                    ·
                      refine ⟨2879018763793928832951985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838691685058571777269313 2879018763793928832951985)
                      ·
                        rfl

theorem cell23_5606869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_5606869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606869 prefixEnd_5606869 := by exact prefixLift 5606869
  have htrace : WordTrace (prefixWord ++ tailWord_5606869) baseStart_5606869 baseEnd_5606869 := by
    simpa [prefixWord, tailWord_5606869, baseEnd_5606869] using wordTrace_append hprefix tailTrace_5606869
  have hstable : (prefixWord ++ tailWord_5606869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606869).length < 2 ^ (prefixWord ++ tailWord_5606869).sum := by decide
  have hdescent : baseEnd_5606869 < baseStart_5606869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606895 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4]
def baseStart_5606895 : Nat := 118140960795 + 5606895 * 2 ^ 59
def prefixEnd_5606895 : Nat := 4983230072969 + 3 ^ 40 * 5606895 * 2
def baseEnd_5606895 : Nat := 2879032114290945731226865

theorem tailTrace_5606895 : CollatzResearch.WordTrace tailWord_5606895 prefixEnd_5606895 2879032114290945731226865 := by
  unfold tailWord_5606895
  simp only [CollatzResearch.WordTrace]
  refine ⟨204500261022184471274158139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136333507348122980849438759 204500261022184471274158139)
  ·
    refine ⟨306750391533276706911237209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204500261022184471274158139 306750391533276706911237209)
    ·
      refine ⟨230062793649957530183427907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306750391533276706911237209 230062793649957530183427907)
      ·
        refine ⟨345094190474936295275141861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230062793649957530183427907 345094190474936295275141861)
        ·
          refine ⟨64705160714050555364089099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345094190474936295275141861 64705160714050555364089099)
          ·
            refine ⟨97057741071075833046133649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64705160714050555364089099 97057741071075833046133649)
            ·
              refine ⟨72793305803306874784600237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97057741071075833046133649 72793305803306874784600237)
              ·
                refine ⟨27297489676240078044225089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72793305803306874784600237 27297489676240078044225089)
                ·
                  refine ⟨20473117257180058533168817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27297489676240078044225089 20473117257180058533168817)
                  ·
                    refine ⟨15354837942885043899876613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20473117257180058533168817 15354837942885043899876613)
                    ·
                      refine ⟨2879032114290945731226865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15354837942885043899876613 2879032114290945731226865)
                      ·
                        rfl

theorem cell23_5606895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_5606895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606895 prefixEnd_5606895 := by exact prefixLift 5606895
  have htrace : WordTrace (prefixWord ++ tailWord_5606895) baseStart_5606895 baseEnd_5606895 := by
    simpa [prefixWord, tailWord_5606895, baseEnd_5606895] using wordTrace_append hprefix tailTrace_5606895
  have hstable : (prefixWord ++ tailWord_5606895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606895).length < 2 ^ (prefixWord ++ tailWord_5606895).sum := by decide
  have hdescent : baseEnd_5606895 < baseStart_5606895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606902 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_5606902 : Nat := 118140960795 + 5606902 * 2 ^ 59
def prefixEnd_5606902 : Nat := 4983230072969 + 3 ^ 40 * 5606902 * 2
def baseEnd_5606902 : Nat := 2879035708655527203839333

theorem tailTrace_5606902 : CollatzResearch.WordTrace tailWord_5606902 prefixEnd_5606902 2879035708655527203839333 := by
  unfold tailWord_5606902
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781282270822444466853935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136333677555439407646441973 12781282270822444466853935)
  ·
    refine ⟨19171923406233666700280903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12781282270822444466853935 19171923406233666700280903)
    ·
      refine ⟨28757885109350500050421355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19171923406233666700280903 28757885109350500050421355)
      ·
        refine ⟨43136827664025750075632033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28757885109350500050421355 43136827664025750075632033)
        ·
          refine ⟨32352620748019312556724025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43136827664025750075632033 32352620748019312556724025)
          ·
            refine ⟨24264465561014484417543019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32352620748019312556724025 24264465561014484417543019)
            ·
              refine ⟨36396698341521726626314529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24264465561014484417543019 36396698341521726626314529)
              ·
                refine ⟨27297523756141294969735897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36396698341521726626314529 27297523756141294969735897)
                ·
                  refine ⟨20473142817105971227301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27297523756141294969735897 20473142817105971227301923)
                  ·
                    refine ⟨30709714225658956840952885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20473142817105971227301923 30709714225658956840952885)
                    ·
                      refine ⟨2879035708655527203839333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30709714225658956840952885 2879035708655527203839333)
                      ·
                        rfl

theorem cell23_5606902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_5606902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606902 prefixEnd_5606902 := by exact prefixLift 5606902
  have htrace : WordTrace (prefixWord ++ tailWord_5606902) baseStart_5606902 baseEnd_5606902 := by
    simpa [prefixWord, tailWord_5606902, baseEnd_5606902] using wordTrace_append hprefix tailTrace_5606902
  have hstable : (prefixWord ++ tailWord_5606902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606902).length < 2 ^ (prefixWord ++ tailWord_5606902).sum := by decide
  have hdescent : baseEnd_5606902 < baseStart_5606902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606915 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3]
def baseStart_5606915 : Nat := 118140960795 + 5606915 * 2 ^ 59
def prefixEnd_5606915 : Nat := 4983230072969 + 3 ^ 40 * 5606915 * 2
def baseEnd_5606915 : Nat := 2879042383904035652976773

theorem tailTrace_5606915 : CollatzResearch.WordTrace tailWord_5606915 prefixEnd_5606915 2879042383904035652976773 := by
  unfold tailWord_5606915
  simp only [CollatzResearch.WordTrace]
  refine ⟨204500990482112014689886199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136333993654741343126590799 204500990482112014689886199)
  ·
    refine ⟨306751485723168022034829299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204500990482112014689886199 306751485723168022034829299)
    ·
      refine ⟨460127228584752033052243949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306751485723168022034829299 460127228584752033052243949)
      ·
        refine ⟨172547710719282012394591481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460127228584752033052243949 172547710719282012394591481)
        ·
          refine ⟨129410783039461509295943611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172547710719282012394591481 129410783039461509295943611)
          ·
            refine ⟨194116174559192263943915417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129410783039461509295943611 194116174559192263943915417)
            ·
              refine ⟨145587130919394197957936563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194116174559192263943915417 145587130919394197957936563)
              ·
                refine ⟨218380696379091296936904845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145587130919394197957936563 218380696379091296936904845)
                ·
                  refine ⟨81892761142159236351339317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218380696379091296936904845 81892761142159236351339317)
                  ·
                    refine ⟨7677446357077428407938061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81892761142159236351339317 7677446357077428407938061)
                    ·
                      refine ⟨2879042383904035652976773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677446357077428407938061 2879042383904035652976773)
                      ·
                        rfl

theorem cell23_5606915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_5606915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606915 prefixEnd_5606915 := by exact prefixLift 5606915
  have htrace : WordTrace (prefixWord ++ tailWord_5606915) baseStart_5606915 baseEnd_5606915 := by
    simpa [prefixWord, tailWord_5606915, baseEnd_5606915] using wordTrace_append hprefix tailTrace_5606915
  have hstable : (prefixWord ++ tailWord_5606915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606915).length < 2 ^ (prefixWord ++ tailWord_5606915).sum := by decide
  have hdescent : baseEnd_5606915 < baseStart_5606915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606916 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5606916 : Nat := 118140960795 + 5606916 * 2 ^ 59
def prefixEnd_5606916 : Nat := 4983230072969 + 3 ^ 40 * 5606916 * 2
def baseEnd_5606916 : Nat := 2879042897384690149064269

theorem tailTrace_5606916 : CollatzResearch.WordTrace tailWord_5606916 prefixEnd_5606916 2879042897384690149064269 := by
  unfold tailWord_5606916
  simp only [CollatzResearch.WordTrace]
  refine ⟨102250513477554195930336301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136334017970072261240448401 102250513477554195930336301)
  ·
    refine ⟨38343942554082823473876113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102250513477554195930336301 38343942554082823473876113)
    ·
      refine ⟨28757956915562117605407085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38343942554082823473876113 28757956915562117605407085)
      ·
        refine ⟨10784233843335794102027657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28757956915562117605407085 10784233843335794102027657)
        ·
          refine ⟨8088175382501845576520743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784233843335794102027657 8088175382501845576520743)
          ·
            refine ⟨12132263073752768364781115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088175382501845576520743 12132263073752768364781115)
            ·
              refine ⟨18198394610629152547171673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12132263073752768364781115 18198394610629152547171673)
              ·
                refine ⟨13648795957971864410378755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18198394610629152547171673 13648795957971864410378755)
                ·
                  refine ⟨20473193936957796615568133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13648795957971864410378755 20473193936957796615568133)
                  ·
                    refine ⟨3838723863179586865419025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20473193936957796615568133 3838723863179586865419025)
                    ·
                      refine ⟨2879042897384690149064269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838723863179586865419025 2879042897384690149064269)
                      ·
                        rfl

theorem cell23_5606916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5606916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606916 prefixEnd_5606916 := by exact prefixLift 5606916
  have htrace : WordTrace (prefixWord ++ tailWord_5606916) baseStart_5606916 baseEnd_5606916 := by
    simpa [prefixWord, tailWord_5606916, baseEnd_5606916] using wordTrace_append hprefix tailTrace_5606916
  have hstable : (prefixWord ++ tailWord_5606916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606916).length < 2 ^ (prefixWord ++ tailWord_5606916).sum := by decide
  have hdescent : baseEnd_5606916 < baseStart_5606916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606969 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 2, 5]
def baseStart_5606969 : Nat := 118140960795 + 5606969 * 2 ^ 59
def prefixEnd_5606969 : Nat := 4983230072969 + 3 ^ 40 * 5606969 * 2
def baseEnd_5606969 : Nat := 959690037286459480567175

theorem tailTrace_5606969 : CollatzResearch.WordTrace tailWord_5606969 prefixEnd_5606969 959690037286459480567175 := by
  unfold tailWord_5606969
  simp only [CollatzResearch.WordTrace]
  refine ⟨204502960023916381912351961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136335306682610921274901307 204502960023916381912351961)
  ·
    refine ⟨153377220017937286434263971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204502960023916381912351961 153377220017937286434263971)
    ·
      refine ⟨230065830026905929651395957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153377220017937286434263971 230065830026905929651395957)
      ·
        refine ⟨21568671565022430904818371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230065830026905929651395957 21568671565022430904818371)
        ·
          refine ⟨32353007347533646357227557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21568671565022430904818371 32353007347533646357227557)
          ·
            refine ⟨6066188877662558691980167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32353007347533646357227557 6066188877662558691980167)
            ·
              refine ⟨9099283316493838037970251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066188877662558691980167 9099283316493838037970251)
              ·
                refine ⟨13648924974740757056955377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099283316493838037970251 13648924974740757056955377)
                ·
                  refine ⟨10236693731055567792716533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13648924974740757056955377 10236693731055567792716533)
                  ·
                    refine ⟨959690037286459480567175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10236693731055567792716533 959690037286459480567175)
                    ·
                      rfl

theorem cell23_5606969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 5].length) (baseStart_5606969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606969 prefixEnd_5606969 := by exact prefixLift 5606969
  have htrace : WordTrace (prefixWord ++ tailWord_5606969) baseStart_5606969 baseEnd_5606969 := by
    simpa [prefixWord, tailWord_5606969, baseEnd_5606969] using wordTrace_append hprefix tailTrace_5606969
  have hstable : (prefixWord ++ tailWord_5606969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606969).length < 2 ^ (prefixWord ++ tailWord_5606969).sum := by decide
  have hdescent : baseEnd_5606969 < baseStart_5606969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606985 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 4]
def baseStart_5606985 : Nat := 118140960795 + 5606985 * 2 ^ 59
def prefixEnd_5606985 : Nat := 4983230072969 + 3 ^ 40 * 5606985 * 2
def baseEnd_5606985 : Nat := 2879078327549850379101451

theorem tailTrace_5606985 : CollatzResearch.WordTrace tailWord_5606985 prefixEnd_5606985 2879078327549850379101451 := by
  unfold tailWord_5606985
  simp only [CollatzResearch.WordTrace]
  refine ⟨204503543591858416644934409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136335695727905611096622939 204503543591858416644934409)
  ·
    refine ⟨153377657693893812483700807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204503543591858416644934409 153377657693893812483700807)
    ·
      refine ⟨230066486540840718725551211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153377657693893812483700807 230066486540840718725551211)
      ·
        refine ⟨345099729811261078088326817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230066486540840718725551211 345099729811261078088326817)
        ·
          refine ⟨258824797358445808566245113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345099729811261078088326817 258824797358445808566245113)
          ·
            refine ⟨194118598018834356424683835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258824797358445808566245113 194118598018834356424683835)
            ·
              refine ⟨291177897028251534637025753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194118598018834356424683835 291177897028251534637025753)
              ·
                refine ⟨218383422771188650977769315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291177897028251534637025753 218383422771188650977769315)
                ·
                  refine ⟨327575134156782976466653973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218383422771188650977769315 327575134156782976466653973)
                  ·
                    refine ⟨15355084413599202021874405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 327575134156782976466653973 15355084413599202021874405)
                    ·
                      refine ⟨2879078327549850379101451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15355084413599202021874405 2879078327549850379101451)
                      ·
                        rfl

theorem cell23_5606985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_5606985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606985 prefixEnd_5606985 := by exact prefixLift 5606985
  have htrace : WordTrace (prefixWord ++ tailWord_5606985) baseStart_5606985 baseEnd_5606985 := by
    simpa [prefixWord, tailWord_5606985, baseEnd_5606985] using wordTrace_append hprefix tailTrace_5606985
  have hstable : (prefixWord ++ tailWord_5606985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606985).length < 2 ^ (prefixWord ++ tailWord_5606985).sum := by decide
  have hdescent : baseEnd_5606985 < baseStart_5606985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606992 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_5606992 : Nat := 118140960795 + 5606992 * 2 ^ 59
def prefixEnd_5606992 : Nat := 4983230072969 + 3 ^ 40 * 5606992 * 2
def baseEnd_5606992 : Nat := 2879081921914431851713919

theorem tailTrace_5606992 : CollatzResearch.WordTrace tailWord_5606992 prefixEnd_5606992 2879081921914431851713919 := by
  unfold tailWord_5606992
  simp only [CollatzResearch.WordTrace]
  refine ⟨102251899451416528420219615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136335865935222037893626153 102251899451416528420219615)
  ·
    refine ⟨153377849177124792630329423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102251899451416528420219615 153377849177124792630329423)
    ·
      refine ⟨230066773765687188945494135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153377849177124792630329423 230066773765687188945494135)
      ·
        refine ⟨345100160648530783418241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230066773765687188945494135 345100160648530783418241203)
        ·
          refine ⟨517650240972796175127361805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345100160648530783418241203 517650240972796175127361805)
          ·
            refine ⟨194118840364798565672760677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517650240972796175127361805 194118840364798565672760677)
            ·
              refine ⟨36397282568399731063642627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194118840364798565672760677 36397282568399731063642627)
              ·
                refine ⟨54595923852599596595463941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36397282568399731063642627 54595923852599596595463941)
                ·
                  refine ⟨10236735722362424361649489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54595923852599596595463941 10236735722362424361649489)
                  ·
                    refine ⟨7677551791771818271237117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10236735722362424361649489 7677551791771818271237117)
                    ·
                      refine ⟨2879081921914431851713919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677551791771818271237117 2879081921914431851713919)
                      ·
                        rfl

theorem cell23_5606992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_5606992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606992 prefixEnd_5606992 := by exact prefixLift 5606992
  have htrace : WordTrace (prefixWord ++ tailWord_5606992) baseStart_5606992 baseEnd_5606992 := by
    simpa [prefixWord, tailWord_5606992, baseEnd_5606992] using wordTrace_append hprefix tailTrace_5606992
  have hstable : (prefixWord ++ tailWord_5606992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606992).length < 2 ^ (prefixWord ++ tailWord_5606992).sum := by decide
  have hdescent : baseEnd_5606992 < baseStart_5606992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5606999 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 3, 4]
def baseStart_5606999 : Nat := 118140960795 + 5606999 * 2 ^ 59
def prefixEnd_5606999 : Nat := 4983230072969 + 3 ^ 40 * 5606999 * 2
def baseEnd_5606999 : Nat := 959695172093004441442129

theorem tailTrace_5606999 : CollatzResearch.WordTrace tailWord_5606999 prefixEnd_5606999 959695172093004441442129 := by
  unfold tailWord_5606999
  simp only [CollatzResearch.WordTrace]
  refine ⟨204504054213807697035944051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136336036142538464690629367 204504054213807697035944051)
  ·
    refine ⟨306756081320711545553916077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204504054213807697035944051 306756081320711545553916077)
    ·
      refine ⟨115033530495266829582718529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306756081320711545553916077 115033530495266829582718529)
      ·
        refine ⟨86275147871450122187038897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115033530495266829582718529 86275147871450122187038897)
        ·
          refine ⟨64706360903587591640279173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86275147871450122187038897 64706360903587591640279173)
          ·
            refine ⟨12132442669422673432552345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64706360903587591640279173 12132442669422673432552345)
            ·
              refine ⟨9099332002067005074414259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12132442669422673432552345 9099332002067005074414259)
              ·
                refine ⟨13648998003100507611621389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099332002067005074414259 13648998003100507611621389)
                ·
                  refine ⟨5118374251162690354358021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13648998003100507611621389 5118374251162690354358021)
                  ·
                    refine ⟨959695172093004441442129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118374251162690354358021 959695172093004441442129)
                    ·
                      rfl

theorem cell23_5606999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_5606999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5606999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5606999 prefixEnd_5606999 := by exact prefixLift 5606999
  have htrace : WordTrace (prefixWord ++ tailWord_5606999) baseStart_5606999 baseEnd_5606999 := by
    simpa [prefixWord, tailWord_5606999, baseEnd_5606999] using wordTrace_append hprefix tailTrace_5606999
  have hstable : (prefixWord ++ tailWord_5606999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5606999).length < 2 ^ (prefixWord ++ tailWord_5606999).sum := by decide
  have hdescent : baseEnd_5606999 < baseStart_5606999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5606999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607025 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 9]
def baseStart_5607025 : Nat := 118140960795 + 5607025 * 2 ^ 59
def prefixEnd_5607025 : Nat := 4983230072969 + 3 ^ 40 * 5607025 * 2
def baseEnd_5607025 : Nat := 959699622258676740867089

theorem tailTrace_5607025 : CollatzResearch.WordTrace tailWord_5607025 prefixEnd_5607025 959699622258676740867089 := by
  unfold tailWord_5607025
  simp only [CollatzResearch.WordTrace]
  refine ⟨204505002511713503476390529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136336668341142335650927019 204505002511713503476390529)
  ·
    refine ⟨153378751883785127607292897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204505002511713503476390529 153378751883785127607292897)
    ·
      refine ⟨115034063912838845705469673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153378751883785127607292897 115034063912838845705469673)
      ·
        refine ⟨86275547934629134279102255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115034063912838845705469673 86275547934629134279102255)
        ·
          refine ⟨129413321901943701418653383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86275547934629134279102255 129413321901943701418653383)
          ·
            refine ⟨194119982852915552127980075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129413321901943701418653383 194119982852915552127980075)
            ·
              refine ⟨291179974279373328191970113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194119982852915552127980075 291179974279373328191970113)
              ·
                refine ⟨218384980709529996143977585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291179974279373328191970113 218384980709529996143977585)
                ·
                  refine ⟨163788735532147497107983189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218384980709529996143977585 163788735532147497107983189)
                  ·
                    refine ⟨959699622258676740867089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163788735532147497107983189 959699622258676740867089)
                    ·
                      rfl

theorem cell23_5607025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_5607025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607025 prefixEnd_5607025 := by exact prefixLift 5607025
  have htrace : WordTrace (prefixWord ++ tailWord_5607025) baseStart_5607025 baseEnd_5607025 := by
    simpa [prefixWord, tailWord_5607025, baseEnd_5607025] using wordTrace_append hprefix tailTrace_5607025
  have hstable : (prefixWord ++ tailWord_5607025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607025).length < 2 ^ (prefixWord ++ tailWord_5607025).sum := by decide
  have hdescent : baseEnd_5607025 < baseStart_5607025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607049 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 4, 3, 2]
def baseStart_5607049 : Nat := 118140960795 + 5607049 * 2 ^ 59
def prefixEnd_5607049 : Nat := 4983230072969 + 3 ^ 40 * 5607049 * 2
def baseEnd_5607049 : Nat := 2879111190311738128701157

theorem tailTrace_5607049 : CollatzResearch.WordTrace tailWord_5607049 prefixEnd_5607049 2879111190311738128701157 := by
  unfold tailWord_5607049
  simp only [CollatzResearch.WordTrace]
  refine ⟨204505877863626555575264201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136337251909084370383509467 204505877863626555575264201)
  ·
    refine ⟨153379408397719916681448151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204505877863626555575264201 153379408397719916681448151)
    ·
      refine ⟨230069112596579875022172227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153379408397719916681448151 230069112596579875022172227)
      ·
        refine ⟨345103668894869812533258341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230069112596579875022172227 345103668894869812533258341)
        ·
          refine ⟨64706937917788089849985939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345103668894869812533258341 64706937917788089849985939)
          ·
            refine ⟨97060406876682134774978909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64706937917788089849985939 97060406876682134774978909)
            ·
              refine ⟨36397652578755800540617091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97060406876682134774978909 36397652578755800540617091)
              ·
                refine ⟨54596478868133700810925637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36397652578755800540617091 54596478868133700810925637)
                ·
                  refine ⟨10236839787775068902048557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54596478868133700810925637 10236839787775068902048557)
                  ·
                    refine ⟨3838814920415650838268209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10236839787775068902048557 3838814920415650838268209)
                    ·
                      refine ⟨2879111190311738128701157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838814920415650838268209 2879111190311738128701157)
                      ·
                        rfl

theorem cell23_5607049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 3, 2].length) (baseStart_5607049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607049 prefixEnd_5607049 := by exact prefixLift 5607049
  have htrace : WordTrace (prefixWord ++ tailWord_5607049) baseStart_5607049 baseEnd_5607049 := by
    simpa [prefixWord, tailWord_5607049, baseEnd_5607049] using wordTrace_append hprefix tailTrace_5607049
  have hstable : (prefixWord ++ tailWord_5607049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607049).length < 2 ^ (prefixWord ++ tailWord_5607049).sum := by decide
  have hdescent : baseEnd_5607049 < baseStart_5607049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607055 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 10]
def baseStart_5607055 : Nat := 118140960795 + 5607055 * 2 ^ 59
def prefixEnd_5607055 : Nat := 4983230072969 + 3 ^ 40 * 5607055 * 2
def baseEnd_5607055 : Nat := 959704757065221701742043

theorem tailTrace_5607055 : CollatzResearch.WordTrace tailWord_5607055 prefixEnd_5607055 959704757065221701742043 := by
  unfold tailWord_5607055
  simp only [CollatzResearch.WordTrace]
  refine ⟨204506096701604818599982619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136337397801069879066655079 204506096701604818599982619)
  ·
    refine ⟨306759145052407227899973929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204506096701604818599982619 306759145052407227899973929)
    ·
      refine ⟨230069358789305420924980447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306759145052407227899973929 230069358789305420924980447)
      ·
        refine ⟨345104038183958131387470671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230069358789305420924980447 345104038183958131387470671)
        ·
          refine ⟨517656057275937197081206007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345104038183958131387470671 517656057275937197081206007)
          ·
            refine ⟨776484085913905795621809011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517656057275937197081206007 776484085913905795621809011)
            ·
              refine ⟨1164726128870858693432713517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776484085913905795621809011 1164726128870858693432713517)
              ·
                refine ⟨436772298326572010037267569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164726128870858693432713517 436772298326572010037267569)
                ·
                  refine ⟨327579223744929007527950677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436772298326572010037267569 327579223744929007527950677)
                  ·
                    refine ⟨959704757065221701742043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 327579223744929007527950677 959704757065221701742043)
                    ·
                      rfl

theorem cell23_5607055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 10].length) (baseStart_5607055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607055 prefixEnd_5607055 := by exact prefixLift 5607055
  have htrace : WordTrace (prefixWord ++ tailWord_5607055) baseStart_5607055 baseEnd_5607055 := by
    simpa [prefixWord, tailWord_5607055, baseEnd_5607055] using wordTrace_append hprefix tailTrace_5607055
  have hstable : (prefixWord ++ tailWord_5607055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607055).length < 2 ^ (prefixWord ++ tailWord_5607055).sum := by decide
  have hdescent : baseEnd_5607055 < baseStart_5607055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 1, 1, 3]
def baseStart_5607056 : Nat := 118140960795 + 5607056 * 2 ^ 59
def prefixEnd_5607056 : Nat := 4983230072969 + 3 ^ 40 * 5607056 * 2
def baseEnd_5607056 : Nat := 2879114784676319601313625

theorem tailTrace_5607056 : CollatzResearch.WordTrace tailWord_5607056 prefixEnd_5607056 2879114784676319601313625 := by
  unfold tailWord_5607056
  simp only [CollatzResearch.WordTrace]
  refine ⟨102253066587300597885384511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136337422116400797180512681 102253066587300597885384511)
  ·
    refine ⟨153379599880950896828076767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102253066587300597885384511 153379599880950896828076767)
    ·
      refine ⟨230069399821426345242115151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153379599880950896828076767 230069399821426345242115151)
      ·
        refine ⟨345104099732139517863172727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230069399821426345242115151 345104099732139517863172727)
        ·
          refine ⟨517656149598209276794759091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345104099732139517863172727 517656149598209276794759091)
          ·
            refine ⟨776484224397313915192138637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517656149598209276794759091 776484224397313915192138637)
            ·
              refine ⟨291181584148992718197051989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776484224397313915192138637 291181584148992718197051989)
              ·
                refine ⟨3412284189246008416371703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 291181584148992718197051989 3412284189246008416371703)
                ·
                  refine ⟨5118426283869012624557555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412284189246008416371703 5118426283869012624557555)
                  ·
                    refine ⟨7677639425803518936836333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118426283869012624557555 7677639425803518936836333)
                    ·
                      refine ⟨2879114784676319601313625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677639425803518936836333 2879114784676319601313625)
                      ·
                        rfl

theorem cell23_5607056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 1, 3].length) (baseStart_5607056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607056 prefixEnd_5607056 := by exact prefixLift 5607056
  have htrace : WordTrace (prefixWord ++ tailWord_5607056) baseStart_5607056 baseEnd_5607056 := by
    simpa [prefixWord, tailWord_5607056, baseEnd_5607056] using wordTrace_append hprefix tailTrace_5607056
  have hstable : (prefixWord ++ tailWord_5607056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607056).length < 2 ^ (prefixWord ++ tailWord_5607056).sum := by decide
  have hdescent : baseEnd_5607056 < baseStart_5607056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607076 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_5607076 : Nat := 118140960795 + 5607076 * 2 ^ 59
def prefixEnd_5607076 : Nat := 4983230072969 + 3 ^ 40 * 5607076 * 2
def baseEnd_5607076 : Nat := 959708351429803174354511

theorem tailTrace_5607076 : CollatzResearch.WordTrace tailWord_5607076 prefixEnd_5607076 959708351429803174354511 := by
  unfold tailWord_5607076
  simp only [CollatzResearch.WordTrace]
  refine ⟨102253431317264369593248541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136337908423019159457664721 102253431317264369593248541)
  ·
    refine ⟨38345036743974138597468203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102253431317264369593248541 38345036743974138597468203)
    ·
      refine ⟨57517555115961207896202305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38345036743974138597468203 57517555115961207896202305)
      ·
        refine ⟨43138166336970905922151729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57517555115961207896202305 43138166336970905922151729)
        ·
          refine ⟨32353624752728179441613797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43138166336970905922151729 32353624752728179441613797)
          ·
            refine ⟨6066304641136533645302587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32353624752728179441613797 6066304641136533645302587)
            ·
              refine ⟨9099456961704800467953881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066304641136533645302587 9099456961704800467953881)
              ·
                refine ⟨6824592721278600350965411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099456961704800467953881 6824592721278600350965411)
                ·
                  refine ⟨10236889081917900526448117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824592721278600350965411 10236889081917900526448117)
                  ·
                    refine ⟨959708351429803174354511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10236889081917900526448117 959708351429803174354511)
                    ·
                      rfl

theorem cell23_5607076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_5607076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607076 prefixEnd_5607076 := by exact prefixLift 5607076
  have htrace : WordTrace (prefixWord ++ tailWord_5607076) baseStart_5607076 baseEnd_5607076 := by
    simpa [prefixWord, tailWord_5607076, baseEnd_5607076] using wordTrace_append hprefix tailTrace_5607076
  have hstable : (prefixWord ++ tailWord_5607076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607076).length < 2 ^ (prefixWord ++ tailWord_5607076).sum := by decide
  have hdescent : baseEnd_5607076 < baseStart_5607076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607093 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_5607093 : Nat := 118140960795 + 5607093 * 2 ^ 59
def prefixEnd_5607093 : Nat := 4983230072969 + 3 ^ 40 * 5607093 * 2
def baseEnd_5607093 : Nat := 959711261153511985516985

theorem tailTrace_5607093 : CollatzResearch.WordTrace tailWord_5607093 prefixEnd_5607093 959711261153511985516985 := by
  unfold tailWord_5607093
  simp only [CollatzResearch.WordTrace]
  refine ⟨204507482675467151089865933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136338321783644767393243955 204507482675467151089865933)
  ·
    refine ⟨76690306003300181658699725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204507482675467151089865933 76690306003300181658699725)
    ·
      refine ⟨28758864751237568122012397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76690306003300181658699725 28758864751237568122012397)
      ·
        refine ⟨10784574281714088045754649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28758864751237568122012397 10784574281714088045754649)
        ·
          refine ⟨8088430711285566034315987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10784574281714088045754649 8088430711285566034315987)
          ·
            refine ⟨12132646066928349051473981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088430711285566034315987 12132646066928349051473981)
            ·
              refine ⟨4549742275098130894302743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12132646066928349051473981 4549742275098130894302743)
              ·
                refine ⟨6824613412647196341454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4549742275098130894302743 6824613412647196341454115)
                ·
                  refine ⟨10236920118970794512181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824613412647196341454115 10236920118970794512181173)
                  ·
                    refine ⟨959711261153511985516985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10236920118970794512181173 959711261153511985516985)
                    ·
                      rfl

theorem cell23_5607093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_5607093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607093 prefixEnd_5607093 := by exact prefixLift 5607093
  have htrace : WordTrace (prefixWord ++ tailWord_5607093) baseStart_5607093 baseEnd_5607093 := by
    simpa [prefixWord, tailWord_5607093, baseEnd_5607093] using wordTrace_append hprefix tailTrace_5607093
  have hstable : (prefixWord ++ tailWord_5607093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607093).length < 2 ^ (prefixWord ++ tailWord_5607093).sum := by decide
  have hdescent : baseEnd_5607093 < baseStart_5607093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607099 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 3]
def baseStart_5607099 : Nat := 118140960795 + 5607099 * 2 ^ 59
def prefixEnd_5607099 : Nat := 4983230072969 + 3 ^ 40 * 5607099 * 2
def baseEnd_5607099 : Nat := 2879136864344462933075927

theorem tailTrace_5607099 : CollatzResearch.WordTrace tailWord_5607099 prefixEnd_5607099 2879136864344462933075927 := by
  unfold tailWord_5607099
  simp only [CollatzResearch.WordTrace]
  refine ⟨204507701513445414114584351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136338467675630276076389567 204507701513445414114584351)
  ·
    refine ⟨306761552270168121171876527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204507701513445414114584351 306761552270168121171876527)
    ·
      refine ⟨460142328405252181757814791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306761552270168121171876527 460142328405252181757814791)
      ·
        refine ⟨690213492607878272636722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460142328405252181757814791 690213492607878272636722187)
        ·
          refine ⟨1035320238911817408955083281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690213492607878272636722187 1035320238911817408955083281)
          ·
            refine ⟨776490179183863056716312461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035320238911817408955083281 776490179183863056716312461)
            ·
              refine ⟨291183817193948646268617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776490179183863056716312461 291183817193948646268617173)
              ·
                refine ⟨6824620715483171396920715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 291183817193948646268617173 6824620715483171396920715)
                ·
                  refine ⟨10236931073224757095381073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6824620715483171396920715 10236931073224757095381073)
                  ·
                    refine ⟨7677698304918567821535805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10236931073224757095381073 7677698304918567821535805)
                    ·
                      refine ⟨2879136864344462933075927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677698304918567821535805 2879136864344462933075927)
                      ·
                        rfl

theorem cell23_5607099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 2, 3].length) (baseStart_5607099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607099 prefixEnd_5607099 := by exact prefixLift 5607099
  have htrace : WordTrace (prefixWord ++ tailWord_5607099) baseStart_5607099 baseEnd_5607099 := by
    simpa [prefixWord, tailWord_5607099, baseEnd_5607099] using wordTrace_append hprefix tailTrace_5607099
  have hstable : (prefixWord ++ tailWord_5607099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607099).length < 2 ^ (prefixWord ++ tailWord_5607099).sum := by decide
  have hdescent : baseEnd_5607099 < baseStart_5607099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607102 : List Nat := [4, 2, 1, 1, 2, 13]
def baseStart_5607102 : Nat := 118140960795 + 5607102 * 2 ^ 59
def prefixEnd_5607102 : Nat := 4983230072969 + 3 ^ 40 * 5607102 * 2
def baseEnd_5607102 : Nat := 11848306192536734244191

theorem tailTrace_5607102 : CollatzResearch.WordTrace tailWord_5607102 prefixEnd_5607102 11848306192536734244191 := by
  unfold tailWord_5607102
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563476366554318203367945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136338540621623030417962373 25563476366554318203367945)
  ·
    refine ⟨19172607274915738652525959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25563476366554318203367945 19172607274915738652525959)
    ·
      refine ⟨28758910912373607978788939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19172607274915738652525959 28758910912373607978788939)
      ·
        refine ⟨43138366368560411968183409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28758910912373607978788939 43138366368560411968183409)
        ·
          refine ⟨32353774776420308976137557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43138366368560411968183409 32353774776420308976137557)
          ·
            refine ⟨11848306192536734244191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 32353774776420308976137557 11848306192536734244191)
            ·
              rfl

theorem cell23_5607102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 13].length) (baseStart_5607102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607102 prefixEnd_5607102 := by exact prefixLift 5607102
  have htrace : WordTrace (prefixWord ++ tailWord_5607102) baseStart_5607102 baseEnd_5607102 := by
    simpa [prefixWord, tailWord_5607102, baseEnd_5607102] using wordTrace_append hprefix tailTrace_5607102
  have hstable : (prefixWord ++ tailWord_5607102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607102).length < 2 ^ (prefixWord ++ tailWord_5607102).sum := by decide
  have hdescent : baseEnd_5607102 < baseStart_5607102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607129 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 3]
def baseStart_5607129 : Nat := 118140960795 + 5607129 * 2 ^ 59
def prefixEnd_5607129 : Nat := 4983230072969 + 3 ^ 40 * 5607129 * 2
def baseEnd_5607129 : Nat := 2879152268764097815700789

theorem tailTrace_5607129 : CollatzResearch.WordTrace tailWord_5607129 prefixEnd_5607129 2879152268764097815700789 := by
  unfold tailWord_5607129
  simp only [CollatzResearch.WordTrace]
  refine ⟨204508795703336729238176441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136339197135557819492117627 204508795703336729238176441)
  ·
    refine ⟨153381596777502546928632331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204508795703336729238176441 153381596777502546928632331)
    ·
      refine ⟨230072395166253820392948497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153381596777502546928632331 230072395166253820392948497)
      ·
        refine ⟨172554296374690365294711373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230072395166253820392948497 172554296374690365294711373)
        ·
          refine ⟨64707861140508886985516765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172554296374690365294711373 64707861140508886985516765)
          ·
            refine ⟨24265447927690832619568787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64707861140508886985516765 24265447927690832619568787)
            ·
              refine ⟨36398171891536248929353181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24265447927690832619568787 36398171891536248929353181)
              ·
                refine ⟨13649314459326093348507443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36398171891536248929353181 13649314459326093348507443)
                ·
                  refine ⟨20473971688989140022761165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13649314459326093348507443 20473971688989140022761165)
                  ·
                    refine ⟨7677739383370927508535437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20473971688989140022761165 7677739383370927508535437)
                    ·
                      refine ⟨2879152268764097815700789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677739383370927508535437 2879152268764097815700789)
                      ·
                        rfl

theorem cell23_5607129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_5607129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607129 prefixEnd_5607129 := by exact prefixLift 5607129
  have htrace : WordTrace (prefixWord ++ tailWord_5607129) baseStart_5607129 baseEnd_5607129 := by
    simpa [prefixWord, tailWord_5607129, baseEnd_5607129] using wordTrace_append hprefix tailTrace_5607129
  have hstable : (prefixWord ++ tailWord_5607129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607129).length < 2 ^ (prefixWord ++ tailWord_5607129).sum := by decide
  have hdescent : baseEnd_5607129 < baseStart_5607129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607152 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_5607152 : Nat := 118140960795 + 5607152 * 2 ^ 59
def prefixEnd_5607152 : Nat := 4983230072969 + 3 ^ 40 * 5607152 * 2
def baseEnd_5607152 : Nat := 2879164078819151225713183

theorem tailTrace_5607152 : CollatzResearch.WordTrace tailWord_5607152 prefixEnd_5607152 2879164078819151225713183 := by
  unfold tailWord_5607152
  simp only [CollatzResearch.WordTrace]
  refine ⟨102254817291126702083131855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136339756388168936110842473 102254817291126702083131855)
  ·
    refine ⟨153382225936690053124697783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102254817291126702083131855 153382225936690053124697783)
    ·
      refine ⟨230073338905035079687046675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153382225936690053124697783 230073338905035079687046675)
      ·
        refine ⟨345110008357552619530570013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230073338905035079687046675 345110008357552619530570013)
        ·
          refine ⟨129416253134082232323963755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345110008357552619530570013 129416253134082232323963755)
          ·
            refine ⟨194124379701123348485945633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129416253134082232323963755 194124379701123348485945633)
            ·
              refine ⟨145593284775842511364459225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194124379701123348485945633 145593284775842511364459225)
              ·
                refine ⟨109194963581881883523344419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145593284775842511364459225 109194963581881883523344419)
                ·
                  refine ⟨163792445372822825285016629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109194963581881883523344419 163792445372822825285016629)
                  ·
                    refine ⟨15355541753702139870470309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 163792445372822825285016629 15355541753702139870470309)
                    ·
                      refine ⟨2879164078819151225713183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15355541753702139870470309 2879164078819151225713183)
                      ·
                        rfl

theorem cell23_5607152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_5607152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607152 prefixEnd_5607152 := by exact prefixLift 5607152
  have htrace : WordTrace (prefixWord ++ tailWord_5607152) baseStart_5607152 baseEnd_5607152 := by
    simpa [prefixWord, tailWord_5607152, baseEnd_5607152] using wordTrace_append hprefix tailTrace_5607152
  have hstable : (prefixWord ++ tailWord_5607152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607152).length < 2 ^ (prefixWord ++ tailWord_5607152).sum := by decide
  have hdescent : baseEnd_5607152 < baseStart_5607152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607174 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5607174 : Nat := 118140960795 + 5607174 * 2 ^ 59
def prefixEnd_5607174 : Nat := 4983230072969 + 3 ^ 40 * 5607174 * 2
def baseEnd_5607174 : Nat := 959725125131183379879361

theorem tailTrace_5607174 : CollatzResearch.WordTrace tailWord_5607174 prefixEnd_5607174 959725125131183379879361 := by
  unfold tailWord_5607174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390951155880428185111393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136340291325449134615709717 6390951155880428185111393)
  ·
    refine ⟨4793213366910321138833545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6390951155880428185111393 4793213366910321138833545)
    ·
      refine ⟨3594910025182740854125159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4793213366910321138833545 3594910025182740854125159)
      ·
        refine ⟨5392365037774111281187739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594910025182740854125159 5392365037774111281187739)
        ·
          refine ⟨8088547556661166921781609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392365037774111281187739 8088547556661166921781609)
          ·
            refine ⟨6066410667495875191336207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088547556661166921781609 6066410667495875191336207)
            ·
              refine ⟨9099616001243812787004311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066410667495875191336207 9099616001243812787004311)
              ·
                refine ⟨13649424001865719180506467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099616001243812787004311 13649424001865719180506467)
                ·
                  refine ⟨20474136002798578770759701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13649424001865719180506467 20474136002798578770759701)
                  ·
                    refine ⟨959725125131183379879361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20474136002798578770759701 959725125131183379879361)
                    ·
                      rfl

theorem cell23_5607174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5607174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607174 prefixEnd_5607174 := by exact prefixLift 5607174
  have htrace : WordTrace (prefixWord ++ tailWord_5607174) baseStart_5607174 baseEnd_5607174 := by
    simpa [prefixWord, tailWord_5607174, baseEnd_5607174] using wordTrace_append hprefix tailTrace_5607174
  have hstable : (prefixWord ++ tailWord_5607174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607174).length < 2 ^ (prefixWord ++ tailWord_5607174).sum := by decide
  have hdescent : baseEnd_5607174 < baseStart_5607174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607198 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5607198 : Nat := 118140960795 + 5607198 * 2 ^ 59
def prefixEnd_5607198 : Nat := 4983230072969 + 3 ^ 40 * 5607198 * 2
def baseEnd_5607198 : Nat := 2879187698929258045737973

theorem tailTrace_5607198 : CollatzResearch.WordTrace tailWord_5607198 prefixEnd_5607198 2879187698929258045737973 := by
  unfold tailWord_5607198
  simp only [CollatzResearch.WordTrace]
  refine ⟨25563914042510844252804781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136340874893391169348292165 25563914042510844252804781)
  ·
    refine ⟨9586467765941566594801793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25563914042510844252804781 9586467765941566594801793)
    ·
      refine ⟨7189850824456174946101345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9586467765941566594801793 7189850824456174946101345)
      ·
        refine ⟨5392388118342131209576009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7189850824456174946101345 5392388118342131209576009)
        ·
          refine ⟨4044291088756598407182007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392388118342131209576009 4044291088756598407182007)
          ·
            refine ⟨6066436633134897610773011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044291088756598407182007 6066436633134897610773011)
            ·
              refine ⟨9099654949702346416159517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066436633134897610773011 9099654949702346416159517)
              ·
                refine ⟨3412370606138379906059819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9099654949702346416159517 3412370606138379906059819)
                ·
                  refine ⟨5118555909207569859089729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412370606138379906059819 5118555909207569859089729)
                  ·
                    refine ⟨3838916931905677394317297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5118555909207569859089729 3838916931905677394317297)
                    ·
                      refine ⟨2879187698929258045737973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838916931905677394317297 2879187698929258045737973)
                      ·
                        rfl

theorem cell23_5607198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5607198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607198 prefixEnd_5607198 := by exact prefixLift 5607198
  have htrace : WordTrace (prefixWord ++ tailWord_5607198) baseStart_5607198 baseEnd_5607198 := by
    simpa [prefixWord, tailWord_5607198, baseEnd_5607198] using wordTrace_append hprefix tailTrace_5607198
  have hstable : (prefixWord ++ tailWord_5607198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607198).length < 2 ^ (prefixWord ++ tailWord_5607198).sum := by decide
  have hdescent : baseEnd_5607198 < baseStart_5607198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607220 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5607220 : Nat := 118140960795 + 5607220 * 2 ^ 59
def prefixEnd_5607220 : Nat := 4983230072969 + 3 ^ 40 * 5607220 * 2
def baseEnd_5607220 : Nat := 2879198995503656959662871

theorem tailTrace_5607220 : CollatzResearch.WordTrace tailWord_5607220 prefixEnd_5607220 2879198995503656959662871 := by
  unfold tailWord_5607220
  simp only [CollatzResearch.WordTrace]
  refine ⟨102256057373003525889869557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136341409830671367853159409 102256057373003525889869557)
  ·
    refine ⟨9586505378719080552175271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102256057373003525889869557 9586505378719080552175271)
    ·
      refine ⟨14379758068078620828262907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9586505378719080552175271 14379758068078620828262907)
      ·
        refine ⟨21569637102117931242394361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379758068078620828262907 21569637102117931242394361)
        ·
          refine ⟨16177227826588448431795771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21569637102117931242394361 16177227826588448431795771)
          ·
            refine ⟨24265841739882672647693657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16177227826588448431795771 24265841739882672647693657)
            ·
              refine ⟨18199381304912004485770243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24265841739882672647693657 18199381304912004485770243)
              ·
                refine ⟨27299071957368006728655365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18199381304912004485770243 27299071957368006728655365)
                ·
                  refine ⟨5118575992006501261622881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27299071957368006728655365 5118575992006501261622881)
                  ·
                    refine ⟨3838931994004875946217161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5118575992006501261622881 3838931994004875946217161)
                    ·
                      refine ⟨2879198995503656959662871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3838931994004875946217161 2879198995503656959662871)
                      ·
                        rfl

theorem cell23_5607220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5607220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607220 prefixEnd_5607220 := by exact prefixLift 5607220
  have htrace : WordTrace (prefixWord ++ tailWord_5607220) baseStart_5607220 baseEnd_5607220 := by
    simpa [prefixWord, tailWord_5607220, baseEnd_5607220] using wordTrace_append hprefix tailTrace_5607220
  have hstable : (prefixWord ++ tailWord_5607220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607220).length < 2 ^ (prefixWord ++ tailWord_5607220).sum := by decide
  have hdescent : baseEnd_5607220 < baseStart_5607220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607226 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 7]
def baseStart_5607226 : Nat := 118140960795 + 5607226 * 2 ^ 59
def prefixEnd_5607226 : Nat := 4983230072969 + 3 ^ 40 * 5607226 * 2
def baseEnd_5607226 : Nat := 319911341820842659576427

theorem tailTrace_5607226 : CollatzResearch.WordTrace tailWord_5607226 prefixEnd_5607226 319911341820842659576427 := by
  unfold tailWord_5607226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51128083395996328701114383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136341555722656876536305021 51128083395996328701114383)
  ·
    refine ⟨76692125093994493051671575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51128083395996328701114383 76692125093994493051671575)
    ·
      refine ⟨115038187640991739577507363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76692125093994493051671575 115038187640991739577507363)
      ·
        refine ⟨172557281461487609366261045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115038187640991739577507363 172557281461487609366261045)
        ·
          refine ⟨16177245137014463378086973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172557281461487609366261045 16177245137014463378086973)
          ·
            refine ⟨6066466926380423766782615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16177245137014463378086973 6066466926380423766782615)
            ·
              refine ⟨9099700389570635650173923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066466926380423766782615 9099700389570635650173923)
              ·
                refine ⟨13649550584355953475260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099700389570635650173923 13649550584355953475260885)
                ·
                  refine ⟨319911341820842659576427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13649550584355953475260885 319911341820842659576427)
                  ·
                    rfl

theorem cell23_5607226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_5607226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607226 prefixEnd_5607226 := by exact prefixLift 5607226
  have htrace : WordTrace (prefixWord ++ tailWord_5607226) baseStart_5607226 baseEnd_5607226 := by
    simpa [prefixWord, tailWord_5607226, baseEnd_5607226] using wordTrace_append hprefix tailTrace_5607226
  have hstable : (prefixWord ++ tailWord_5607226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607226).length < 2 ^ (prefixWord ++ tailWord_5607226).sum := by decide
  have hdescent : baseEnd_5607226 < baseStart_5607226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607266 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5607266 : Nat := 118140960795 + 5607266 * 2 ^ 59
def prefixEnd_5607266 : Nat := 4983230072969 + 3 ^ 40 * 5607266 * 2
def baseEnd_5607266 : Nat := 2879222615613763779687659

theorem tailTrace_5607266 : CollatzResearch.WordTrace tailWord_5607266 prefixEnd_5607266 2879222615613763779687659 := by
  unfold tailWord_5607266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51128448125960100408978413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136342528335893601090609101 51128448125960100408978413)
  ·
    refine ⟨19173168047235037653366905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51128448125960100408978413 19173168047235037653366905)
    ·
      refine ⟨14379876035426278240025179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19173168047235037653366905 14379876035426278240025179)
      ·
        refine ⟨21569814053139417360037769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14379876035426278240025179 21569814053139417360037769)
        ·
          refine ⟨16177360539854563020028327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21569814053139417360037769 16177360539854563020028327)
          ·
            refine ⟨24266040809781844530042491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16177360539854563020028327 24266040809781844530042491)
            ·
              refine ⟨36399061214672766795063737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24266040809781844530042491 36399061214672766795063737)
              ·
                refine ⟨27299295911004575096297803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36399061214672766795063737 27299295911004575096297803)
                ·
                  refine ⟨40948943866506862644446705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27299295911004575096297803 40948943866506862644446705)
                  ·
                    refine ⟨30711707899880146983335029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40948943866506862644446705 30711707899880146983335029)
                    ·
                      refine ⟨2879222615613763779687659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30711707899880146983335029 2879222615613763779687659)
                      ·
                        rfl

theorem cell23_5607266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5607266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607266 prefixEnd_5607266 := by exact prefixLift 5607266
  have htrace : WordTrace (prefixWord ++ tailWord_5607266) baseStart_5607266 baseEnd_5607266 := by
    simpa [prefixWord, tailWord_5607266, baseEnd_5607266] using wordTrace_append hprefix tailTrace_5607266
  have hstable : (prefixWord ++ tailWord_5607266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607266).length < 2 ^ (prefixWord ++ tailWord_5607266).sum := by decide
  have hdescent : baseEnd_5607266 < baseStart_5607266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607276 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5607276 : Nat := 118140960795 + 5607276 * 2 ^ 59
def prefixEnd_5607276 : Nat := 4983230072969 + 3 ^ 40 * 5607276 * 2
def baseEnd_5607276 : Nat := 2879227750420308740562613

theorem tailTrace_5607276 : CollatzResearch.WordTrace tailWord_5607276 prefixEnd_5607276 2879227750420308740562613 := by
  unfold tailWord_5607276
  simp only [CollatzResearch.WordTrace]
  refine ⟨102257078616902086671888841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136342771489202782229185121 102257078616902086671888841)
  ·
    refine ⟨76692808962676565003916631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102257078616902086671888841 76692808962676565003916631)
    ·
      refine ⟨115039213444014847505874947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76692808962676565003916631 115039213444014847505874947)
      ·
        refine ⟨172558820166022271258812421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115039213444014847505874947 172558820166022271258812421)
        ·
          refine ⟨32354778781129175861027329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172558820166022271258812421 32354778781129175861027329)
          ·
            refine ⟨24266084085846881895770497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32354778781129175861027329 24266084085846881895770497)
            ·
              refine ⟨18199563064385161421827873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24266084085846881895770497 18199563064385161421827873)
              ·
                refine ⟨13649672298288871066370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18199563064385161421827873 13649672298288871066370905)
                ·
                  refine ⟨10237254223716653299778179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13649672298288871066370905 10237254223716653299778179)
                  ·
                    refine ⟨15355881335574979949667269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10237254223716653299778179 15355881335574979949667269)
                    ·
                      refine ⟨2879227750420308740562613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15355881335574979949667269 2879227750420308740562613)
                      ·
                        rfl

theorem cell23_5607276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5607276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607276 prefixEnd_5607276 := by exact prefixLift 5607276
  have htrace : WordTrace (prefixWord ++ tailWord_5607276) baseStart_5607276 baseEnd_5607276 := by
    simpa [prefixWord, tailWord_5607276, baseEnd_5607276] using wordTrace_append hprefix tailTrace_5607276
  have hstable : (prefixWord ++ tailWord_5607276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607276).length < 2 ^ (prefixWord ++ tailWord_5607276).sum := by decide
  have hdescent : baseEnd_5607276 < baseStart_5607276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607279 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3]
def baseStart_5607279 : Nat := 118140960795 + 5607279 * 2 ^ 59
def prefixEnd_5607279 : Nat := 4983230072969 + 3 ^ 40 * 5607279 * 2
def baseEnd_5607279 : Nat := 2879229290862272228825099

theorem tailTrace_5607279 : CollatzResearch.WordTrace tailWord_5607279 prefixEnd_5607279 2879229290862272228825099 := by
  unfold tailWord_5607279
  simp only [CollatzResearch.WordTrace]
  refine ⟨204514266652793304856136891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136342844435195536570757927 204514266652793304856136891)
  ·
    refine ⟨306771399979189957284205337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204514266652793304856136891 306771399979189957284205337)
    ·
      refine ⟨230078549984392467963154003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306771399979189957284205337 230078549984392467963154003)
      ·
        refine ⟨345117824976588701944731005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230078549984392467963154003 345117824976588701944731005)
        ·
          refine ⟨129419184366220763229274127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345117824976588701944731005 129419184366220763229274127)
          ·
            refine ⟨194128776549331144843911191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129419184366220763229274127 194128776549331144843911191)
            ·
              refine ⟨291193164823996717265866787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194128776549331144843911191 291193164823996717265866787)
              ·
                refine ⟨436789747235995075898800181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291193164823996717265866787 436789747235995075898800181)
                ·
                  refine ⟨40949038803374538365512517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436789747235995075898800181 40949038803374538365512517)
                  ·
                    refine ⟨7677944775632725943533597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40949038803374538365512517 7677944775632725943533597)
                    ·
                      refine ⟨2879229290862272228825099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7677944775632725943533597 2879229290862272228825099)
                      ·
                        rfl

theorem cell23_5607279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 4, 3].length) (baseStart_5607279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607279 prefixEnd_5607279 := by exact prefixLift 5607279
  have htrace : WordTrace (prefixWord ++ tailWord_5607279) baseStart_5607279 baseEnd_5607279 := by
    simpa [prefixWord, tailWord_5607279, baseEnd_5607279] using wordTrace_append hprefix tailTrace_5607279
  have hstable : (prefixWord ++ tailWord_5607279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607279).length < 2 ^ (prefixWord ++ tailWord_5607279).sum := by decide
  have hdescent : baseEnd_5607279 < baseStart_5607279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607303 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 3, 4]
def baseStart_5607303 : Nat := 118140960795 + 5607303 * 2 ^ 59
def prefixEnd_5607303 : Nat := 4983230072969 + 3 ^ 40 * 5607303 * 2
def baseEnd_5607303 : Nat := 959747204799326711641663

theorem tailTrace_5607303 : CollatzResearch.WordTrace tailWord_5607303 prefixEnd_5607303 959747204799326711641663 := by
  unfold tailWord_5607303
  simp only [CollatzResearch.WordTrace]
  refine ⟨204515142004706356955010563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136343428003137571303340375 204515142004706356955010563)
  ·
    refine ⟨306772713007059535432515845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204515142004706356955010563 306772713007059535432515845)
    ·
      refine ⟨57519883688823662893596721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306772713007059535432515845 57519883688823662893596721)
      ·
        refine ⟨43139912766617747170197541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57519883688823662893596721 43139912766617747170197541)
        ·
          refine ⟨8088733643740827594412039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43139912766617747170197541 8088733643740827594412039)
          ·
            refine ⟨12133100465611241391618059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088733643740827594412039 12133100465611241391618059)
            ·
              refine ⟨18199650698416862087427089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12133100465611241391618059 18199650698416862087427089)
              ·
                refine ⟨13649738023812646565570317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18199650698416862087427089 13649738023812646565570317)
                ·
                  refine ⟨5118651758929742462088869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13649738023812646565570317 5118651758929742462088869)
                  ·
                    refine ⟨959747204799326711641663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118651758929742462088869 959747204799326711641663)
                    ·
                      rfl

theorem cell23_5607303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_5607303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607303 prefixEnd_5607303 := by exact prefixLift 5607303
  have htrace : WordTrace (prefixWord ++ tailWord_5607303) baseStart_5607303 baseEnd_5607303 := by
    simpa [prefixWord, tailWord_5607303, baseEnd_5607303] using wordTrace_append hprefix tailTrace_5607303
  have hstable : (prefixWord ++ tailWord_5607303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607303).length < 2 ^ (prefixWord ++ tailWord_5607303).sum := by decide
  have hdescent : baseEnd_5607303 < baseStart_5607303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607343 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 3]
def baseStart_5607343 : Nat := 118140960795 + 5607343 * 2 ^ 59
def prefixEnd_5607343 : Nat := 4983230072969 + 3 ^ 40 * 5607343 * 2
def baseEnd_5607343 : Nat := 2879262153624159978424805

theorem tailTrace_5607343 : CollatzResearch.WordTrace tailWord_5607343 prefixEnd_5607343 2879262153624159978424805 := by
  unfold tailWord_5607343
  simp only [CollatzResearch.WordTrace]
  refine ⟨204516600924561443786466683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136344400616374295857644455 204516600924561443786466683)
  ·
    refine ⟨306774901386842165679700025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204516600924561443786466683 306774901386842165679700025)
    ·
      refine ⟨230081176040131624259775019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306774901386842165679700025 230081176040131624259775019)
      ·
        refine ⟨345121764060197436389662529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230081176040131624259775019 345121764060197436389662529)
        ·
          refine ⟨258841323045148077292246897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345121764060197436389662529 258841323045148077292246897)
          ·
            refine ⟨194130992283861057969185173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258841323045148077292246897 194130992283861057969185173)
            ·
              refine ⟨9099890263305987092305555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194130992283861057969185173 9099890263305987092305555)
              ·
                refine ⟨13649835394958980638458333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099890263305987092305555 13649835394958980638458333)
                ·
                  refine ⟨5118688273109617739421875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13649835394958980638458333 5118688273109617739421875)
                  ·
                    refine ⟨7678032409664426609132813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118688273109617739421875 7678032409664426609132813)
                    ·
                      refine ⟨2879262153624159978424805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678032409664426609132813 2879262153624159978424805)
                      ·
                        rfl

theorem cell23_5607343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 3].length) (baseStart_5607343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607343 prefixEnd_5607343 := by exact prefixLift 5607343
  have htrace : WordTrace (prefixWord ++ tailWord_5607343) baseStart_5607343 baseEnd_5607343 := by
    simpa [prefixWord, tailWord_5607343, baseEnd_5607343] using wordTrace_append hprefix tailTrace_5607343
  have hstable : (prefixWord ++ tailWord_5607343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607343).length < 2 ^ (prefixWord ++ tailWord_5607343).sum := by decide
  have hdescent : baseEnd_5607343 < baseStart_5607343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607376 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_5607376 : Nat := 118140960795 + 5607376 * 2 ^ 59
def prefixEnd_5607376 : Nat := 4983230072969 + 3 ^ 40 * 5607376 * 2
def baseEnd_5607376 : Nat := 959759699495252783104051

theorem tailTrace_5607376 : CollatzResearch.WordTrace tailWord_5607376 prefixEnd_5607376 959759699495252783104051 := by
  unfold tailWord_5607376
  simp only [CollatzResearch.WordTrace]
  refine ⟨102258902266720945211208991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136345203022294593614945321 102258902266720945211208991)
  ·
    refine ⟨153388353400081417816813487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102258902266720945211208991 153388353400081417816813487)
    ·
      refine ⟨230082530100122126725220231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153388353400081417816813487 230082530100122126725220231)
      ·
        refine ⟨345123795150183190087830347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230082530100122126725220231 345123795150183190087830347)
        ·
          refine ⟨517685692725274785131745521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345123795150183190087830347 517685692725274785131745521)
          ·
            refine ⟨388264269543956088848809141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517685692725274785131745521 388264269543956088848809141)
            ·
              refine ⟨36399775269745883329575857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 388264269543956088848809141 36399775269745883329575857)
              ·
                refine ⟨27299831452309412497181893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36399775269745883329575857 27299831452309412497181893)
                ·
                  refine ⟨5118718397308014843221605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27299831452309412497181893 5118718397308014843221605)
                  ·
                    refine ⟨959759699495252783104051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118718397308014843221605 959759699495252783104051)
                    ·
                      rfl

theorem cell23_5607376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_5607376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607376 prefixEnd_5607376 := by exact prefixLift 5607376
  have htrace : WordTrace (prefixWord ++ tailWord_5607376) baseStart_5607376 baseEnd_5607376 := by
    simpa [prefixWord, tailWord_5607376, baseEnd_5607376] using wordTrace_append hprefix tailTrace_5607376
  have hstable : (prefixWord ++ tailWord_5607376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607376).length < 2 ^ (prefixWord ++ tailWord_5607376).sum := by decide
  have hdescent : baseEnd_5607376 < baseStart_5607376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607394 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5607394 : Nat := 118140960795 + 5607394 * 2 ^ 59
def prefixEnd_5607394 : Nat := 4983230072969 + 3 ^ 40 * 5607394 * 2
def baseEnd_5607394 : Nat := 2879288341137539278887071

theorem tailTrace_5607394 : CollatzResearch.WordTrace tailWord_5607394 prefixEnd_5607394 2879288341137539278887071 := by
  unfold tailWord_5607394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51129615261844169874143309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136345640698251119664382157 51129615261844169874143309)
  ·
    refine ⟨19173605723191563702803741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51129615261844169874143309 19173605723191563702803741)
    ·
      refine ⟨7190102146196836388551403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19173605723191563702803741 7190102146196836388551403)
      ·
        refine ⟨10785153219295254582827105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190102146196836388551403 10785153219295254582827105)
        ·
          refine ⟨8088864914471440937120329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785153219295254582827105 8088864914471440937120329)
          ·
            refine ⟨6066648685853580702840247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088864914471440937120329 6066648685853580702840247)
            ·
              refine ⟨9099973028780371054260371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066648685853580702840247 9099973028780371054260371)
              ·
                refine ⟨13649959543170556581390557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099973028780371054260371 13649959543170556581390557)
                ·
                  refine ⟨5118734828688958718021459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13649959543170556581390557 5118734828688958718021459)
                  ·
                    refine ⟨7678102243033438077032189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118734828688958718021459 7678102243033438077032189)
                    ·
                      refine ⟨2879288341137539278887071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678102243033438077032189 2879288341137539278887071)
                      ·
                        rfl

theorem cell23_5607394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5607394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607394 prefixEnd_5607394 := by exact prefixLift 5607394
  have htrace : WordTrace (prefixWord ++ tailWord_5607394) baseStart_5607394 baseEnd_5607394 := by
    simpa [prefixWord, tailWord_5607394, baseEnd_5607394] using wordTrace_append hprefix tailTrace_5607394
  have hstable : (prefixWord ++ tailWord_5607394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607394).length < 2 ^ (prefixWord ++ tailWord_5607394).sum := by decide
  have hdescent : baseEnd_5607394 < baseStart_5607394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607406 : List Nat := [4, 1, 2, 1, 3, 1, 1, 10]
def baseStart_5607406 : Nat := 118140960795 + 5607406 * 2 ^ 59
def prefixEnd_5607406 : Nat := 4983230072969 + 3 ^ 40 * 5607406 * 2
def baseEnd_5607406 : Nat := 106640537144644193775445

theorem tailTrace_5607406 : CollatzResearch.WordTrace tailWord_5607406 prefixEnd_5607406 106640537144644193775445 := by
  unfold tailWord_5607406
  simp only [CollatzResearch.WordTrace]
  refine ⟨25564862340416650693251259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136345932482222137030673381 25564862340416650693251259)
  ·
    refine ⟨38347293510624976039876889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25564862340416650693251259 38347293510624976039876889)
    ·
      refine ⟨28760470132968732029907667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38347293510624976039876889 28760470132968732029907667)
      ·
        refine ⟨43140705199453098044861501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28760470132968732029907667 43140705199453098044861501)
        ·
          refine ⟨16177764449794911766823063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43140705199453098044861501 16177764449794911766823063)
          ·
            refine ⟨24266646674692367650234595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16177764449794911766823063 24266646674692367650234595)
            ·
              refine ⟨36399970012038551475351893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24266646674692367650234595 36399970012038551475351893)
              ·
                refine ⟨106640537144644193775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36399970012038551475351893 106640537144644193775445)
                ·
                  rfl

theorem cell23_5607406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_5607406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607406 prefixEnd_5607406 := by exact prefixLift 5607406
  have htrace : WordTrace (prefixWord ++ tailWord_5607406) baseStart_5607406 baseEnd_5607406 := by
    simpa [prefixWord, tailWord_5607406, baseEnd_5607406] using wordTrace_append hprefix tailTrace_5607406
  have hstable : (prefixWord ++ tailWord_5607406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607406).length < 2 ^ (prefixWord ++ tailWord_5607406).sum := by decide
  have hdescent : baseEnd_5607406 < baseStart_5607406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607444 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5607444 : Nat := 118140960795 + 5607444 * 2 ^ 59
def prefixEnd_5607444 : Nat := 4983230072969 + 3 ^ 40 * 5607444 * 2
def baseEnd_5607444 : Nat := 959771338390088027753947

theorem tailTrace_5607444 : CollatzResearch.WordTrace tailWord_5607444 prefixEnd_5607444 959771338390088027753947 := by
  unfold tailWord_5607444
  simp only [CollatzResearch.WordTrace]
  refine ⟨102260142348597769017946693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136346856464797025357262257 102260142348597769017946693)
  ·
    refine ⟨19173776690362081690865005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102260142348597769017946693 19173776690362081690865005)
    ·
      refine ⟨7190166258885780634074377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19173776690362081690865005 7190166258885780634074377)
      ·
        refine ⟨5392624694164335475555783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7190166258885780634074377 5392624694164335475555783)
        ·
          refine ⟨8088937041246503213333675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392624694164335475555783 8088937041246503213333675)
          ·
            refine ⟨12133405561869754820000513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088937041246503213333675 12133405561869754820000513)
            ·
              refine ⟨9100054171402316115000385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133405561869754820000513 9100054171402316115000385)
              ·
                refine ⟨6825040628551737086250289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9100054171402316115000385 6825040628551737086250289)
                ·
                  refine ⟨5118780471413802814687717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825040628551737086250289 5118780471413802814687717)
                  ·
                    refine ⟨959771338390088027753947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118780471413802814687717 959771338390088027753947)
                    ·
                      rfl

theorem cell23_5607444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5607444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607444 prefixEnd_5607444 := by exact prefixLift 5607444
  have htrace : WordTrace (prefixWord ++ tailWord_5607444) baseStart_5607444 baseEnd_5607444 := by
    simpa [prefixWord, tailWord_5607444, baseEnd_5607444] using wordTrace_append hprefix tailTrace_5607444
  have hstable : (prefixWord ++ tailWord_5607444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607444).length < 2 ^ (prefixWord ++ tailWord_5607444).sum := by decide
  have hdescent : baseEnd_5607444 < baseStart_5607444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607450 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_5607450 : Nat := 118140960795 + 5607450 * 2 ^ 59
def prefixEnd_5607450 : Nat := 4983230072969 + 3 ^ 40 * 5607450 * 2
def baseEnd_5607450 : Nat := 2879317096054191059786813

theorem tailTrace_5607450 : CollatzResearch.WordTrace tailWord_5607450 prefixEnd_5607450 2879317096054191059786813 := by
  unfold tailWord_5607450
  simp only [CollatzResearch.WordTrace]
  refine ⟨51130125883793450265152951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136347002356782534040407869 51130125883793450265152951)
  ·
    refine ⟨76695188825690175397729427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51130125883793450265152951 76695188825690175397729427)
    ·
      refine ⟨115042783238535263096594141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76695188825690175397729427 115042783238535263096594141)
      ·
        refine ⟨43141043714450723661222803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115042783238535263096594141 43141043714450723661222803)
        ·
          refine ⟨64711565571676085491834205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43141043714450723661222803 64711565571676085491834205)
          ·
            refine ⟨24266837089378532059437827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64711565571676085491834205 24266837089378532059437827)
            ·
              refine ⟨36400255634067798089156741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24266837089378532059437827 36400255634067798089156741)
              ·
                refine ⟨6825047931387712141716889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36400255634067798089156741 6825047931387712141716889)
                ·
                  refine ⟨5118785948540784106287667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825047931387712141716889 5118785948540784106287667)
                  ·
                    refine ⟨7678178922811176159431501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118785948540784106287667 7678178922811176159431501)
                    ·
                      refine ⟨2879317096054191059786813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678178922811176159431501 2879317096054191059786813)
                      ·
                        rfl

theorem cell23_5607450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_5607450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607450 prefixEnd_5607450 := by exact prefixLift 5607450
  have htrace : WordTrace (prefixWord ++ tailWord_5607450) baseStart_5607450 baseEnd_5607450 := by
    simpa [prefixWord, tailWord_5607450, baseEnd_5607450] using wordTrace_append hprefix tailTrace_5607450
  have hstable : (prefixWord ++ tailWord_5607450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607450).length < 2 ^ (prefixWord ++ tailWord_5607450).sum := by decide
  have hdescent : baseEnd_5607450 < baseStart_5607450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607494 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5607494 : Nat := 118140960795 + 5607494 * 2 ^ 59
def prefixEnd_5607494 : Nat := 4983230072969 + 3 ^ 40 * 5607494 * 2
def baseEnd_5607494 : Nat := 2879339689202988887636611

theorem tailTrace_5607494 : CollatzResearch.WordTrace tailWord_5607494 prefixEnd_5607494 2879339689202988887636611 := by
  unfold tailWord_5607494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391315885844199892975423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136348072231342931050142357 6391315885844199892975423)
  ·
    refine ⟨9586973828766299839463135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391315885844199892975423 9586973828766299839463135)
    ·
      refine ⟨14380460743149449759194703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9586973828766299839463135 14380460743149449759194703)
      ·
        refine ⟨21570691114724174638792055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14380460743149449759194703 21570691114724174638792055)
        ·
          refine ⟨32356036672086261958188083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21570691114724174638792055 32356036672086261958188083)
          ·
            refine ⟨48534055008129392937282125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32356036672086261958188083 48534055008129392937282125)
            ·
              refine ⟨18200270628048522351480797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48534055008129392937282125 18200270628048522351480797)
              ·
                refine ⟨6825101485518195881805299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18200270628048522351480797 6825101485518195881805299)
                ·
                  refine ⟨10237652228277293822707949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825101485518195881805299 10237652228277293822707949)
                  ·
                    refine ⟨3839119585603985183515481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10237652228277293822707949 3839119585603985183515481)
                    ·
                      refine ⟨2879339689202988887636611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839119585603985183515481 2879339689202988887636611)
                      ·
                        rfl

theorem cell23_5607494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5607494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607494 prefixEnd_5607494 := by exact prefixLift 5607494
  have htrace : WordTrace (prefixWord ++ tailWord_5607494) baseStart_5607494 baseEnd_5607494 := by
    simpa [prefixWord, tailWord_5607494, baseEnd_5607494] using wordTrace_append hprefix tailTrace_5607494
  have hstable : (prefixWord ++ tailWord_5607494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607494).length < 2 ^ (prefixWord ++ tailWord_5607494).sum := by decide
  have hdescent : baseEnd_5607494 < baseStart_5607494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607513 : List Nat := [1, 2, 1, 2, 2, 1, 3, 6, 5]
def baseStart_5607513 : Nat := 118140960795 + 5607513 * 2 ^ 59
def prefixEnd_5607513 : Nat := 4983230072969 + 3 ^ 40 * 5607513 * 2
def baseEnd_5607513 : Nat := 319927716148380479255447

theorem tailTrace_5607513 : CollatzResearch.WordTrace tailWord_5607513 prefixEnd_5607513 319927716148380479255447 := by
  unfold tailWord_5607513
  simp only [CollatzResearch.WordTrace]
  refine ⟨204522801333945562820155193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136348534222630375213436795 204522801333945562820155193)
  ·
    refine ⟨153392101000459172115116395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204522801333945562820155193 153392101000459172115116395)
    ·
      refine ⟨230088151500688758172674593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153392101000459172115116395 230088151500688758172674593)
      ·
        refine ⟨172566113625516568629505945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230088151500688758172674593 172566113625516568629505945)
        ·
          refine ⟨129424585219137426472129459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172566113625516568629505945 129424585219137426472129459)
          ·
            refine ⟨194136877828706139708194189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129424585219137426472129459 194136877828706139708194189)
            ·
              refine ⟨72801329185764802390572821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194136877828706139708194189 72801329185764802390572821)
              ·
                refine ⟨3412562305582725112058101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72801329185764802390572821 3412562305582725112058101)
                ·
                  refine ⟨319927716148380479255447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412562305582725112058101 319927716148380479255447)
                  ·
                    rfl

theorem cell23_5607513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 6, 5].length) (baseStart_5607513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607513 prefixEnd_5607513 := by exact prefixLift 5607513
  have htrace : WordTrace (prefixWord ++ tailWord_5607513) baseStart_5607513 baseEnd_5607513 := by
    simpa [prefixWord, tailWord_5607513, baseEnd_5607513] using wordTrace_append hprefix tailTrace_5607513
  have hstable : (prefixWord ++ tailWord_5607513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607513).length < 2 ^ (prefixWord ++ tailWord_5607513).sum := by decide
  have hdescent : baseEnd_5607513 < baseStart_5607513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607518 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5607518 : Nat := 118140960795 + 5607518 * 2 ^ 59
def prefixEnd_5607518 : Nat := 4983230072969 + 3 ^ 40 * 5607518 * 2
def baseEnd_5607518 : Nat := 2879352012738696793736501

theorem tailTrace_5607518 : CollatzResearch.WordTrace tailWord_5607518 prefixEnd_5607518 2879352012738696793736501 := by
  unfold tailWord_5607518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25565372962365931084260901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136348655799284965782724805 25565372962365931084260901)
  ·
    refine ⟨4793507430443612078298919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25565372962365931084260901 4793507430443612078298919)
    ·
      refine ⟨7190261145665418117448379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793507430443612078298919 7190261145665418117448379)
      ·
        refine ⟨10785391718498127176172569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190261145665418117448379 10785391718498127176172569)
        ·
          refine ⟨8089043788873595382129427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785391718498127176172569 8089043788873595382129427)
          ·
            refine ⟨12133565683310393073194141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089043788873595382129427 12133565683310393073194141)
            ·
              refine ⟨4550087131241397402447803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12133565683310393073194141 4550087131241397402447803)
              ·
                refine ⟨6825130696862096103671705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550087131241397402447803 6825130696862096103671705)
                ·
                  refine ⟨5118848022646572077753779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825130696862096103671705 5118848022646572077753779)
                  ·
                    refine ⟨7678272033969858116630669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118848022646572077753779 7678272033969858116630669)
                    ·
                      refine ⟨2879352012738696793736501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678272033969858116630669 2879352012738696793736501)
                      ·
                        rfl

theorem cell23_5607518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5607518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607518 prefixEnd_5607518 := by exact prefixLift 5607518
  have htrace : WordTrace (prefixWord ++ tailWord_5607518) baseStart_5607518 baseEnd_5607518 := by
    simpa [prefixWord, tailWord_5607518, baseEnd_5607518] using wordTrace_append hprefix tailTrace_5607518
  have hstable : (prefixWord ++ tailWord_5607518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607518).length < 2 ^ (prefixWord ++ tailWord_5607518).sum := by decide
  have hdescent : baseEnd_5607518 < baseStart_5607518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607523 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5607523 : Nat := 118140960795 + 5607523 * 2 ^ 59
def prefixEnd_5607523 : Nat := 4983230072969 + 3 ^ 40 * 5607523 * 2
def baseEnd_5607523 : Nat := 2879354580141969274173977

theorem tailTrace_5607523 : CollatzResearch.WordTrace tailWord_5607523 prefixEnd_5607523 2879354580141969274173977 := by
  unfold tailWord_5607523
  simp only [CollatzResearch.WordTrace]
  refine ⟨204523166063909334528019223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136348777375939556352012815 204523166063909334528019223)
  ·
    refine ⟨306784749095864001792028835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204523166063909334528019223 306784749095864001792028835)
    ·
      refine ⟨460177123643796002688043253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306784749095864001792028835 460177123643796002688043253)
      ·
        refine ⟨43141605341605875252004055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 460177123643796002688043253 43141605341605875252004055)
        ·
          refine ⟨64712408012408812878006083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43141605341605875252004055 64712408012408812878006083)
          ·
            refine ⟨97068612018613219317009125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64712408012408812878006083 97068612018613219317009125)
            ·
              refine ⟨18200364753489978621939211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97068612018613219317009125 18200364753489978621939211)
              ·
                refine ⟨27300547130234967932908817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18200364753489978621939211 27300547130234967932908817)
                ·
                  refine ⟨20475410347676225949681613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27300547130234967932908817 20475410347676225949681613)
                  ·
                    refine ⟨7678278880378584731130605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20475410347676225949681613 7678278880378584731130605)
                    ·
                      refine ⟨2879354580141969274173977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678278880378584731130605 2879354580141969274173977)
                      ·
                        rfl

theorem cell23_5607523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5607523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607523 prefixEnd_5607523 := by exact prefixLift 5607523
  have htrace : WordTrace (prefixWord ++ tailWord_5607523) baseStart_5607523 baseEnd_5607523 := by
    simpa [prefixWord, tailWord_5607523, baseEnd_5607523] using wordTrace_append hprefix tailTrace_5607523
  have hstable : (prefixWord ++ tailWord_5607523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607523).length < 2 ^ (prefixWord ++ tailWord_5607523).sum := by decide
  have hdescent : baseEnd_5607523 < baseStart_5607523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607560 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_5607560 : Nat := 118140960795 + 5607560 * 2 ^ 59
def prefixEnd_5607560 : Nat := 4983230072969 + 3 ^ 40 * 5607560 * 2
def baseEnd_5607560 : Nat := 959791192975395209803769

theorem tailTrace_5607560 : CollatzResearch.WordTrace tailWord_5607560 prefixEnd_5607560 959791192975395209803769 := by
  unfold tailWord_5607560
  simp only [CollatzResearch.WordTrace]
  refine ⟨102262257782387644923558067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136349677043183526564744089 102262257782387644923558067)
  ·
    refine ⟨153393386673581467385337101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102262257782387644923558067 153393386673581467385337101)
    ·
      refine ⟨57522520002593050269501413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153393386673581467385337101 57522520002593050269501413)
      ·
        refine ⟨10785472500486196925531515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57522520002593050269501413 10785472500486196925531515)
        ·
          refine ⟨16178208750729295388297273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785472500486196925531515 16178208750729295388297273)
          ·
            refine ⟨12133656563046971541222955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16178208750729295388297273 12133656563046971541222955)
            ·
              refine ⟨18200484844570457311834433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12133656563046971541222955 18200484844570457311834433)
              ·
                refine ⟨13650363633427842983875825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18200484844570457311834433 13650363633427842983875825)
                ·
                  refine ⟨10237772725070882237906869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13650363633427842983875825 10237772725070882237906869)
                  ·
                    refine ⟨959791192975395209803769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10237772725070882237906869 959791192975395209803769)
                    ·
                      rfl

theorem cell23_5607560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_5607560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607560 prefixEnd_5607560 := by exact prefixLift 5607560
  have htrace : WordTrace (prefixWord ++ tailWord_5607560) baseStart_5607560 baseEnd_5607560 := by
    simpa [prefixWord, tailWord_5607560, baseEnd_5607560] using wordTrace_append hprefix tailTrace_5607560
  have hstable : (prefixWord ++ tailWord_5607560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607560).length < 2 ^ (prefixWord ++ tailWord_5607560).sum := by decide
  have hdescent : baseEnd_5607560 < baseStart_5607560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607580 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5607580 : Nat := 118140960795 + 5607580 * 2 ^ 59
def prefixEnd_5607580 : Nat := 4983230072969 + 3 ^ 40 * 5607580 * 2
def baseEnd_5607580 : Nat := 2879383848539275551161215

theorem tailTrace_5607580 : CollatzResearch.WordTrace tailWord_5607580 prefixEnd_5607580 2879383848539275551161215 := by
  unfold tailWord_5607580
  simp only [CollatzResearch.WordTrace]
  refine ⟨102262622512351416631422097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136350163349801888841896129 102262622512351416631422097)
  ·
    refine ⟨76696966884263562473566573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102262622512351416631422097 76696966884263562473566573)
    ·
      refine ⟨28761362581598835927587465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76696966884263562473566573 28761362581598835927587465)
      ·
        refine ⟨21571021936199126945690599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28761362581598835927587465 21571021936199126945690599)
        ·
          refine ⟨32356532904298690418535899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21571021936199126945690599 32356532904298690418535899)
          ·
            refine ⟨48534799356448035627803849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32356532904298690418535899 48534799356448035627803849)
            ·
              refine ⟨36401099517336026720852887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48534799356448035627803849 36401099517336026720852887)
              ·
                refine ⟨54601649276004040081279331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36401099517336026720852887 54601649276004040081279331)
                ·
                  refine ⟨81902473914006060121918997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54601649276004040081279331 81902473914006060121918997)
                  ·
                    refine ⟨3839178464719034068214953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81902473914006060121918997 3839178464719034068214953)
                    ·
                      refine ⟨2879383848539275551161215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839178464719034068214953 2879383848539275551161215)
                      ·
                        rfl

theorem cell23_5607580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5607580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607580 prefixEnd_5607580 := by exact prefixLift 5607580
  have htrace : WordTrace (prefixWord ++ tailWord_5607580) baseStart_5607580 baseEnd_5607580 := by
    simpa [prefixWord, tailWord_5607580, baseEnd_5607580] using wordTrace_append hprefix tailTrace_5607580
  have hstable : (prefixWord ++ tailWord_5607580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607580).length < 2 ^ (prefixWord ++ tailWord_5607580).sum := by decide
  have hdescent : baseEnd_5607580 < baseStart_5607580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607597 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_5607597 : Nat := 118140960795 + 5607597 * 2 ^ 59
def prefixEnd_5607597 : Nat := 4983230072969 + 3 ^ 40 * 5607597 * 2
def baseEnd_5607597 : Nat := 2879392577710401984648637

theorem tailTrace_5607597 : CollatzResearch.WordTrace tailWord_5607597 prefixEnd_5607597 2879392577710401984648637 := by
  unfold tailWord_5607597
  simp only [CollatzResearch.WordTrace]
  refine ⟨204525865065641245166213045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136350576710427496777475363 204525865065641245166213045)
  ·
    refine ⟨19174299849903866734332473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204525865065641245166213045 19174299849903866734332473)
    ·
      refine ⟨14380724887427900050749355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19174299849903866734332473 14380724887427900050749355)
      ·
        refine ⟨21571087331141850076124033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14380724887427900050749355 21571087331141850076124033)
        ·
          refine ⟨16178315498356387557093025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21571087331141850076124033 16178315498356387557093025)
          ·
            refine ⟨12133736623767290667819769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16178315498356387557093025 12133736623767290667819769)
            ·
              refine ⟨9100302467825468000864827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133736623767290667819769 9100302467825468000864827)
              ·
                refine ⟨13650453701738202001297241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9100302467825468000864827 13650453701738202001297241)
                ·
                  refine ⟨10237840276303651500972931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13650453701738202001297241 10237840276303651500972931)
                  ·
                    refine ⟨15356760414455477251459397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10237840276303651500972931 15356760414455477251459397)
                    ·
                      refine ⟨2879392577710401984648637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15356760414455477251459397 2879392577710401984648637)
                      ·
                        rfl

theorem cell23_5607597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_5607597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607597 prefixEnd_5607597 := by exact prefixLift 5607597
  have htrace : WordTrace (prefixWord ++ tailWord_5607597) baseStart_5607597 baseEnd_5607597 := by
    simpa [prefixWord, tailWord_5607597, baseEnd_5607597] using wordTrace_append hprefix tailTrace_5607597
  have hstable : (prefixWord ++ tailWord_5607597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607597).length < 2 ^ (prefixWord ++ tailWord_5607597).sum := by decide
  have hdescent : baseEnd_5607597 < baseStart_5607597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607620 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 6]
def baseStart_5607620 : Nat := 118140960795 + 5607620 * 2 ^ 59
def prefixEnd_5607620 : Nat := 4983230072969 + 3 ^ 40 * 5607620 * 2
def baseEnd_5607620 : Nat := 319933820862828377184559

theorem tailTrace_5607620 : CollatzResearch.WordTrace tailWord_5607620 prefixEnd_5607620 319933820862828377184559 := by
  unfold tailWord_5607620
  simp only [CollatzResearch.WordTrace]
  refine ⟨102263351972278960047150157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136351135963038613396200209 102263351972278960047150157)
  ·
    refine ⟨38348756989604610017681309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102263351972278960047150157 38348756989604610017681309)
    ·
      refine ⟨14380783871101728756630491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38348756989604610017681309 14380783871101728756630491)
      ·
        refine ⟨21571175806652593134945737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14380783871101728756630491 21571175806652593134945737)
        ·
          refine ⟨16178381854989444851209303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21571175806652593134945737 16178381854989444851209303)
          ·
            refine ⟨24267572782484167276813955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178381854989444851209303 24267572782484167276813955)
            ·
              refine ⟨36401359173726250915220933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24267572782484167276813955 36401359173726250915220933)
              ·
                refine ⟨6825254845073672046603925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36401359173726250915220933 6825254845073672046603925)
                ·
                  refine ⟨319933820862828377184559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6825254845073672046603925 319933820862828377184559)
                  ·
                    rfl

theorem cell23_5607620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_5607620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607620 prefixEnd_5607620 := by exact prefixLift 5607620
  have htrace : WordTrace (prefixWord ++ tailWord_5607620) baseStart_5607620 baseEnd_5607620 := by
    simpa [prefixWord, tailWord_5607620, baseEnd_5607620] using wordTrace_append hprefix tailTrace_5607620
  have hstable : (prefixWord ++ tailWord_5607620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607620).length < 2 ^ (prefixWord ++ tailWord_5607620).sum := by decide
  have hdescent : baseEnd_5607620 < baseStart_5607620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607633 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 3, 5]
def baseStart_5607633 : Nat := 118140960795 + 5607633 * 2 ^ 59
def prefixEnd_5607633 : Nat := 4983230072969 + 3 ^ 40 * 5607633 * 2
def baseEnd_5607633 : Nat := 959803687671321281266157

theorem tailTrace_5607633 : CollatzResearch.WordTrace tailWord_5607633 prefixEnd_5607633 959803687671321281266157 := by
  unfold tailWord_5607633
  simp only [CollatzResearch.WordTrace]
  refine ⟨204527178093510823314523553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136351452062340548876349035 204527178093510823314523553)
  ·
    refine ⟨153395383570133117485892665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204527178093510823314523553 153395383570133117485892665)
    ·
      refine ⟨115046537677599838114419499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153395383570133117485892665 115046537677599838114419499)
      ·
        refine ⟨172569806516399757171629249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115046537677599838114419499 172569806516399757171629249)
        ·
          refine ⟨129427354887299817878721937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172569806516399757171629249 129427354887299817878721937)
          ·
            refine ⟨97070516165474863409041453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129427354887299817878721937 97070516165474863409041453)
            ·
              refine ⟨36401443562053073778390545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97070516165474863409041453 36401443562053073778390545)
              ·
                refine ⟨27301082671539805333792909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36401443562053073778390545 27301082671539805333792909)
                ·
                  refine ⟨10237906001827427000172341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27301082671539805333792909 10237906001827427000172341)
                  ·
                    refine ⟨959803687671321281266157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10237906001827427000172341 959803687671321281266157)
                    ·
                      rfl

theorem cell23_5607633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_5607633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607633 prefixEnd_5607633 := by exact prefixLift 5607633
  have htrace : WordTrace (prefixWord ++ tailWord_5607633) baseStart_5607633 baseEnd_5607633 := by
    simpa [prefixWord, tailWord_5607633, baseEnd_5607633] using wordTrace_append hprefix tailTrace_5607633
  have hstable : (prefixWord ++ tailWord_5607633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607633).length < 2 ^ (prefixWord ++ tailWord_5607633).sum := by decide
  have hdescent : baseEnd_5607633 < baseStart_5607633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607651 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5607651 : Nat := 118140960795 + 5607651 * 2 ^ 59
def prefixEnd_5607651 : Nat := 4983230072969 + 3 ^ 40 * 5607651 * 2
def baseEnd_5607651 : Nat := 2879420305665744773373389

theorem tailTrace_5607651 : CollatzResearch.WordTrace tailWord_5607651 prefixEnd_5607651 2879420305665744773373389 := by
  unfold tailWord_5607651
  simp only [CollatzResearch.WordTrace]
  refine ⟨204527834607445612388678807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136351889738297074925785871 204527834607445612388678807)
  ·
    refine ⟨306791751911168418583018211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204527834607445612388678807 306791751911168418583018211)
    ·
      refine ⟨460187627866752627874527317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306791751911168418583018211 460187627866752627874527317)
      ·
        refine ⟨5392823764063507357904617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 460187627866752627874527317 5392823764063507357904617)
        ·
          refine ⟨4044617823047630518428463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5392823764063507357904617 4044617823047630518428463)
          ·
            refine ⟨6066926734571445777642695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044617823047630518428463 6066926734571445777642695)
            ·
              refine ⟨9100390101857168666464043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066926734571445777642695 9100390101857168666464043)
              ·
                refine ⟨13650585152785752999696065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9100390101857168666464043 13650585152785752999696065)
                ·
                  refine ⟨10237938864589314749772049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13650585152785752999696065 10237938864589314749772049)
                  ·
                    refine ⟨7678454148441986062329037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10237938864589314749772049 7678454148441986062329037)
                    ·
                      refine ⟨2879420305665744773373389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678454148441986062329037 2879420305665744773373389)
                      ·
                        rfl

theorem cell23_5607651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5607651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607651 prefixEnd_5607651 := by exact prefixLift 5607651
  have htrace : WordTrace (prefixWord ++ tailWord_5607651) baseStart_5607651 baseEnd_5607651 := by
    simpa [prefixWord, tailWord_5607651, baseEnd_5607651] using wordTrace_append hprefix tailTrace_5607651
  have hstable : (prefixWord ++ tailWord_5607651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607651).length < 2 ^ (prefixWord ++ tailWord_5607651).sum := by decide
  have hdescent : baseEnd_5607651 < baseStart_5607651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607683 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_5607683 : Nat := 118140960795 + 5607683 * 2 ^ 59
def prefixEnd_5607683 : Nat := 4983230072969 + 3 ^ 40 * 5607683 * 2
def baseEnd_5607683 : Nat := 2879436737046688648173241

theorem tailTrace_5607683 : CollatzResearch.WordTrace tailWord_5607683 prefixEnd_5607683 2879436737046688648173241 := by
  unfold tailWord_5607683
  simp only [CollatzResearch.WordTrace]
  refine ⟨204529001743329681853843703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136352667828886454569229135 204529001743329681853843703)
  ·
    refine ⟨306793502614994522780765555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204529001743329681853843703 306793502614994522780765555)
    ·
      refine ⟨460190253922491784171148333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306793502614994522780765555 460190253922491784171148333)
      ·
        refine ⟨172571345220934419064180625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460190253922491784171148333 172571345220934419064180625)
        ·
          refine ⟨129428508915700814298135469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172571345220934419064180625 129428508915700814298135469)
          ·
            refine ⟨48535690843387805361800801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129428508915700814298135469 48535690843387805361800801)
            ·
              refine ⟨36401768132540854021350601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48535690843387805361800801 36401768132540854021350601)
              ·
                refine ⟨27301326099405640516012951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36401768132540854021350601 27301326099405640516012951)
                ·
                  refine ⟨40951989149108460774019427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27301326099405640516012951 40951989149108460774019427)
                  ·
                    refine ⟨61427983723662691161029141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40951989149108460774019427 61427983723662691161029141)
                    ·
                      refine ⟨2879436737046688648173241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61427983723662691161029141 2879436737046688648173241)
                      ·
                        rfl

theorem cell23_5607683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_5607683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607683 prefixEnd_5607683 := by exact prefixLift 5607683
  have htrace : WordTrace (prefixWord ++ tailWord_5607683) baseStart_5607683 baseEnd_5607683 := by
    simpa [prefixWord, tailWord_5607683, baseEnd_5607683] using wordTrace_append hprefix tailTrace_5607683
  have hstable : (prefixWord ++ tailWord_5607683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607683).length < 2 ^ (prefixWord ++ tailWord_5607683).sum := by decide
  have hdescent : baseEnd_5607683 < baseStart_5607683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607690 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_5607690 : Nat := 118140960795 + 5607690 * 2 ^ 59
def prefixEnd_5607690 : Nat := 4983230072969 + 3 ^ 40 * 5607690 * 2
def baseEnd_5607690 : Nat := 2879440331411270120785709

theorem tailTrace_5607690 : CollatzResearch.WordTrace tailWord_5607690 prefixEnd_5607690 2879440331411270120785709 := by
  unfold tailWord_5607690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51132314263576080512337131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136352838036202881366232349 51132314263576080512337131)
  ·
    refine ⟨76698471395364120768505697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51132314263576080512337131 76698471395364120768505697)
    ·
      refine ⟨57523853546523090576379273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76698471395364120768505697 57523853546523090576379273)
      ·
        refine ⟨43142890159892317932284455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57523853546523090576379273 43142890159892317932284455)
        ·
          refine ⟨64714335239838476898426683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43142890159892317932284455 64714335239838476898426683)
          ·
            refine ⟨97071502859757715347640025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64714335239838476898426683 97071502859757715347640025)
            ·
              refine ⟨72803627144818286510730019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97071502859757715347640025 72803627144818286510730019)
              ·
                refine ⟨109205440717227429766095029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72803627144818286510730019 109205440717227429766095029)
                ·
                  refine ⟨10238010067240071540571409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109205440717227429766095029 10238010067240071540571409)
                  ·
                    refine ⟨7678507550430053655428557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10238010067240071540571409 7678507550430053655428557)
                    ·
                      refine ⟨2879440331411270120785709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678507550430053655428557 2879440331411270120785709)
                      ·
                        rfl

theorem cell23_5607690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_5607690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607690 prefixEnd_5607690 := by exact prefixLift 5607690
  have htrace : WordTrace (prefixWord ++ tailWord_5607690) baseStart_5607690 baseEnd_5607690 := by
    simpa [prefixWord, tailWord_5607690, baseEnd_5607690] using wordTrace_append hprefix tailTrace_5607690
  have hstable : (prefixWord ++ tailWord_5607690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607690).length < 2 ^ (prefixWord ++ tailWord_5607690).sum := by decide
  have hdescent : baseEnd_5607690 < baseStart_5607690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607738 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_5607738 : Nat := 118140960795 + 5607738 * 2 ^ 59
def prefixEnd_5607738 : Nat := 4983230072969 + 3 ^ 40 * 5607738 * 2
def baseEnd_5607738 : Nat := 2879464978482685932985489

theorem tailTrace_5607738 : CollatzResearch.WordTrace tailWord_5607738 prefixEnd_5607738 2879464978482685932985489 := by
  unfold tailWord_5607738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51132751939532606561773967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136354005172086950831397245 51132751939532606561773967)
  ·
    refine ⟨76699127909298909842660951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51132751939532606561773967 76699127909298909842660951)
    ·
      refine ⟨115048691863948364763991427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76699127909298909842660951 115048691863948364763991427)
      ·
        refine ⟨172573037795922547145987141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115048691863948364763991427 172573037795922547145987141)
        ·
          refine ⟨32357444586735477589872589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172573037795922547145987141 32357444586735477589872589)
          ·
            refine ⟨12134041720025804096202221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32357444586735477589872589 12134041720025804096202221)
            ·
              refine ⟨4550265645009676536075833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134041720025804096202221 4550265645009676536075833)
              ·
                refine ⟨3412699233757257402056875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550265645009676536075833 3412699233757257402056875)
                ·
                  refine ⟨5119048850635886103085313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412699233757257402056875 5119048850635886103085313)
                  ·
                    refine ⟨3839286637976914577313985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119048850635886103085313 3839286637976914577313985)
                    ·
                      refine ⟨2879464978482685932985489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839286637976914577313985 2879464978482685932985489)
                      ·
                        rfl

theorem cell23_5607738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_5607738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607738 prefixEnd_5607738 := by exact prefixLift 5607738
  have htrace : WordTrace (prefixWord ++ tailWord_5607738) baseStart_5607738 baseEnd_5607738 := by
    simpa [prefixWord, tailWord_5607738, baseEnd_5607738] using wordTrace_append hprefix tailTrace_5607738
  have hstable : (prefixWord ++ tailWord_5607738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607738).length < 2 ^ (prefixWord ++ tailWord_5607738).sum := by decide
  have hdescent : baseEnd_5607738 < baseStart_5607738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607748 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5607748 : Nat := 118140960795 + 5607748 * 2 ^ 59
def prefixEnd_5607748 : Nat := 4983230072969 + 3 ^ 40 * 5607748 * 2
def baseEnd_5607748 : Nat := 959823371096410297953481

theorem tailTrace_5607748 : CollatzResearch.WordTrace tailWord_5607748 prefixEnd_5607748 959823371096410297953481 := by
  unfold tailWord_5607748
  simp only [CollatzResearch.WordTrace]
  refine ⟨102265686244047098977479949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136354248325396131969973265 102265686244047098977479949)
  ·
    refine ⟨38349632341517662116554981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102265686244047098977479949 38349632341517662116554981)
    ·
      refine ⟨7190556064034561646854059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38349632341517662116554981 7190556064034561646854059)
      ·
        refine ⟨10785834096051842470281089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190556064034561646854059 10785834096051842470281089)
        ·
          refine ⟨8089375572038881852710817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10785834096051842470281089 8089375572038881852710817)
          ·
            refine ⟨6067031679029161389533113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089375572038881852710817 6067031679029161389533113)
            ·
              refine ⟨4550273759271871042149835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067031679029161389533113 4550273759271871042149835)
              ·
                refine ⟨6825410638907806563224753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550273759271871042149835 6825410638907806563224753)
                ·
                  refine ⟨5119057979180854922418565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825410638907806563224753 5119057979180854922418565)
                  ·
                    refine ⟨959823371096410297953481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119057979180854922418565 959823371096410297953481)
                    ·
                      rfl

theorem cell23_5607748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5607748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607748 prefixEnd_5607748 := by exact prefixLift 5607748
  have htrace : WordTrace (prefixWord ++ tailWord_5607748) baseStart_5607748 baseEnd_5607748 := by
    simpa [prefixWord, tailWord_5607748, baseEnd_5607748] using wordTrace_append hprefix tailTrace_5607748
  have hstable : (prefixWord ++ tailWord_5607748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607748).length < 2 ^ (prefixWord ++ tailWord_5607748).sum := by decide
  have hdescent : baseEnd_5607748 < baseStart_5607748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607753 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 8]
def baseStart_5607753 : Nat := 118140960795 + 5607753 * 2 ^ 59
def prefixEnd_5607753 : Nat := 4983230072969 + 3 ^ 40 * 5607753 * 2
def baseEnd_5607753 : Nat := 959824226897501124765973

theorem tailTrace_5607753 : CollatzResearch.WordTrace tailWord_5607753 prefixEnd_5607753 959824226897501124765973 := by
  unfold tailWord_5607753
  simp only [CollatzResearch.WordTrace]
  refine ⟨204531554853076083808891913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136354369902050722539261275 204531554853076083808891913)
  ·
    refine ⟨153398666139807062856668935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204531554853076083808891913 153398666139807062856668935)
    ·
      refine ⟨230097999209710594285003403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153398666139807062856668935 230097999209710594285003403)
      ·
        refine ⟨345146998814565891427505105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230097999209710594285003403 345146998814565891427505105)
        ·
          refine ⟨258860249110924418570628829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345146998814565891427505105 258860249110924418570628829)
          ·
            refine ⟨97072593416596656963985811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258860249110924418570628829 97072593416596656963985811)
            ·
              refine ⟨145608890124894985445978717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97072593416596656963985811 145608890124894985445978717)
              ·
                refine ⟨54603333796835619542242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145608890124894985445978717 54603333796835619542242019)
                ·
                  refine ⟨81905000695253429313363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54603333796835619542242019 81905000695253429313363029)
                  ·
                    refine ⟨959824226897501124765973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81905000695253429313363029 959824226897501124765973)
                    ·
                      rfl

theorem cell23_5607753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_5607753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607753 prefixEnd_5607753 := by exact prefixLift 5607753
  have htrace : WordTrace (prefixWord ++ tailWord_5607753) baseStart_5607753 baseEnd_5607753 := by
    simpa [prefixWord, tailWord_5607753, baseEnd_5607753] using wordTrace_append hprefix tailTrace_5607753
  have hstable : (prefixWord ++ tailWord_5607753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607753).length < 2 ^ (prefixWord ++ tailWord_5607753).sum := by decide
  have hdescent : baseEnd_5607753 < baseStart_5607753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607764 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_5607764 : Nat := 118140960795 + 5607764 * 2 ^ 59
def prefixEnd_5607764 : Nat := 4983230072969 + 3 ^ 40 * 5607764 * 2
def baseEnd_5607764 : Nat := 2879478328979702831260369

theorem tailTrace_5607764 : CollatzResearch.WordTrace tailWord_5607764 prefixEnd_5607764 2879478328979702831260369 := by
  unfold tailWord_5607764
  simp only [CollatzResearch.WordTrace]
  refine ⟨102265978028018116343771173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136354637370690821791694897 102265978028018116343771173)
  ·
    refine ⟨19174870880253396814457095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102265978028018116343771173 19174870880253396814457095)
    ·
      refine ⟨28762306320380095221685643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19174870880253396814457095 28762306320380095221685643)
      ·
        refine ⟨43143459480570142832528465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28762306320380095221685643 43143459480570142832528465)
        ·
          refine ⟨32357594610427607124396349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43143459480570142832528465 32357594610427607124396349)
          ·
            refine ⟨12134097978910352671648631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32357594610427607124396349 12134097978910352671648631)
            ·
              refine ⟨18201146968365529007472947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12134097978910352671648631 18201146968365529007472947)
              ·
                refine ⟨27301720452548293511209421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18201146968365529007472947 27301720452548293511209421)
                ·
                  refine ⟨10238145169705610066703533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27301720452548293511209421 10238145169705610066703533)
                  ·
                    refine ⟨3839304438639603775013825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10238145169705610066703533 3839304438639603775013825)
                    ·
                      refine ⟨2879478328979702831260369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839304438639603775013825 2879478328979702831260369)
                      ·
                        rfl

theorem cell23_5607764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_5607764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607764 prefixEnd_5607764 := by exact prefixLift 5607764
  have htrace : WordTrace (prefixWord ++ tailWord_5607764) baseStart_5607764 baseEnd_5607764 := by
    simpa [prefixWord, tailWord_5607764, baseEnd_5607764] using wordTrace_append hprefix tailTrace_5607764
  have hstable : (prefixWord ++ tailWord_5607764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607764).length < 2 ^ (prefixWord ++ tailWord_5607764).sum := by decide
  have hdescent : baseEnd_5607764 < baseStart_5607764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607780 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_5607780 : Nat := 118140960795 + 5607780 * 2 ^ 59
def prefixEnd_5607780 : Nat := 4983230072969 + 3 ^ 40 * 5607780 * 2
def baseEnd_5607780 : Nat := 2879486544670174768660295

theorem tailTrace_5607780 : CollatzResearch.WordTrace tailWord_5607780 prefixEnd_5607780 2879486544670174768660295 := by
  unfold tailWord_5607780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102266269811989133710062397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136355026415985511613416529 102266269811989133710062397)
  ·
    refine ⟨38349851179495925141273399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102266269811989133710062397 38349851179495925141273399)
    ·
      refine ⟨57524776769243887711910099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38349851179495925141273399 57524776769243887711910099)
      ·
        refine ⟨86287165153865831567865149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57524776769243887711910099 86287165153865831567865149)
        ·
          refine ⟨32357686932699686837949431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86287165153865831567865149 32357686932699686837949431)
          ·
            refine ⟨48536530399049530256924147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32357686932699686837949431 48536530399049530256924147)
            ·
              refine ⟨72804795598574295385386221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48536530399049530256924147 72804795598574295385386221)
              ·
                refine ⟨27301798349465360769519833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72804795598574295385386221 27301798349465360769519833)
                ·
                  refine ⟨20476348762099020577139875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27301798349465360769519833 20476348762099020577139875)
                  ·
                    refine ⟨30714523143148530865709813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20476348762099020577139875 30714523143148530865709813)
                    ·
                      refine ⟨2879486544670174768660295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30714523143148530865709813 2879486544670174768660295)
                      ·
                        rfl

theorem cell23_5607780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_5607780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607780 prefixEnd_5607780 := by exact prefixLift 5607780
  have htrace : WordTrace (prefixWord ++ tailWord_5607780) baseStart_5607780 baseEnd_5607780 := by
    simpa [prefixWord, tailWord_5607780, baseEnd_5607780] using wordTrace_append hprefix tailTrace_5607780
  have hstable : (prefixWord ++ tailWord_5607780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607780).length < 2 ^ (prefixWord ++ tailWord_5607780).sum := by decide
  have hdescent : baseEnd_5607780 < baseStart_5607780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607781 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_5607781 : Nat := 118140960795 + 5607781 * 2 ^ 59
def prefixEnd_5607781 : Nat := 4983230072969 + 3 ^ 40 * 5607781 * 2
def baseEnd_5607781 : Nat := 2879487058150829264747791

theorem tailTrace_5607781 : CollatzResearch.WordTrace tailWord_5607781 prefixEnd_5607781 2879487058150829264747791 := by
  unfold tailWord_5607781
  simp only [CollatzResearch.WordTrace]
  refine ⟨204532576096974644590911197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136355050731316429727274131 204532576096974644590911197)
  ·
    refine ⟨76699716036365491721591699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204532576096974644590911197 76699716036365491721591699)
    ·
      refine ⟨115049574054548237582387549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76699716036365491721591699 115049574054548237582387549)
      ·
        refine ⟨43143590270455589093395331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115049574054548237582387549 43143590270455589093395331)
        ·
          refine ⟨64715385405683383640092997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43143590270455589093395331 64715385405683383640092997)
          ·
            refine ⟨12134134763565634432517437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64715385405683383640092997 12134134763565634432517437)
            ·
              refine ⟨4550300536337112912194039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134134763565634432517437 4550300536337112912194039)
              ·
                refine ⟨6825450804505669368291059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550300536337112912194039 6825450804505669368291059)
                ·
                  refine ⟨10238176206758504052436589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825450804505669368291059 10238176206758504052436589)
                  ·
                    refine ⟨3839316077534439019663721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10238176206758504052436589 3839316077534439019663721)
                    ·
                      refine ⟨2879487058150829264747791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839316077534439019663721 2879487058150829264747791)
                      ·
                        rfl

theorem cell23_5607781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_5607781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607781 prefixEnd_5607781 := by exact prefixLift 5607781
  have htrace : WordTrace (prefixWord ++ tailWord_5607781) baseStart_5607781 baseEnd_5607781 := by
    simpa [prefixWord, tailWord_5607781, baseEnd_5607781] using wordTrace_append hprefix tailTrace_5607781
  have hstable : (prefixWord ++ tailWord_5607781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607781).length < 2 ^ (prefixWord ++ tailWord_5607781).sum := by decide
  have hdescent : baseEnd_5607781 < baseStart_5607781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607797 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5607797 : Nat := 118140960795 + 5607797 * 2 ^ 59
def prefixEnd_5607797 : Nat := 4983230072969 + 3 ^ 40 * 5607797 * 2
def baseEnd_5607797 : Nat := 2879495273841301202147717

theorem tailTrace_5607797 : CollatzResearch.WordTrace tailWord_5607797 prefixEnd_5607797 2879495273841301202147717 := by
  unfold tailWord_5607797
  simp only [CollatzResearch.WordTrace]
  refine ⟨204533159664916679323493645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136355439776611119548995763 204533159664916679323493645)
  ·
    refine ⟨76699934874343754746310117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204533159664916679323493645 76699934874343754746310117)
    ·
      refine ⟨14381237788939454014933147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76699934874343754746310117 14381237788939454014933147)
      ·
        refine ⟨21571856683409181022399721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381237788939454014933147 21571856683409181022399721)
        ·
          refine ⟨16178892512556885766799791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21571856683409181022399721 16178892512556885766799791)
          ·
            refine ⟨24268338768835328650199687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178892512556885766799791 24268338768835328650199687)
            ·
              refine ⟨36402508153252992975299531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24268338768835328650199687 36402508153252992975299531)
              ·
                refine ⟨54603762229879489462949297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36402508153252992975299531 54603762229879489462949297)
                ·
                  refine ⟨40952821672409617097211973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54603762229879489462949297 40952821672409617097211973)
                  ·
                    refine ⟨7678654063576803205727245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40952821672409617097211973 7678654063576803205727245)
                    ·
                      refine ⟨2879495273841301202147717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678654063576803205727245 2879495273841301202147717)
                      ·
                        rfl

theorem cell23_5607797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5607797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607797 prefixEnd_5607797 := by exact prefixLift 5607797
  have htrace : WordTrace (prefixWord ++ tailWord_5607797) baseStart_5607797 baseEnd_5607797 := by
    simpa [prefixWord, tailWord_5607797, baseEnd_5607797] using wordTrace_append hprefix tailTrace_5607797
  have hstable : (prefixWord ++ tailWord_5607797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607797).length < 2 ^ (prefixWord ++ tailWord_5607797).sum := by decide
  have hdescent : baseEnd_5607797 < baseStart_5607797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607834 : List Nat := [3, 1, 1, 4, 1, 3, 2, 3, 5]
def baseStart_5607834 : Nat := 118140960795 + 5607834 * 2 ^ 59
def prefixEnd_5607834 : Nat := 4983230072969 + 3 ^ 40 * 5607834 * 2
def baseEnd_5607834 : Nat := 319946030291724173042783

theorem tailTrace_5607834 : CollatzResearch.WordTrace tailWord_5607834 prefixEnd_5607834 319946030291724173042783 := by
  unfold tailWord_5607834
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133627291445658660647639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136356339443855089761727037 51133627291445658660647639)
  ·
    refine ⟨76700440937168487990971459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51133627291445658660647639 76700440937168487990971459)
    ·
      refine ⟨115050661405752731986457189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76700440937168487990971459 115050661405752731986457189)
      ·
        refine ⟨21571999013578637247460723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115050661405752731986457189 21571999013578637247460723)
        ·
          refine ⟨32357998520367955871191085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21571999013578637247460723 32357998520367955871191085)
          ·
            refine ⟨12134249445137983451696657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32357998520367955871191085 12134249445137983451696657)
            ·
              refine ⟨9100687083853487588772493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134249445137983451696657 9100687083853487588772493)
              ·
                refine ⟨3412757656445057845789685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9100687083853487588772493 3412757656445057845789685)
                ·
                  refine ⟨319946030291724173042783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412757656445057845789685 319946030291724173042783)
                  ·
                    rfl

theorem cell23_5607834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_5607834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607834 prefixEnd_5607834 := by exact prefixLift 5607834
  have htrace : WordTrace (prefixWord ++ tailWord_5607834) baseStart_5607834 baseEnd_5607834 := by
    simpa [prefixWord, tailWord_5607834, baseEnd_5607834] using wordTrace_append hprefix tailTrace_5607834
  have hstable : (prefixWord ++ tailWord_5607834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607834).length < 2 ^ (prefixWord ++ tailWord_5607834).sum := by decide
  have hdescent : baseEnd_5607834 < baseStart_5607834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607887 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3]
def baseStart_5607887 : Nat := 118140960795 + 5607887 * 2 ^ 59
def prefixEnd_5607887 : Nat := 4983230072969 + 3 ^ 40 * 5607887 * 2
def baseEnd_5607887 : Nat := 2879541487100205850022303

theorem tailTrace_5607887 : CollatzResearch.WordTrace tailWord_5607887 prefixEnd_5607887 2879541487100205850022303 := by
  unfold tailWord_5607887
  simp only [CollatzResearch.WordTrace]
  refine ⟨204536442234590624694269915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136357628156393749796179943 204536442234590624694269915)
  ·
    refine ⟨306804663351885937041404873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204536442234590624694269915 306804663351885937041404873)
    ·
      refine ⟨230103497513914452781053655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306804663351885937041404873 230103497513914452781053655)
      ·
        refine ⟨345155246270871679171580483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230103497513914452781053655 345155246270871679171580483)
        ·
          refine ⟨517732869406307518757370725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345155246270871679171580483 517732869406307518757370725)
          ·
            refine ⟨97074913013682659767007011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 517732869406307518757370725 97074913013682659767007011)
            ·
              refine ⟨145612369520523989650510517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97074913013682659767007011 145612369520523989650510517)
              ·
                refine ⟨13651159642549124029735361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145612369520523989650510517 13651159642549124029735361)
                ·
                  refine ⟨10238369731911843022301521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13651159642549124029735361 10238369731911843022301521)
                  ·
                    refine ⟨7678777298933882266726141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10238369731911843022301521 7678777298933882266726141)
                    ·
                      refine ⟨2879541487100205850022303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678777298933882266726141 2879541487100205850022303)
                      ·
                        rfl

theorem cell23_5607887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 3].length) (baseStart_5607887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607887 prefixEnd_5607887 := by exact prefixLift 5607887
  have htrace : WordTrace (prefixWord ++ tailWord_5607887) baseStart_5607887 baseEnd_5607887 := by
    simpa [prefixWord, tailWord_5607887, baseEnd_5607887] using wordTrace_append hprefix tailTrace_5607887
  have hstable : (prefixWord ++ tailWord_5607887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607887).length < 2 ^ (prefixWord ++ tailWord_5607887).sum := by decide
  have hdescent : baseEnd_5607887 < baseStart_5607887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607930 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_5607930 : Nat := 118140960795 + 5607930 * 2 ^ 59
def prefixEnd_5607930 : Nat := 4983230072969 + 3 ^ 40 * 5607930 * 2
def baseEnd_5607930 : Nat := 2879563566768349181784605

theorem tailTrace_5607930 : CollatzResearch.WordTrace tailWord_5607930 prefixEnd_5607930 2879563566768349181784605 := by
  unfold tailWord_5607930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51134502643358710759521311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136358673715623228692056829 51134502643358710759521311)
  ·
    refine ⟨76701753965038066139281967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51134502643358710759521311 76701753965038066139281967)
    ·
      refine ⟨115052630947557099208922951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76701753965038066139281967 115052630947557099208922951)
      ·
        refine ⟨172578946421335648813384427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115052630947557099208922951 172578946421335648813384427)
        ·
          refine ⟨258868419632003473220076641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172578946421335648813384427 258868419632003473220076641)
          ·
            refine ⟨194151314724002604915057481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258868419632003473220076641 194151314724002604915057481)
            ·
              refine ⟨145613486043001953686293111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194151314724002604915057481 145613486043001953686293111)
              ·
                refine ⟨218420229064502930529439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145613486043001953686293111 218420229064502930529439667)
                ·
                  refine ⟨327630343596754395794159501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218420229064502930529439667 327630343596754395794159501)
                  ·
                    refine ⟨122861378848782898422809813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327630343596754395794159501 122861378848782898422809813)
                    ·
                      refine ⟨2879563566768349181784605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122861378848782898422809813 2879563566768349181784605)
                      ·
                        rfl

theorem cell23_5607930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_5607930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607930 prefixEnd_5607930 := by exact prefixLift 5607930
  have htrace : WordTrace (prefixWord ++ tailWord_5607930) baseStart_5607930 baseEnd_5607930 := by
    simpa [prefixWord, tailWord_5607930, baseEnd_5607930] using wordTrace_append hprefix tailTrace_5607930
  have hstable : (prefixWord ++ tailWord_5607930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607930).length < 2 ^ (prefixWord ++ tailWord_5607930).sum := by decide
  have hdescent : baseEnd_5607930 < baseStart_5607930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607938 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5607938 : Nat := 118140960795 + 5607938 * 2 ^ 59
def prefixEnd_5607938 : Nat := 4983230072969 + 3 ^ 40 * 5607938 * 2
def baseEnd_5607938 : Nat := 2879567674613585150484569

theorem tailTrace_5607938 : CollatzResearch.WordTrace tailWord_5607938 prefixEnd_5607938 2879567674613585150484569 := by
  unfold tailWord_5607938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51134575589351465101094117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136358868238270573602917645 51134575589351465101094117)
  ·
    refine ⟨9587732923003399706455147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51134575589351465101094117 9587732923003399706455147)
    ·
      refine ⟨14381599384505099559682721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587732923003399706455147 14381599384505099559682721)
      ·
        refine ⟨10786199538378824669762041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14381599384505099559682721 10786199538378824669762041)
        ·
          refine ⟨8089649653784118502321531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10786199538378824669762041 8089649653784118502321531)
          ·
            refine ⟨12134474480676177753482297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089649653784118502321531 12134474480676177753482297)
            ·
              refine ⟨9100855860507133315111723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134474480676177753482297 9100855860507133315111723)
              ·
                refine ⟨13651283790760699972667585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9100855860507133315111723 13651283790760699972667585)
                ·
                  refine ⟨10238462843070524979500689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13651283790760699972667585 10238462843070524979500689)
                  ·
                    refine ⟨7678847132302893734625517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10238462843070524979500689 7678847132302893734625517)
                    ·
                      refine ⟨2879567674613585150484569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678847132302893734625517 2879567674613585150484569)
                      ·
                        rfl

theorem cell23_5607938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5607938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607938 prefixEnd_5607938 := by exact prefixLift 5607938
  have htrace : WordTrace (prefixWord ++ tailWord_5607938) baseStart_5607938 baseEnd_5607938 := by
    simpa [prefixWord, tailWord_5607938, baseEnd_5607938] using wordTrace_append hprefix tailTrace_5607938
  have hstable : (prefixWord ++ tailWord_5607938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607938).length < 2 ^ (prefixWord ++ tailWord_5607938).sum := by decide
  have hdescent : baseEnd_5607938 < baseStart_5607938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607984 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_5607984 : Nat := 118140960795 + 5607984 * 2 ^ 59
def prefixEnd_5607984 : Nat := 4983230072969 + 3 ^ 40 * 5607984 * 2
def baseEnd_5607984 : Nat := 959863764907897323503119

theorem tailTrace_5607984 : CollatzResearch.WordTrace tailWord_5607984 prefixEnd_5607984 959863764907897323503119 := by
  unfold tailWord_5607984
  simp only [CollatzResearch.WordTrace]
  refine ⟨102269990057619605130275503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136359986743492806840367337 102269990057619605130275503)
  ·
    refine ⟨153404985086429407695413255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102269990057619605130275503 153404985086429407695413255)
    ·
      refine ⟨230107477629644111543119883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153404985086429407695413255 230107477629644111543119883)
      ·
        refine ⟨345161216444466167314679825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230107477629644111543119883 345161216444466167314679825)
        ·
          refine ⟨258870912333349625486009869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345161216444466167314679825 258870912333349625486009869)
          ·
            refine ⟨97076592125006109557253701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258870912333349625486009869 97076592125006109557253701)
            ·
              refine ⟨18201861023438645541985069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97076592125006109557253701 18201861023438645541985069)
              ·
                refine ⟨6825697883789492078244401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18201861023438645541985069 6825697883789492078244401)
                ·
                  refine ⟨5119273412842119058683301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825697883789492078244401 5119273412842119058683301)
                  ·
                    refine ⟨959863764907897323503119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119273412842119058683301 959863764907897323503119)
                    ·
                      rfl

theorem cell23_5607984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_5607984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607984 prefixEnd_5607984 := by exact prefixLift 5607984
  have htrace : WordTrace (prefixWord ++ tailWord_5607984) baseStart_5607984 baseEnd_5607984 := by
    simpa [prefixWord, tailWord_5607984, baseEnd_5607984] using wordTrace_append hprefix tailTrace_5607984
  have hstable : (prefixWord ++ tailWord_5607984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607984).length < 2 ^ (prefixWord ++ tailWord_5607984).sum := by decide
  have hdescent : baseEnd_5607984 < baseStart_5607984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607991 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 3, 2, 2]
def baseStart_5607991 : Nat := 118140960795 + 5607991 * 2 ^ 59
def prefixEnd_5607991 : Nat := 4983230072969 + 3 ^ 40 * 5607991 * 2
def baseEnd_5607991 : Nat := 2879594889088273443121825

theorem tailTrace_5607991 : CollatzResearch.WordTrace tailWord_5607991 prefixEnd_5607991 2879594889088273443121825 := by
  unfold tailWord_5607991
  simp only [CollatzResearch.WordTrace]
  refine ⟨204540235426213850456055827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136360156950809233637370551 204540235426213850456055827)
  ·
    refine ⟨306810353139320775684083741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204540235426213850456055827 306810353139320775684083741)
    ·
      refine ⟨115053882427245290881531403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306810353139320775684083741 115053882427245290881531403)
      ·
        refine ⟨172580823640867936322297105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115053882427245290881531403 172580823640867936322297105)
        ·
          refine ⟨129435617730650952241722829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172580823640867936322297105 129435617730650952241722829)
          ·
            refine ⟨48538356648994107090646061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129435617730650952241722829 48538356648994107090646061)
            ·
              refine ⟨18201883743372790158992273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48538356648994107090646061 18201883743372790158992273)
              ·
                refine ⟨13651412807529592619244205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18201883743372790158992273 13651412807529592619244205)
                ·
                  refine ⟨5119279802823597232216577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13651412807529592619244205 5119279802823597232216577)
                  ·
                    refine ⟨3839459852117697924162433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119279802823597232216577 3839459852117697924162433)
                    ·
                      refine ⟨2879594889088273443121825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839459852117697924162433 2879594889088273443121825)
                      ·
                        rfl

theorem cell23_5607991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_5607991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607991 prefixEnd_5607991 := by exact prefixLift 5607991
  have htrace : WordTrace (prefixWord ++ tailWord_5607991) baseStart_5607991 baseEnd_5607991 := by
    simpa [prefixWord, tailWord_5607991, baseEnd_5607991] using wordTrace_append hprefix tailTrace_5607991
  have hstable : (prefixWord ++ tailWord_5607991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607991).length < 2 ^ (prefixWord ++ tailWord_5607991).sum := by decide
  have hdescent : baseEnd_5607991 < baseStart_5607991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5607994 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_5607994 : Nat := 118140960795 + 5607994 * 2 ^ 59
def prefixEnd_5607994 : Nat := 4983230072969 + 3 ^ 40 * 5607994 * 2
def baseEnd_5607994 : Nat := 2879596429530236931384311

theorem tailTrace_5607994 : CollatzResearch.WordTrace tailWord_5607994 prefixEnd_5607994 2879596429530236931384311 := by
  unfold tailWord_5607994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51135086211300745492103759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136360229896801987978943357 51135086211300745492103759)
  ·
    refine ⟨76702629316951118238155639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51135086211300745492103759 76702629316951118238155639)
    ·
      refine ⟨115053943975426677357233459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76702629316951118238155639 115053943975426677357233459)
      ·
        refine ⟨172580915963140016035850189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115053943975426677357233459 172580915963140016035850189)
        ·
          refine ⟨64717843486177506013443821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172580915963140016035850189 64717843486177506013443821)
          ·
            refine ⟨24269191307316564755041433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64717843486177506013443821 24269191307316564755041433)
            ·
              refine ⟨18201893480487423566281075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24269191307316564755041433 18201893480487423566281075)
              ·
                refine ⟨27302840220731135349421613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18201893480487423566281075 27302840220731135349421613)
                ·
                  refine ⟨10238565082774175756033105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27302840220731135349421613 10238565082774175756033105)
                  ·
                    refine ⟨7678923812080631817024829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10238565082774175756033105 7678923812080631817024829)
                    ·
                      refine ⟨2879596429530236931384311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678923812080631817024829 2879596429530236931384311)
                      ·
                        rfl

theorem cell23_5607994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_5607994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5607994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5607994 prefixEnd_5607994 := by exact prefixLift 5607994
  have htrace : WordTrace (prefixWord ++ tailWord_5607994) baseStart_5607994 baseEnd_5607994 := by
    simpa [prefixWord, tailWord_5607994, baseEnd_5607994] using wordTrace_append hprefix tailTrace_5607994
  have hstable : (prefixWord ++ tailWord_5607994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5607994).length < 2 ^ (prefixWord ++ tailWord_5607994).sum := by decide
  have hdescent : baseEnd_5607994 < baseStart_5607994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5607994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608011 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 1, 2, 3]
def baseStart_5608011 : Nat := 118140960795 + 5608011 * 2 ^ 59
def prefixEnd_5608011 : Nat := 4983230072969 + 3 ^ 40 * 5608011 * 2
def baseEnd_5608011 : Nat := 2879605158701363364871733

theorem tailTrace_5608011 : CollatzResearch.WordTrace tailWord_5608011 prefixEnd_5608011 2879605158701363364871733 := by
  unfold tailWord_5608011
  simp only [CollatzResearch.WordTrace]
  refine ⟨204540964886141393871783887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136360643257427595914522591 204540964886141393871783887)
  ·
    refine ⟨306811447329212090807675831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204540964886141393871783887 306811447329212090807675831)
    ·
      refine ⟨460217170993818136211513747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306811447329212090807675831 460217170993818136211513747)
      ·
        refine ⟨690325756490727204317270621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460217170993818136211513747 690325756490727204317270621)
        ·
          refine ⟨258872158684022701618976483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 690325756490727204317270621 258872158684022701618976483)
          ·
            refine ⟨388308238026034052428464725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258872158684022701618976483 388308238026034052428464725)
            ·
              refine ⟨4550487164367586551896071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 388308238026034052428464725 4550487164367586551896071)
              ·
                refine ⟨6825730746551379827844107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550487164367586551896071 6825730746551379827844107)
                ·
                  refine ⟨10238596119827069741766161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825730746551379827844107 10238596119827069741766161)
                  ·
                    refine ⟨7678947089870302306324621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10238596119827069741766161 7678947089870302306324621)
                    ·
                      refine ⟨2879605158701363364871733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7678947089870302306324621 2879605158701363364871733)
                      ·
                        rfl

theorem cell23_5608011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 2, 3].length) (baseStart_5608011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608011 prefixEnd_5608011 := by exact prefixLift 5608011
  have htrace : WordTrace (prefixWord ++ tailWord_5608011) baseStart_5608011 baseEnd_5608011 := by
    simpa [prefixWord, tailWord_5608011, baseEnd_5608011] using wordTrace_append hprefix tailTrace_5608011
  have hstable : (prefixWord ++ tailWord_5608011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608011).length < 2 ^ (prefixWord ++ tailWord_5608011).sum := by decide
  have hdescent : baseEnd_5608011 < baseStart_5608011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608047 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4]
def baseStart_5608047 : Nat := 118140960795 + 5608047 * 2 ^ 59
def prefixEnd_5608047 : Nat := 4983230072969 + 3 ^ 40 * 5608047 * 2
def baseEnd_5608047 : Nat := 2879623644004925224021567

theorem tailTrace_5608047 : CollatzResearch.WordTrace tailWord_5608047 prefixEnd_5608047 2879623644004925224021567 := by
  unfold tailWord_5608047
  simp only [CollatzResearch.WordTrace]
  refine ⟨204542277914010972020094395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136361518609340648013396263 204542277914010972020094395)
  ·
    refine ⟨306813416871016458030141593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204542277914010972020094395 306813416871016458030141593)
    ·
      refine ⟨230110062653262343522606195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306813416871016458030141593 230110062653262343522606195)
      ·
        refine ⟨345165093979893515283909293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230110062653262343522606195 345165093979893515283909293)
        ·
          refine ⟨129436910242460068231465985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345165093979893515283909293 129436910242460068231465985)
          ·
            refine ⟨97077682681845051173599489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129436910242460068231465985 97077682681845051173599489)
            ·
              refine ⟨72808262011383788380199617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97077682681845051173599489 72808262011383788380199617)
              ·
                refine ⟨54606196508537841285149713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72808262011383788380199617 54606196508537841285149713)
                ·
                  refine ⟨40954647381403380963862285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54606196508537841285149713 40954647381403380963862285)
                  ·
                    refine ⟨15357992768026267861448357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40954647381403380963862285 15357992768026267861448357)
                    ·
                      refine ⟨2879623644004925224021567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15357992768026267861448357 2879623644004925224021567)
                      ·
                        rfl

theorem cell23_5608047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_5608047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608047 prefixEnd_5608047 := by exact prefixLift 5608047
  have htrace : WordTrace (prefixWord ++ tailWord_5608047) baseStart_5608047 baseEnd_5608047 := by
    simpa [prefixWord, tailWord_5608047, baseEnd_5608047] using wordTrace_append hprefix tailTrace_5608047
  have hstable : (prefixWord ++ tailWord_5608047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608047).length < 2 ^ (prefixWord ++ tailWord_5608047).sum := by decide
  have hdescent : baseEnd_5608047 < baseStart_5608047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608067 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_5608067 : Nat := 118140960795 + 5608067 * 2 ^ 59
def prefixEnd_5608067 : Nat := 4983230072969 + 3 ^ 40 * 5608067 * 2
def baseEnd_5608067 : Nat := 2879633913618015145771475

theorem tailTrace_5608067 : CollatzResearch.WordTrace tailWord_5608067 prefixEnd_5608067 2879633913618015145771475 := by
  unfold tailWord_5608067
  simp only [CollatzResearch.WordTrace]
  refine ⟨204543007373938515435822455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136362004915959010290548303 204543007373938515435822455)
  ·
    refine ⟨306814511060907773153733683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204543007373938515435822455 306814511060907773153733683)
    ·
      refine ⟨460221766591361659730600525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306814511060907773153733683 460221766591361659730600525)
      ·
        refine ⟨172583162471760622398975197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460221766591361659730600525 172583162471760622398975197)
        ·
          refine ⟨64718685926910233399615699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172583162471760622398975197 64718685926910233399615699)
          ·
            refine ⟨97078028890365350099423549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64718685926910233399615699 97078028890365350099423549)
            ·
              refine ⟨36404260833887006287283831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97078028890365350099423549 36404260833887006287283831)
              ·
                refine ⟨54606391250830509430925747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36404260833887006287283831 54606391250830509430925747)
                ·
                  refine ⟨81909586876245764146388621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54606391250830509430925747 81909586876245764146388621)
                  ·
                    refine ⟨30716095078592161554895733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81909586876245764146388621 30716095078592161554895733)
                    ·
                      refine ⟨2879633913618015145771475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30716095078592161554895733 2879633913618015145771475)
                      ·
                        rfl

theorem cell23_5608067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_5608067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608067 prefixEnd_5608067 := by exact prefixLift 5608067
  have htrace : WordTrace (prefixWord ++ tailWord_5608067) baseStart_5608067 baseEnd_5608067 := by
    simpa [prefixWord, tailWord_5608067, baseEnd_5608067] using wordTrace_append hprefix tailTrace_5608067
  have hstable : (prefixWord ++ tailWord_5608067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608067).length < 2 ^ (prefixWord ++ tailWord_5608067).sum := by decide
  have hdescent : baseEnd_5608067 < baseStart_5608067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608068 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5608068 : Nat := 118140960795 + 5608068 * 2 ^ 59
def prefixEnd_5608068 : Nat := 4983230072969 + 3 ^ 40 * 5608068 * 2
def baseEnd_5608068 : Nat := 2879634427098669641858971

theorem tailTrace_5608068 : CollatzResearch.WordTrace tailWord_5608068 prefixEnd_5608068 2879634427098669641858971 := by
  unfold tailWord_5608068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102271521923467446303304429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136362029231289928404405905 102271521923467446303304429)
  ·
    refine ⟨38351820721300292363739161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102271521923467446303304429 38351820721300292363739161)
    ·
      refine ⟨28763865540975219272804371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38351820721300292363739161 28763865540975219272804371)
      ·
        refine ⟨43145798311462828909206557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28763865540975219272804371 43145798311462828909206557)
        ·
          refine ⟨16179674366798560840952459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43145798311462828909206557 16179674366798560840952459)
          ·
            refine ⟨24269511550197841261428689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16179674366798560840952459 24269511550197841261428689)
            ·
              refine ⟨18202133662648380946071517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24269511550197841261428689 18202133662648380946071517)
              ·
                refine ⟨6825800123493142854776819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18202133662648380946071517 6825800123493142854776819)
                ·
                  refine ⟨10238700185239714282165229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6825800123493142854776819 10238700185239714282165229)
                  ·
                    refine ⟨3839512569464892855811961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10238700185239714282165229 3839512569464892855811961)
                    ·
                      refine ⟨2879634427098669641858971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839512569464892855811961 2879634427098669641858971)
                      ·
                        rfl

theorem cell23_5608068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5608068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608068 prefixEnd_5608068 := by exact prefixLift 5608068
  have htrace : WordTrace (prefixWord ++ tailWord_5608068) baseStart_5608068 baseEnd_5608068 := by
    simpa [prefixWord, tailWord_5608068, baseEnd_5608068] using wordTrace_append hprefix tailTrace_5608068
  have hstable : (prefixWord ++ tailWord_5608068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608068).length < 2 ^ (prefixWord ++ tailWord_5608068).sum := by decide
  have hdescent : baseEnd_5608068 < baseStart_5608068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608114 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_5608114 : Nat := 118140960795 + 5608114 * 2 ^ 59
def prefixEnd_5608114 : Nat := 4983230072969 + 3 ^ 40 * 5608114 * 2
def baseEnd_5608114 : Nat := 2879658047208776461883759

theorem tailTrace_5608114 : CollatzResearch.WordTrace tailWord_5608114 prefixEnd_5608114 2879658047208776461883759 := by
  unfold tailWord_5608114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51136180401192060615695849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136363147736512161641855597 51136180401192060615695849)
  ·
    refine ⟨38352135300894045461771887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51136180401192060615695849 38352135300894045461771887)
    ·
      refine ⟨57528202951341068192657831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38352135300894045461771887 57528202951341068192657831)
      ·
        refine ⟨86292304427011602288986747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57528202951341068192657831 86292304427011602288986747)
        ·
          refine ⟨129438456640517403433480121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86292304427011602288986747 129438456640517403433480121)
          ·
            refine ⟨97078842480388052575110091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129438456640517403433480121 97078842480388052575110091)
            ·
              refine ⟨145618263720582078862665137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97078842480388052575110091 145618263720582078862665137)
              ·
                refine ⟨109213697790436559146998853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145618263720582078862665137 109213697790436559146998853)
                ·
                  refine ⟨20477568335706854840062285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109213697790436559146998853 20477568335706854840062285)
                  ·
                    refine ⟨7679088125890070565023357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20477568335706854840062285 7679088125890070565023357)
                    ·
                      refine ⟨2879658047208776461883759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7679088125890070565023357 2879658047208776461883759)
                      ·
                        rfl

theorem cell23_5608114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_5608114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608114 prefixEnd_5608114 := by exact prefixLift 5608114
  have htrace : WordTrace (prefixWord ++ tailWord_5608114) baseStart_5608114 baseEnd_5608114 := by
    simpa [prefixWord, tailWord_5608114, baseEnd_5608114] using wordTrace_append hprefix tailTrace_5608114
  have hstable : (prefixWord ++ tailWord_5608114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608114).length < 2 ^ (prefixWord ++ tailWord_5608114).sum := by decide
  have hdescent : baseEnd_5608114 < baseStart_5608114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608138 : List Nat := [3, 1, 2, 1, 4, 1, 4, 2, 5]
def baseStart_5608138 : Nat := 118140960795 + 5608138 * 2 ^ 59
def prefixEnd_5608138 : Nat := 4983230072969 + 3 ^ 40 * 5608138 * 2
def baseEnd_5608138 : Nat := 319963374527164929775961

theorem tailTrace_5608138 : CollatzResearch.WordTrace tailWord_5608138 prefixEnd_5608138 319963374527164929775961 := by
  unfold tailWord_5608138
  simp only [CollatzResearch.WordTrace]
  refine ⟨51136399239170323640414267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136363731304454196374438045 51136399239170323640414267)
  ·
    refine ⟨76704598858755485460621401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51136399239170323640414267 76704598858755485460621401)
    ·
      refine ⟨57528449144066614095466051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76704598858755485460621401 57528449144066614095466051)
      ·
        refine ⟨86292673716099921143199077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57528449144066614095466051 86292673716099921143199077)
        ·
          refine ⟨16179876321768735214349827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86292673716099921143199077 16179876321768735214349827)
          ·
            refine ⟨24269814482653102821524741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16179876321768735214349827 24269814482653102821524741)
            ·
              refine ⟨4550590215497456779035889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24269814482653102821524741 4550590215497456779035889)
              ·
                refine ⟨3412942661623092584276917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550590215497456779035889 3412942661623092584276917)
                ·
                  refine ⟨319963374527164929775961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3412942661623092584276917 319963374527164929775961)
                  ·
                    rfl

theorem cell23_5608138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_5608138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608138 prefixEnd_5608138 := by exact prefixLift 5608138
  have htrace : WordTrace (prefixWord ++ tailWord_5608138) baseStart_5608138 baseEnd_5608138 := by
    simpa [prefixWord, tailWord_5608138, baseEnd_5608138] using wordTrace_append hprefix tailTrace_5608138
  have hstable : (prefixWord ++ tailWord_5608138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608138).length < 2 ^ (prefixWord ++ tailWord_5608138).sum := by decide
  have hdescent : baseEnd_5608138 < baseStart_5608138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608148 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5608148 : Nat := 118140960795 + 5608148 * 2 ^ 59
def prefixEnd_5608148 : Nat := 4983230072969 + 3 ^ 40 * 5608148 * 2
def baseEnd_5608148 : Nat := 2879675505551029328858603

theorem tailTrace_5608148 : CollatzResearch.WordTrace tailWord_5608148 prefixEnd_5608148 2879675505551029328858603 := by
  unfold tailWord_5608148
  simp only [CollatzResearch.WordTrace]
  refine ⟨102272980843322533134760549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136363974457763377513014065 102272980843322533134760549)
  ·
    refine ⟨19176183908122974962767603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102272980843322533134760549 19176183908122974962767603)
    ·
      refine ⟨28764275862184462444151405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19176183908122974962767603 28764275862184462444151405)
      ·
        refine ⟨10786603448319173416556777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28764275862184462444151405 10786603448319173416556777)
        ·
          refine ⟨8089952586239380062417583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10786603448319173416556777 8089952586239380062417583)
          ·
            refine ⟨12134928879359070093626375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089952586239380062417583 12134928879359070093626375)
            ·
              refine ⟨18202393319038605140439563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12134928879359070093626375 18202393319038605140439563)
              ·
                refine ⟨27303589978557907710659345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18202393319038605140439563 27303589978557907710659345)
                ·
                  refine ⟨20477692483918430782994509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27303589978557907710659345 20477692483918430782994509)
                  ·
                    refine ⟨7679134681469411543622941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20477692483918430782994509 7679134681469411543622941)
                    ·
                      refine ⟨2879675505551029328858603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7679134681469411543622941 2879675505551029328858603)
                      ·
                        rfl

theorem cell23_5608148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5608148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608148 prefixEnd_5608148 := by exact prefixLift 5608148
  have htrace : WordTrace (prefixWord ++ tailWord_5608148) baseStart_5608148 baseEnd_5608148 := by
    simpa [prefixWord, tailWord_5608148, baseEnd_5608148] using wordTrace_append hprefix tailTrace_5608148
  have hstable : (prefixWord ++ tailWord_5608148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608148).length < 2 ^ (prefixWord ++ tailWord_5608148).sum := by decide
  have hdescent : baseEnd_5608148 < baseStart_5608148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608154 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5608154 : Nat := 118140960795 + 5608154 * 2 ^ 59
def prefixEnd_5608154 : Nat := 4983230072969 + 3 ^ 40 * 5608154 * 2
def baseEnd_5608154 : Nat := 2879678586434956305383575

theorem tailTrace_5608154 : CollatzResearch.WordTrace tailWord_5608154 prefixEnd_5608154 2879678586434956305383575 := by
  unfold tailWord_5608154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51136545131155832323559879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136364120349748886196159677 51136545131155832323559879)
  ·
    refine ⟨76704817696733748485339819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51136545131155832323559879 76704817696733748485339819)
    ·
      refine ⟨115057226545100622728009729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76704817696733748485339819 115057226545100622728009729)
      ·
        refine ⟨86292919908825467046007297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115057226545100622728009729 86292919908825467046007297)
        ·
          refine ⟨64719689931619100284505473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86292919908825467046007297 64719689931619100284505473)
          ·
            refine ⟨48539767448714325213379105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64719689931619100284505473 48539767448714325213379105)
            ·
              refine ⟨36404825586535743910034329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48539767448714325213379105 36404825586535743910034329)
              ·
                refine ⟨27303619189901807932525747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36404825586535743910034329 27303619189901807932525747)
                ·
                  refine ⟨40955428784852711898788621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27303619189901807932525747 40955428784852711898788621)
                  ·
                    refine ⟨15358285794319766962045733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40955428784852711898788621 15358285794319766962045733)
                    ·
                      refine ⟨2879678586434956305383575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15358285794319766962045733 2879678586434956305383575)
                      ·
                        rfl

theorem cell23_5608154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5608154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608154 prefixEnd_5608154 := by exact prefixLift 5608154
  have htrace : WordTrace (prefixWord ++ tailWord_5608154) baseStart_5608154 baseEnd_5608154 := by
    simpa [prefixWord, tailWord_5608154, baseEnd_5608154] using wordTrace_append hprefix tailTrace_5608154
  have hstable : (prefixWord ++ tailWord_5608154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608154).length < 2 ^ (prefixWord ++ tailWord_5608154).sum := by decide
  have hdescent : baseEnd_5608154 < baseStart_5608154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608168 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_5608168 : Nat := 118140960795 + 5608168 * 2 ^ 59
def prefixEnd_5608168 : Nat := 4983230072969 + 3 ^ 40 * 5608168 * 2
def baseEnd_5608168 : Nat := 959895258388039750202837

theorem tailTrace_5608168 : CollatzResearch.WordTrace tailWord_5608168 prefixEnd_5608168 959895258388039750202837 := by
  unfold tailWord_5608168
  simp only [CollatzResearch.WordTrace]
  refine ⟨102273345573286304842624579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136364460764381739790166105 102273345573286304842624579)
  ·
    refine ⟨153410018359929457263936869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102273345573286304842624579 153410018359929457263936869)
    ·
      refine ⟨28764378442486773236988163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153410018359929457263936869 28764378442486773236988163)
      ·
        refine ⟨43146567663730159855482245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28764378442486773236988163 43146567663730159855482245)
        ·
          refine ⟨8089981436949404972902921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43146567663730159855482245 8089981436949404972902921)
          ·
            refine ⟨6067486077712053729677191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089981436949404972902921 6067486077712053729677191)
            ·
              refine ⟨9101229116568080594515787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067486077712053729677191 9101229116568080594515787)
              ·
                refine ⟨13651843674852120891773681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101229116568080594515787 13651843674852120891773681)
                ·
                  refine ⟨10238882756139090668830261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13651843674852120891773681 10238882756139090668830261)
                  ·
                    refine ⟨959895258388039750202837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10238882756139090668830261 959895258388039750202837)
                    ·
                      rfl

theorem cell23_5608168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_5608168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608168 prefixEnd_5608168 := by exact prefixLift 5608168
  have htrace : WordTrace (prefixWord ++ tailWord_5608168) baseStart_5608168 baseEnd_5608168 := by
    simpa [prefixWord, tailWord_5608168, baseEnd_5608168] using wordTrace_append hprefix tailTrace_5608168
  have hstable : (prefixWord ++ tailWord_5608168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608168).length < 2 ^ (prefixWord ++ tailWord_5608168).sum := by decide
  have hdescent : baseEnd_5608168 < baseStart_5608168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608211 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 6]
def baseStart_5608211 : Nat := 118140960795 + 5608211 * 2 ^ 59
def prefixEnd_5608211 : Nat := 4983230072969 + 3 ^ 40 * 5608211 * 2
def baseEnd_5608211 : Nat := 319967539425806953596757

theorem tailTrace_5608211 : CollatzResearch.WordTrace tailWord_5608211 prefixEnd_5608211 319967539425806953596757 := by
  unfold tailWord_5608211
  simp only [CollatzResearch.WordTrace]
  refine ⟨204548259485416828029064487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136365506323611218686042991 204548259485416828029064487)
  ·
    refine ⟨306822389228125242043596731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204548259485416828029064487 306822389228125242043596731)
    ·
      refine ⟨460233583842187863065395097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306822389228125242043596731 460233583842187863065395097)
      ·
        refine ⟨345175187881640897299046323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460233583842187863065395097 345175187881640897299046323)
        ·
          refine ⟨517762781822461345948569485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345175187881640897299046323 517762781822461345948569485)
          ·
            refine ⟨194161043183423004730713557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517762781822461345948569485 194161043183423004730713557)
            ·
              refine ⟨4550649449611476673376099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 194161043183423004730713557 4550649449611476673376099)
              ·
                refine ⟨6825974174417215010064149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550649449611476673376099 6825974174417215010064149)
                ·
                  refine ⟨319967539425806953596757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6825974174417215010064149 319967539425806953596757)
                  ·
                    rfl

theorem cell23_5608211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 6].length) (baseStart_5608211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608211 prefixEnd_5608211 := by exact prefixLift 5608211
  have htrace : WordTrace (prefixWord ++ tailWord_5608211) baseStart_5608211 baseEnd_5608211 := by
    simpa [prefixWord, tailWord_5608211, baseEnd_5608211] using wordTrace_append hprefix tailTrace_5608211
  have hstable : (prefixWord ++ tailWord_5608211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608211).length < 2 ^ (prefixWord ++ tailWord_5608211).sum := by decide
  have hdescent : baseEnd_5608211 < baseStart_5608211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608241 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 1, 5]
def baseStart_5608241 : Nat := 118140960795 + 5608241 * 2 ^ 59
def prefixEnd_5608241 : Nat := 4983230072969 + 3 ^ 40 * 5608241 * 2
def baseEnd_5608241 : Nat := 959907753083965821665225

theorem tailTrace_5608241 : CollatzResearch.WordTrace tailWord_5608241 prefixEnd_5608241 959907753083965821665225 := by
  unfold tailWord_5608241
  simp only [CollatzResearch.WordTrace]
  refine ⟨204549353675308143152656577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136366235783538762101771051 204549353675308143152656577)
  ·
    refine ⟨153412015256481107364492433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204549353675308143152656577 153412015256481107364492433)
    ·
      refine ⟨115059011442360830523369325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153412015256481107364492433 115059011442360830523369325)
      ·
        refine ⟨43147129290885311446263497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115059011442360830523369325 43147129290885311446263497)
        ·
          refine ⟨32360346968163983584697623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43147129290885311446263497 32360346968163983584697623)
          ·
            refine ⟨48540520452245975377046435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32360346968163983584697623 48540520452245975377046435)
            ·
              refine ⟨72810780678368963065569653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48540520452245975377046435 72810780678368963065569653)
              ·
                refine ⟨6826010688597090287397155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72810780678368963065569653 6826010688597090287397155)
                ·
                  refine ⟨10239016032895635431095733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6826010688597090287397155 10239016032895635431095733)
                  ·
                    refine ⟨959907753083965821665225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10239016032895635431095733 959907753083965821665225)
                    ·
                      rfl

theorem cell23_5608241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 5].length) (baseStart_5608241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608241 prefixEnd_5608241 := by exact prefixLift 5608241
  have htrace : WordTrace (prefixWord ++ tailWord_5608241) baseStart_5608241 baseEnd_5608241 := by
    simpa [prefixWord, tailWord_5608241, baseEnd_5608241] using wordTrace_append hprefix tailTrace_5608241
  have hstable : (prefixWord ++ tailWord_5608241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608241).length < 2 ^ (prefixWord ++ tailWord_5608241).sum := by decide
  have hdescent : baseEnd_5608241 < baseStart_5608241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608248 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_5608248 : Nat := 118140960795 + 5608248 * 2 ^ 59
def prefixEnd_5608248 : Nat := 4983230072969 + 3 ^ 40 * 5608248 * 2
def baseEnd_5608248 : Nat := 2879726853616478937608143

theorem tailTrace_5608248 : CollatzResearch.WordTrace tailWord_5608248 prefixEnd_5608248 2879726853616478937608143 := by
  unfold tailWord_5608248
  simp only [CollatzResearch.WordTrace]
  refine ⟨102274804493141391674080699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136366405990855188898774265 102274804493141391674080699)
  ·
    refine ⟨153412206739712087511121049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102274804493141391674080699 153412206739712087511121049)
    ·
      refine ⟨115059155054784065633340787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153412206739712087511121049 115059155054784065633340787)
      ·
        refine ⟨172588732582176098450011181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115059155054784065633340787 172588732582176098450011181)
        ·
          refine ⟨64720774718316036918754193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172588732582176098450011181 64720774718316036918754193)
          ·
            refine ⟨48540581038737027689065645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64720774718316036918754193 48540581038737027689065645)
            ·
              refine ⟨18202717889526385383399617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48540581038737027689065645 18202717889526385383399617)
              ·
                refine ⟨13652038417144789037549713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18202717889526385383399617 13652038417144789037549713)
                ·
                  refine ⟨10239028812858591778162285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13652038417144789037549713 10239028812858591778162285)
                  ·
                    refine ⟨3839635804821971916810857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10239028812858591778162285 3839635804821971916810857)
                    ·
                      refine ⟨2879726853616478937608143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839635804821971916810857 2879726853616478937608143)
                      ·
                        rfl

theorem cell23_5608248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_5608248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608248 prefixEnd_5608248 := by exact prefixLift 5608248
  have htrace : WordTrace (prefixWord ++ tailWord_5608248) baseStart_5608248 baseEnd_5608248 := by
    simpa [prefixWord, tailWord_5608248, baseEnd_5608248] using wordTrace_append hprefix tailTrace_5608248
  have hstable : (prefixWord ++ tailWord_5608248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608248).length < 2 ^ (prefixWord ++ tailWord_5608248).sum := by decide
  have hdescent : baseEnd_5608248 < baseStart_5608248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608255 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 3]
def baseStart_5608255 : Nat := 118140960795 + 5608255 * 2 ^ 59
def prefixEnd_5608255 : Nat := 4983230072969 + 3 ^ 40 * 5608255 * 2
def baseEnd_5608255 : Nat := 2879730447981060410220611

theorem tailTrace_5608255 : CollatzResearch.WordTrace tailWord_5608255 prefixEnd_5608255 2879730447981060410220611 := by
  unfold tailWord_5608255
  simp only [CollatzResearch.WordTrace]
  refine ⟨204549864297257423543666219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136366576198171615695777479 204549864297257423543666219)
  ·
    refine ⟨306824796445886135315499329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204549864297257423543666219 306824796445886135315499329)
    ·
      refine ⟨230118597334414601486624497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306824796445886135315499329 230118597334414601486624497)
      ·
        refine ⟨172588948000810951114968373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230118597334414601486624497 172588948000810951114968373)
        ·
          refine ⟨16180213875076026667028285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172588948000810951114968373 16180213875076026667028285)
          ·
            refine ⟨6067580203153510000135607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16180213875076026667028285 6067580203153510000135607)
            ·
              refine ⟨9101370304730265000203411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067580203153510000135607 9101370304730265000203411)
              ·
                refine ⟨13652055457095397500305117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101370304730265000203411 13652055457095397500305117)
                ·
                  refine ⟨5119520796410774062614419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13652055457095397500305117 5119520796410774062614419)
                  ·
                    refine ⟨7679281194616161093921629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5119520796410774062614419 7679281194616161093921629)
                    ·
                      refine ⟨2879730447981060410220611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7679281194616161093921629 2879730447981060410220611)
                      ·
                        rfl

theorem cell23_5608255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_5608255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608255 prefixEnd_5608255 := by exact prefixLift 5608255
  have htrace : WordTrace (prefixWord ++ tailWord_5608255) baseStart_5608255 baseEnd_5608255 := by
    simpa [prefixWord, tailWord_5608255, baseEnd_5608255] using wordTrace_append hprefix tailTrace_5608255
  have hstable : (prefixWord ++ tailWord_5608255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608255).length < 2 ^ (prefixWord ++ tailWord_5608255).sum := by decide
  have hdescent : baseEnd_5608255 < baseStart_5608255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608261 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_5608261 : Nat := 118140960795 + 5608261 * 2 ^ 59
def prefixEnd_5608261 : Nat := 4983230072969 + 3 ^ 40 * 5608261 * 2
def baseEnd_5608261 : Nat := 2879733528864987386745583

theorem tailTrace_5608261 : CollatzResearch.WordTrace tailWord_5608261 prefixEnd_5608261 2879733528864987386745583 := by
  unfold tailWord_5608261
  simp only [CollatzResearch.WordTrace]
  refine ⟨204550083135235686568384637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136366722090157124378923091 204550083135235686568384637)
  ·
    refine ⟨76706281175713382463144239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204550083135235686568384637 76706281175713382463144239)
    ·
      refine ⟨115059421763570073694716359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76706281175713382463144239 115059421763570073694716359)
      ·
        refine ⟨172589132645355110542074539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115059421763570073694716359 172589132645355110542074539)
        ·
          refine ⟨258883698968032665813111809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172589132645355110542074539 258883698968032665813111809)
          ·
            refine ⟨194162774226024499359833857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258883698968032665813111809 194162774226024499359833857)
            ·
              refine ⟨145622080669518374519875393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194162774226024499359833857 145622080669518374519875393)
              ·
                refine ⟨109216560502138780889906545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145622080669518374519875393 109216560502138780889906545)
                ·
                  refine ⟨81912420376604085667429909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109216560502138780889906545 81912420376604085667429909)
                  ·
                    refine ⟨3839644705153316515660777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81912420376604085667429909 3839644705153316515660777)
                    ·
                      refine ⟨2879733528864987386745583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839644705153316515660777 2879733528864987386745583)
                      ·
                        rfl

theorem cell23_5608261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_5608261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608261 prefixEnd_5608261 := by exact prefixLift 5608261
  have htrace : WordTrace (prefixWord ++ tailWord_5608261) baseStart_5608261 baseEnd_5608261 := by
    simpa [prefixWord, tailWord_5608261, baseEnd_5608261] using wordTrace_append hprefix tailTrace_5608261
  have hstable : (prefixWord ++ tailWord_5608261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608261).length < 2 ^ (prefixWord ++ tailWord_5608261).sum := by decide
  have hdescent : baseEnd_5608261 < baseStart_5608261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608291 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5608291 : Nat := 118140960795 + 5608291 * 2 ^ 59
def prefixEnd_5608291 : Nat := 4983230072969 + 3 ^ 40 * 5608291 * 2
def baseEnd_5608291 : Nat := 2879748933284622269370445

theorem tailTrace_5608291 : CollatzResearch.WordTrace tailWord_5608291 prefixEnd_5608291 2879748933284622269370445 := by
  unfold tailWord_5608291
  simp only [CollatzResearch.WordTrace]
  refine ⟨204551177325127001691976727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136367451550084667794651151 204551177325127001691976727)
  ·
    refine ⟨306826765987690502537965091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204551177325127001691976727 306826765987690502537965091)
    ·
      refine ⟨460240148981535753806947637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306826765987690502537965091 460240148981535753806947637)
      ·
        refine ⟨43147513967018976919401341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 460240148981535753806947637 43147513967018976919401341)
        ·
          refine ⟨16180317737632116344775503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43147513967018976919401341 16180317737632116344775503)
          ·
            refine ⟨24270476606448174517163255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16180317737632116344775503 24270476606448174517163255)
            ·
              refine ⟨36405714909672261775744883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24270476606448174517163255 36405714909672261775744883)
              ·
                refine ⟨54608572364508392663617325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36405714909672261775744883 54608572364508392663617325)
                ·
                  refine ⟨20478214636690647248856497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54608572364508392663617325 20478214636690647248856497)
                  ·
                    refine ⟨15358660977517985436642373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20478214636690647248856497 15358660977517985436642373)
                    ·
                      refine ⟨2879748933284622269370445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15358660977517985436642373 2879748933284622269370445)
                      ·
                        rfl

theorem cell23_5608291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5608291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608291 prefixEnd_5608291 := by exact prefixLift 5608291
  have htrace : WordTrace (prefixWord ++ tailWord_5608291) baseStart_5608291 baseEnd_5608291 := by
    simpa [prefixWord, tailWord_5608291, baseEnd_5608291] using wordTrace_append hprefix tailTrace_5608291
  have hstable : (prefixWord ++ tailWord_5608291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608291).length < 2 ^ (prefixWord ++ tailWord_5608291).sum := by decide
  have hdescent : baseEnd_5608291 < baseStart_5608291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608295 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_5608295 : Nat := 118140960795 + 5608295 * 2 ^ 59
def prefixEnd_5608295 : Nat := 4983230072969 + 3 ^ 40 * 5608295 * 2
def baseEnd_5608295 : Nat := 2879750987207240253720427

theorem tailTrace_5608295 : CollatzResearch.WordTrace tailWord_5608295 prefixEnd_5608295 2879750987207240253720427 := by
  unfold tailWord_5608295
  simp only [CollatzResearch.WordTrace]
  refine ⟨204551323217112510375122339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136367548811408340250081559 204551323217112510375122339)
  ·
    refine ⟨306826984825668765562683509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204551323217112510375122339 306826984825668765562683509)
    ·
      refine ⟨28765029827406446771501579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306826984825668765562683509 28765029827406446771501579)
      ·
        refine ⟨43147544741109670157252369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28765029827406446771501579 43147544741109670157252369)
        ·
          refine ⟨32360658555832252617939277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43147544741109670157252369 32360658555832252617939277)
          ·
            refine ⟨12135246958437094731727229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32360658555832252617939277 12135246958437094731727229)
            ·
              refine ⟨4550717609413910524397711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12135246958437094731727229 4550717609413910524397711)
              ·
                refine ⟨6826076414120865786596567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550717609413910524397711 6826076414120865786596567)
                ·
                  refine ⟨10239114621181298679894851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6826076414120865786596567 10239114621181298679894851)
                  ·
                    refine ⟨15358671931771948019842277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10239114621181298679894851 15358671931771948019842277)
                    ·
                      refine ⟨2879750987207240253720427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15358671931771948019842277 2879750987207240253720427)
                      ·
                        rfl

theorem cell23_5608295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_5608295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608295 prefixEnd_5608295 := by exact prefixLift 5608295
  have htrace : WordTrace (prefixWord ++ tailWord_5608295) baseStart_5608295 baseEnd_5608295 := by
    simpa [prefixWord, tailWord_5608295, baseEnd_5608295] using wordTrace_append hprefix tailTrace_5608295
  have hstable : (prefixWord ++ tailWord_5608295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608295).length < 2 ^ (prefixWord ++ tailWord_5608295).sum := by decide
  have hdescent : baseEnd_5608295 < baseStart_5608295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608322 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5608322 : Nat := 118140960795 + 5608322 * 2 ^ 59
def prefixEnd_5608322 : Nat := 4983230072969 + 3 ^ 40 * 5608322 * 2
def baseEnd_5608322 : Nat := 959921617061637216027601

theorem tailTrace_5608322 : CollatzResearch.WordTrace tailWord_5608322 prefixEnd_5608322 959921617061637216027601 := by
  unfold tailWord_5608322
  simp only [CollatzResearch.WordTrace]
  refine ⟨51138076997003673496588805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136368205325343129324236813 51138076997003673496588805)
  ·
    refine ⟨9588389436938188780610401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51138076997003673496588805 9588389436938188780610401)
    ·
      refine ⟨7191292077703641585457801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9588389436938188780610401 7191292077703641585457801)
      ·
        refine ⟨5393469058277731189093351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191292077703641585457801 5393469058277731189093351)
        ·
          refine ⟨8090203587416596783640027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393469058277731189093351 8090203587416596783640027)
          ·
            refine ⟨12135305381124895175460041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090203587416596783640027 12135305381124895175460041)
            ·
              refine ⟨9101479035843671381595031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12135305381124895175460041 9101479035843671381595031)
              ·
                refine ⟨13652218553765507072392547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101479035843671381595031 13652218553765507072392547)
                ·
                  refine ⟨20478327830648260608588821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13652218553765507072392547 20478327830648260608588821)
                  ·
                    refine ⟨959921617061637216027601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20478327830648260608588821 959921617061637216027601)
                    ·
                      rfl

theorem cell23_5608322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5608322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608322 prefixEnd_5608322 := by exact prefixLift 5608322
  have htrace : WordTrace (prefixWord ++ tailWord_5608322) baseStart_5608322 baseEnd_5608322 := by
    simpa [prefixWord, tailWord_5608322, baseEnd_5608322] using wordTrace_append hprefix tailTrace_5608322
  have hstable : (prefixWord ++ tailWord_5608322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608322).length < 2 ^ (prefixWord ++ tailWord_5608322).sum := by decide
  have hdescent : baseEnd_5608322 < baseStart_5608322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608328 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_5608328 : Nat := 118140960795 + 5608328 * 2 ^ 59
def prefixEnd_5608328 : Nat := 4983230072969 + 3 ^ 40 * 5608328 * 2
def baseEnd_5608328 : Nat := 2879767932068838624607775

theorem tailTrace_5608328 : CollatzResearch.WordTrace tailWord_5608328 prefixEnd_5608328 2879767932068838624607775 := by
  unfold tailWord_5608328
  simp only [CollatzResearch.WordTrace]
  refine ⟨102276263412996478505536819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136368351217328638007382425 102276263412996478505536819)
  ·
    refine ⟨153414395119494717758305229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102276263412996478505536819 153414395119494717758305229)
    ·
      refine ⟨57530398169810519159364461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153414395119494717758305229 57530398169810519159364461)
      ·
        refine ⟨21573899313678944684761673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57530398169810519159364461 21573899313678944684761673)
        ·
          refine ⟨16180424485259208513571255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21573899313678944684761673 16180424485259208513571255)
          ·
            refine ⟨24270636727888812770356883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16180424485259208513571255 24270636727888812770356883)
            ·
              refine ⟨36405955091833219155535325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24270636727888812770356883 36405955091833219155535325)
              ·
                refine ⟨13652233159437457183325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36405955091833219155535325 13652233159437457183325747)
                ·
                  refine ⟨20478349739156185774988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13652233159437457183325747 20478349739156185774988621)
                  ·
                    refine ⟨7679381152183569665620733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20478349739156185774988621 7679381152183569665620733)
                    ·
                      refine ⟨2879767932068838624607775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7679381152183569665620733 2879767932068838624607775)
                      ·
                        rfl

theorem cell23_5608328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_5608328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608328 prefixEnd_5608328 := by exact prefixLift 5608328
  have htrace : WordTrace (prefixWord ++ tailWord_5608328) baseStart_5608328 baseEnd_5608328 := by
    simpa [prefixWord, tailWord_5608328, baseEnd_5608328] using wordTrace_append hprefix tailTrace_5608328
  have hstable : (prefixWord ++ tailWord_5608328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608328).length < 2 ^ (prefixWord ++ tailWord_5608328).sum := by decide
  have hdescent : baseEnd_5608328 < baseStart_5608328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608342 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5608342 : Nat := 118140960795 + 5608342 * 2 ^ 59
def prefixEnd_5608342 : Nat := 4983230072969 + 3 ^ 40 * 5608342 * 2
def baseEnd_5608342 : Nat := 2879775120798001569832711

theorem tailTrace_5608342 : CollatzResearch.WordTrace tailWord_5608342 prefixEnd_5608342 2879775120798001569832711 := by
  unfold tailWord_5608342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784564840496389837630205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136368691631961491601388853 12784564840496389837630205)
  ·
    refine ⟨4794211815186146189111327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12784564840496389837630205 4794211815186146189111327)
    ·
      refine ⟨7191317722779219283666991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794211815186146189111327 7191317722779219283666991)
      ·
        refine ⟨10786976584168828925500487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7191317722779219283666991 10786976584168828925500487)
        ·
          refine ⟨16180464876253243388250731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10786976584168828925500487 16180464876253243388250731)
          ·
            refine ⟨24270697314379865082376097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16180464876253243388250731 24270697314379865082376097)
            ·
              refine ⟨18203022985784898811782073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24270697314379865082376097 18203022985784898811782073)
              ·
                refine ⟨13652267239338674108836555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18203022985784898811782073 13652267239338674108836555)
                ·
                  refine ⟨20478400859008011163254833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13652267239338674108836555 20478400859008011163254833)
                  ·
                    refine ⟨15358800644256008372441125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20478400859008011163254833 15358800644256008372441125)
                    ·
                      refine ⟨2879775120798001569832711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15358800644256008372441125 2879775120798001569832711)
                      ·
                        rfl

theorem cell23_5608342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5608342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608342 prefixEnd_5608342 := by exact prefixLift 5608342
  have htrace : WordTrace (prefixWord ++ tailWord_5608342) baseStart_5608342 baseEnd_5608342 := by
    simpa [prefixWord, tailWord_5608342, baseEnd_5608342] using wordTrace_append hprefix tailTrace_5608342
  have hstable : (prefixWord ++ tailWord_5608342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608342).length < 2 ^ (prefixWord ++ tailWord_5608342).sum := by decide
  have hdescent : baseEnd_5608342 < baseStart_5608342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608371 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3]
def baseStart_5608371 : Nat := 118140960795 + 5608371 * 2 ^ 59
def prefixEnd_5608371 : Nat := 4983230072969 + 3 ^ 40 * 5608371 * 2
def baseEnd_5608371 : Nat := 2879790011736981956370077

theorem tailTrace_5608371 : CollatzResearch.WordTrace tailWord_5608371 prefixEnd_5608371 2879790011736981956370077 := by
  unfold tailWord_5608371
  simp only [CollatzResearch.WordTrace]
  refine ⟨204554095164837175354888967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136369396776558116903259311 204554095164837175354888967)
  ·
    refine ⟨306831142747255763032333451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204554095164837175354888967 306831142747255763032333451)
    ·
      refine ⟨460246714120883644548500177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306831142747255763032333451 460246714120883644548500177)
      ·
        refine ⟨345185035590662733411375133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460246714120883644548500177 345185035590662733411375133)
        ·
          refine ⟨129444388346498525029265675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345185035590662733411375133 129444388346498525029265675)
          ·
            refine ⟨194166582519747787543898513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129444388346498525029265675 194166582519747787543898513)
            ·
              refine ⟨145624936889810840657923885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194166582519747787543898513 145624936889810840657923885)
              ·
                refine ⟨54609351333679065246721457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145624936889810840657923885 54609351333679065246721457)
                ·
                  refine ⟨40957013500259298935041093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54609351333679065246721457 40957013500259298935041093)
                  ·
                    refine ⟨7679440031298618550320205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40957013500259298935041093 7679440031298618550320205)
                    ·
                      refine ⟨2879790011736981956370077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7679440031298618550320205 2879790011736981956370077)
                      ·
                        rfl

theorem cell23_5608371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_5608371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608371 prefixEnd_5608371 := by exact prefixLift 5608371
  have htrace : WordTrace (prefixWord ++ tailWord_5608371) baseStart_5608371 baseEnd_5608371 := by
    simpa [prefixWord, tailWord_5608371, baseEnd_5608371] using wordTrace_append hprefix tailTrace_5608371
  have hstable : (prefixWord ++ tailWord_5608371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608371).length < 2 ^ (prefixWord ++ tailWord_5608371).sum := by decide
  have hdescent : baseEnd_5608371 < baseStart_5608371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608391 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 7]
def baseStart_5608391 : Nat := 118140960795 + 5608391 * 2 ^ 59
def prefixEnd_5608391 : Nat := 4983230072969 + 3 ^ 40 * 5608391 * 2
def baseEnd_5608391 : Nat := 319977809038896875346665

theorem tailTrace_5608391 : CollatzResearch.WordTrace tailWord_5608391 prefixEnd_5608391 319977809038896875346665 := by
  unfold tailWord_5608391
  simp only [CollatzResearch.WordTrace]
  refine ⟨204554824624764718770617027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136369883083176479180411351 204554824624764718770617027)
  ·
    refine ⟨306832236937147078155925541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204554824624764718770617027 306832236937147078155925541)
    ·
      refine ⟨57531044425715077154236039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306832236937147078155925541 57531044425715077154236039)
      ·
        refine ⟨86296566638572615731354059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57531044425715077154236039 86296566638572615731354059)
        ·
          refine ⟨129444849957858923597031089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86296566638572615731354059 129444849957858923597031089)
          ·
            refine ⟨97083637468394192697773317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129444849957858923597031089 97083637468394192697773317)
            ·
              refine ⟨18203182025323911130832497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97083637468394192697773317 18203182025323911130832497)
              ·
                refine ⟨13652386518992933348124373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18203182025323911130832497 13652386518992933348124373)
                ·
                  refine ⟨319977809038896875346665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13652386518992933348124373 319977809038896875346665)
                  ·
                    rfl

theorem cell23_5608391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 7].length) (baseStart_5608391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608391 prefixEnd_5608391 := by exact prefixLift 5608391
  have htrace : WordTrace (prefixWord ++ tailWord_5608391) baseStart_5608391 baseEnd_5608391 := by
    simpa [prefixWord, tailWord_5608391, baseEnd_5608391] using wordTrace_append hprefix tailTrace_5608391
  have hstable : (prefixWord ++ tailWord_5608391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608391).length < 2 ^ (prefixWord ++ tailWord_5608391).sum := by decide
  have hdescent : baseEnd_5608391 < baseStart_5608391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608397 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5608397 : Nat := 118140960795 + 5608397 * 2 ^ 59
def prefixEnd_5608397 : Nat := 4983230072969 + 3 ^ 40 * 5608397 * 2
def baseEnd_5608397 : Nat := 2879803362233998854644959

theorem tailTrace_5608397 : CollatzResearch.WordTrace tailWord_5608397 prefixEnd_5608397 2879803362233998854644959 := by
  unfold tailWord_5608397
  simp only [CollatzResearch.WordTrace]
  refine ⟨204555043462742981795335445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136370028975161987863556963 204555043462742981795335445)
  ·
    refine ⟨9588517662316077271656349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204555043462742981795335445 9588517662316077271656349)
    ·
      refine ⟨3595694123368528976871131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9588517662316077271656349 3595694123368528976871131)
      ·
        refine ⟨5393541185052793465306697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595694123368528976871131 5393541185052793465306697)
        ·
          refine ⟨4045155888789595098980023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393541185052793465306697 4045155888789595098980023)
          ·
            refine ⟨6067733833184392648470035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045155888789595098980023 6067733833184392648470035)
            ·
              refine ⟨9101600749776588972705053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067733833184392648470035 9101600749776588972705053)
              ·
                refine ⟨3413100281166220864764395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9101600749776588972705053 3413100281166220864764395)
                ·
                  refine ⟨5119650421749331297146593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413100281166220864764395 5119650421749331297146593)
                  ·
                    refine ⟨3839737816311998472859945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119650421749331297146593 3839737816311998472859945)
                    ·
                      refine ⟨2879803362233998854644959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839737816311998472859945 2879803362233998854644959)
                      ·
                        rfl

theorem cell23_5608397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5608397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608397 prefixEnd_5608397 := by exact prefixLift 5608397
  have htrace : WordTrace (prefixWord ++ tailWord_5608397) baseStart_5608397 baseEnd_5608397 := by
    simpa [prefixWord, tailWord_5608397, baseEnd_5608397] using wordTrace_append hprefix tailTrace_5608397
  have hstable : (prefixWord ++ tailWord_5608397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608397).length < 2 ^ (prefixWord ++ tailWord_5608397).sum := by decide
  have hdescent : baseEnd_5608397 < baseStart_5608397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608402 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5608402 : Nat := 118140960795 + 5608402 * 2 ^ 59
def prefixEnd_5608402 : Nat := 4983230072969 + 3 ^ 40 * 5608402 * 2
def baseEnd_5608402 : Nat := 2879805929637271335082435

theorem tailTrace_5608402 : CollatzResearch.WordTrace tailWord_5608402 prefixEnd_5608402 2879805929637271335082435 := by
  unfold tailWord_5608402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51138806456931216912316865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136370150551816578432844973 51138806456931216912316865)
  ·
    refine ⟨38354104842698412684237649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51138806456931216912316865 38354104842698412684237649)
    ·
      refine ⟨28765578632023809513178237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38354104842698412684237649 28765578632023809513178237)
      ·
        refine ⟨10787091987008928567441839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28765578632023809513178237 10787091987008928567441839)
        ·
          refine ⟨16180637980513392851162759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787091987008928567441839 16180637980513392851162759)
          ·
            refine ⟨24270956970770089276744139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16180637980513392851162759 24270956970770089276744139)
            ·
              refine ⟨36406435456155133915116209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24270956970770089276744139 36406435456155133915116209)
              ·
                refine ⟨27304826592116350436337157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36406435456155133915116209 27304826592116350436337157)
                ·
                  refine ⟨5119654986021815706813217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27304826592116350436337157 5119654986021815706813217)
                  ·
                    refine ⟨3839741239516361780109913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119654986021815706813217 3839741239516361780109913)
                    ·
                      refine ⟨2879805929637271335082435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839741239516361780109913 2879805929637271335082435)
                      ·
                        rfl

theorem cell23_5608402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5608402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608402 prefixEnd_5608402 := by exact prefixLift 5608402
  have htrace : WordTrace (prefixWord ++ tailWord_5608402) baseStart_5608402 baseEnd_5608402 := by
    simpa [prefixWord, tailWord_5608402, baseEnd_5608402] using wordTrace_append hprefix tailTrace_5608402
  have hstable : (prefixWord ++ tailWord_5608402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608402).length < 2 ^ (prefixWord ++ tailWord_5608402).sum := by decide
  have hdescent : baseEnd_5608402 < baseStart_5608402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608431 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7]
def baseStart_5608431 : Nat := 118140960795 + 5608431 * 2 ^ 59
def prefixEnd_5608431 : Nat := 4983230072969 + 3 ^ 40 * 5608431 * 2
def baseEnd_5608431 : Nat := 2879820820576251721619801

theorem tailTrace_5608431 : CollatzResearch.WordTrace tailWord_5608431 prefixEnd_5608431 2879820820576251721619801 := by
  unfold tailWord_5608431
  simp only [CollatzResearch.WordTrace]
  refine ⟨204556283544619805602073147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136370855696413203734715431 204556283544619805602073147)
  ·
    refine ⟨306834425316929708403109721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204556283544619805602073147 306834425316929708403109721)
    ·
      refine ⟨230125818987697281302332291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306834425316929708403109721 230125818987697281302332291)
      ·
        refine ⟨345188728481545921953498437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230125818987697281302332291 345188728481545921953498437)
        ·
          refine ⟨64722886590289860366280957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345188728481545921953498437 64722886590289860366280957)
          ·
            refine ⟨24271082471358697637355359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64722886590289860366280957 24271082471358697637355359)
            ·
              refine ⟨36406623707038046456033039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24271082471358697637355359 36406623707038046456033039)
              ·
                refine ⟨54609935560557069684049559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36406623707038046456033039 54609935560557069684049559)
                ·
                  refine ⟨81914903340835604526074339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54609935560557069684049559 81914903340835604526074339)
                  ·
                    refine ⟨122872355011253406789111509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81914903340835604526074339 122872355011253406789111509)
                    ·
                      refine ⟨2879820820576251721619801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122872355011253406789111509 2879820820576251721619801)
                      ·
                        rfl

theorem cell23_5608431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_5608431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608431 prefixEnd_5608431 := by exact prefixLift 5608431
  have htrace : WordTrace (prefixWord ++ tailWord_5608431) baseStart_5608431 baseEnd_5608431 := by
    simpa [prefixWord, tailWord_5608431, baseEnd_5608431] using wordTrace_append hprefix tailTrace_5608431
  have hstable : (prefixWord ++ tailWord_5608431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608431).length < 2 ^ (prefixWord ++ tailWord_5608431).sum := by decide
  have hdescent : baseEnd_5608431 < baseStart_5608431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608498 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 6]
def baseStart_5608498 : Nat := 118140960795 + 5608498 * 2 ^ 59
def prefixEnd_5608498 : Nat := 4983230072969 + 3 ^ 40 * 5608498 * 2
def baseEnd_5608498 : Nat := 319983913753344773275777

theorem tailTrace_5608498 : CollatzResearch.WordTrace tailWord_5608498 prefixEnd_5608498 319983913753344773275777 := by
  unfold tailWord_5608498
  simp only [CollatzResearch.WordTrace]
  refine ⟨51139681808844269011190537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136372484823584717363174765 51139681808844269011190537)
  ·
    refine ⟨38354761356633201758392903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51139681808844269011190537 38354761356633201758392903)
    ·
      refine ⟨57532142034949802637589355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38354761356633201758392903 57532142034949802637589355)
      ·
        refine ⟨86298213052424703956384033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57532142034949802637589355 86298213052424703956384033)
        ·
          refine ⟨64723659789318527967288025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86298213052424703956384033 64723659789318527967288025)
          ·
            refine ⟨48542744841988895975466019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64723659789318527967288025 48542744841988895975466019)
            ·
              refine ⟨72814117262983343963199029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48542744841988895975466019 72814117262983343963199029)
              ·
                refine ⟨6826323493404688496549909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72814117262983343963199029 6826323493404688496549909)
                ·
                  refine ⟨319983913753344773275777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6826323493404688496549909 319983913753344773275777)
                  ·
                    rfl

theorem cell23_5608498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_5608498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608498 prefixEnd_5608498 := by exact prefixLift 5608498
  have htrace : WordTrace (prefixWord ++ tailWord_5608498) baseStart_5608498 baseEnd_5608498 := by
    simpa [prefixWord, tailWord_5608498, baseEnd_5608498] using wordTrace_append hprefix tailTrace_5608498
  have hstable : (prefixWord ++ tailWord_5608498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608498).length < 2 ^ (prefixWord ++ tailWord_5608498).sum := by decide
  have hdescent : baseEnd_5608498 < baseStart_5608498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608502 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_5608502 : Nat := 118140960795 + 5608502 * 2 ^ 59
def prefixEnd_5608502 : Nat := 4983230072969 + 3 ^ 40 * 5608502 * 2
def baseEnd_5608502 : Nat := 959952425900906981277325

theorem tailTrace_5608502 : CollatzResearch.WordTrace tailWord_5608502 prefixEnd_5608502 959952425900906981277325 := by
  unfold tailWord_5608502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784929570460161545494235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136372582084908389818605173 12784929570460161545494235)
  ·
    refine ⟨19177394355690242318241353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12784929570460161545494235 19177394355690242318241353)
    ·
      refine ⟨14383045766767681738681015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19177394355690242318241353 14383045766767681738681015)
      ·
        refine ⟨21574568650151522608021523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14383045766767681738681015 21574568650151522608021523)
        ·
          refine ⟨32361852975227283912032285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21574568650151522608021523 32361852975227283912032285)
          ·
            refine ⟨12135694865710231467012107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32361852975227283912032285 12135694865710231467012107)
            ·
              refine ⟨18203542298565347200518161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12135694865710231467012107 18203542298565347200518161)
              ·
                refine ⟨13652656723924010400388621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18203542298565347200518161 13652656723924010400388621)
                ·
                  refine ⟨5119746271471503900145733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13652656723924010400388621 5119746271471503900145733)
                  ·
                    refine ⟨959952425900906981277325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119746271471503900145733 959952425900906981277325)
                    ·
                      rfl

theorem cell23_5608502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_5608502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608502 prefixEnd_5608502 := by exact prefixLift 5608502
  have htrace : WordTrace (prefixWord ++ tailWord_5608502) baseStart_5608502 baseEnd_5608502 := by
    simpa [prefixWord, tailWord_5608502, baseEnd_5608502] using wordTrace_append hprefix tailTrace_5608502
  have hstable : (prefixWord ++ tailWord_5608502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608502).length < 2 ^ (prefixWord ++ tailWord_5608502).sum := by decide
  have hdescent : baseEnd_5608502 < baseStart_5608502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608535 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 4, 3, 2]
def baseStart_5608535 : Nat := 118140960795 + 5608535 * 2 ^ 59
def prefixEnd_5608535 : Nat := 4983230072969 + 3 ^ 40 * 5608535 * 2
def baseEnd_5608535 : Nat := 2879874222564319314719323

theorem tailTrace_5608535 : CollatzResearch.WordTrace tailWord_5608535 prefixEnd_5608535 2879874222564319314719323 := by
  unfold tailWord_5608535
  simp only [CollatzResearch.WordTrace]
  refine ⟨204560076736243031363859059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136373384490828687575906039 204560076736243031363859059)
  ·
    refine ⟨306840115104364547045788589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204560076736243031363859059 306840115104364547045788589)
    ·
      refine ⟨115065043164136705142170721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306840115104364547045788589 115065043164136705142170721)
      ·
        refine ⟨86298782373102528856628041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115065043164136705142170721 86298782373102528856628041)
        ·
          refine ⟨64724086779826896642471031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86298782373102528856628041 64724086779826896642471031)
          ·
            refine ⟨97086130169740344963706547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64724086779826896642471031 97086130169740344963706547)
            ·
              refine ⟨145629195254610517445559821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97086130169740344963706547 145629195254610517445559821)
              ·
                refine ⟨54610948220478944042084933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145629195254610517445559821 54610948220478944042084933)
                ·
                  refine ⟨10239552791339802007890925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54610948220478944042084933 10239552791339802007890925)
                  ·
                    refine ⟨3839832296752425752959097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10239552791339802007890925 3839832296752425752959097)
                    ·
                      refine ⟨2879874222564319314719323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839832296752425752959097 2879874222564319314719323)
                      ·
                        rfl

theorem cell23_5608535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_5608535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608535 prefixEnd_5608535 := by exact prefixLift 5608535
  have htrace : WordTrace (prefixWord ++ tailWord_5608535) baseStart_5608535 baseEnd_5608535 := by
    simpa [prefixWord, tailWord_5608535, baseEnd_5608535] using wordTrace_append hprefix tailTrace_5608535
  have hstable : (prefixWord ++ tailWord_5608535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608535).length < 2 ^ (prefixWord ++ tailWord_5608535).sum := by decide
  have hdescent : baseEnd_5608535 < baseStart_5608535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608585 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_5608585 : Nat := 118140960795 + 5608585 * 2 ^ 59
def prefixEnd_5608585 : Nat := 4983230072969 + 3 ^ 40 * 5608585 * 2
def baseEnd_5608585 : Nat := 2879899896597044119094093

theorem tailTrace_5608585 : CollatzResearch.WordTrace tailWord_5608585 prefixEnd_5608585 2879899896597044119094093 := by
  unfold tailWord_5608585
  simp only [CollatzResearch.WordTrace]
  refine ⟨204561900386061889903179209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136374600257374593268786139 204561900386061889903179209)
  ·
    refine ⟨153421425289546417427384407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204561900386061889903179209 153421425289546417427384407)
    ·
      refine ⟨230132137934319626141076611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153421425289546417427384407 230132137934319626141076611)
      ·
        refine ⟨345198206901479439211614917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230132137934319626141076611 345198206901479439211614917)
        ·
          refine ⟨64724663794027394852177797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345198206901479439211614917 64724663794027394852177797)
          ·
            refine ⟨12135874461380136534783337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64724663794027394852177797 12135874461380136534783337)
            ·
              refine ⟨9101905846035102401087503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12135874461380136534783337 9101905846035102401087503)
              ·
                refine ⟨13652858769052653601631255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101905846035102401087503 13652858769052653601631255)
                ·
                  refine ⟨20479288153578980402446883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13652858769052653601631255 20479288153578980402446883)
                  ·
                    refine ⟨30718932230368470603670325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20479288153578980402446883 30718932230368470603670325)
                    ·
                      refine ⟨2879899896597044119094093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30718932230368470603670325 2879899896597044119094093)
                      ·
                        rfl

theorem cell23_5608585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_5608585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608585 prefixEnd_5608585 := by exact prefixLift 5608585
  have htrace : WordTrace (prefixWord ++ tailWord_5608585) baseStart_5608585 baseEnd_5608585 := by
    simpa [prefixWord, tailWord_5608585, baseEnd_5608585] using wordTrace_append hprefix tailTrace_5608585
  have hstable : (prefixWord ++ tailWord_5608585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608585).length < 2 ^ (prefixWord ++ tailWord_5608585).sum := by decide
  have hdescent : baseEnd_5608585 < baseStart_5608585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608599 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 3, 2, 2]
def baseStart_5608599 : Nat := 118140960795 + 5608599 * 2 ^ 59
def prefixEnd_5608599 : Nat := 4983230072969 + 3 ^ 40 * 5608599 * 2
def baseEnd_5608599 : Nat := 2879907085326207064319029

theorem tailTrace_5608599 : CollatzResearch.WordTrace tailWord_5608599 prefixEnd_5608599 2879907085326207064319029 := by
  unfold tailWord_5608599
  simp only [CollatzResearch.WordTrace]
  refine ⟨204562411008011170294188851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136374940672007446862792567 204562411008011170294188851)
  ·
    refine ⟨306843616512016755441283277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204562411008011170294188851 306843616512016755441283277)
    ·
      refine ⟨115066356192006283290481229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306843616512016755441283277 115066356192006283290481229)
      ·
        refine ⟨43149883572002356233930461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115066356192006283290481229 43149883572002356233930461)
        ·
          refine ⟨16181206339500883587723923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43149883572002356233930461 16181206339500883587723923)
          ·
            refine ⟨24271809509251325381585885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16181206339500883587723923 24271809509251325381585885)
            ·
              refine ⟨9101928565969247018094707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24271809509251325381585885 9101928565969247018094707)
              ·
                refine ⟨13652892848953870527142061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101928565969247018094707 13652892848953870527142061)
                ·
                  refine ⟨5119834818357701447678273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13652892848953870527142061 5119834818357701447678273)
                  ·
                    refine ⟨3839876113768276085758705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119834818357701447678273 3839876113768276085758705)
                    ·
                      refine ⟨2879907085326207064319029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839876113768276085758705 2879907085326207064319029)
                      ·
                        rfl

theorem cell23_5608599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_5608599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608599 prefixEnd_5608599 := by exact prefixLift 5608599
  have htrace : WordTrace (prefixWord ++ tailWord_5608599) baseStart_5608599 baseEnd_5608599 := by
    simpa [prefixWord, tailWord_5608599, baseEnd_5608599] using wordTrace_append hprefix tailTrace_5608599
  have hstable : (prefixWord ++ tailWord_5608599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608599).length < 2 ^ (prefixWord ++ tailWord_5608599).sum := by decide
  have hdescent : baseEnd_5608599 < baseStart_5608599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608608 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5608608 : Nat := 118140960795 + 5608608 * 2 ^ 59
def prefixEnd_5608608 : Nat := 4983230072969 + 3 ^ 40 * 5608608 * 2
def baseEnd_5608608 : Nat := 2879911706652097529106487

theorem tailTrace_5608608 : CollatzResearch.WordTrace tailWord_5608608 prefixEnd_5608608 2879911706652097529106487 := by
  unfold tailWord_5608608
  simp only [CollatzResearch.WordTrace]
  refine ⟨102281369632489282415633239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136375159509985709887510985 102281369632489282415633239)
  ·
    refine ⟨153422054448733923623449859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102281369632489282415633239 153422054448733923623449859)
    ·
      refine ⟨230133081673100885435174789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153422054448733923623449859 230133081673100885435174789)
      ·
        refine ⟨43149952813706416019095273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230133081673100885435174789 43149952813706416019095273)
        ·
          refine ⟨32362464610279812014321455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43149952813706416019095273 32362464610279812014321455)
          ·
            refine ⟨48543696915419718021482183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32362464610279812014321455 48543696915419718021482183)
            ·
              refine ⟨72815545373129577032223275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48543696915419718021482183 72815545373129577032223275)
              ·
                refine ⟨109223318059694365548334913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72815545373129577032223275 109223318059694365548334913)
                ·
                  refine ⟨81917488544770774161251185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109223318059694365548334913 81917488544770774161251185)
                  ·
                    refine ⟨61438116408578080620938389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81917488544770774161251185 61438116408578080620938389)
                    ·
                      refine ⟨2879911706652097529106487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61438116408578080620938389 2879911706652097529106487)
                      ·
                        rfl

theorem cell23_5608608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5608608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608608 prefixEnd_5608608 := by exact prefixLift 5608608
  have htrace : WordTrace (prefixWord ++ tailWord_5608608) baseStart_5608608 baseEnd_5608608 := by
    simpa [prefixWord, tailWord_5608608, baseEnd_5608608] using wordTrace_append hprefix tailTrace_5608608
  have hstable : (prefixWord ++ tailWord_5608608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608608).length < 2 ^ (prefixWord ++ tailWord_5608608).sum := by decide
  have hdescent : baseEnd_5608608 < baseStart_5608608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608672 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2]
def baseStart_5608672 : Nat := 118140960795 + 5608672 * 2 ^ 59
def prefixEnd_5608672 : Nat := 4983230072969 + 3 ^ 40 * 5608672 * 2
def baseEnd_5608672 : Nat := 2879944569413985278706193

theorem tailTrace_5608672 : CollatzResearch.WordTrace tailWord_5608672 prefixEnd_5608672 2879944569413985278706193 := by
  unfold tailWord_5608672
  simp only [CollatzResearch.WordTrace]
  refine ⟨102282536768373351880798135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136376715691164469174397513 102282536768373351880798135)
  ·
    refine ⟨153423805152560027821197203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102282536768373351880798135 153423805152560027821197203)
    ·
      refine ⟨230135707728840041731795805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153423805152560027821197203 230135707728840041731795805)
      ·
        refine ⟨86300890398315015649423427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230135707728840041731795805 86300890398315015649423427)
        ·
          refine ⟨129451335597472523474135141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86300890398315015649423427 129451335597472523474135141)
          ·
            refine ⟨24272125424526098151400339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129451335597472523474135141 24272125424526098151400339)
            ·
              refine ⟨36408188136789147227100509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24272125424526098151400339 36408188136789147227100509)
              ·
                refine ⟨13653070551295930210162691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36408188136789147227100509 13653070551295930210162691)
                ·
                  refine ⟨20479605826943895315244037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13653070551295930210162691 20479605826943895315244037)
                  ·
                    refine ⟨3839926092551980371608257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20479605826943895315244037 3839926092551980371608257)
                    ·
                      refine ⟨2879944569413985278706193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839926092551980371608257 2879944569413985278706193)
                      ·
                        rfl

theorem cell23_5608672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_5608672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608672 prefixEnd_5608672 := by exact prefixLift 5608672
  have htrace : WordTrace (prefixWord ++ tailWord_5608672) baseStart_5608672 baseEnd_5608672 := by
    simpa [prefixWord, tailWord_5608672, baseEnd_5608672] using wordTrace_append hprefix tailTrace_5608672
  have hstable : (prefixWord ++ tailWord_5608672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608672).length < 2 ^ (prefixWord ++ tailWord_5608672).sum := by decide
  have hdescent : baseEnd_5608672 < baseStart_5608672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608688 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_5608688 : Nat := 118140960795 + 5608688 * 2 ^ 59
def prefixEnd_5608688 : Nat := 4983230072969 + 3 ^ 40 * 5608688 * 2
def baseEnd_5608688 : Nat := 2879952785104457216106119

theorem tailTrace_5608688 : CollatzResearch.WordTrace tailWord_5608688 prefixEnd_5608688 2879952785104457216106119 := by
  unfold tailWord_5608688
  simp only [CollatzResearch.WordTrace]
  refine ⟨102282828552344369247089359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136377104736459158996119145 102282828552344369247089359)
  ·
    refine ⟨153424242828516553870634039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102282828552344369247089359 153424242828516553870634039)
    ·
      refine ⟨230136364242774830805951059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153424242828516553870634039 230136364242774830805951059)
      ·
        refine ⟨345204546364162246208926589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230136364242774830805951059 345204546364162246208926589)
        ·
          refine ⟨129451704886560842328347471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345204546364162246208926589 129451704886560842328347471)
          ·
            refine ⟨194177557329841263492521207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129451704886560842328347471 194177557329841263492521207)
            ·
              refine ⟨291266335994761895238781811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194177557329841263492521207 291266335994761895238781811)
              ·
                refine ⟨436899503992142842858172717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291266335994761895238781811 436899503992142842858172717)
                ·
                  refine ⟨163837313997053566071814769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 436899503992142842858172717 163837313997053566071814769)
                  ·
                    refine ⟨122877985497790174553861077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163837313997053566071814769 122877985497790174553861077)
                    ·
                      refine ⟨2879952785104457216106119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122877985497790174553861077 2879952785104457216106119)
                      ·
                        rfl

theorem cell23_5608688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_5608688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608688 prefixEnd_5608688 := by exact prefixLift 5608688
  have htrace : WordTrace (prefixWord ++ tailWord_5608688) baseStart_5608688 baseEnd_5608688 := by
    simpa [prefixWord, tailWord_5608688, baseEnd_5608688] using wordTrace_append hprefix tailTrace_5608688
  have hstable : (prefixWord ++ tailWord_5608688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608688).length < 2 ^ (prefixWord ++ tailWord_5608688).sum := by decide
  have hdescent : baseEnd_5608688 < baseStart_5608688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608702 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5608702 : Nat := 118140960795 + 5608702 * 2 ^ 59
def prefixEnd_5608702 : Nat := 4983230072969 + 3 ^ 40 * 5608702 * 2
def baseEnd_5608702 : Nat := 2879959973833620161331055

theorem tailTrace_5608702 : CollatzResearch.WordTrace tailWord_5608702 prefixEnd_5608702 2879959973833620161331055 := by
  unfold tailWord_5608702
  simp only [CollatzResearch.WordTrace]
  refine ⟨25570770965829752360648545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136377445151092012590125573 25570770965829752360648545)
  ·
    refine ⟨19178078224372314270486409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25570770965829752360648545 19178078224372314270486409)
    ·
      refine ⟨14383558668279235702864807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19178078224372314270486409 14383558668279235702864807)
      ·
        refine ⟨21575338002418853554297211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14383558668279235702864807 21575338002418853554297211)
        ·
          refine ⟨32363007003628280331445817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21575338002418853554297211 32363007003628280331445817)
          ·
            refine ⟨24272255252721210248584363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32363007003628280331445817 24272255252721210248584363)
            ·
              refine ⟨36408382879081815372876545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24272255252721210248584363 36408382879081815372876545)
              ·
                refine ⟨27306287159311361529657409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36408382879081815372876545 27306287159311361529657409)
                ·
                  refine ⟨20479715369483521147243057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27306287159311361529657409 20479715369483521147243057)
                  ·
                    refine ⟨15359786527112640860432293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20479715369483521147243057 15359786527112640860432293)
                    ·
                      refine ⟨2879959973833620161331055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15359786527112640860432293 2879959973833620161331055)
                      ·
                        rfl

theorem cell23_5608702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5608702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608702 prefixEnd_5608702 := by exact prefixLift 5608702
  have htrace : WordTrace (prefixWord ++ tailWord_5608702) baseStart_5608702 baseEnd_5608702 := by
    simpa [prefixWord, tailWord_5608702, baseEnd_5608702] using wordTrace_append hprefix tailTrace_5608702
  have hstable : (prefixWord ++ tailWord_5608702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608702).length < 2 ^ (prefixWord ++ tailWord_5608702).sum := by decide
  have hdescent : baseEnd_5608702 < baseStart_5608702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608712 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 7]
def baseStart_5608712 : Nat := 118140960795 + 5608712 * 2 ^ 59
def prefixEnd_5608712 : Nat := 4983230072969 + 3 ^ 40 * 5608712 * 2
def baseEnd_5608712 : Nat := 319996123182240569134001

theorem tailTrace_5608712 : CollatzResearch.WordTrace tailWord_5608712 prefixEnd_5608712 319996123182240569134001 := by
  unfold tailWord_5608712
  simp only [CollatzResearch.WordTrace]
  refine ⟨102283266228300895296526195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136377688304401193728701593 102283266228300895296526195)
  ·
    refine ⟨153424899342451342944789293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102283266228300895296526195 153424899342451342944789293)
    ·
      refine ⟨57534337253419253604295985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153424899342451342944789293 57534337253419253604295985)
      ·
        refine ⟨43150752940064440203221989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57534337253419253604295985 43150752940064440203221989)
        ·
          refine ⟨8090766176262082538104123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43150752940064440203221989 8090766176262082538104123)
          ·
            refine ⟨12136149264393123807156185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090766176262082538104123 12136149264393123807156185)
            ·
              refine ⟨9102111948294842855367139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136149264393123807156185 9102111948294842855367139)
              ·
                refine ⟨13653167922442264283050709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9102111948294842855367139 13653167922442264283050709)
                ·
                  refine ⟨319996123182240569134001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13653167922442264283050709 319996123182240569134001)
                  ·
                    rfl

theorem cell23_5608712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_5608712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608712 prefixEnd_5608712 := by exact prefixLift 5608712
  have htrace : WordTrace (prefixWord ++ tailWord_5608712) baseStart_5608712 baseEnd_5608712 := by
    simpa [prefixWord, tailWord_5608712, baseEnd_5608712] using wordTrace_append hprefix tailTrace_5608712
  have hstable : (prefixWord ++ tailWord_5608712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608712).length < 2 ^ (prefixWord ++ tailWord_5608712).sum := by decide
  have hdescent : baseEnd_5608712 < baseStart_5608712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608732 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5608732 : Nat := 118140960795 + 5608732 * 2 ^ 59
def prefixEnd_5608732 : Nat := 4983230072969 + 3 ^ 40 * 5608732 * 2
def baseEnd_5608732 : Nat := 2879975378253255043955917

theorem tailTrace_5608732 : CollatzResearch.WordTrace tailWord_5608732 prefixEnd_5608732 2879975378253255043955917 := by
  unfold tailWord_5608732
  simp only [CollatzResearch.WordTrace]
  refine ⟨102283630958264667004390225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136378174611019556005853633 102283630958264667004390225)
  ·
    refine ⟨76712723218698500253292669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102283630958264667004390225 76712723218698500253292669)
    ·
      refine ⟨28767271207011937594984751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76712723218698500253292669 28767271207011937594984751)
      ·
        refine ⟨43150906810517906392477127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28767271207011937594984751 43150906810517906392477127)
        ·
          refine ⟨64726360215776859588715691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43150906810517906392477127 64726360215776859588715691)
          ·
            refine ⟨97089540323665289383073537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64726360215776859588715691 97089540323665289383073537)
            ·
              refine ⟨72817155242748967037305153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97089540323665289383073537 72817155242748967037305153)
              ·
                refine ⟨54612866432061725277978865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72817155242748967037305153 54612866432061725277978865)
                ·
                  refine ⟨40959649824046293958484149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54612866432061725277978865 40959649824046293958484149)
                  ·
                    refine ⟨3839967171004340058607889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40959649824046293958484149 3839967171004340058607889)
                    ·
                      refine ⟨2879975378253255043955917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839967171004340058607889 2879975378253255043955917)
                      ·
                        rfl

theorem cell23_5608732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5608732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608732 prefixEnd_5608732 := by exact prefixLift 5608732
  have htrace : WordTrace (prefixWord ++ tailWord_5608732) baseStart_5608732 baseEnd_5608732 := by
    simpa [prefixWord, tailWord_5608732, baseEnd_5608732] using wordTrace_append hprefix tailTrace_5608732
  have hstable : (prefixWord ++ tailWord_5608732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608732).length < 2 ^ (prefixWord ++ tailWord_5608732).sum := by decide
  have hdescent : baseEnd_5608732 < baseStart_5608732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608746 : List Nat := [3, 1, 4, 2, 1, 3, 1, 3, 5]
def baseStart_5608746 : Nat := 118140960795 + 5608746 * 2 ^ 59
def prefixEnd_5608746 : Nat := 4983230072969 + 3 ^ 40 * 5608746 * 2
def baseEnd_5608746 : Nat := 319998062998046443242317

theorem tailTrace_5608746 : CollatzResearch.WordTrace tailWord_5608746 prefixEnd_5608746 319998062998046443242317 := by
  unfold tailWord_5608746
  simp only [CollatzResearch.WordTrace]
  refine ⟨51141943134619653599947523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136378515025652409599860061 51141943134619653599947523)
  ·
    refine ⟨76712914701929480399921285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51141943134619653599947523 76712914701929480399921285)
    ·
      refine ⟨14383671506611777574985241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76712914701929480399921285 14383671506611777574985241)
      ·
        refine ⟨10787753629958833181238931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14383671506611777574985241 10787753629958833181238931)
        ·
          refine ⟨16181630444938249771858397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10787753629958833181238931 16181630444938249771858397)
          ·
            refine ⟨6068111416851843664446899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16181630444938249771858397 6068111416851843664446899)
            ·
              refine ⟨9102167125277765496670349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068111416851843664446899 9102167125277765496670349)
              ·
                refine ⟨3413312671979162061251381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9102167125277765496670349 3413312671979162061251381)
                ·
                  refine ⟨319998062998046443242317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413312671979162061251381 319998062998046443242317)
                  ·
                    rfl

theorem cell23_5608746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_5608746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608746 prefixEnd_5608746 := by exact prefixLift 5608746
  have htrace : WordTrace (prefixWord ++ tailWord_5608746) baseStart_5608746 baseEnd_5608746 := by
    simpa [prefixWord, tailWord_5608746, baseEnd_5608746] using wordTrace_append hprefix tailTrace_5608746
  have hstable : (prefixWord ++ tailWord_5608746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608746).length < 2 ^ (prefixWord ++ tailWord_5608746).sum := by decide
  have hdescent : baseEnd_5608746 < baseStart_5608746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608762 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_5608762 : Nat := 118140960795 + 5608762 * 2 ^ 59
def prefixEnd_5608762 : Nat := 4983230072969 + 3 ^ 40 * 5608762 * 2
def baseEnd_5608762 : Nat := 2879990782672889926580779

theorem tailTrace_5608762 : CollatzResearch.WordTrace tailWord_5608762 prefixEnd_5608762 2879990782672889926580779 := by
  unfold tailWord_5608762
  simp only [CollatzResearch.WordTrace]
  refine ⟨51142089026605162283093135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136378904070947099421581693 51142089026605162283093135)
  ·
    refine ⟨76713133539907743424639703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51142089026605162283093135 76713133539907743424639703)
    ·
      refine ⟨115069700309861615136959555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76713133539907743424639703 115069700309861615136959555)
      ·
        refine ⟨172604550464792422705439333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115069700309861615136959555 172604550464792422705439333)
        ·
          refine ⟨32363353212148579257269875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172604550464792422705439333 32363353212148579257269875)
          ·
            refine ⟨48545029818222868885904813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32363353212148579257269875 48545029818222868885904813)
            ·
              refine ⟨18204386181833575832214305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48545029818222868885904813 18204386181833575832214305)
              ·
                refine ⟨13653289636375181874160729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18204386181833575832214305 13653289636375181874160729)
                ·
                  refine ⟨10239967227281386405620547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13653289636375181874160729 10239967227281386405620547)
                  ·
                    refine ⟨15359950840922079608430821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10239967227281386405620547 15359950840922079608430821)
                    ·
                      refine ⟨2879990782672889926580779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15359950840922079608430821 2879990782672889926580779)
                      ·
                        rfl

theorem cell23_5608762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_5608762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608762 prefixEnd_5608762 := by exact prefixLift 5608762
  have htrace : WordTrace (prefixWord ++ tailWord_5608762) baseStart_5608762 baseEnd_5608762 := by
    simpa [prefixWord, tailWord_5608762, baseEnd_5608762] using wordTrace_append hprefix tailTrace_5608762
  have hstable : (prefixWord ++ tailWord_5608762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608762).length < 2 ^ (prefixWord ++ tailWord_5608762).sum := by decide
  have hdescent : baseEnd_5608762 < baseStart_5608762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608774 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5608774 : Nat := 118140960795 + 5608774 * 2 ^ 59
def prefixEnd_5608774 : Nat := 4983230072969 + 3 ^ 40 * 5608774 * 2
def baseEnd_5608774 : Nat := 2879996944440743879630725

theorem tailTrace_5608774 : CollatzResearch.WordTrace tailWord_5608774 prefixEnd_5608774 2879996944440743879630725 := by
  unfold tailWord_5608774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6392774805699286724431543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136379195854918116787872917 6392774805699286724431543)
  ·
    refine ⟨9589162208548930086647315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6392774805699286724431543 9589162208548930086647315)
    ·
      refine ⟨14383743312823395129970973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9589162208548930086647315 14383743312823395129970973)
      ·
        refine ⟨5393903742308773173739115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14383743312823395129970973 5393903742308773173739115)
        ·
          refine ⟨8090855613463159760608673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393903742308773173739115 8090855613463159760608673)
          ·
            refine ⟨6068141710097369820456505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8090855613463159760608673 6068141710097369820456505)
            ·
              refine ⟨4551106282573027365342379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068141710097369820456505 4551106282573027365342379)
              ·
                refine ⟨6826659423859541048013569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551106282573027365342379 6826659423859541048013569)
                ·
                  refine ⟨5119994567894655786010177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826659423859541048013569 5119994567894655786010177)
                  ·
                    refine ⟨3839995925920991839507633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5119994567894655786010177 3839995925920991839507633)
                    ·
                      refine ⟨2879996944440743879630725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3839995925920991839507633 2879996944440743879630725)
                      ·
                        rfl

theorem cell23_5608774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5608774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608774 prefixEnd_5608774 := by exact prefixLift 5608774
  have htrace : WordTrace (prefixWord ++ tailWord_5608774) baseStart_5608774 baseEnd_5608774 := by
    simpa [prefixWord, tailWord_5608774, baseEnd_5608774] using wordTrace_append hprefix tailTrace_5608774
  have hstable : (prefixWord ++ tailWord_5608774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608774).length < 2 ^ (prefixWord ++ tailWord_5608774).sum := by decide
  have hdescent : baseEnd_5608774 < baseStart_5608774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608782 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_5608782 : Nat := 118140960795 + 5608782 * 2 ^ 59
def prefixEnd_5608782 : Nat := 4983230072969 + 3 ^ 40 * 5608782 * 2
def baseEnd_5608782 : Nat := 2880001052285979848330687

theorem tailTrace_5608782 : CollatzResearch.WordTrace tailWord_5608782 prefixEnd_5608782 2880001052285979848330687 := by
  unfold tailWord_5608782
  simp only [CollatzResearch.WordTrace]
  refine ⟨25571135695793524068512575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136379390377565461698733733 25571135695793524068512575)
  ·
    refine ⟨38356703543690286102768863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25571135695793524068512575 38356703543690286102768863)
    ·
      refine ⟨57535055315535429154153295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38356703543690286102768863 57535055315535429154153295)
      ·
        refine ⟨86302582973303143731229943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57535055315535429154153295 86302582973303143731229943)
        ·
          refine ⟨129453874459954715596844915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86302582973303143731229943 129453874459954715596844915)
          ·
            refine ⟨194180811689932073395267373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129453874459954715596844915 194180811689932073395267373)
            ·
              refine ⟨72817804383724527523225265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194180811689932073395267373 72817804383724527523225265)
              ·
                refine ⟨54613353287793395642418949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72817804383724527523225265 54613353287793395642418949)
                ·
                  refine ⟨10240003741461261682953553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54613353287793395642418949 10240003741461261682953553)
                  ·
                    refine ⟨7680002806095946262215165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10240003741461261682953553 7680002806095946262215165)
                    ·
                      refine ⟨2880001052285979848330687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680002806095946262215165 2880001052285979848330687)
                      ·
                        rfl

theorem cell23_5608782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_5608782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608782 prefixEnd_5608782 := by exact prefixLift 5608782
  have htrace : WordTrace (prefixWord ++ tailWord_5608782) baseStart_5608782 baseEnd_5608782 := by
    simpa [prefixWord, tailWord_5608782, baseEnd_5608782] using wordTrace_append hprefix tailTrace_5608782
  have hstable : (prefixWord ++ tailWord_5608782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608782).length < 2 ^ (prefixWord ++ tailWord_5608782).sum := by decide
  have hdescent : baseEnd_5608782 < baseStart_5608782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608829 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 3]
def baseStart_5608829 : Nat := 118140960795 + 5608829 * 2 ^ 59
def prefixEnd_5608829 : Nat := 4983230072969 + 3 ^ 40 * 5608829 * 2
def baseEnd_5608829 : Nat := 2880025185876741164442971

theorem tailTrace_5608829 : CollatzResearch.WordTrace tailWord_5608829 prefixEnd_5608829 2880025185876741164442971 := by
  unfold tailWord_5608829
  simp only [CollatzResearch.WordTrace]
  refine ⟨204570799797177919575061541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136380533198118613050041027 204570799797177919575061541)
  ·
    refine ⟨38357024961970859920324039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204570799797177919575061541 38357024961970859920324039)
    ·
      refine ⟨57535537442956289880486059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38357024961970859920324039 57535537442956289880486059)
      ·
        refine ⟨86303306164434434820729089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57535537442956289880486059 86303306164434434820729089)
        ·
          refine ⟨64727479623325826115546817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86303306164434434820729089 64727479623325826115546817)
          ·
            refine ⟨48545609717494369586660113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64727479623325826115546817 48545609717494369586660113)
            ·
              refine ⟨36409207288120777189995085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48545609717494369586660113 36409207288120777189995085)
              ·
                refine ⟨13653452733045291446248157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36409207288120777189995085 13653452733045291446248157)
                ·
                  refine ⟨5120044774891984292343059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13653452733045291446248157 5120044774891984292343059)
                  ·
                    refine ⟨7680067162337976438514589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120044774891984292343059 7680067162337976438514589)
                    ·
                      refine ⟨2880025185876741164442971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680067162337976438514589 2880025185876741164442971)
                      ·
                        rfl

theorem cell23_5608829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_5608829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608829 prefixEnd_5608829 := by exact prefixLift 5608829
  have htrace : WordTrace (prefixWord ++ tailWord_5608829) baseStart_5608829 baseEnd_5608829 := by
    simpa [prefixWord, tailWord_5608829, baseEnd_5608829] using wordTrace_append hprefix tailTrace_5608829
  have hstable : (prefixWord ++ tailWord_5608829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608829).length < 2 ^ (prefixWord ++ tailWord_5608829).sum := by decide
  have hdescent : baseEnd_5608829 < baseStart_5608829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608850 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5608850 : Nat := 118140960795 + 5608850 * 2 ^ 59
def prefixEnd_5608850 : Nat := 4983230072969 + 3 ^ 40 * 5608850 * 2
def baseEnd_5608850 : Nat := 2880035968970485582280375

theorem tailTrace_5608850 : CollatzResearch.WordTrace tailWord_5608850 prefixEnd_5608850 2880035968970485582280375 := by
  unfold tailWord_5608850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51142891432525460040394001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136381043820067893441050669 51142891432525460040394001)
  ·
    refine ⟨38357168574394095030295501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51142891432525460040394001 38357168574394095030295501)
    ·
      refine ⟨14383938215397785636360813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38357168574394095030295501 14383938215397785636360813)
      ·
        refine ⟨5393976830774169613635305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14383938215397785636360813 5393976830774169613635305)
        ·
          refine ⟨4045482623080627210226479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5393976830774169613635305 4045482623080627210226479)
          ·
            refine ⟨6068223934620940815339719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045482623080627210226479 6068223934620940815339719)
            ·
              refine ⟨9102335901931411223009579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068223934620940815339719 9102335901931411223009579)
              ·
                refine ⟨13653503852897116834514369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9102335901931411223009579 13653503852897116834514369)
                ·
                  refine ⟨10240127889672837625885777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13653503852897116834514369 10240127889672837625885777)
                  ·
                    refine ⟨7680095917254628219414333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10240127889672837625885777 7680095917254628219414333)
                    ·
                      refine ⟨2880035968970485582280375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680095917254628219414333 2880035968970485582280375)
                      ·
                        rfl

theorem cell23_5608850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5608850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608850 prefixEnd_5608850 := by exact prefixLift 5608850
  have htrace : WordTrace (prefixWord ++ tailWord_5608850) baseStart_5608850 baseEnd_5608850 := by
    simpa [prefixWord, tailWord_5608850, baseEnd_5608850] using wordTrace_append hprefix tailTrace_5608850
  have hstable : (prefixWord ++ tailWord_5608850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608850).length < 2 ^ (prefixWord ++ tailWord_5608850).sum := by decide
  have hdescent : baseEnd_5608850 < baseStart_5608850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608856 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5608856 : Nat := 118140960795 + 5608856 * 2 ^ 59
def prefixEnd_5608856 : Nat := 4983230072969 + 3 ^ 40 * 5608856 * 2
def baseEnd_5608856 : Nat := 2880039049854412558805347

theorem tailTrace_5608856 : CollatzResearch.WordTrace tailWord_5608856 prefixEnd_5608856 2880039049854412558805347 := by
  unfold tailWord_5608856
  simp only [CollatzResearch.WordTrace]
  refine ⟨102285892284040051593147211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136381189712053402124196281 102285892284040051593147211)
  ·
    refine ⟨153428838426060077389720817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102285892284040051593147211 153428838426060077389720817)
    ·
      refine ⟨115071628819545058042290613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153428838426060077389720817 115071628819545058042290613)
      ·
        refine ⟨10787965201832349191464745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115071628819545058042290613 10787965201832349191464745)
        ·
          refine ⟨8090973901374261893598559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10787965201832349191464745 8090973901374261893598559)
          ·
            refine ⟨12136460852061392840397839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090973901374261893598559 12136460852061392840397839)
            ·
              refine ⟨18204691278092089260596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136460852061392840397839 18204691278092089260596759)
              ·
                refine ⟨27307036917138133890895139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18204691278092089260596759 27307036917138133890895139)
                ·
                  refine ⟨40960555375707200836342709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27307036917138133890895139 40960555375707200836342709)
                  ·
                    refine ⟨3840052066472550078407129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40960555375707200836342709 3840052066472550078407129)
                    ·
                      refine ⟨2880039049854412558805347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840052066472550078407129 2880039049854412558805347)
                      ·
                        rfl

theorem cell23_5608856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5608856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608856 prefixEnd_5608856 := by exact prefixLift 5608856
  have htrace : WordTrace (prefixWord ++ tailWord_5608856) baseStart_5608856 baseEnd_5608856 := by
    simpa [prefixWord, tailWord_5608856, baseEnd_5608856] using wordTrace_append hprefix tailTrace_5608856
  have hstable : (prefixWord ++ tailWord_5608856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608856).length < 2 ^ (prefixWord ++ tailWord_5608856).sum := by decide
  have hdescent : baseEnd_5608856 < baseStart_5608856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608863 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5608863 : Nat := 118140960795 + 5608863 * 2 ^ 59
def prefixEnd_5608863 : Nat := 4983230072969 + 3 ^ 40 * 5608863 * 2
def baseEnd_5608863 : Nat := 2880042644218994031417815

theorem tailTrace_5608863 : CollatzResearch.WordTrace tailWord_5608863 prefixEnd_5608863 2880042644218994031417815 := by
  unfold tailWord_5608863
  simp only [CollatzResearch.WordTrace]
  refine ⟨204572039879054743381799243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136381359919369828921199495 204572039879054743381799243)
  ·
    refine ⟨306858059818582115072698865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204572039879054743381799243 306858059818582115072698865)
    ·
      refine ⟨230143544863936586304524149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306858059818582115072698865 230143544863936586304524149)
      ·
        refine ⟨21575957330994054966049139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230143544863936586304524149 21575957330994054966049139)
        ·
          refine ⟨32363935996491082449073709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21575957330994054966049139 32363935996491082449073709)
          ·
            refine ⟨12136475998684155918402641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32363935996491082449073709 12136475998684155918402641)
            ·
              refine ⟨9102356999013116938801981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136475998684155918402641 9102356999013116938801981)
              ·
                refine ⟨3413383874629918852050743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9102356999013116938801981 3413383874629918852050743)
                ·
                  refine ⟨5120075811944878278076115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413383874629918852050743 5120075811944878278076115)
                  ·
                    refine ⟨7680113717917317417114173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120075811944878278076115 7680113717917317417114173)
                    ·
                      refine ⟨2880042644218994031417815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680113717917317417114173 2880042644218994031417815)
                      ·
                        rfl

theorem cell23_5608863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5608863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608863 prefixEnd_5608863 := by exact prefixLift 5608863
  have htrace : WordTrace (prefixWord ++ tailWord_5608863) baseStart_5608863 baseEnd_5608863 := by
    simpa [prefixWord, tailWord_5608863, baseEnd_5608863] using wordTrace_append hprefix tailTrace_5608863
  have hstable : (prefixWord ++ tailWord_5608863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608863).length < 2 ^ (prefixWord ++ tailWord_5608863).sum := by decide
  have hdescent : baseEnd_5608863 < baseStart_5608863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608866 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5608866 : Nat := 118140960795 + 5608866 * 2 ^ 59
def prefixEnd_5608866 : Nat := 4983230072969 + 3 ^ 40 * 5608866 * 2
def baseEnd_5608866 : Nat := 960014728220319173226767

theorem tailTrace_5608866 : CollatzResearch.WordTrace tailWord_5608866 prefixEnd_5608866 960014728220319173226767 := by
  unfold tailWord_5608866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51143037324510968723539613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136381432865362583262772301 51143037324510968723539613)
  ·
    refine ⟨19178638996691613271327355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51143037324510968723539613 19178638996691613271327355)
    ·
      refine ⟨28767958495037419906991033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19178638996691613271327355 28767958495037419906991033)
      ·
        refine ⟨21575968871278064930243275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28767958495037419906991033 21575968871278064930243275)
        ·
          refine ⟨32363953306917097395364913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21575968871278064930243275 32363953306917097395364913)
          ·
            refine ⟨24272964980187823046523685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32363953306917097395364913 24272964980187823046523685)
            ·
              refine ⟨4551180933785216821223191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24272964980187823046523685 4551180933785216821223191)
              ·
                refine ⟨6826771400677825231834787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551180933785216821223191 6826771400677825231834787)
                ·
                  refine ⟨10240157101016737847752181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6826771400677825231834787 10240157101016737847752181)
                  ·
                    refine ⟨960014728220319173226767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10240157101016737847752181 960014728220319173226767)
                    ·
                      rfl

theorem cell23_5608866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5608866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608866 prefixEnd_5608866 := by exact prefixLift 5608866
  have htrace : WordTrace (prefixWord ++ tailWord_5608866) baseStart_5608866 baseEnd_5608866 := by
    simpa [prefixWord, tailWord_5608866, baseEnd_5608866] using wordTrace_append hprefix tailTrace_5608866
  have hstable : (prefixWord ++ tailWord_5608866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608866).length < 2 ^ (prefixWord ++ tailWord_5608866).sum := by decide
  have hdescent : baseEnd_5608866 < baseStart_5608866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608889 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5608889 : Nat := 118140960795 + 5608889 * 2 ^ 59
def prefixEnd_5608889 : Nat := 4983230072969 + 3 ^ 40 * 5608889 * 2
def baseEnd_5608889 : Nat := 2880055994716010929692695

theorem tailTrace_5608889 : CollatzResearch.WordTrace tailWord_5608889 prefixEnd_5608889 2880055994716010929692695 := by
  unfold tailWord_5608889
  simp only [CollatzResearch.WordTrace]
  refine ⟨204572988176960549822245721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136381992117973699881497147 204572988176960549822245721)
  ·
    refine ⟨153429741132720412366684291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204572988176960549822245721 153429741132720412366684291)
    ·
      refine ⟨230144611699080618550026437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153429741132720412366684291 230144611699080618550026437)
      ·
        refine ⟨43152114693577615978129957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230144611699080618550026437 43152114693577615978129957)
        ·
          refine ⟨8091021505045802995899367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43152114693577615978129957 8091021505045802995899367)
          ·
            refine ⟨12136532257568704493849051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091021505045802995899367 12136532257568704493849051)
            ·
              refine ⟨18204798386353056740773577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136532257568704493849051 18204798386353056740773577)
              ·
                refine ⟨13653598789764792555580183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18204798386353056740773577 13653598789764792555580183)
                ·
                  refine ⟨20480398184647188833370275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13653598789764792555580183 20480398184647188833370275)
                  ·
                    refine ⟨30720597276970783250055413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20480398184647188833370275 30720597276970783250055413)
                    ·
                      refine ⟨2880055994716010929692695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30720597276970783250055413 2880055994716010929692695)
                      ·
                        rfl

theorem cell23_5608889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5608889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608889 prefixEnd_5608889 := by exact prefixLift 5608889
  have htrace : WordTrace (prefixWord ++ tailWord_5608889) baseStart_5608889 baseEnd_5608889 := by
    simpa [prefixWord, tailWord_5608889, baseEnd_5608889] using wordTrace_append hprefix tailTrace_5608889
  have hstable : (prefixWord ++ tailWord_5608889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608889).length < 2 ^ (prefixWord ++ tailWord_5608889).sum := by decide
  have hdescent : baseEnd_5608889 < baseStart_5608889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608906 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_5608906 : Nat := 118140960795 + 5608906 * 2 ^ 59
def prefixEnd_5608906 : Nat := 4983230072969 + 3 ^ 40 * 5608906 * 2
def baseEnd_5608906 : Nat := 2880064723887137363180117

theorem tailTrace_5608906 : CollatzResearch.WordTrace tailWord_5608906 prefixEnd_5608906 2880064723887137363180117 := by
  unfold tailWord_5608906
  simp only [CollatzResearch.WordTrace]
  refine ⟨51143402054474740431403643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136382405478599307817076381 51143402054474740431403643)
  ·
    refine ⟨76715103081712110647105465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51143402054474740431403643 76715103081712110647105465)
    ·
      refine ⟨57536327311284082985329099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76715103081712110647105465 57536327311284082985329099)
      ·
        refine ⟨86304490966926124477993649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57536327311284082985329099 86304490966926124477993649)
        ·
          refine ⟨64728368225194593358495237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86304490966926124477993649 64728368225194593358495237)
          ·
            refine ⟨12136569042223986254717857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64728368225194593358495237 12136569042223986254717857)
            ·
              refine ⟨9102426781667989691038393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136569042223986254717857 9102426781667989691038393)
              ·
                refine ⟨6826820086250992268278795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9102426781667989691038393 6826820086250992268278795)
                ·
                  refine ⟨10240230129376488402418193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6826820086250992268278795 10240230129376488402418193)
                  ·
                    refine ⟨7680172597032366301813645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10240230129376488402418193 7680172597032366301813645)
                    ·
                      refine ⟨2880064723887137363180117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680172597032366301813645 2880064723887137363180117)
                      ·
                        rfl

theorem cell23_5608906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_5608906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608906 prefixEnd_5608906 := by exact prefixLift 5608906
  have htrace : WordTrace (prefixWord ++ tailWord_5608906) baseStart_5608906 baseEnd_5608906 := by
    simpa [prefixWord, tailWord_5608906, baseEnd_5608906] using wordTrace_append hprefix tailTrace_5608906
  have hstable : (prefixWord ++ tailWord_5608906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608906).length < 2 ^ (prefixWord ++ tailWord_5608906).sum := by decide
  have hdescent : baseEnd_5608906 < baseStart_5608906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608936 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5608936 : Nat := 118140960795 + 5608936 * 2 ^ 59
def prefixEnd_5608936 : Nat := 4983230072969 + 3 ^ 40 * 5608936 * 2
def baseEnd_5608936 : Nat := 2880080128306772245804979

theorem tailTrace_5608936 : CollatzResearch.WordTrace tailWord_5608936 prefixEnd_5608936 2880080128306772245804979 := by
  unfold tailWord_5608936
  simp only [CollatzResearch.WordTrace]
  refine ⟨102287351203895138424603331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136383134938526851232804441 102287351203895138424603331)
  ·
    refine ⟨153431026805842707636904997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102287351203895138424603331 153431026805842707636904997)
    ·
      refine ⟨28768317526095507681919687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153431026805842707636904997 28768317526095507681919687)
      ·
        refine ⟨43152476289143261522879531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28768317526095507681919687 43152476289143261522879531)
        ·
          refine ⟨64728714433714892284319297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43152476289143261522879531 64728714433714892284319297)
          ·
            refine ⟨48546535825286169213239473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64728714433714892284319297 48546535825286169213239473)
            ·
              refine ⟨36409901868964626909929605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48546535825286169213239473 36409901868964626909929605)
              ·
                refine ⟨6826856600430867545611801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36409901868964626909929605 6826856600430867545611801)
                ·
                  refine ⟨5120142450323150659208851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826856600430867545611801 5120142450323150659208851)
                  ·
                    refine ⟨7680213675484725988813277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120142450323150659208851 7680213675484725988813277)
                    ·
                      refine ⟨2880080128306772245804979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680213675484725988813277 2880080128306772245804979)
                      ·
                        rfl

theorem cell23_5608936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5608936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608936 prefixEnd_5608936 := by exact prefixLift 5608936
  have htrace : WordTrace (prefixWord ++ tailWord_5608936) baseStart_5608936 baseEnd_5608936 := by
    simpa [prefixWord, tailWord_5608936, baseEnd_5608936] using wordTrace_append hprefix tailTrace_5608936
  have hstable : (prefixWord ++ tailWord_5608936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608936).length < 2 ^ (prefixWord ++ tailWord_5608936).sum := by decide
  have hdescent : baseEnd_5608936 < baseStart_5608936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608989 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5608989 : Nat := 118140960795 + 5608989 * 2 ^ 59
def prefixEnd_5608989 : Nat := 4983230072969 + 3 ^ 40 * 5608989 * 2
def baseEnd_5608989 : Nat := 2880107342781460538442235

theorem tailTrace_5608989 : CollatzResearch.WordTrace tailWord_5608989 prefixEnd_5608989 2880107342781460538442235 := by
  unfold tailWord_5608989
  simp only [CollatzResearch.WordTrace]
  refine ⟨204576635476598266900886021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136384423651065511267257347 204576635476598266900886021)
  ·
    refine ⟨38358119151862175043916129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204576635476598266900886021 38358119151862175043916129)
    ·
      refine ⟨28768589363896631282937097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38358119151862175043916129 28768589363896631282937097)
      ·
        refine ⟨21576442022922473462202823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28768589363896631282937097 21576442022922473462202823)
        ·
          refine ⟨32364663034383710193304235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21576442022922473462202823 32364663034383710193304235)
          ·
            refine ⟨48546994551575565289956353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32364663034383710193304235 48546994551575565289956353)
            ·
              refine ⟨36410245913681673967467265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48546994551575565289956353 36410245913681673967467265)
              ·
                refine ⟨27307684435261255475600449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36410245913681673967467265 27307684435261255475600449)
                ·
                  refine ⟨20480763326445941606700337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27307684435261255475600449 20480763326445941606700337)
                  ·
                    refine ⟨15360572494834456205025253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20480763326445941606700337 15360572494834456205025253)
                    ·
                      refine ⟨2880107342781460538442235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15360572494834456205025253 2880107342781460538442235)
                      ·
                        rfl

theorem cell23_5608989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5608989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608989 prefixEnd_5608989 := by exact prefixLift 5608989
  have htrace : WordTrace (prefixWord ++ tailWord_5608989) baseStart_5608989 baseEnd_5608989 := by
    simpa [prefixWord, tailWord_5608989, baseEnd_5608989] using wordTrace_append hprefix tailTrace_5608989
  have hstable : (prefixWord ++ tailWord_5608989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608989).length < 2 ^ (prefixWord ++ tailWord_5608989).sum := by decide
  have hdescent : baseEnd_5608989 < baseStart_5608989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5608993 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 2, 2, 2]
def baseStart_5608993 : Nat := 118140960795 + 5608993 * 2 ^ 59
def prefixEnd_5608993 : Nat := 4983230072969 + 3 ^ 40 * 5608993 * 2
def baseEnd_5608993 : Nat := 2880109396704078522792217

theorem tailTrace_5608993 : CollatzResearch.WordTrace tailWord_5608993 prefixEnd_5608993 2880109396704078522792217 := by
  unfold tailWord_5608993
  simp only [CollatzResearch.WordTrace]
  refine ⟨204576781368583775584031633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136384520912389183722687755 204576781368583775584031633)
  ·
    refine ⟨153432586026437831688023725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204576781368583775584031633 153432586026437831688023725)
    ·
      refine ⟨57537219759914186883008897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153432586026437831688023725 57537219759914186883008897)
      ·
        refine ⟨43152914819935640162256673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57537219759914186883008897 43152914819935640162256673)
        ·
          refine ⟨32364686114951730121692505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43152914819935640162256673 32364686114951730121692505)
          ·
            refine ⟨24273514586213797591269379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32364686114951730121692505 24273514586213797591269379)
            ·
              refine ⟨36410271879320696386904069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24273514586213797591269379 36410271879320696386904069)
              ·
                refine ⟨6826925977372630572544513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36410271879320696386904069 6826925977372630572544513)
                ·
                  refine ⟨5120194483029472929408385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826925977372630572544513 5120194483029472929408385)
                  ·
                    refine ⟨3840145862272104697056289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5120194483029472929408385 3840145862272104697056289)
                    ·
                      refine ⟨2880109396704078522792217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840145862272104697056289 2880109396704078522792217)
                      ·
                        rfl

theorem cell23_5608993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_5608993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5608993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5608993 prefixEnd_5608993 := by exact prefixLift 5608993
  have htrace : WordTrace (prefixWord ++ tailWord_5608993) baseStart_5608993 baseEnd_5608993 := by
    simpa [prefixWord, tailWord_5608993, baseEnd_5608993] using wordTrace_append hprefix tailTrace_5608993
  have hstable : (prefixWord ++ tailWord_5608993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5608993).length < 2 ^ (prefixWord ++ tailWord_5608993).sum := by decide
  have hdescent : baseEnd_5608993 < baseStart_5608993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5608993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609006 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5609006 : Nat := 118140960795 + 5609006 * 2 ^ 59
def prefixEnd_5609006 : Nat := 4983230072969 + 3 ^ 40 * 5609006 * 2
def baseEnd_5609006 : Nat := 2880116071952586971929657

theorem tailTrace_5609006 : CollatzResearch.WordTrace tailWord_5609006 prefixEnd_5609006 2880116071952586971929657 := by
  unfold tailWord_5609006
  simp only [CollatzResearch.WordTrace]
  refine ⟨25572156939692084850531859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136384837011691119202836581 25572156939692084850531859)
  ·
    refine ⟨38358235409538127275797789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25572156939692084850531859 38358235409538127275797789)
    ·
      refine ⟨14384338278576797728424171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38358235409538127275797789 14384338278576797728424171)
      ·
        refine ⟨21576507417865196592636257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14384338278576797728424171 21576507417865196592636257)
        ·
          refine ⟨16182380563398897444477193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21576507417865196592636257 16182380563398897444477193)
          ·
            refine ⟨12136785422549173083357895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16182380563398897444477193 12136785422549173083357895)
            ·
              refine ⟨18205178133823759625036843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12136785422549173083357895 18205178133823759625036843)
              ·
                refine ⟨27307767200735639437555265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18205178133823759625036843 27307767200735639437555265)
                ·
                  refine ⟨20480825400551729578166449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27307767200735639437555265 20480825400551729578166449)
                  ·
                    refine ⟨15360619050413797183624837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20480825400551729578166449 15360619050413797183624837)
                    ·
                      refine ⟨2880116071952586971929657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15360619050413797183624837 2880116071952586971929657)
                      ·
                        rfl

theorem cell23_5609006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5609006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609006 prefixEnd_5609006 := by exact prefixLift 5609006
  have htrace : WordTrace (prefixWord ++ tailWord_5609006) baseStart_5609006 baseEnd_5609006 := by
    simpa [prefixWord, tailWord_5609006, baseEnd_5609006] using wordTrace_append hprefix tailTrace_5609006
  have hstable : (prefixWord ++ tailWord_5609006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609006).length < 2 ^ (prefixWord ++ tailWord_5609006).sum := by decide
  have hdescent : baseEnd_5609006 < baseStart_5609006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609049 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_5609049 : Nat := 118140960795 + 5609049 * 2 ^ 59
def prefixEnd_5609049 : Nat := 4983230072969 + 3 ^ 40 * 5609049 * 2
def baseEnd_5609049 : Nat := 2880138151620730303691959

theorem tailTrace_5609049 : CollatzResearch.WordTrace tailWord_5609049 prefixEnd_5609049 2880138151620730303691959 := by
  unfold tailWord_5609049
  simp only [CollatzResearch.WordTrace]
  refine ⟨204578823856380897148070201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136385882570920598098713467 204578823856380897148070201)
  ·
    refine ⟨153434117892285672861052651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204578823856380897148070201 153434117892285672861052651)
    ·
      refine ⟨230151176838428509291578977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153434117892285672861052651 230151176838428509291578977)
      ·
        refine ⟨172613382628821381968684233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230151176838428509291578977 172613382628821381968684233)
        ·
          refine ⟨129460036971616036476513175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172613382628821381968684233 129460036971616036476513175)
          ·
            refine ⟨194190055457424054714769763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129460036971616036476513175 194190055457424054714769763)
            ·
              refine ⟨291285083186136082072154645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194190055457424054714769763 291285083186136082072154645)
              ·
                refine ⟨13653988274350128847132249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291285083186136082072154645 13653988274350128847132249)
                ·
                  refine ⟨10240491205762596635349187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13653988274350128847132249 10240491205762596635349187)
                  ·
                    refine ⟨15360736808643894953023781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10240491205762596635349187 15360736808643894953023781)
                    ·
                      refine ⟨2880138151620730303691959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15360736808643894953023781 2880138151620730303691959)
                      ·
                        rfl

theorem cell23_5609049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_5609049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609049 prefixEnd_5609049 := by exact prefixLift 5609049
  have htrace : WordTrace (prefixWord ++ tailWord_5609049) baseStart_5609049 baseEnd_5609049 := by
    simpa [prefixWord, tailWord_5609049, baseEnd_5609049] using wordTrace_append hprefix tailTrace_5609049
  have hstable : (prefixWord ++ tailWord_5609049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609049).length < 2 ^ (prefixWord ++ tailWord_5609049).sum := by decide
  have hdescent : baseEnd_5609049 < baseStart_5609049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609089 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 8]
def baseStart_5609089 : Nat := 118140960795 + 5609089 * 2 ^ 59
def prefixEnd_5609089 : Nat := 4983230072969 + 3 ^ 40 * 5609089 * 2
def baseEnd_5609089 : Nat := 320017632316323349687975

theorem tailTrace_5609089 : CollatzResearch.WordTrace tailWord_5609089 prefixEnd_5609089 320017632316323349687975 := by
  unfold tailWord_5609089
  simp only [CollatzResearch.WordTrace]
  refine ⟨204580282776235983979526321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136386855184157322653017547 204580282776235983979526321)
  ·
    refine ⟨153435212082176987984644741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204580282776235983979526321 153435212082176987984644741)
    ·
      refine ⟨28769102265408185247120889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153435212082176987984644741 28769102265408185247120889)
      ·
        refine ⟨21576826699056138935340667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28769102265408185247120889 21576826699056138935340667)
        ·
          refine ⟨32365240048584208403011001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21576826699056138935340667 32365240048584208403011001)
          ·
            refine ⟨24273930036438156302258251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32365240048584208403011001 24273930036438156302258251)
            ·
              refine ⟨36410895054657234453387377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24273930036438156302258251 36410895054657234453387377)
              ·
                refine ⟨27308171290992925840040533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36410895054657234453387377 27308171290992925840040533)
                ·
                  refine ⟨320017632316323349687975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27308171290992925840040533 320017632316323349687975)
                  ·
                    rfl

theorem cell23_5609089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 8].length) (baseStart_5609089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609089 prefixEnd_5609089 := by exact prefixLift 5609089
  have htrace : WordTrace (prefixWord ++ tailWord_5609089) baseStart_5609089 baseEnd_5609089 := by
    simpa [prefixWord, tailWord_5609089, baseEnd_5609089] using wordTrace_append hprefix tailTrace_5609089
  have hstable : (prefixWord ++ tailWord_5609089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609089).length < 2 ^ (prefixWord ++ tailWord_5609089).sum := by decide
  have hdescent : baseEnd_5609089 < baseStart_5609089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609133 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_5609133 : Nat := 118140960795 + 5609133 * 2 ^ 59
def prefixEnd_5609133 : Nat := 4983230072969 + 3 ^ 40 * 5609133 * 2
def baseEnd_5609133 : Nat := 2880181283995707975041573

theorem tailTrace_5609133 : CollatzResearch.WordTrace tailWord_5609133 prefixEnd_5609133 2880181283995707975041573 := by
  unfold tailWord_5609133
  simp only [CollatzResearch.WordTrace]
  refine ⟨204581887588076579494128053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136387925058717719662752035 204581887588076579494128053)
  ·
    refine ⟨19179551961382179327574505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204581887588076579494128053 19179551961382179327574505)
    ·
      refine ⟨14384663971036634495680879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19179551961382179327574505 14384663971036634495680879)
      ·
        refine ⟨21576995956554951743521319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14384663971036634495680879 21576995956554951743521319)
        ·
          refine ⟨32365493934832427615281979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21576995956554951743521319 32365493934832427615281979)
          ·
            refine ⟨48548240902248641422922969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32365493934832427615281979 48548240902248641422922969)
            ·
              refine ⟨36411180676686481067192227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48548240902248641422922969 36411180676686481067192227)
              ·
                refine ⟨54616771015029721600788341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36411180676686481067192227 54616771015029721600788341)
                ·
                  refine ⟨5120322282659036400073907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54616771015029721600788341 5120322282659036400073907)
                  ·
                    refine ⟨7680483423988554600110861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120322282659036400073907 7680483423988554600110861)
                    ·
                      refine ⟨2880181283995707975041573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680483423988554600110861 2880181283995707975041573)
                      ·
                        rfl

theorem cell23_5609133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_5609133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609133 prefixEnd_5609133 := by exact prefixLift 5609133
  have htrace : WordTrace (prefixWord ++ tailWord_5609133) baseStart_5609133 baseEnd_5609133 := by
    simpa [prefixWord, tailWord_5609133, baseEnd_5609133] using wordTrace_append hprefix tailTrace_5609133
  have hstable : (prefixWord ++ tailWord_5609133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609133).length < 2 ^ (prefixWord ++ tailWord_5609133).sum := by decide
  have hdescent : baseEnd_5609133 < baseStart_5609133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609136 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_5609136 : Nat := 118140960795 + 5609136 * 2 ^ 59
def prefixEnd_5609136 : Nat := 4983230072969 + 3 ^ 40 * 5609136 * 2
def baseEnd_5609136 : Nat := 960060941479223821101353

theorem tailTrace_5609136 : CollatzResearch.WordTrace tailWord_5609136 prefixEnd_5609136 960060941479223821101353 := by
  unfold tailWord_5609136
  simp only [CollatzResearch.WordTrace]
  refine ⟨102290998503532855503243631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136387998004710474004324841 102290998503532855503243631)
  ·
    refine ⟨153436497755299283254865447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102290998503532855503243631 153436497755299283254865447)
    ·
      refine ⟨230154746632948924882298171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153436497755299283254865447 230154746632948924882298171)
      ·
        refine ⟨345232119949423387323447257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230154746632948924882298171 345232119949423387323447257)
        ·
          refine ⟨258924089962067540492585443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345232119949423387323447257 258924089962067540492585443)
          ·
            refine ⟨388386134943101310738878165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258924089962067540492585443 388386134943101310738878165)
            ·
              refine ⟨9102800037728936970442457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 388386134943101310738878165 9102800037728936970442457)
              ·
                refine ⟨6827100028296702727831843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9102800037728936970442457 6827100028296702727831843)
                ·
                  refine ⟨10240650042445054091747765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827100028296702727831843 10240650042445054091747765)
                  ·
                    refine ⟨960060941479223821101353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10240650042445054091747765 960060941479223821101353)
                    ·
                      rfl

theorem cell23_5609136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_5609136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609136 prefixEnd_5609136 := by exact prefixLift 5609136
  have htrace : WordTrace (prefixWord ++ tailWord_5609136) baseStart_5609136 baseEnd_5609136 := by
    simpa [prefixWord, tailWord_5609136, baseEnd_5609136] using wordTrace_append hprefix tailTrace_5609136
  have hstable : (prefixWord ++ tailWord_5609136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609136).length < 2 ^ (prefixWord ++ tailWord_5609136).sum := by decide
  have hdescent : baseEnd_5609136 < baseStart_5609136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609143 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 2, 3, 2]
def baseStart_5609143 : Nat := 118140960795 + 5609143 * 2 ^ 59
def prefixEnd_5609143 : Nat := 4983230072969 + 3 ^ 40 * 5609143 * 2
def baseEnd_5609143 : Nat := 2880186418802252935916527

theorem tailTrace_5609143 : CollatzResearch.WordTrace tailWord_5609143 prefixEnd_5609143 2880186418802252935916527 := by
  unfold tailWord_5609143
  simp only [CollatzResearch.WordTrace]
  refine ⟨204582252318040351201992083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136388168212026900801328055 204582252318040351201992083)
  ·
    refine ⟨306873378477060526802988125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204582252318040351201992083 306873378477060526802988125)
    ·
      refine ⟨115077516928897697551120547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306873378477060526802988125 115077516928897697551120547)
      ·
        refine ⟨172616275393346546326680821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115077516928897697551120547 172616275393346546326680821)
        ·
          refine ⟨16182775818126238718126327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172616275393346546326680821 16182775818126238718126327)
          ·
            refine ⟨24274163727189358077189491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16182775818126238718126327 24274163727189358077189491)
            ·
              refine ⟨36411245590784037115784237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24274163727189358077189491 36411245590784037115784237)
              ·
                refine ⟨13654217096544013918419089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36411245590784037115784237 13654217096544013918419089)
                ·
                  refine ⟨10240662822408010438814317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13654217096544013918419089 10240662822408010438814317)
                  ·
                    refine ⟨3840248558403003914555369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10240662822408010438814317 3840248558403003914555369)
                    ·
                      refine ⟨2880186418802252935916527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840248558403003914555369 2880186418802252935916527)
                      ·
                        rfl

theorem cell23_5609143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_5609143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609143 prefixEnd_5609143 := by exact prefixLift 5609143
  have htrace : WordTrace (prefixWord ++ tailWord_5609143) baseStart_5609143 baseEnd_5609143 := by
    simpa [prefixWord, tailWord_5609143, baseEnd_5609143] using wordTrace_append hprefix tailTrace_5609143
  have hstable : (prefixWord ++ tailWord_5609143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609143).length < 2 ^ (prefixWord ++ tailWord_5609143).sum := by decide
  have hdescent : baseEnd_5609143 < baseStart_5609143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609176 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_5609176 : Nat := 118140960795 + 5609176 * 2 ^ 59
def prefixEnd_5609176 : Nat := 4983230072969 + 3 ^ 40 * 5609176 * 2
def baseEnd_5609176 : Nat := 2880203363663851306803875

theorem tailTrace_5609176 : CollatzResearch.WordTrace tailWord_5609176 prefixEnd_5609176 2880203363663851306803875 := by
  unfold tailWord_5609176
  simp only [CollatzResearch.WordTrace]
  refine ⟨102291727963460398918971691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136388970617947198558628921 102291727963460398918971691)
  ·
    refine ⟨153437591945190598378457537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102291727963460398918971691 153437591945190598378457537)
    ·
      refine ⟨115078193958892948783843153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153437591945190598378457537 115078193958892948783843153)
      ·
        refine ⟨86308645469169711587882365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115078193958892948783843153 86308645469169711587882365)
        ·
          refine ⟨32365742050938641845455887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86308645469169711587882365 32365742050938641845455887)
          ·
            refine ⟨48548613076407962768183831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32365742050938641845455887 48548613076407962768183831)
            ·
              refine ⟨72822919614611944152275747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48548613076407962768183831 72822919614611944152275747)
              ·
                refine ⟨109234379421917916228413621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72822919614611944152275747 109234379421917916228413621)
                ·
                  refine ⟨10240723070804804646413777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109234379421917916228413621 10240723070804804646413777)
                  ·
                    refine ⟨7680542303103603484810333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10240723070804804646413777 7680542303103603484810333)
                    ·
                      refine ⟨2880203363663851306803875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680542303103603484810333 2880203363663851306803875)
                      ·
                        rfl

theorem cell23_5609176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_5609176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609176 prefixEnd_5609176 := by exact prefixLift 5609176
  have htrace : WordTrace (prefixWord ++ tailWord_5609176) baseStart_5609176 baseEnd_5609176 := by
    simpa [prefixWord, tailWord_5609176, baseEnd_5609176] using wordTrace_append hprefix tailTrace_5609176
  have hstable : (prefixWord ++ tailWord_5609176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609176).length < 2 ^ (prefixWord ++ tailWord_5609176).sum := by decide
  have hdescent : baseEnd_5609176 < baseStart_5609176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609204 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_5609204 : Nat := 118140960795 + 5609204 * 2 ^ 59
def prefixEnd_5609204 : Nat := 4983230072969 + 3 ^ 40 * 5609204 * 2
def baseEnd_5609204 : Nat := 960072580374059065751249

theorem tailTrace_5609204 : CollatzResearch.WordTrace tailWord_5609204 prefixEnd_5609204 960072580374059065751249 := by
  unfold tailWord_5609204
  simp only [CollatzResearch.WordTrace]
  refine ⟨102292238585409679309981333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136389651447212905746641777 102292238585409679309981333)
  ·
    refine ⟨4794948683691078717655375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102292238585409679309981333 4794948683691078717655375)
    ·
      refine ⟨7192423025536618076483063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794948683691078717655375 7192423025536618076483063)
      ·
        refine ⟨10788634538304927114724595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192423025536618076483063 10788634538304927114724595)
        ·
          refine ⟨16182951807457390672086893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10788634538304927114724595 16182951807457390672086893)
          ·
            refine ⟨6068606927796521502032585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16182951807457390672086893 6068606927796521502032585)
            ·
              refine ⟨4551455195847391126524439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6068606927796521502032585 4551455195847391126524439)
              ·
                refine ⟨6827182793771086689786659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551455195847391126524439 6827182793771086689786659)
                ·
                  refine ⟨10240774190656630034679989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827182793771086689786659 10240774190656630034679989)
                  ·
                    refine ⟨960072580374059065751249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10240774190656630034679989 960072580374059065751249)
                    ·
                      rfl

theorem cell23_5609204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_5609204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609204 prefixEnd_5609204 := by exact prefixLift 5609204
  have htrace : WordTrace (prefixWord ++ tailWord_5609204) baseStart_5609204 baseEnd_5609204 := by
    simpa [prefixWord, tailWord_5609204, baseEnd_5609204] using wordTrace_append hprefix tailTrace_5609204
  have hstable : (prefixWord ++ tailWord_5609204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609204).length < 2 ^ (prefixWord ++ tailWord_5609204).sum := by decide
  have hdescent : baseEnd_5609204 < baseStart_5609204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609259 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6]
def baseStart_5609259 : Nat := 118140960795 + 5609259 * 2 ^ 59
def prefixEnd_5609259 : Nat := 4983230072969 + 3 ^ 40 * 5609259 * 2
def baseEnd_5609259 : Nat := 2880245982558174482065993

theorem tailTrace_5609259 : CollatzResearch.WordTrace tailWord_5609259 prefixEnd_5609259 2880245982558174482065993 := by
  unfold tailWord_5609259
  simp only [CollatzResearch.WordTrace]
  refine ⟨204586483185620103013214831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136390988790413402008809887 204586483185620103013214831)
  ·
    refine ⟨306879724778430154519822247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204586483185620103013214831 306879724778430154519822247)
    ·
      refine ⟨460319587167645231779733371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306879724778430154519822247 460319587167645231779733371)
      ·
        refine ⟨690479380751467847669600057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460319587167645231779733371 690479380751467847669600057)
        ·
          refine ⟨517859535563600885752200043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690479380751467847669600057 517859535563600885752200043)
          ·
            refine ⟨776789303345401328628300065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517859535563600885752200043 776789303345401328628300065)
            ·
              refine ⟨582591977509050996471225049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776789303345401328628300065 582591977509050996471225049)
              ·
                refine ⟨436943983131788247353418787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582591977509050996471225049 436943983131788247353418787)
                ·
                  refine ⟨655415974697682371030128181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436943983131788247353418787 655415974697682371030128181)
                  ·
                    refine ⟨61445247627907722284074517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 655415974697682371030128181 61445247627907722284074517)
                    ·
                      refine ⟨2880245982558174482065993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61445247627907722284074517 2880245982558174482065993)
                      ·
                        rfl

theorem cell23_5609259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 6].length) (baseStart_5609259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609259 prefixEnd_5609259 := by exact prefixLift 5609259
  have htrace : WordTrace (prefixWord ++ tailWord_5609259) baseStart_5609259 baseEnd_5609259 := by
    simpa [prefixWord, tailWord_5609259, baseEnd_5609259] using wordTrace_append hprefix tailTrace_5609259
  have hstable : (prefixWord ++ tailWord_5609259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609259).length < 2 ^ (prefixWord ++ tailWord_5609259).sum := by decide
  have hdescent : baseEnd_5609259 < baseStart_5609259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609266 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_5609266 : Nat := 118140960795 + 5609266 * 2 ^ 59
def prefixEnd_5609266 : Nat := 4983230072969 + 3 ^ 40 * 5609266 * 2
def baseEnd_5609266 : Nat := 2880249576922755954678461

theorem tailTrace_5609266 : CollatzResearch.WordTrace tailWord_5609266 prefixEnd_5609266 2880249576922755954678461 := by
  unfold tailWord_5609266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51146684624148685802179913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136391158997729828805813101 51146684624148685802179913)
  ·
    refine ⟨38360013468111514351634935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51146684624148685802179913 38360013468111514351634935)
    ·
      refine ⟨57540020202167271527452403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38360013468111514351634935 57540020202167271527452403)
      ·
        refine ⟨86310030303250907291178605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57540020202167271527452403 86310030303250907291178605)
        ·
          refine ⟨32366261363719090234191977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86310030303250907291178605 32366261363719090234191977)
          ·
            refine ⟨24274696022789317675643983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32366261363719090234191977 24274696022789317675643983)
            ·
              refine ⟨36412044034183976513465975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24274696022789317675643983 36412044034183976513465975)
              ·
                refine ⟨54618066051275964770198963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36412044034183976513465975 54618066051275964770198963)
                ·
                  refine ⟨81927099076913947155298445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54618066051275964770198963 81927099076913947155298445)
                  ·
                    refine ⟨30722662153842730183236917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81927099076913947155298445 30722662153842730183236917)
                    ·
                      refine ⟨2880249576922755954678461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30722662153842730183236917 2880249576922755954678461)
                      ·
                        rfl

theorem cell23_5609266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_5609266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609266 prefixEnd_5609266 := by exact prefixLift 5609266
  have htrace : WordTrace (prefixWord ++ tailWord_5609266) baseStart_5609266 baseEnd_5609266 := by
    simpa [prefixWord, tailWord_5609266, baseEnd_5609266] using wordTrace_append hprefix tailTrace_5609266
  have hstable : (prefixWord ++ tailWord_5609266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609266).length < 2 ^ (prefixWord ++ tailWord_5609266).sum := by decide
  have hdescent : baseEnd_5609266 < baseStart_5609266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609276 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_5609276 : Nat := 118140960795 + 5609276 * 2 ^ 59
def prefixEnd_5609276 : Nat := 4983230072969 + 3 ^ 40 * 5609276 * 2
def baseEnd_5609276 : Nat := 2880254711729300915553415

theorem tailTrace_5609276 : CollatzResearch.WordTrace tailWord_5609276 prefixEnd_5609276 2880254711729300915553415 := by
  unfold tailWord_5609276
  simp only [CollatzResearch.WordTrace]
  refine ⟨102293551613279257458291841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136391402151039009944389121 102293551613279257458291841)
  ·
    refine ⟨76720163709959443093718881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102293551613279257458291841 76720163709959443093718881)
    ·
      refine ⟨57540122782469582320289161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76720163709959443093718881 57540122782469582320289161)
      ·
        refine ⟨43155092086852186740216871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57540122782469582320289161 43155092086852186740216871)
        ·
          refine ⟨64732638130278280110325307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43155092086852186740216871 64732638130278280110325307)
          ·
            refine ⟨97098957195417420165487961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64732638130278280110325307 97098957195417420165487961)
            ·
              refine ⟨72824217896563065124115971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97098957195417420165487961 72824217896563065124115971)
              ·
                refine ⟨109236326844844597686173957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72824217896563065124115971 109236326844844597686173957)
                ·
                  refine ⟨20481811283408362066157617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109236326844844597686173957 20481811283408362066157617)
                  ·
                    refine ⟨15361358462556271549618213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20481811283408362066157617 15361358462556271549618213)
                    ·
                      refine ⟨2880254711729300915553415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15361358462556271549618213 2880254711729300915553415)
                      ·
                        rfl

theorem cell23_5609276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_5609276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609276 prefixEnd_5609276 := by exact prefixLift 5609276
  have htrace : WordTrace (prefixWord ++ tailWord_5609276) baseStart_5609276 baseEnd_5609276 := by
    simpa [prefixWord, tailWord_5609276, baseEnd_5609276] using wordTrace_append hprefix tailTrace_5609276
  have hstable : (prefixWord ++ tailWord_5609276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609276).length < 2 ^ (prefixWord ++ tailWord_5609276).sum := by decide
  have hdescent : baseEnd_5609276 < baseStart_5609276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609296 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_5609296 : Nat := 118140960795 + 5609296 * 2 ^ 59
def prefixEnd_5609296 : Nat := 4983230072969 + 3 ^ 40 * 5609296 * 2
def baseEnd_5609296 : Nat := 2880264981342390837303323

theorem tailTrace_5609296 : CollatzResearch.WordTrace tailWord_5609296 prefixEnd_5609296 2880264981342390837303323 := by
  unfold tailWord_5609296
  simp only [CollatzResearch.WordTrace]
  refine ⟨102293916343243029166155871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136391888457657372221541161 102293916343243029166155871)
  ·
    refine ⟨153440874514864543749233807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102293916343243029166155871 153440874514864543749233807)
    ·
      refine ⟨230161311772296815623850711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153440874514864543749233807 230161311772296815623850711)
      ·
        refine ⟨345241967658445223435776067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230161311772296815623850711 345241967658445223435776067)
        ·
          refine ⟨517862951487667835153664101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345241967658445223435776067 517862951487667835153664101)
          ·
            refine ⟨97099303403937719091312019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 517862951487667835153664101 97099303403937719091312019)
            ·
              refine ⟨145648955105906578636968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97099303403937719091312019 145648955105906578636968029)
              ·
                refine ⟨54618358164714966988863011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145648955105906578636968029 54618358164714966988863011)
                ·
                  refine ⟨81927537247072450483294517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54618358164714966988863011 81927537247072450483294517)
                  ·
                    refine ⟨7680706616913042232808861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81927537247072450483294517 7680706616913042232808861)
                    ·
                      refine ⟨2880264981342390837303323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680706616913042232808861 2880264981342390837303323)
                      ·
                        rfl

theorem cell23_5609296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_5609296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609296 prefixEnd_5609296 := by exact prefixLift 5609296
  have htrace : WordTrace (prefixWord ++ tailWord_5609296) baseStart_5609296 baseEnd_5609296 := by
    simpa [prefixWord, tailWord_5609296, baseEnd_5609296] using wordTrace_append hprefix tailTrace_5609296
  have hstable : (prefixWord ++ tailWord_5609296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609296).length < 2 ^ (prefixWord ++ tailWord_5609296).sum := by decide
  have hdescent : baseEnd_5609296 < baseStart_5609296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609297 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 2, 2, 2]
def baseStart_5609297 : Nat := 118140960795 + 5609297 * 2 ^ 59
def prefixEnd_5609297 : Nat := 4983230072969 + 3 ^ 40 * 5609297 * 2
def baseEnd_5609297 : Nat := 2880265494823045333390819

theorem tailTrace_5609297 : CollatzResearch.WordTrace tailWord_5609297 prefixEnd_5609297 2880265494823045333390819 := by
  unfold tailWord_5609297
  simp only [CollatzResearch.WordTrace]
  refine ⟨204587869159482435503098145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136391912772988290335398763 204587869159482435503098145)
  ·
    refine ⟨153440901869611826627323609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204587869159482435503098145 153440901869611826627323609)
    ·
      refine ⟨115080676402208869970492707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153440901869611826627323609 115080676402208869970492707)
      ·
        refine ⟨172621014603313304955739061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115080676402208869970492707 172621014603313304955739061)
        ·
          refine ⟨16183220119060622339600537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172621014603313304955739061 16183220119060622339600537)
          ·
            refine ⟨12137415089295466754700403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16183220119060622339600537 12137415089295466754700403)
            ·
              refine ⟨18206122633943200132050605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137415089295466754700403 18206122633943200132050605)
              ·
                refine ⟨6827295987728700049518977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18206122633943200132050605 6827295987728700049518977)
                ·
                  refine ⟨5120471990796525037139233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827295987728700049518977 5120471990796525037139233)
                  ·
                    refine ⟨3840353993097393777854425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5120471990796525037139233 3840353993097393777854425)
                    ·
                      refine ⟨2880265494823045333390819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840353993097393777854425 2880265494823045333390819)
                      ·
                        rfl

theorem cell23_5609297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_5609297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609297 prefixEnd_5609297 := by exact prefixLift 5609297
  have htrace : WordTrace (prefixWord ++ tailWord_5609297) baseStart_5609297 baseEnd_5609297 := by
    simpa [prefixWord, tailWord_5609297, baseEnd_5609297] using wordTrace_append hprefix tailTrace_5609297
  have hstable : (prefixWord ++ tailWord_5609297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609297).length < 2 ^ (prefixWord ++ tailWord_5609297).sum := by decide
  have hdescent : baseEnd_5609297 < baseStart_5609297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609333 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 2, 5]
def baseStart_5609333 : Nat := 118140960795 + 5609333 * 2 ^ 59
def prefixEnd_5609333 : Nat := 4983230072969 + 3 ^ 40 * 5609333 * 2
def baseEnd_5609333 : Nat := 960094660042202397513551

theorem tailTrace_5609333 : CollatzResearch.WordTrace tailWord_5609333 prefixEnd_5609333 960094660042202397513551 := by
  unfold tailWord_5609333
  simp only [CollatzResearch.WordTrace]
  refine ⟨204589182187352013651408653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136392788124901342434272435 204589182187352013651408653)
  ·
    refine ⟨76720943320257005119278245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204589182187352013651408653 76720943320257005119278245)
    ·
      refine ⟨14385176872548188459864671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76720943320257005119278245 14385176872548188459864671)
      ·
        refine ⟨21577765308822282689797007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385176872548188459864671 21577765308822282689797007)
        ·
          refine ⟨32366647963233424034695511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21577765308822282689797007 32366647963233424034695511)
          ·
            refine ⟨48549971944850136052043267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32366647963233424034695511 48549971944850136052043267)
            ·
              refine ⟨72824957917275204078064901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48549971944850136052043267 72824957917275204078064901)
              ·
                refine ⟨13654679609489100764637169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72824957917275204078064901 13654679609489100764637169)
                ·
                  refine ⟨10241009707116825573477877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13654679609489100764637169 10241009707116825573477877)
                  ·
                    refine ⟨960094660042202397513551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10241009707116825573477877 960094660042202397513551)
                    ·
                      rfl

theorem cell23_5609333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_5609333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609333 prefixEnd_5609333 := by exact prefixLift 5609333
  have htrace : WordTrace (prefixWord ++ tailWord_5609333) baseStart_5609333 baseEnd_5609333 := by
    simpa [prefixWord, tailWord_5609333, baseEnd_5609333] using wordTrace_append hprefix tailTrace_5609333
  have hstable : (prefixWord ++ tailWord_5609333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609333).length < 2 ^ (prefixWord ++ tailWord_5609333).sum := by decide
  have hdescent : baseEnd_5609333 < baseStart_5609333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609370 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5609370 : Nat := 118140960795 + 5609370 * 2 ^ 59
def prefixEnd_5609370 : Nat := 4983230072969 + 3 ^ 40 * 5609370 * 2
def baseEnd_5609370 : Nat := 2880302978910823547777983

theorem tailTrace_5609370 : CollatzResearch.WordTrace tailWord_5609370 prefixEnd_5609370 2880302978910823547777983 := by
  unfold tailWord_5609370
  simp only [CollatzResearch.WordTrace]
  refine ⟨51147632922054492242626391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136393687792145312647003709 51147632922054492242626391)
  ·
    refine ⟨76721449383081738363939587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51147632922054492242626391 76721449383081738363939587)
    ·
      refine ⟨115082174074622607545909381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76721449383081738363939587 115082174074622607545909381)
      ·
        refine ⟨21577907638991738914858009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115082174074622607545909381 21577907638991738914858009)
        ·
          refine ⟨16183430729243804186143507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21577907638991738914858009 16183430729243804186143507)
          ·
            refine ⟨24275146093865706279215261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16183430729243804186143507 24275146093865706279215261)
            ·
              refine ⟨9103179785199639854705723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24275146093865706279215261 9103179785199639854705723)
              ·
                refine ⟨13654769677799459782058585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103179785199639854705723 13654769677799459782058585)
                ·
                  refine ⟨10241077258349594836543939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13654769677799459782058585 10241077258349594836543939)
                  ·
                    refine ⟨15361615887524392254815909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241077258349594836543939 15361615887524392254815909)
                    ·
                      refine ⟨2880302978910823547777983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15361615887524392254815909 2880302978910823547777983)
                      ·
                        rfl

theorem cell23_5609370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5609370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609370 prefixEnd_5609370 := by exact prefixLift 5609370
  have htrace : WordTrace (prefixWord ++ tailWord_5609370) baseStart_5609370 baseEnd_5609370 := by
    simpa [prefixWord, tailWord_5609370, baseEnd_5609370] using wordTrace_append hprefix tailTrace_5609370
  have hstable : (prefixWord ++ tailWord_5609370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609370).length < 2 ^ (prefixWord ++ tailWord_5609370).sum := by decide
  have hdescent : baseEnd_5609370 < baseStart_5609370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609376 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 8]
def baseStart_5609376 : Nat := 118140960795 + 5609376 * 2 ^ 59
def prefixEnd_5609376 : Nat := 4983230072969 + 3 ^ 40 * 5609376 * 2
def baseEnd_5609376 : Nat := 320034006643861169366995

theorem tailTrace_5609376 : CollatzResearch.WordTrace tailWord_5609376 prefixEnd_5609376 320034006643861169366995 := by
  unfold tailWord_5609376
  simp only [CollatzResearch.WordTrace]
  refine ⟨102295375263098115997611991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136393833684130821330149321 102295375263098115997611991)
  ·
    refine ⟨153443062894647173996417987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102295375263098115997611991 153443062894647173996417987)
    ·
      refine ⟨230164594341970760994626981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153443062894647173996417987 230164594341970760994626981)
      ·
        refine ⟨43155861439119517686492559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230164594341970760994626981 43155861439119517686492559)
        ·
          refine ⟨64733792158679276529738839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43155861439119517686492559 64733792158679276529738839)
          ·
            refine ⟨97100688238018914794608259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64733792158679276529738839 97100688238018914794608259)
            ·
              refine ⟨145651032357028372191912389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97100688238018914794608259 145651032357028372191912389)
              ·
                refine ⟨27309568566942819785983573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145651032357028372191912389 27309568566942819785983573)
                ·
                  refine ⟨320034006643861169366995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27309568566942819785983573 320034006643861169366995)
                  ·
                    rfl

theorem cell23_5609376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_5609376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609376 prefixEnd_5609376 := by exact prefixLift 5609376
  have htrace : WordTrace (prefixWord ++ tailWord_5609376) baseStart_5609376 baseEnd_5609376 := by
    simpa [prefixWord, tailWord_5609376, baseEnd_5609376] using wordTrace_append hprefix tailTrace_5609376
  have hstable : (prefixWord ++ tailWord_5609376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609376).length < 2 ^ (prefixWord ++ tailWord_5609376).sum := by decide
  have hdescent : baseEnd_5609376 < baseStart_5609376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609383 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6]
def baseStart_5609383 : Nat := 118140960795 + 5609383 * 2 ^ 59
def prefixEnd_5609383 : Nat := 4983230072969 + 3 ^ 40 * 5609383 * 2
def baseEnd_5609383 : Nat := 2880309654159331996915423

theorem tailTrace_5609383 : CollatzResearch.WordTrace tailWord_5609383 prefixEnd_5609383 2880309654159331996915423 := by
  unfold tailWord_5609383
  simp only [CollatzResearch.WordTrace]
  refine ⟨204591005837170872190728803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136394003891447248127152535 204591005837170872190728803)
  ·
    refine ⟨306886508755756308286093205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204591005837170872190728803 306886508755756308286093205)
    ·
      refine ⟨14385305097926076950910619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 306886508755756308286093205 14385305097926076950910619)
      ·
        refine ⟨21577957646889115426365929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385305097926076950910619 21577957646889115426365929)
        ·
          refine ⟨16183468235166836569774447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21577957646889115426365929 16183468235166836569774447)
          ·
            refine ⟨24275202352750254854661671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16183468235166836569774447 24275202352750254854661671)
            ·
              refine ⟨36412803529125382281992507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24275202352750254854661671 36412803529125382281992507)
              ·
                refine ⟨54619205293688073422988761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36412803529125382281992507 54619205293688073422988761)
                ·
                  refine ⟨40964403970266055067241571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54619205293688073422988761 40964403970266055067241571)
                  ·
                    refine ⟨61446605955399082600862357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40964403970266055067241571 61446605955399082600862357)
                    ·
                      refine ⟨2880309654159331996915423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61446605955399082600862357 2880309654159331996915423)
                      ·
                        rfl

theorem cell23_5609383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_5609383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609383 prefixEnd_5609383 := by exact prefixLift 5609383
  have htrace : WordTrace (prefixWord ++ tailWord_5609383) baseStart_5609383 baseEnd_5609383 := by
    simpa [prefixWord, tailWord_5609383, baseEnd_5609383] using wordTrace_append hprefix tailTrace_5609383
  have hstable : (prefixWord ++ tailWord_5609383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609383).length < 2 ^ (prefixWord ++ tailWord_5609383).sum := by decide
  have hdescent : baseEnd_5609383 < baseStart_5609383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609393 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 8]
def baseStart_5609393 : Nat := 118140960795 + 5609393 * 2 ^ 59
def prefixEnd_5609393 : Nat := 4983230072969 + 3 ^ 40 * 5609393 * 2
def baseEnd_5609393 : Nat := 320034976551764106421153

theorem tailTrace_5609393 : CollatzResearch.WordTrace tailWord_5609393 prefixEnd_5609393 320034976551764106421153 := by
  unfold tailWord_5609393
  simp only [CollatzResearch.WordTrace]
  refine ⟨204591370567134643898592833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136394247044756429265728555 204591370567134643898592833)
  ·
    refine ⟨153443527925350982923944625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204591370567134643898592833 153443527925350982923944625)
    ·
      refine ⟨115082645944013237192958469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153443527925350982923944625 115082645944013237192958469)
      ·
        refine ⟨21577996114502481973679713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115082645944013237192958469 21577996114502481973679713)
        ·
          refine ⟨16183497085876861480259785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21577996114502481973679713 16183497085876861480259785)
          ·
            refine ⟨12137622814407646110194839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16183497085876861480259785 12137622814407646110194839)
            ·
              refine ⟨18206434221611469165292259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12137622814407646110194839 18206434221611469165292259)
              ·
                refine ⟨27309651332417203747938389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18206434221611469165292259 27309651332417203747938389)
                ·
                  refine ⟨320034976551764106421153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27309651332417203747938389 320034976551764106421153)
                  ·
                    rfl

theorem cell23_5609393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 8].length) (baseStart_5609393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609393 prefixEnd_5609393 := by exact prefixLift 5609393
  have htrace : WordTrace (prefixWord ++ tailWord_5609393) baseStart_5609393 baseEnd_5609393 := by
    simpa [prefixWord, tailWord_5609393, baseEnd_5609393] using wordTrace_append hprefix tailTrace_5609393
  have hstable : (prefixWord ++ tailWord_5609393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609393).length < 2 ^ (prefixWord ++ tailWord_5609393).sum := by decide
  have hdescent : baseEnd_5609393 < baseStart_5609393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609397 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_5609397 : Nat := 118140960795 + 5609397 * 2 ^ 59
def prefixEnd_5609397 : Nat := 4983230072969 + 3 ^ 40 * 5609397 * 2
def baseEnd_5609397 : Nat := 960105614296164980713453

theorem tailTrace_5609397 : CollatzResearch.WordTrace tailWord_5609397 prefixEnd_5609397 960105614296164980713453 := by
  unfold tailWord_5609397
  simp only [CollatzResearch.WordTrace]
  refine ⟨204591516459120152581738445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136394344306080101721158963 204591516459120152581738445)
  ·
    refine ⟨76721818672170057218151917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204591516459120152581738445 76721818672170057218151917)
    ·
      refine ⟨28770682002063771456806969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76721818672170057218151917 28770682002063771456806969)
      ·
        refine ⟨21578011501547828592605227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28770682002063771456806969 21578011501547828592605227)
        ·
          refine ⟨32367017252321742888907841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21578011501547828592605227 32367017252321742888907841)
          ·
            refine ⟨24275262939241307166680881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32367017252321742888907841 24275262939241307166680881)
            ·
              refine ⟨18206447204430980375010661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24275262939241307166680881 18206447204430980375010661)
              ·
                refine ⟨3413708850830808820314499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18206447204430980375010661 3413708850830808820314499)
                ·
                  refine ⟨5120563276246213230471749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413708850830808820314499 5120563276246213230471749)
                  ·
                    refine ⟨960105614296164980713453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5120563276246213230471749 960105614296164980713453)
                    ·
                      rfl

theorem cell23_5609397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_5609397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609397 prefixEnd_5609397 := by exact prefixLift 5609397
  have htrace : WordTrace (prefixWord ++ tailWord_5609397) baseStart_5609397 baseEnd_5609397 := by
    simpa [prefixWord, tailWord_5609397, baseEnd_5609397] using wordTrace_append hprefix tailTrace_5609397
  have hstable : (prefixWord ++ tailWord_5609397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609397).length < 2 ^ (prefixWord ++ tailWord_5609397).sum := by decide
  have hdescent : baseEnd_5609397 < baseStart_5609397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609454 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_5609454 : Nat := 118140960795 + 5609454 * 2 ^ 59
def prefixEnd_5609454 : Nat := 4983230072969 + 3 ^ 40 * 5609454 * 2
def baseEnd_5609454 : Nat := 2880346111285801219127597

theorem tailTrace_5609454 : CollatzResearch.WordTrace tailWord_5609454 prefixEnd_5609454 2880346111285801219127597 := by
  unfold tailWord_5609454
  simp only [CollatzResearch.WordTrace]
  refine ⟨25574199427489206414570427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136395730279942434211042277 25574199427489206414570427)
  ·
    refine ⟨38361299141233809621855641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25574199427489206414570427 38361299141233809621855641)
    ·
      refine ⟨28770974355925357216391731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38361299141233809621855641 28770974355925357216391731)
      ·
        refine ⟨43156461533888035824587597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28770974355925357216391731 43156461533888035824587597)
        ·
          refine ⟨16183673075208013434220349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43156461533888035824587597 16183673075208013434220349)
          ·
            refine ⟨6068877403203005037832631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16183673075208013434220349 6068877403203005037832631)
            ·
              refine ⟨9103316104804507556748947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068877403203005037832631 9103316104804507556748947)
              ·
                refine ⟨13654974157206761335123421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103316104804507556748947 13654974157206761335123421)
                ·
                  refine ⟨5120615308952535500671283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13654974157206761335123421 5120615308952535500671283)
                  ·
                    refine ⟨7680922963428803251006925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120615308952535500671283 7680922963428803251006925)
                    ·
                      refine ⟨2880346111285801219127597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680922963428803251006925 2880346111285801219127597)
                      ·
                        rfl

theorem cell23_5609454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_5609454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609454 prefixEnd_5609454 := by exact prefixLift 5609454
  have htrace : WordTrace (prefixWord ++ tailWord_5609454) baseStart_5609454 baseEnd_5609454 := by
    simpa [prefixWord, tailWord_5609454, baseEnd_5609454] using wordTrace_append hprefix tailTrace_5609454
  have hstable : (prefixWord ++ tailWord_5609454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609454).length < 2 ^ (prefixWord ++ tailWord_5609454).sum := by decide
  have hdescent : baseEnd_5609454 < baseStart_5609454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609473 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_5609473 : Nat := 118140960795 + 5609473 * 2 ^ 59
def prefixEnd_5609473 : Nat := 4983230072969 + 3 ^ 40 * 5609473 * 2
def baseEnd_5609473 : Nat := 2880355867418236644790009

theorem tailTrace_5609473 : CollatzResearch.WordTrace tailWord_5609473 prefixEnd_5609473 2880355867418236644790009 := by
  unfold tailWord_5609473
  simp only [CollatzResearch.WordTrace]
  refine ⟨204594288406844817561505073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136396192271229878374336715 204594288406844817561505073)
  ·
    refine ⟨153445716305133613171128805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204594288406844817561505073 153445716305133613171128805)
    ·
      refine ⟨28771071807212552469586651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153445716305133613171128805 28771071807212552469586651)
      ·
        refine ⟨43156607710818828704379977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28771071807212552469586651 43156607710818828704379977)
        ·
          refine ⟨32367455783114121528284983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43156607710818828704379977 32367455783114121528284983)
          ·
            refine ⟨48551183674671182292427475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32367455783114121528284983 48551183674671182292427475)
            ·
              refine ⟨72826775512006773438641213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48551183674671182292427475 72826775512006773438641213)
              ·
                refine ⟨27310040817002540039490455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72826775512006773438641213 27310040817002540039490455)
                ·
                  refine ⟨40965061225503810059235683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27310040817002540039490455 40965061225503810059235683)
                  ·
                    refine ⟨61447591838255715088853525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40965061225503810059235683 61447591838255715088853525)
                    ·
                      refine ⟨2880355867418236644790009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61447591838255715088853525 2880355867418236644790009)
                      ·
                        rfl

theorem cell23_5609473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_5609473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609473 prefixEnd_5609473 := by exact prefixLift 5609473
  have htrace : WordTrace (prefixWord ++ tailWord_5609473) baseStart_5609473 baseEnd_5609473 := by
    simpa [prefixWord, tailWord_5609473, baseEnd_5609473] using wordTrace_append hprefix tailTrace_5609473
  have hstable : (prefixWord ++ tailWord_5609473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609473).length < 2 ^ (prefixWord ++ tailWord_5609473).sum := by decide
  have hdescent : baseEnd_5609473 < baseStart_5609473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609477 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_5609477 : Nat := 118140960795 + 5609477 * 2 ^ 59
def prefixEnd_5609477 : Nat := 4983230072969 + 3 ^ 40 * 5609477 * 2
def baseEnd_5609477 : Nat := 2880357921340854629139991

theorem tailTrace_5609477 : CollatzResearch.WordTrace tailWord_5609477 prefixEnd_5609477 2880357921340854629139991 := by
  unfold tailWord_5609477
  simp only [CollatzResearch.WordTrace]
  refine ⟨204594434298830326244650685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136396289532553550829767123 204594434298830326244650685)
  ·
    refine ⟨76722912862061372341744007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204594434298830326244650685 76722912862061372341744007)
    ·
      refine ⟨115084369293092058512616011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76722912862061372341744007 115084369293092058512616011)
      ·
        refine ⟨172626553939638087768924017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115084369293092058512616011 172626553939638087768924017)
        ·
          refine ⟨129469915454728565826693013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172626553939638087768924017 129469915454728565826693013)
          ·
            refine ⟨6068902286940401523126235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129469915454728565826693013 6068902286940401523126235)
            ·
              refine ⟨9103353430410602284689353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6068902286940401523126235 9103353430410602284689353)
              ·
                refine ⟨6827515072807951713517015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9103353430410602284689353 6827515072807951713517015)
                ·
                  refine ⟨10241272609211927570275523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827515072807951713517015 10241272609211927570275523)
                  ·
                    refine ⟨15361908913817891355413285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241272609211927570275523 15361908913817891355413285)
                    ·
                      refine ⟨2880357921340854629139991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15361908913817891355413285 2880357921340854629139991)
                      ·
                        rfl

theorem cell23_5609477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_5609477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609477 prefixEnd_5609477 := by exact prefixLift 5609477
  have htrace : WordTrace (prefixWord ++ tailWord_5609477) baseStart_5609477 baseEnd_5609477 := by
    simpa [prefixWord, tailWord_5609477, baseEnd_5609477] using wordTrace_append hprefix tailTrace_5609477
  have hstable : (prefixWord ++ tailWord_5609477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609477).length < 2 ^ (prefixWord ++ tailWord_5609477).sum := by decide
  have hdescent : baseEnd_5609477 < baseStart_5609477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609480 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_5609480 : Nat := 118140960795 + 5609480 * 2 ^ 59
def prefixEnd_5609480 : Nat := 4983230072969 + 3 ^ 40 * 5609480 * 2
def baseEnd_5609480 : Nat := 2880359461782818117402477

theorem tailTrace_5609480 : CollatzResearch.WordTrace tailWord_5609480 prefixEnd_5609480 2880359461782818117402477 := by
  unfold tailWord_5609480
  simp only [CollatzResearch.WordTrace]
  refine ⟨102297271858909728878504947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136396362478546305171339929 102297271858909728878504947)
  ·
    refine ⟨153445907788364593317757421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102297271858909728878504947 153445907788364593317757421)
    ·
      refine ⟨57542215420636722494159033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153445907788364593317757421 57542215420636722494159033)
      ·
        refine ⟨43156661565477541870619275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57542215420636722494159033 43156661565477541870619275)
        ·
          refine ⟨64734992348216312805928913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43156661565477541870619275 64734992348216312805928913)
          ·
            refine ⟨48551244261162234604446685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64734992348216312805928913 48551244261162234604446685)
            ·
              refine ⟨18206716597935837976667507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48551244261162234604446685 18206716597935837976667507)
              ·
                refine ⟨27310074896903756965001261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18206716597935837976667507 27310074896903756965001261)
                ·
                  refine ⟨10241278086338908861875473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27310074896903756965001261 10241278086338908861875473)
                  ·
                    refine ⟨7680958564754181646406605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10241278086338908861875473 7680958564754181646406605)
                    ·
                      refine ⟨2880359461782818117402477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7680958564754181646406605 2880359461782818117402477)
                      ·
                        rfl

theorem cell23_5609480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_5609480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609480 prefixEnd_5609480 := by exact prefixLift 5609480
  have htrace : WordTrace (prefixWord ++ tailWord_5609480) baseStart_5609480 baseEnd_5609480 := by
    simpa [prefixWord, tailWord_5609480, baseEnd_5609480] using wordTrace_append hprefix tailTrace_5609480
  have hstable : (prefixWord ++ tailWord_5609480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609480).length < 2 ^ (prefixWord ++ tailWord_5609480).sum := by decide
  have hdescent : baseEnd_5609480 < baseStart_5609480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609524 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5609524 : Nat := 118140960795 + 5609524 * 2 ^ 59
def prefixEnd_5609524 : Nat := 4983230072969 + 3 ^ 40 * 5609524 * 2
def baseEnd_5609524 : Nat := 2880382054931615945252275

theorem tailTrace_5609524 : CollatzResearch.WordTrace tailWord_5609524 prefixEnd_5609524 2880382054931615945252275 := by
  unfold tailWord_5609524
  simp only [CollatzResearch.WordTrace]
  refine ⟨102298074264830026635805813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136397432353106702181074417 102298074264830026635805813)
  ·
    refine ⟨9590444462327814997106795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102298074264830026635805813 9590444462327814997106795)
    ·
      refine ⟨14385666693491722495660193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9590444462327814997106795 14385666693491722495660193)
      ·
        refine ⟨10789250020118791871745145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14385666693491722495660193 10789250020118791871745145)
        ·
          refine ⟨8091937515089093903808859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789250020118791871745145 8091937515089093903808859)
          ·
            refine ⟨12137906272633640855713289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8091937515089093903808859 12137906272633640855713289)
            ·
              refine ⟨9103429704475230641784967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12137906272633640855713289 9103429704475230641784967)
              ·
                refine ⟨13655144556712845962677451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103429704475230641784967 13655144556712845962677451)
                ·
                  refine ⟨20482716835069268944016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13655144556712845962677451 20482716835069268944016177)
                  ·
                    refine ⟨15362037626301951708012133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20482716835069268944016177 15362037626301951708012133)
                    ·
                      refine ⟨2880382054931615945252275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15362037626301951708012133 2880382054931615945252275)
                      ·
                        rfl

theorem cell23_5609524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5609524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609524 prefixEnd_5609524 := by exact prefixLift 5609524
  have htrace : WordTrace (prefixWord ++ tailWord_5609524) baseStart_5609524 baseEnd_5609524 := by
    simpa [prefixWord, tailWord_5609524, baseEnd_5609524] using wordTrace_append hprefix tailTrace_5609524
  have hstable : (prefixWord ++ tailWord_5609524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609524).length < 2 ^ (prefixWord ++ tailWord_5609524).sum := by decide
  have hdescent : baseEnd_5609524 < baseStart_5609524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609527 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 3]
def baseStart_5609527 : Nat := 118140960795 + 5609527 * 2 ^ 59
def prefixEnd_5609527 : Nat := 4983230072969 + 3 ^ 40 * 5609527 * 2
def baseEnd_5609527 : Nat := 2880383595373579433514761

theorem tailTrace_5609527 : CollatzResearch.WordTrace tailWord_5609527 prefixEnd_5609527 2880383595373579433514761 := by
  unfold tailWord_5609527
  simp only [CollatzResearch.WordTrace]
  refine ⟨204596257948649184783970835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136397505299099456522647223 204596257948649184783970835)
  ·
    refine ⟨306894386922973777175956253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204596257948649184783970835 306894386922973777175956253)
    ·
      refine ⟨115085395096115166440983595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306894386922973777175956253 115085395096115166440983595)
      ·
        refine ⟨172628092644172749661475393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115085395096115166440983595 172628092644172749661475393)
        ·
          refine ⟨129471069483129562246106545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172628092644172749661475393 129471069483129562246106545)
          ·
            refine ⟨97103302112347171684579909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129471069483129562246106545 97103302112347171684579909)
            ·
              refine ⟨18206869146065094690858733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97103302112347171684579909 18206869146065094690858733)
              ·
                refine ⟨6827575929774410509072025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18206869146065094690858733 6827575929774410509072025)
                ·
                  refine ⟨5120681947330807881804019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827575929774410509072025 5120681947330807881804019)
                  ·
                    refine ⟨7681022920996211822706029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120681947330807881804019 7681022920996211822706029)
                    ·
                      refine ⟨2880383595373579433514761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7681022920996211822706029 2880383595373579433514761)
                      ·
                        rfl

theorem cell23_5609527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_5609527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609527 prefixEnd_5609527 := by exact prefixLift 5609527
  have htrace : WordTrace (prefixWord ++ tailWord_5609527) baseStart_5609527 baseEnd_5609527 := by
    simpa [prefixWord, tailWord_5609527, baseEnd_5609527] using wordTrace_append hprefix tailTrace_5609527
  have hstable : (prefixWord ++ tailWord_5609527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609527).length < 2 ^ (prefixWord ++ tailWord_5609527).sum := by decide
  have hdescent : baseEnd_5609527 < baseStart_5609527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609543 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 8]
def baseStart_5609543 : Nat := 118140960795 + 5609543 * 2 ^ 59
def prefixEnd_5609543 : Nat := 4983230072969 + 3 ^ 40 * 5609543 * 2
def baseEnd_5609543 : Nat := 960130603688017123638229

theorem tailTrace_5609543 : CollatzResearch.WordTrace tailWord_5609543 prefixEnd_5609543 960130603688017123638229 := by
  unfold tailWord_5609543
  simp only [CollatzResearch.WordTrace]
  refine ⟨204596841516591219516553283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136397894344394146344368855 204596841516591219516553283)
  ·
    refine ⟨306895262274886829274829925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204596841516591219516553283 306895262274886829274829925)
    ·
      refine ⟨57542861676541280489030611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306895262274886829274829925 57542861676541280489030611)
      ·
        refine ⟨86314292514811920733545917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57542861676541280489030611 86314292514811920733545917)
        ·
          refine ⟨32367859693054470275079719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86314292514811920733545917 32367859693054470275079719)
          ·
            refine ⟨48551789539581705412619579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32367859693054470275079719 48551789539581705412619579)
            ·
              refine ⟨72827684309372558118929369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48551789539581705412619579 72827684309372558118929369)
              ·
                refine ⟨54620763232029418589197027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72827684309372558118929369 54620763232029418589197027)
                ·
                  refine ⟨81931144848044127883795541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54620763232029418589197027 81931144848044127883795541)
                  ·
                    refine ⟨960130603688017123638229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81931144848044127883795541 960130603688017123638229)
                    ·
                      rfl

theorem cell23_5609543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_5609543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609543 prefixEnd_5609543 := by exact prefixLift 5609543
  have htrace : WordTrace (prefixWord ++ tailWord_5609543) baseStart_5609543 baseEnd_5609543 := by
    simpa [prefixWord, tailWord_5609543, baseEnd_5609543] using wordTrace_append hprefix tailTrace_5609543
  have hstable : (prefixWord ++ tailWord_5609543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609543).length < 2 ^ (prefixWord ++ tailWord_5609543).sum := by decide
  have hdescent : baseEnd_5609543 < baseStart_5609543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609553 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 5]
def baseStart_5609553 : Nat := 118140960795 + 5609553 * 2 ^ 59
def prefixEnd_5609553 : Nat := 4983230072969 + 3 ^ 40 * 5609553 * 2
def baseEnd_5609553 : Nat := 2880396945870596331789641

theorem tailTrace_5609553 : CollatzResearch.WordTrace tailWord_5609553 prefixEnd_5609553 2880396945870596331789641 := by
  unfold tailWord_5609553
  simp only [CollatzResearch.WordTrace]
  refine ⟨204597206246554991224417313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136398137497703327482944875 204597206246554991224417313)
  ·
    refine ⟨153447904684916243418312985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204597206246554991224417313 153447904684916243418312985)
    ·
      refine ⟨115085928513687182563734739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153447904684916243418312985 115085928513687182563734739)
      ·
        refine ⟨172628892770530773845602109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115085928513687182563734739 172628892770530773845602109)
        ·
          refine ⟨64735834788949040192100791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172628892770530773845602109 64735834788949040192100791)
          ·
            refine ⟨97103752183423560288151187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64735834788949040192100791 97103752183423560288151187)
            ·
              refine ⟨145655628275135340432226781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97103752183423560288151187 145655628275135340432226781)
              ·
                refine ⟨54620860603175752662085043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145655628275135340432226781 54620860603175752662085043)
                ·
                  refine ⟨81931290904763628993127565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54620860603175752662085043 81931290904763628993127565)
                  ·
                    refine ⟨30724234089286360872422837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81931290904763628993127565 30724234089286360872422837)
                    ·
                      refine ⟨2880396945870596331789641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30724234089286360872422837 2880396945870596331789641)
                      ·
                        rfl

theorem cell23_5609553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_5609553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609553 prefixEnd_5609553 := by exact prefixLift 5609553
  have htrace : WordTrace (prefixWord ++ tailWord_5609553) baseStart_5609553 baseEnd_5609553 := by
    simpa [prefixWord, tailWord_5609553, baseEnd_5609553] using wordTrace_append hprefix tailTrace_5609553
  have hstable : (prefixWord ++ tailWord_5609553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609553).length < 2 ^ (prefixWord ++ tailWord_5609553).sum := by decide
  have hdescent : baseEnd_5609553 < baseStart_5609553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609580 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5609580 : Nat := 118140960795 + 5609580 * 2 ^ 59
def prefixEnd_5609580 : Nat := 4983230072969 + 3 ^ 40 * 5609580 * 2
def baseEnd_5609580 : Nat := 2880410809848267726152017

theorem tailTrace_5609580 : CollatzResearch.WordTrace tailWord_5609580 prefixEnd_5609580 2880410809848267726152017 := by
  unfold tailWord_5609580
  simp only [CollatzResearch.WordTrace]
  refine ⟨102299095508728587417825097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136398794011638116557100129 102299095508728587417825097)
  ·
    refine ⟨76724321631546440563368823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102299095508728587417825097 76724321631546440563368823)
    ·
      refine ⟨115086482447319660845053235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76724321631546440563368823 115086482447319660845053235)
      ·
        refine ⟨172629723670979491267579853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115086482447319660845053235 172629723670979491267579853)
        ·
          refine ⟨64736146376617309225342445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172629723670979491267579853 64736146376617309225342445)
          ·
            refine ⟨24276054891231490959503417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64736146376617309225342445 24276054891231490959503417)
            ·
              refine ⟨18207041168423618219627563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24276054891231490959503417 18207041168423618219627563)
              ·
                refine ⟨27310561752635427329441345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18207041168423618219627563 27310561752635427329441345)
                ·
                  refine ⟨20482921314476570497081009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27310561752635427329441345 20482921314476570497081009)
                  ·
                    refine ⟨15362190985857427872810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20482921314476570497081009 15362190985857427872810757)
                    ·
                      refine ⟨2880410809848267726152017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15362190985857427872810757 2880410809848267726152017)
                      ·
                        rfl

theorem cell23_5609580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5609580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609580 prefixEnd_5609580 := by exact prefixLift 5609580
  have htrace : WordTrace (prefixWord ++ tailWord_5609580) baseStart_5609580 baseEnd_5609580 := by
    simpa [prefixWord, tailWord_5609580, baseEnd_5609580] using wordTrace_append hprefix tailTrace_5609580
  have hstable : (prefixWord ++ tailWord_5609580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609580).length < 2 ^ (prefixWord ++ tailWord_5609580).sum := by decide
  have hdescent : baseEnd_5609580 < baseStart_5609580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609584 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2]
def baseStart_5609584 : Nat := 118140960795 + 5609584 * 2 ^ 59
def prefixEnd_5609584 : Nat := 4983230072969 + 3 ^ 40 * 5609584 * 2
def baseEnd_5609584 : Nat := 2880412863770885710501999

theorem tailTrace_5609584 : CollatzResearch.WordTrace tailWord_5609584 prefixEnd_5609584 2880412863770885710501999 := by
  unfold tailWord_5609584
  simp only [CollatzResearch.WordTrace]
  refine ⟨102299168454721341759397903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136398891272961789012530537 102299168454721341759397903)
  ·
    refine ⟨153448752682082012639096855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102299168454721341759397903 153448752682082012639096855)
    ·
      refine ⟨230173129023123018958645283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153448752682082012639096855 230173129023123018958645283)
      ·
        refine ⟨345259693534684528437967925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230173129023123018958645283 345259693534684528437967925)
        ·
          refine ⟨32368096268876674541059493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 345259693534684528437967925 32368096268876674541059493)
          ·
            refine ⟨6069018050414376476448655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32368096268876674541059493 6069018050414376476448655)
            ·
              refine ⟨9103527075621564714672983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069018050414376476448655 9103527075621564714672983)
              ·
                refine ⟨13655290613432347072009475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103527075621564714672983 13655290613432347072009475)
                ·
                  refine ⟨20482935920148520608014213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13655290613432347072009475 20482935920148520608014213)
                  ·
                    refine ⟨3840550485027847614002665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20482935920148520608014213 3840550485027847614002665)
                    ·
                      refine ⟨2880412863770885710501999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840550485027847614002665 2880412863770885710501999)
                      ·
                        rfl

theorem cell23_5609584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2].length) (baseStart_5609584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609584 prefixEnd_5609584 := by exact prefixLift 5609584
  have htrace : WordTrace (prefixWord ++ tailWord_5609584) baseStart_5609584 baseEnd_5609584 := by
    simpa [prefixWord, tailWord_5609584, baseEnd_5609584] using wordTrace_append hprefix tailTrace_5609584
  have hstable : (prefixWord ++ tailWord_5609584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609584).length < 2 ^ (prefixWord ++ tailWord_5609584).sum := by decide
  have hdescent : baseEnd_5609584 < baseStart_5609584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609607 : List Nat := [1, 1, 4, 2, 1, 1, 5, 3, 5]
def baseStart_5609607 : Nat := 118140960795 + 5609607 * 2 ^ 59
def prefixEnd_5609607 : Nat := 4983230072969 + 3 ^ 40 * 5609607 * 2
def baseEnd_5609607 : Nat := 320047185980659902279377

theorem tailTrace_5609607 : CollatzResearch.WordTrace tailWord_5609607 prefixEnd_5609607 320047185980659902279377 := by
  unfold tailWord_5609607
  simp only [CollatzResearch.WordTrace]
  refine ⟨204599175788359358446883075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136399450525572905631255383 204599175788359358446883075)
  ·
    refine ⟨306898763682539037670324613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204599175788359358446883075 306898763682539037670324613)
    ·
      refine ⟨57543518190476069563185865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306898763682539037670324613 57543518190476069563185865)
      ·
        refine ⟨43157638642857052172389399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57543518190476069563185865 43157638642857052172389399)
        ·
          refine ⟨64736457964285578258584099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43157638642857052172389399 64736457964285578258584099)
          ·
            refine ⟨97104686946428367387876149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64736457964285578258584099 97104686946428367387876149)
            ·
              refine ⟨9103564401227659442613389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97104686946428367387876149 9103564401227659442613389)
              ·
                refine ⟨3413836650460372290980021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9103564401227659442613389 3413836650460372290980021)
                ·
                  refine ⟨320047185980659902279377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3413836650460372290980021 320047185980659902279377)
                  ·
                    rfl

theorem cell23_5609607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 3, 5].length) (baseStart_5609607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609607 prefixEnd_5609607 := by exact prefixLift 5609607
  have htrace : WordTrace (prefixWord ++ tailWord_5609607) baseStart_5609607 baseEnd_5609607 := by
    simpa [prefixWord, tailWord_5609607, baseEnd_5609607] using wordTrace_append hprefix tailTrace_5609607
  have hstable : (prefixWord ++ tailWord_5609607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609607).length < 2 ^ (prefixWord ++ tailWord_5609607).sum := by decide
  have hdescent : baseEnd_5609607 < baseStart_5609607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609624 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 7]
def baseStart_5609624 : Nat := 118140960795 + 5609624 * 2 ^ 59
def prefixEnd_5609624 : Nat := 4983230072969 + 3 ^ 40 * 5609624 * 2
def baseEnd_5609624 : Nat := 320048155888562839333535

theorem tailTrace_5609624 : CollatzResearch.WordTrace tailWord_5609624 prefixEnd_5609624 320048155888562839333535 := by
  unfold tailWord_5609624
  simp only [CollatzResearch.WordTrace]
  refine ⟨102299897914648885175125963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136399863886198513566834617 102299897914648885175125963)
  ·
    refine ⟨153449846871973327762688945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102299897914648885175125963 153449846871973327762688945)
    ·
      refine ⟨115087385153979995822016709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153449846871973327762688945 115087385153979995822016709)
      ·
        refine ⟨21578884716371249216628133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115087385153979995822016709 21578884716371249216628133)
        ·
          refine ⟨4046040884319609228117775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21578884716371249216628133 4046040884319609228117775)
          ·
            refine ⟨6069061326479413842176663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046040884319609228117775 6069061326479413842176663)
            ·
              refine ⟨9103591989719120763264995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069061326479413842176663 9103591989719120763264995)
              ·
                refine ⟨13655387984578681144897493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103591989719120763264995 13655387984578681144897493)
                ·
                  refine ⟨320048155888562839333535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13655387984578681144897493 320048155888562839333535)
                  ·
                    rfl

theorem cell23_5609624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_5609624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609624 prefixEnd_5609624 := by exact prefixLift 5609624
  have htrace : WordTrace (prefixWord ++ tailWord_5609624) baseStart_5609624 baseEnd_5609624 := by
    simpa [prefixWord, tailWord_5609624, baseEnd_5609624] using wordTrace_append hprefix tailTrace_5609624
  have hstable : (prefixWord ++ tailWord_5609624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609624).length < 2 ^ (prefixWord ++ tailWord_5609624).sum := by decide
  have hdescent : baseEnd_5609624 < baseStart_5609624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609643 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9]
def baseStart_5609643 : Nat := 118140960795 + 5609643 * 2 ^ 59
def prefixEnd_5609643 : Nat := 4983230072969 + 3 ^ 40 * 5609643 * 2
def baseEnd_5609643 : Nat := 2880443159129500979664227

theorem tailTrace_5609643 : CollatzResearch.WordTrace tailWord_5609643 prefixEnd_5609643 2880443159129500979664227 := by
  unfold tailWord_5609643
  simp only [CollatzResearch.WordTrace]
  refine ⟨204600488816228936595193583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136400325877485957730129055 204600488816228936595193583)
  ·
    refine ⟨306900733224343404892790375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204600488816228936595193583 306900733224343404892790375)
    ·
      refine ⟨460351099836515107339185563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306900733224343404892790375 460351099836515107339185563)
      ·
        refine ⟨690526649754772661008778345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460351099836515107339185563 690526649754772661008778345)
        ·
          refine ⟨517894987316079495756583759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690526649754772661008778345 517894987316079495756583759)
          ·
            refine ⟨776842480974119243634875639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517894987316079495756583759 776842480974119243634875639)
            ·
              refine ⟨1165263721461178865452313459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776842480974119243634875639 1165263721461178865452313459)
              ·
                refine ⟨1747895582191768298178470189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165263721461178865452313459 1747895582191768298178470189)
                ·
                  refine ⟨655460843321913111816926321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1747895582191768298178470189 655460843321913111816926321)
                  ·
                    refine ⟨491595632491434833862694741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 655460843321913111816926321 491595632491434833862694741)
                    ·
                      refine ⟨2880443159129500979664227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 491595632491434833862694741 2880443159129500979664227)
                      ·
                        rfl

theorem cell23_5609643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 9].length) (baseStart_5609643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609643 prefixEnd_5609643 := by exact prefixLift 5609643
  have htrace : WordTrace (prefixWord ++ tailWord_5609643) baseStart_5609643 baseEnd_5609643 := by
    simpa [prefixWord, tailWord_5609643, baseEnd_5609643] using wordTrace_append hprefix tailTrace_5609643
  have hstable : (prefixWord ++ tailWord_5609643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609643).length < 2 ^ (prefixWord ++ tailWord_5609643).sum := by decide
  have hdescent : baseEnd_5609643 < baseStart_5609643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609657 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5609657 : Nat := 118140960795 + 5609657 * 2 ^ 59
def prefixEnd_5609657 : Nat := 4983230072969 + 3 ^ 40 * 5609657 * 2
def baseEnd_5609657 : Nat := 2880450347858663924889163

theorem tailTrace_5609657 : CollatzResearch.WordTrace tailWord_5609657 prefixEnd_5609657 2880450347858663924889163 := by
  unfold tailWord_5609657
  simp only [CollatzResearch.WordTrace]
  refine ⟨204600999438178216986203225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136400666292118811324135483 204600999438178216986203225)
  ·
    refine ⟨153450749578633662739652419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204600999438178216986203225 153450749578633662739652419)
    ·
      refine ⟨230176124367950494109478629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153450749578633662739652419 230176124367950494109478629)
      ·
        refine ⟨43158023318990717645527243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230176124367950494109478629 43158023318990717645527243)
        ·
          refine ⟨64737034978486076468290865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43158023318990717645527243 64737034978486076468290865)
          ·
            refine ⟨48552776233864557351218149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64737034978486076468290865 48552776233864557351218149)
            ·
              refine ⟨9103645543849604503353403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48552776233864557351218149 9103645543849604503353403)
              ·
                refine ⟨13655468315774406755030105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9103645543849604503353403 13655468315774406755030105)
                ·
                  refine ⟨10241601236830805066272579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13655468315774406755030105 10241601236830805066272579)
                  ·
                    refine ⟨15362401855246207599408869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241601236830805066272579 15362401855246207599408869)
                    ·
                      refine ⟨2880450347858663924889163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15362401855246207599408869 2880450347858663924889163)
                      ·
                        rfl

theorem cell23_5609657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5609657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609657 prefixEnd_5609657 := by exact prefixLift 5609657
  have htrace : WordTrace (prefixWord ++ tailWord_5609657) baseStart_5609657 baseEnd_5609657 := by
    simpa [prefixWord, tailWord_5609657, baseEnd_5609657] using wordTrace_append hprefix tailTrace_5609657
  have hstable : (prefixWord ++ tailWord_5609657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609657).length < 2 ^ (prefixWord ++ tailWord_5609657).sum := by decide
  have hdescent : baseEnd_5609657 < baseStart_5609657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609727 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 1, 5]
def baseStart_5609727 : Nat := 118140960795 + 5609727 * 2 ^ 59
def prefixEnd_5609727 : Nat := 4983230072969 + 3 ^ 40 * 5609727 * 2
def baseEnd_5609727 : Nat := 960162097168159550337947

theorem tailTrace_5609727 : CollatzResearch.WordTrace tailWord_5609727 prefixEnd_5609727 960162097168159550337947 := by
  unfold tailWord_5609727
  simp only [CollatzResearch.WordTrace]
  refine ⟨204603552547924618941251435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136402368365283079294167623 204603552547924618941251435)
  ·
    refine ⟨306905328821886928411877153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204603552547924618941251435 306905328821886928411877153)
    ·
      refine ⟨230178996616415196308907865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306905328821886928411877153 230178996616415196308907865)
      ·
        refine ⟨172634247462311397231680899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230178996616415196308907865 172634247462311397231680899)
        ·
          refine ⟨258951371193467095847521349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172634247462311397231680899 258951371193467095847521349)
          ·
            refine ⟨48553382098775080471410253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 258951371193467095847521349 48553382098775080471410253)
            ·
              refine ⟨18207518287040655176778845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48553382098775080471410253 18207518287040655176778845)
              ·
                refine ⟨6827819357640245691292067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18207518287040655176778845 6827819357640245691292067)
                ·
                  refine ⟨10241729036460368536938101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827819357640245691292067 10241729036460368536938101)
                  ·
                    refine ⟨960162097168159550337947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10241729036460368536938101 960162097168159550337947)
                    ·
                      rfl

theorem cell23_5609727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 5].length) (baseStart_5609727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609727 prefixEnd_5609727 := by exact prefixLift 5609727
  have htrace : WordTrace (prefixWord ++ tailWord_5609727) baseStart_5609727 baseEnd_5609727 := by
    simpa [prefixWord, tailWord_5609727, baseEnd_5609727] using wordTrace_append hprefix tailTrace_5609727
  have hstable : (prefixWord ++ tailWord_5609727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609727).length < 2 ^ (prefixWord ++ tailWord_5609727).sum := by decide
  have hdescent : baseEnd_5609727 < baseStart_5609727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609758 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5609758 : Nat := 118140960795 + 5609758 * 2 ^ 59
def prefixEnd_5609758 : Nat := 4983230072969 + 3 ^ 40 * 5609758 * 2
def baseEnd_5609758 : Nat := 2880502209404768029726199

theorem tailTrace_5609758 : CollatzResearch.WordTrace tailWord_5609758 prefixEnd_5609758 2880502209404768029726199 := by
  unfold tailWord_5609758
  simp only [CollatzResearch.WordTrace]
  refine ⟨25575585401351538904453741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136403122140541540823753285 25575585401351538904453741)
  ·
    refine ⟨9590844525506827089170153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25575585401351538904453741 9590844525506827089170153)
    ·
      refine ⟨7193133394130120316877615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9590844525506827089170153 7193133394130120316877615)
      ·
        refine ⟨10789700091195180475316423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7193133394130120316877615 10789700091195180475316423)
        ·
          refine ⟨16184550136792770712974635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10789700091195180475316423 16184550136792770712974635)
          ·
            refine ⟨24276825205189156069461953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16184550136792770712974635 24276825205189156069461953)
            ·
              refine ⟨18207618903891867052096465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24276825205189156069461953 18207618903891867052096465)
              ·
                refine ⟨13655714177918900289072349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18207618903891867052096465 13655714177918900289072349)
                ·
                  refine ⟨5120892816719587608402131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13655714177918900289072349 5120892816719587608402131)
                  ·
                    refine ⟨7681339225079381412603197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120892816719587608402131 7681339225079381412603197)
                    ·
                      refine ⟨2880502209404768029726199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7681339225079381412603197 2880502209404768029726199)
                      ·
                        rfl

theorem cell23_5609758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5609758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609758 prefixEnd_5609758 := by exact prefixLift 5609758
  have htrace : WordTrace (prefixWord ++ tailWord_5609758) baseStart_5609758 baseEnd_5609758 := by
    simpa [prefixWord, tailWord_5609758, baseEnd_5609758] using wordTrace_append hprefix tailTrace_5609758
  have hstable : (prefixWord ++ tailWord_5609758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609758).length < 2 ^ (prefixWord ++ tailWord_5609758).sum := by decide
  have hdescent : baseEnd_5609758 < baseStart_5609758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609764 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_5609764 : Nat := 118140960795 + 5609764 * 2 ^ 59
def prefixEnd_5609764 : Nat := 4983230072969 + 3 ^ 40 * 5609764 * 2
def baseEnd_5609764 : Nat := 2880505290288695006251171

theorem tailTrace_5609764 : CollatzResearch.WordTrace tailWord_5609764 prefixEnd_5609764 2880505290288695006251171 := by
  unfold tailWord_5609764
  simp only [CollatzResearch.WordTrace]
  refine ⟨102302451024395287130174173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136403268032527049506898897 102302451024395287130174173)
  ·
    refine ⟨38363419134148232673815315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102302451024395287130174173 38363419134148232673815315)
    ·
      refine ⟨57545128701222349010722973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38363419134148232673815315 57545128701222349010722973)
      ·
        refine ⟨21579423262958380879021115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57545128701222349010722973 21579423262958380879021115)
        ·
          refine ⟨32369134894437571318531673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21579423262958380879021115 32369134894437571318531673)
          ·
            refine ⟨24276851170828178488898755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32369134894437571318531673 24276851170828178488898755)
            ·
              refine ⟨36415276756242267733348133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24276851170828178488898755 36415276756242267733348133)
              ·
                refine ⟨6827864391795425200002775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36415276756242267733348133 6827864391795425200002775)
                ·
                  refine ⟨10241796587693137800004163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827864391795425200002775 10241796587693137800004163)
                  ·
                    refine ⟨15362694881539706700006245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10241796587693137800004163 15362694881539706700006245)
                    ·
                      refine ⟨2880505290288695006251171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15362694881539706700006245 2880505290288695006251171)
                      ·
                        rfl

theorem cell23_5609764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_5609764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609764 prefixEnd_5609764 := by exact prefixLift 5609764
  have htrace : WordTrace (prefixWord ++ tailWord_5609764) baseStart_5609764 baseEnd_5609764 := by
    simpa [prefixWord, tailWord_5609764, baseEnd_5609764] using wordTrace_append hprefix tailTrace_5609764
  have hstable : (prefixWord ++ tailWord_5609764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609764).length < 2 ^ (prefixWord ++ tailWord_5609764).sum := by decide
  have hdescent : baseEnd_5609764 < baseStart_5609764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609784 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_5609784 : Nat := 118140960795 + 5609784 * 2 ^ 59
def prefixEnd_5609784 : Nat := 4983230072969 + 3 ^ 40 * 5609784 * 2
def baseEnd_5609784 : Nat := 2880515559901784928001079

theorem tailTrace_5609784 : CollatzResearch.WordTrace tailWord_5609784 prefixEnd_5609784 2880515559901784928001079 := by
  unfold tailWord_5609784
  simp only [CollatzResearch.WordTrace]
  refine ⟨102302815754359058838038203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136403754339145411784050937 102302815754359058838038203)
  ·
    refine ⟨153454223631538588257057305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102302815754359058838038203 153454223631538588257057305)
    ·
      refine ⟨115090667723653941192792979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153454223631538588257057305 115090667723653941192792979)
      ·
        refine ⟨172636001585480911789189469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115090667723653941192792979 172636001585480911789189469)
        ·
          refine ⟨64738500594555341920946051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172636001585480911789189469 64738500594555341920946051)
          ·
            refine ⟨97107750891833012881419077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64738500594555341920946051 97107750891833012881419077)
            ·
              refine ⟨18207703292218689915266077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97107750891833012881419077 18207703292218689915266077)
              ·
                refine ⟨6827888734582008718224779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18207703292218689915266077 6827888734582008718224779)
                ·
                  refine ⟨10241833101873013077337169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6827888734582008718224779 10241833101873013077337169)
                  ·
                    refine ⟨7681374826404759808002877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10241833101873013077337169 7681374826404759808002877)
                    ·
                      refine ⟨2880515559901784928001079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7681374826404759808002877 2880515559901784928001079)
                      ·
                        rfl

theorem cell23_5609784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_5609784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609784 prefixEnd_5609784 := by exact prefixLift 5609784
  have htrace : WordTrace (prefixWord ++ tailWord_5609784) baseStart_5609784 baseEnd_5609784 := by
    simpa [prefixWord, tailWord_5609784, baseEnd_5609784] using wordTrace_append hprefix tailTrace_5609784
  have hstable : (prefixWord ++ tailWord_5609784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609784).length < 2 ^ (prefixWord ++ tailWord_5609784).sum := by decide
  have hdescent : baseEnd_5609784 < baseStart_5609784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609867 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4]
def baseStart_5609867 : Nat := 118140960795 + 5609867 * 2 ^ 59
def prefixEnd_5609867 : Nat := 4983230072969 + 3 ^ 40 * 5609867 * 2
def baseEnd_5609867 : Nat := 2880558178796108103263197

theorem tailTrace_5609867 : CollatzResearch.WordTrace tailWord_5609867 prefixEnd_5609867 2880558178796108103263197 := by
  unfold tailWord_5609867
  simp only [CollatzResearch.WordTrace]
  refine ⟨204608658767417422851347855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136405772511611615234231903 204608658767417422851347855)
  ·
    refine ⟨306912988151126134277021783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204608658767417422851347855 306912988151126134277021783)
    ·
      refine ⟨460369482226689201415532675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306912988151126134277021783 460369482226689201415532675)
      ·
        refine ⟨690554223340033802123299013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460369482226689201415532675 690554223340033802123299013)
        ·
          refine ⟨129478916876256337898118565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 690554223340033802123299013 129478916876256337898118565)
          ·
            refine ⟨24277296914298063355897231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129478916876256337898118565 24277296914298063355897231)
            ·
              refine ⟨36415945371447095033845847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24277296914298063355897231 36415945371447095033845847)
              ·
                refine ⟨54623918057170642550768771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36415945371447095033845847 54623918057170642550768771)
                ·
                  refine ⟨81935877085755963826153157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54623918057170642550768771 81935877085755963826153157)
                  ·
                    refine ⟨15362976953579243217403717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81935877085755963826153157 15362976953579243217403717)
                    ·
                      refine ⟨2880558178796108103263197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15362976953579243217403717 2880558178796108103263197)
                      ·
                        rfl

theorem cell23_5609867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 4].length) (baseStart_5609867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609867 prefixEnd_5609867 := by exact prefixLift 5609867
  have htrace : WordTrace (prefixWord ++ tailWord_5609867) baseStart_5609867 baseEnd_5609867 := by
    simpa [prefixWord, tailWord_5609867, baseEnd_5609867] using wordTrace_append hprefix tailTrace_5609867
  have hstable : (prefixWord ++ tailWord_5609867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609867).length < 2 ^ (prefixWord ++ tailWord_5609867).sum := by decide
  have hdescent : baseEnd_5609867 < baseStart_5609867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609905 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 2, 2, 2]
def baseStart_5609905 : Nat := 118140960795 + 5609905 * 2 ^ 59
def prefixEnd_5609905 : Nat := 4983230072969 + 3 ^ 40 * 5609905 * 2
def baseEnd_5609905 : Nat := 2880577691060978954588023

theorem tailTrace_5609905 : CollatzResearch.WordTrace tailWord_5609905 prefixEnd_5609905 2880577691060978954588023 := by
  unfold tailWord_5609905
  simp only [CollatzResearch.WordTrace]
  refine ⟨204610044741279755341231169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136406696494186503560820779 204610044741279755341231169)
  ·
    refine ⟨153457533555959816505923377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204610044741279755341231169 153457533555959816505923377)
    ·
      refine ⟨115093150166969862379442533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153457533555959816505923377 115093150166969862379442533)
      ·
        refine ⟨21579965656306849196145475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115093150166969862379442533 21579965656306849196145475)
        ·
          refine ⟨32369948484460273794218213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21579965656306849196145475 32369948484460273794218213)
          ·
            refine ⟨6069365340836301336415915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32369948484460273794218213 6069365340836301336415915)
            ·
              refine ⟨9104048011254452004623873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069365340836301336415915 9104048011254452004623873)
              ·
                refine ⟨6828036008440839003467905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9104048011254452004623873 6828036008440839003467905)
                ·
                  refine ⟨5121027006330629252600929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6828036008440839003467905 5121027006330629252600929)
                  ·
                    refine ⟨3840770254747971939450697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5121027006330629252600929 3840770254747971939450697)
                    ·
                      refine ⟨2880577691060978954588023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840770254747971939450697 2880577691060978954588023)
                      ·
                        rfl

theorem cell23_5609905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_5609905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609905 prefixEnd_5609905 := by exact prefixLift 5609905
  have htrace : WordTrace (prefixWord ++ tailWord_5609905) baseStart_5609905 baseEnd_5609905 := by
    simpa [prefixWord, tailWord_5609905, baseEnd_5609905] using wordTrace_append hprefix tailTrace_5609905
  have hstable : (prefixWord ++ tailWord_5609905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609905).length < 2 ^ (prefixWord ++ tailWord_5609905).sum := by decide
  have hdescent : baseEnd_5609905 < baseStart_5609905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609914 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_5609914 : Nat := 118140960795 + 5609914 * 2 ^ 59
def prefixEnd_5609914 : Nat := 4983230072969 + 3 ^ 40 * 5609914 * 2
def baseEnd_5609914 : Nat := 2880582312386869419375481

theorem tailTrace_5609914 : CollatzResearch.WordTrace tailWord_5609914 prefixEnd_5609914 2880582312386869419375481 := by
  unfold tailWord_5609914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51152593249561787469577199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136406915332164766585539197 51152593249561787469577199)
  ·
    refine ⟨76728889874342681204365799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51152593249561787469577199 76728889874342681204365799)
    ·
      refine ⟨115093334811514021806548699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76728889874342681204365799 115093334811514021806548699)
      ·
        refine ⟨172640002217271032709823049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115093334811514021806548699 172640002217271032709823049)
        ·
          refine ⟨129480001662953274532367287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172640002217271032709823049 129480001662953274532367287)
          ·
            refine ⟨194220002494429911798550931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129480001662953274532367287 194220002494429911798550931)
            ·
              refine ⟨291330003741644867697826397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194220002494429911798550931 291330003741644867697826397)
              ·
                refine ⟨109248751403116825386684899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291330003741644867697826397 109248751403116825386684899)
                ·
                  refine ⟨163873127104675238080027349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109248751403116825386684899 163873127104675238080027349)
                  ·
                    refine ⟨3840776416515825892500641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163873127104675238080027349 3840776416515825892500641)
                    ·
                      refine ⟨2880582312386869419375481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840776416515825892500641 2880582312386869419375481)
                      ·
                        rfl

theorem cell23_5609914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_5609914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609914 prefixEnd_5609914 := by exact prefixLift 5609914
  have htrace : WordTrace (prefixWord ++ tailWord_5609914) baseStart_5609914 baseEnd_5609914 := by
    simpa [prefixWord, tailWord_5609914, baseEnd_5609914] using wordTrace_append hprefix tailTrace_5609914
  have hstable : (prefixWord ++ tailWord_5609914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609914).length < 2 ^ (prefixWord ++ tailWord_5609914).sum := by decide
  have hdescent : baseEnd_5609914 < baseStart_5609914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609944 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5609944 : Nat := 118140960795 + 5609944 * 2 ^ 59
def prefixEnd_5609944 : Nat := 4983230072969 + 3 ^ 40 * 5609944 * 2
def baseEnd_5609944 : Nat := 2880597716806504302000343

theorem tailTrace_5609944 : CollatzResearch.WordTrace tailWord_5609944 prefixEnd_5609944 2880597716806504302000343 := by
  unfold tailWord_5609944
  simp only [CollatzResearch.WordTrace]
  refine ⟨102305733594069232500950443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136407644792092310001267257 102305733594069232500950443)
  ·
    refine ⟨153458600391103848751425665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102305733594069232500950443 153458600391103848751425665)
    ·
      refine ⟨115093950293327886563569249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153458600391103848751425665 115093950293327886563569249)
      ·
        refine ⟨86320462719995914922676937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115093950293327886563569249 86320462719995914922676937)
        ·
          refine ⟨64740347039996936192007703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86320462719995914922676937 64740347039996936192007703)
          ·
            refine ⟨97110520559995404288011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64740347039996936192007703 97110520559995404288011555)
            ·
              refine ⟨145665780839993106432017333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97110520559995404288011555 145665780839993106432017333)
              ·
                refine ⟨13656166953749353728001625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145665780839993106432017333 13656166953749353728001625)
                ·
                  refine ⟨10242125215312015296001219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13656166953749353728001625 10242125215312015296001219)
                  ·
                    refine ⟨15363187822968022944001829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10242125215312015296001219 15363187822968022944001829)
                    ·
                      refine ⟨2880597716806504302000343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15363187822968022944001829 2880597716806504302000343)
                      ·
                        rfl

theorem cell23_5609944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5609944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609944 prefixEnd_5609944 := by exact prefixLift 5609944
  have htrace : WordTrace (prefixWord ++ tailWord_5609944) baseStart_5609944 baseEnd_5609944 := by
    simpa [prefixWord, tailWord_5609944, baseEnd_5609944] using wordTrace_append hprefix tailTrace_5609944
  have hstable : (prefixWord ++ tailWord_5609944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609944).length < 2 ^ (prefixWord ++ tailWord_5609944).sum := by decide
  have hdescent : baseEnd_5609944 < baseStart_5609944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5609998 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5609998 : Nat := 118140960795 + 5609998 * 2 ^ 59
def prefixEnd_5609998 : Nat := 4983230072969 + 3 ^ 40 * 5609998 * 2
def baseEnd_5609998 : Nat := 2880625444761847090725095

theorem tailTrace_5609998 : CollatzResearch.WordTrace tailWord_5609998 prefixEnd_5609998 2880625444761847090725095 := by
  unfold tailWord_5609998
  simp only [CollatzResearch.WordTrace]
  refine ⟨25576679591242854028045831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136408957819961888149577765 25576679591242854028045831)
  ·
    refine ⟨38365019386864281042068747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25576679591242854028045831 38365019386864281042068747)
    ·
      refine ⟨57547529080296421563103121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38365019386864281042068747 57547529080296421563103121)
      ·
        refine ⟨43160646810222316172327341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57547529080296421563103121 43160646810222316172327341)
        ·
          refine ⟨16185242553833368564622753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43160646810222316172327341 16185242553833368564622753)
          ·
            refine ⟨12138931915375026423467065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16185242553833368564622753 12138931915375026423467065)
            ·
              refine ⟨9104198936531269817600299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12138931915375026423467065 9104198936531269817600299)
              ·
                refine ⟨13656298404796904726400449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104198936531269817600299 13656298404796904726400449)
                ·
                  refine ⟨10242223803597678544800337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13656298404796904726400449 10242223803597678544800337)
                  ·
                    refine ⟨7681667852698258908600253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10242223803597678544800337 7681667852698258908600253)
                    ·
                      refine ⟨2880625444761847090725095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7681667852698258908600253 2880625444761847090725095)
                      ·
                        rfl

theorem cell23_5609998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5609998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5609998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5609998 prefixEnd_5609998 := by exact prefixLift 5609998
  have htrace : WordTrace (prefixWord ++ tailWord_5609998) baseStart_5609998 baseEnd_5609998 := by
    simpa [prefixWord, tailWord_5609998, baseEnd_5609998] using wordTrace_append hprefix tailTrace_5609998
  have hstable : (prefixWord ++ tailWord_5609998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5609998).length < 2 ^ (prefixWord ++ tailWord_5609998).sum := by decide
  have hdescent : baseEnd_5609998 < baseStart_5609998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5609998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610055 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 2, 3, 2]
def baseStart_5610055 : Nat := 118140960795 + 5610055 * 2 ^ 59
def prefixEnd_5610055 : Nat := 4983230072969 + 3 ^ 40 * 5610055 * 2
def baseEnd_5610055 : Nat := 2880654713159153367712333

theorem tailTrace_5610055 : CollatzResearch.WordTrace tailWord_5610055 prefixEnd_5610055 2880654713159153367712333 := by
  unfold tailWord_5610055
  simp only [CollatzResearch.WordTrace]
  refine ⟨204615515690736330959191619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136410343793824220639461079 204615515690736330959191619)
  ·
    refine ⟨306923273536104496438787429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204615515690736330959191619 306923273536104496438787429)
    ·
      refine ⟨57548113788019593082272643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306923273536104496438787429 57548113788019593082272643)
      ·
        refine ⟨86322170682029389623408965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57548113788019593082272643 86322170682029389623408965)
        ·
          refine ⟨16185407002880510554389181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86322170682029389623408965 16185407002880510554389181)
          ·
            refine ⟨6069527626080191457895943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16185407002880510554389181 6069527626080191457895943)
            ·
              refine ⟨9104291439120287186843915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069527626080191457895943 9104291439120287186843915)
              ·
                refine ⟨13656437158680430780265873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104291439120287186843915 13656437158680430780265873)
                ·
                  refine ⟨10242327869010323085199405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13656437158680430780265873 10242327869010323085199405)
                  ·
                    refine ⟨3840872950878871156949777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10242327869010323085199405 3840872950878871156949777)
                    ·
                      refine ⟨2880654713159153367712333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840872950878871156949777 2880654713159153367712333)
                      ·
                        rfl

theorem cell23_5610055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_5610055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610055 prefixEnd_5610055 := by exact prefixLift 5610055
  have htrace : WordTrace (prefixWord ++ tailWord_5610055) baseStart_5610055 baseEnd_5610055 := by
    simpa [prefixWord, tailWord_5610055, baseEnd_5610055] using wordTrace_append hprefix tailTrace_5610055
  have hstable : (prefixWord ++ tailWord_5610055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610055).length < 2 ^ (prefixWord ++ tailWord_5610055).sum := by decide
  have hdescent : baseEnd_5610055 < baseStart_5610055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610064 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_5610064 : Nat := 118140960795 + 5610064 * 2 ^ 59
def prefixEnd_5610064 : Nat := 4983230072969 + 3 ^ 40 * 5610064 * 2
def baseEnd_5610064 : Nat := 2880659334485043832499791

theorem tailTrace_5610064 : CollatzResearch.WordTrace tailWord_5610064 prefixEnd_5610064 2880659334485043832499791 := by
  unfold tailWord_5610064
  simp only [CollatzResearch.WordTrace]
  refine ⟨102307921973851862748134623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136410562631802483664179497 102307921973851862748134623)
  ·
    refine ⟨153461882960777794122201935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102307921973851862748134623 153461882960777794122201935)
    ·
      refine ⟨230192824441166691183302903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153461882960777794122201935 230192824441166691183302903)
      ·
        refine ⟨345289236661750036774954355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230192824441166691183302903 345289236661750036774954355)
        ·
          refine ⟨517933854992625055162431533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345289236661750036774954355 517933854992625055162431533)
          ·
            refine ⟨194225195622234395685911825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517933854992625055162431533 194225195622234395685911825)
            ·
              refine ⟨145668896716675796764433869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194225195622234395685911825 145668896716675796764433869)
              ·
                refine ⟨54625836268753423786662701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145668896716675796764433869 54625836268753423786662701)
                ·
                  refine ⟨20484688600782533919998513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54625836268753423786662701 20484688600782533919998513)
                  ·
                    refine ⟨15363516450586900439998885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20484688600782533919998513 15363516450586900439998885)
                    ·
                      refine ⟨2880659334485043832499791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15363516450586900439998885 2880659334485043832499791)
                      ·
                        rfl

theorem cell23_5610064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_5610064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610064 prefixEnd_5610064 := by exact prefixLift 5610064
  have htrace : WordTrace (prefixWord ++ tailWord_5610064) baseStart_5610064 baseEnd_5610064 := by
    simpa [prefixWord, tailWord_5610064, baseEnd_5610064] using wordTrace_append hprefix tailTrace_5610064
  have hstable : (prefixWord ++ tailWord_5610064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610064).length < 2 ^ (prefixWord ++ tailWord_5610064).sum := by decide
  have hdescent : baseEnd_5610064 < baseStart_5610064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610068 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_5610068 : Nat := 118140960795 + 5610068 * 2 ^ 59
def prefixEnd_5610068 : Nat := 4983230072969 + 3 ^ 40 * 5610068 * 2
def baseEnd_5610068 : Nat := 2880661388407661816849773

theorem tailTrace_5610068 : CollatzResearch.WordTrace tailWord_5610068 prefixEnd_5610068 2880661388407661816849773 := by
  unfold tailWord_5610068
  simp only [CollatzResearch.WordTrace]
  refine ⟨102307994919844617089707429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136410659893126156119609905 102307994919844617089707429)
  ·
    refine ⟨19182749047470865704320143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102307994919844617089707429 19182749047470865704320143)
    ·
      refine ⟨28774123571206298556480215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19182749047470865704320143 28774123571206298556480215)
      ·
        refine ⟨43161185356809447834720323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28774123571206298556480215 43161185356809447834720323)
        ·
          refine ⟨64741778035214171752080485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43161185356809447834720323 64741778035214171752080485)
          ·
            refine ⟨12139083381602657203515091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64741778035214171752080485 12139083381602657203515091)
            ·
              refine ⟨18208625072403985805272637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12139083381602657203515091 18208625072403985805272637)
              ·
                refine ⟨6828234402151494676977239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18208625072403985805272637 6828234402151494676977239)
                ·
                  refine ⟨10242351603227242015465859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828234402151494676977239 10242351603227242015465859)
                  ·
                    refine ⟨15363527404840863023198789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10242351603227242015465859 15363527404840863023198789)
                    ·
                      refine ⟨2880661388407661816849773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15363527404840863023198789 2880661388407661816849773)
                      ·
                        rfl

theorem cell23_5610068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_5610068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610068 prefixEnd_5610068 := by exact prefixLift 5610068
  have htrace : WordTrace (prefixWord ++ tailWord_5610068) baseStart_5610068 baseEnd_5610068 := by
    simpa [prefixWord, tailWord_5610068, baseEnd_5610068] using wordTrace_append hprefix tailTrace_5610068
  have hstable : (prefixWord ++ tailWord_5610068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610068).length < 2 ^ (prefixWord ++ tailWord_5610068).sum := by decide
  have hdescent : baseEnd_5610068 < baseStart_5610068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610088 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5610088 : Nat := 118140960795 + 5610088 * 2 ^ 59
def prefixEnd_5610088 : Nat := 4983230072969 + 3 ^ 40 * 5610088 * 2
def baseEnd_5610088 : Nat := 2880671658020751738599681

theorem tailTrace_5610088 : CollatzResearch.WordTrace tailWord_5610088 prefixEnd_5610088 2880671658020751738599681 := by
  unfold tailWord_5610088
  simp only [CollatzResearch.WordTrace]
  refine ⟨102308359649808388797571459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136411146199744518396761945 102308359649808388797571459)
  ·
    refine ⟨153462539474712583196357189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102308359649808388797571459 153462539474712583196357189)
    ·
      refine ⟨28774226151508609349316973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153462539474712583196357189 28774226151508609349316973)
      ·
        refine ⟨10790334806815728505993865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28774226151508609349316973 10790334806815728505993865)
        ·
          refine ⟨8092751105111796379495399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10790334806815728505993865 8092751105111796379495399)
          ·
            refine ⟨12139126657667694569243099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092751105111796379495399 12139126657667694569243099)
            ·
              refine ⟨18208689986501541853864649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12139126657667694569243099 18208689986501541853864649)
              ·
                refine ⟨13656517489876156390398487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18208689986501541853864649 13656517489876156390398487)
                ·
                  refine ⟨20484776234814234585597731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13656517489876156390398487 20484776234814234585597731)
                  ·
                    refine ⟨30727164352221351878396597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20484776234814234585597731 30727164352221351878396597)
                    ·
                      refine ⟨2880671658020751738599681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30727164352221351878396597 2880671658020751738599681)
                      ·
                        rfl

theorem cell23_5610088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5610088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610088 prefixEnd_5610088 := by exact prefixLift 5610088
  have htrace : WordTrace (prefixWord ++ tailWord_5610088) baseStart_5610088 baseEnd_5610088 := by
    simpa [prefixWord, tailWord_5610088, baseEnd_5610088] using wordTrace_append hprefix tailTrace_5610088
  have hstable : (prefixWord ++ tailWord_5610088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610088).length < 2 ^ (prefixWord ++ tailWord_5610088).sum := by decide
  have hdescent : baseEnd_5610088 < baseStart_5610088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610218 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2]
def baseStart_5610218 : Nat := 118140960795 + 5610218 * 2 ^ 59
def prefixEnd_5610218 : Nat := 4983230072969 + 3 ^ 40 * 5610218 * 2
def baseEnd_5610218 : Nat := 2880738410505836229974083

theorem tailTrace_5610218 : CollatzResearch.WordTrace tailWord_5610218 prefixEnd_5610218 2880738410505836229974083 := by
  unfold tailWord_5610218
  simp only [CollatzResearch.WordTrace]
  refine ⟨51155365197286452449343827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136414307192763873198250205 51155365197286452449343827)
  ·
    refine ⟨76733047795929678674015741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51155365197286452449343827 76733047795929678674015741)
    ·
      refine ⟨28774892923473629502755903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76733047795929678674015741 28774892923473629502755903)
      ·
        refine ⟨43162339385210444254133855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28774892923473629502755903 43162339385210444254133855)
        ·
          refine ⟨64743509077815666381200783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43162339385210444254133855 64743509077815666381200783)
          ·
            refine ⟨97115263616723499571801175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64743509077815666381200783 97115263616723499571801175)
            ·
              refine ⟨145672895425085249357701763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97115263616723499571801175 145672895425085249357701763)
              ·
                refine ⟨218509343137627874036552645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145672895425085249357701763 218509343137627874036552645)
                ·
                  refine ⟨40970501838305226381853621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218509343137627874036552645 40970501838305226381853621)
                  ·
                    refine ⟨3840984547341114973298777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40970501838305226381853621 3840984547341114973298777)
                    ·
                      refine ⟨2880738410505836229974083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3840984547341114973298777 2880738410505836229974083)
                      ·
                        rfl

theorem cell23_5610218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_5610218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610218 prefixEnd_5610218 := by exact prefixLift 5610218
  have htrace : WordTrace (prefixWord ++ tailWord_5610218) baseStart_5610218 baseEnd_5610218 := by
    simpa [prefixWord, tailWord_5610218, baseEnd_5610218] using wordTrace_append hprefix tailTrace_5610218
  have hstable : (prefixWord ++ tailWord_5610218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610218).length < 2 ^ (prefixWord ++ tailWord_5610218).sum := by decide
  have hdescent : baseEnd_5610218 < baseStart_5610218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610261 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_5610261 : Nat := 118140960795 + 5610261 * 2 ^ 59
def prefixEnd_5610261 : Nat := 4983230072969 + 3 ^ 40 * 5610261 * 2
def baseEnd_5610261 : Nat := 2880760490173979561736385

theorem tailTrace_5610261 : CollatzResearch.WordTrace tailWord_5610261 prefixEnd_5610261 2880760490173979561736385 := by
  unfold tailWord_5610261
  simp only [CollatzResearch.WordTrace]
  refine ⟨204623029127990028141190637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136415352751993352094127091 204623029127990028141190637)
  ·
    refine ⟨76733635922996260552946489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204623029127990028141190637 76733635922996260552946489)
    ·
      refine ⟨57550226942247195414709867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76733635922996260552946489 57550226942247195414709867)
      ·
        refine ⟨86325340413370793122064801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57550226942247195414709867 86325340413370793122064801)
        ·
          refine ⟨64744005310028094841548601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86325340413370793122064801 64744005310028094841548601)
          ·
            refine ⟨48558003982521071131161451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64744005310028094841548601 48558003982521071131161451)
            ·
              refine ⟨72837005973781606696742177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48558003982521071131161451 72837005973781606696742177)
              ·
                refine ⟨54627754480336205022556633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72837005973781606696742177 54627754480336205022556633)
                ·
                  refine ⟨40970815860252153766917475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54627754480336205022556633 40970815860252153766917475)
                  ·
                    refine ⟨61456223790378230650376213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40970815860252153766917475 61456223790378230650376213)
                    ·
                      refine ⟨2880760490173979561736385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61456223790378230650376213 2880760490173979561736385)
                      ·
                        rfl

theorem cell23_5610261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_5610261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610261 prefixEnd_5610261 := by exact prefixLift 5610261
  have htrace : WordTrace (prefixWord ++ tailWord_5610261) baseStart_5610261 baseEnd_5610261 := by
    simpa [prefixWord, tailWord_5610261, baseEnd_5610261] using wordTrace_append hprefix tailTrace_5610261
  have hstable : (prefixWord ++ tailWord_5610261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610261).length < 2 ^ (prefixWord ++ tailWord_5610261).sum := by decide
  have hdescent : baseEnd_5610261 < baseStart_5610261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610268 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5610268 : Nat := 118140960795 + 5610268 * 2 ^ 59
def prefixEnd_5610268 : Nat := 4983230072969 + 3 ^ 40 * 5610268 * 2
def baseEnd_5610268 : Nat := 2880764084538561034348853

theorem tailTrace_5610268 : CollatzResearch.WordTrace tailWord_5610268 prefixEnd_5610268 2880764084538561034348853 := by
  unfold tailWord_5610268
  simp only [CollatzResearch.WordTrace]
  refine ⟨102311642219482334168347729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136415522959309778891130305 102311642219482334168347729)
  ·
    refine ⟨76733731664611750626260797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102311642219482334168347729 76733731664611750626260797)
    ·
      refine ⟨28775149374229406484847799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76733731664611750626260797 28775149374229406484847799)
      ·
        refine ⟨43162724061344109727271699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28775149374229406484847799 43162724061344109727271699)
        ·
          refine ⟨64744086092016164590907549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43162724061344109727271699 64744086092016164590907549)
          ·
            refine ⟨24279032284506061721590331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64744086092016164590907549 24279032284506061721590331)
            ·
              refine ⟨36418548426759092582385497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24279032284506061721590331 36418548426759092582385497)
              ·
                refine ⟨27313911320069319436789123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36418548426759092582385497 27313911320069319436789123)
                ·
                  refine ⟨40970866980103979155183685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27313911320069319436789123 40970866980103979155183685)
                  ·
                    refine ⟨7682037558769496091596941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40970866980103979155183685 7682037558769496091596941)
                    ·
                      refine ⟨2880764084538561034348853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682037558769496091596941 2880764084538561034348853)
                      ·
                        rfl

theorem cell23_5610268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5610268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610268 prefixEnd_5610268 := by exact prefixLift 5610268
  have htrace : WordTrace (prefixWord ++ tailWord_5610268) baseStart_5610268 baseEnd_5610268 := by
    simpa [prefixWord, tailWord_5610268, baseEnd_5610268] using wordTrace_append hprefix tailTrace_5610268
  have hstable : (prefixWord ++ tailWord_5610268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610268).length < 2 ^ (prefixWord ++ tailWord_5610268).sum := by decide
  have hdescent : baseEnd_5610268 < baseStart_5610268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610302 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_5610302 : Nat := 118140960795 + 5610302 * 2 ^ 59
def prefixEnd_5610302 : Nat := 4983230072969 + 3 ^ 40 * 5610302 * 2
def baseEnd_5610302 : Nat := 2880781542880813901323697

theorem tailTrace_5610302 : CollatzResearch.WordTrace tailWord_5610302 prefixEnd_5610302 2880781542880813901323697 := by
  unfold tailWord_5610302
  simp only [CollatzResearch.WordTrace]
  refine ⟨25578065565105186517929145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136416349680560994762288773 25578065565105186517929145)
  ·
    refine ⟨19183549173828889888446859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25578065565105186517929145 19183549173828889888446859)
    ·
      refine ⟨28775323760743334832670289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19183549173828889888446859 28775323760743334832670289)
      ·
        refine ⟨21581492820557501124502717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28775323760743334832670289 21581492820557501124502717)
        ·
          refine ⟨8093059807709062921688519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21581492820557501124502717 8093059807709062921688519)
          ·
            refine ⟨12139589711563594382532779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093059807709062921688519 12139589711563594382532779)
            ·
              refine ⟨18209384567345391573799169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12139589711563594382532779 18209384567345391573799169)
              ·
                refine ⟨13657038425509043680349377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18209384567345391573799169 13657038425509043680349377)
                ·
                  refine ⟨10242778819131782760262033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13657038425509043680349377 10242778819131782760262033)
                  ·
                    refine ⟨7682084114348837070196525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10242778819131782760262033 7682084114348837070196525)
                    ·
                      refine ⟨2880781542880813901323697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682084114348837070196525 2880781542880813901323697)
                      ·
                        rfl

theorem cell23_5610302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_5610302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610302 prefixEnd_5610302 := by exact prefixLift 5610302
  have htrace : WordTrace (prefixWord ++ tailWord_5610302) baseStart_5610302 baseEnd_5610302 := by
    simpa [prefixWord, tailWord_5610302, baseEnd_5610302] using wordTrace_append hprefix tailTrace_5610302
  have hstable : (prefixWord ++ tailWord_5610302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610302).length < 2 ^ (prefixWord ++ tailWord_5610302).sum := by decide
  have hdescent : baseEnd_5610302 < baseStart_5610302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610311 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5610311 : Nat := 118140960795 + 5610311 * 2 ^ 59
def prefixEnd_5610311 : Nat := 4983230072969 + 3 ^ 40 * 5610311 * 2
def baseEnd_5610311 : Nat := 2880786164206704366111155

theorem tailTrace_5610311 : CollatzResearch.WordTrace tailWord_5610311 prefixEnd_5610311 2880786164206704366111155 := by
  unfold tailWord_5610311
  simp only [CollatzResearch.WordTrace]
  refine ⟨204624852777808886680510787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136416568518539257787007191 204624852777808886680510787)
  ·
    refine ⟨306937279166713330020766181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204624852777808886680510787 306937279166713330020766181)
    ·
      refine ⟨57550739843758749378893659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306937279166713330020766181 57550739843758749378893659)
      ·
        refine ⟨86326109765638124068340489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57550739843758749378893659 86326109765638124068340489)
        ·
          refine ⟨64744582324228593051255367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86326109765638124068340489 64744582324228593051255367)
          ·
            refine ⟨97116873486342889576883051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64744582324228593051255367 97116873486342889576883051)
            ·
              refine ⟨145675310229514334365324577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97116873486342889576883051 145675310229514334365324577)
              ·
                refine ⟨109256482672135750773993433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145675310229514334365324577 109256482672135750773993433)
                ·
                  refine ⟨81942362004101813080495075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109256482672135750773993433 81942362004101813080495075)
                  ·
                    refine ⟨122913543006152719620742613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81942362004101813080495075 122913543006152719620742613)
                    ·
                      refine ⟨2880786164206704366111155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122913543006152719620742613 2880786164206704366111155)
                      ·
                        rfl

theorem cell23_5610311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5610311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610311 prefixEnd_5610311 := by exact prefixLift 5610311
  have htrace : WordTrace (prefixWord ++ tailWord_5610311) baseStart_5610311 baseEnd_5610311 := by
    simpa [prefixWord, tailWord_5610311, baseEnd_5610311] using wordTrace_append hprefix tailTrace_5610311
  have hstable : (prefixWord ++ tailWord_5610311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610311).length < 2 ^ (prefixWord ++ tailWord_5610311).sum := by decide
  have hdescent : baseEnd_5610311 < baseStart_5610311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610325 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 4, 3, 2]
def baseStart_5610325 : Nat := 118140960795 + 5610325 * 2 ^ 59
def prefixEnd_5610325 : Nat := 4983230072969 + 3 ^ 40 * 5610325 * 2
def baseEnd_5610325 : Nat := 2880793352935867311336091

theorem tailTrace_5610325 : CollatzResearch.WordTrace tailWord_5610325 prefixEnd_5610325 2880793352935867311336091 := by
  unfold tailWord_5610325
  simp only [CollatzResearch.WordTrace]
  refine ⟨204625363399758167071520429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136416908933172111381013619 204625363399758167071520429)
  ·
    refine ⟨76734511274909312651820161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204625363399758167071520429 76734511274909312651820161)
    ·
      refine ⟨57550883456181984488865121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76734511274909312651820161 57550883456181984488865121)
      ·
        refine ⟨43163162592136488366648841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57550883456181984488865121 43163162592136488366648841)
        ·
          refine ⟨32372371944102366274986631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43163162592136488366648841 32372371944102366274986631)
          ·
            refine ⟨48558557916153549412479947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32372371944102366274986631 48558557916153549412479947)
            ·
              refine ⟨72837836874230324118719921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48558557916153549412479947 72837836874230324118719921)
              ·
                refine ⟨54628377655672743089039941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72837836874230324118719921 54628377655672743089039941)
                ·
                  refine ⟨10242820810438639329194989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54628377655672743089039941 10242820810438639329194989)
                  ·
                    refine ⟨3841057803914489748448121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10242820810438639329194989 3841057803914489748448121)
                    ·
                      refine ⟨2880793352935867311336091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841057803914489748448121 2880793352935867311336091)
                      ·
                        rfl

theorem cell23_5610325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_5610325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610325 prefixEnd_5610325 := by exact prefixLift 5610325
  have htrace : WordTrace (prefixWord ++ tailWord_5610325) baseStart_5610325 baseEnd_5610325 := by
    simpa [prefixWord, tailWord_5610325, baseEnd_5610325] using wordTrace_append hprefix tailTrace_5610325
  have hstable : (prefixWord ++ tailWord_5610325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610325).length < 2 ^ (prefixWord ++ tailWord_5610325).sum := by decide
  have hdescent : baseEnd_5610325 < baseStart_5610325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610348 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_5610348 : Nat := 118140960795 + 5610348 * 2 ^ 59
def prefixEnd_5610348 : Nat := 4983230072969 + 3 ^ 40 * 5610348 * 2
def baseEnd_5610348 : Nat := 960268387663640240449495

theorem tailTrace_5610348 : CollatzResearch.WordTrace tailWord_5610348 prefixEnd_5610348 960268387663640240449495 := by
  unfold tailWord_5610348
  simp only [CollatzResearch.WordTrace]
  refine ⟨102313101139337420999803849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136417468185783227999738465 102313101139337420999803849)
  ·
    refine ⟨76734825854503065749852887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102313101139337420999803849 76734825854503065749852887)
    ·
      refine ⟨115102238781754598624779331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76734825854503065749852887 115102238781754598624779331)
      ·
        refine ⟨172653358172631897937168997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115102238781754598624779331 172653358172631897937168997)
        ·
          refine ⟨32372504657368480863219187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172653358172631897937168997 32372504657368480863219187)
          ·
            refine ⟨48558756986052721294828781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32372504657368480863219187 48558756986052721294828781)
            ·
              refine ⟨18209533869769770485560793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48558756986052721294828781 18209533869769770485560793)
              ·
                refine ⟨13657150402327327864170595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18209533869769770485560793 13657150402327327864170595)
                ·
                  refine ⟨20485725603490991796255893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13657150402327327864170595 20485725603490991796255893)
                  ·
                    refine ⟨960268387663640240449495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20485725603490991796255893 960268387663640240449495)
                    ·
                      rfl

theorem cell23_5610348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_5610348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610348 prefixEnd_5610348 := by exact prefixLift 5610348
  have htrace : WordTrace (prefixWord ++ tailWord_5610348) baseStart_5610348 baseEnd_5610348 := by
    simpa [prefixWord, tailWord_5610348, baseEnd_5610348] using wordTrace_append hprefix tailTrace_5610348
  have hstable : (prefixWord ++ tailWord_5610348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610348).length < 2 ^ (prefixWord ++ tailWord_5610348).sum := by decide
  have hdescent : baseEnd_5610348 < baseStart_5610348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610361 : List Nat := [1, 2, 1, 3, 2, 14]
def baseStart_5610361 : Nat := 118140960795 + 5610361 * 2 ^ 59
def prefixEnd_5610361 : Nat := 4983230072969 + 3 ^ 40 * 5610361 * 2
def baseEnd_5610361 : Nat := 11855192749956498643975

theorem tailTrace_5610361 : CollatzResearch.WordTrace tailWord_5610361 prefixEnd_5610361 11855192749956498643975 := by
  unfold tailWord_5610361
  simp only [CollatzResearch.WordTrace]
  refine ⟨204626676427627745219830937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136417784285085163479887291 204626676427627745219830937)
  ·
    refine ⟨153470007320720808914873203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204626676427627745219830937 153470007320720808914873203)
    ·
      refine ⟨230205010981081213372309805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153470007320720808914873203 230205010981081213372309805)
      ·
        refine ⟨86326879117905455014616177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230205010981081213372309805 86326879117905455014616177)
        ·
          refine ⟨64745159338429091260962133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86326879117905455014616177 64745159338429091260962133)
          ·
            refine ⟨11855192749956498643975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 64745159338429091260962133 11855192749956498643975)
            ·
              rfl

theorem cell23_5610361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 14].length) (baseStart_5610361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610361 prefixEnd_5610361 := by exact prefixLift 5610361
  have htrace : WordTrace (prefixWord ++ tailWord_5610361) baseStart_5610361 baseEnd_5610361 := by
    simpa [prefixWord, tailWord_5610361, baseEnd_5610361] using wordTrace_append hprefix tailTrace_5610361
  have hstable : (prefixWord ++ tailWord_5610361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610361).length < 2 ^ (prefixWord ++ tailWord_5610361).sum := by decide
  have hdescent : baseEnd_5610361 < baseStart_5610361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610365 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_5610365 : Nat := 118140960795 + 5610365 * 2 ^ 59
def prefixEnd_5610365 : Nat := 4983230072969 + 3 ^ 40 * 5610365 * 2
def baseEnd_5610365 : Nat := 960271297387349051611969

theorem tailTrace_5610365 : CollatzResearch.WordTrace tailWord_5610365 prefixEnd_5610365 960271297387349051611969 := by
  unfold tailWord_5610365
  simp only [CollatzResearch.WordTrace]
  refine ⟨204626822319613253902976549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136417881546408835935317699 204626822319613253902976549)
  ·
    refine ⟨38367529184927485106808103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204626822319613253902976549 38367529184927485106808103)
    ·
      refine ⟨57551293777391227660212155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38367529184927485106808103 57551293777391227660212155)
      ·
        refine ⟨86326940666086841490318233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57551293777391227660212155 86326940666086841490318233)
        ·
          refine ⟨64745205499565131117738675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86326940666086841490318233 64745205499565131117738675)
          ·
            refine ⟨97117808249347696676608013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64745205499565131117738675 97117808249347696676608013)
            ·
              refine ⟨36419178093505386253728005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97117808249347696676608013 36419178093505386253728005)
              ·
                refine ⟨6828595892532259922574001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36419178093505386253728005 6828595892532259922574001)
                ·
                  refine ⟨5121446919399194941930501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6828595892532259922574001 5121446919399194941930501)
                  ·
                    refine ⟨960271297387349051611969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121446919399194941930501 960271297387349051611969)
                    ·
                      rfl

theorem cell23_5610365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_5610365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610365 prefixEnd_5610365 := by exact prefixLift 5610365
  have htrace : WordTrace (prefixWord ++ tailWord_5610365) baseStart_5610365 baseEnd_5610365 := by
    simpa [prefixWord, tailWord_5610365, baseEnd_5610365] using wordTrace_append hprefix tailTrace_5610365
  have hstable : (prefixWord ++ tailWord_5610365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610365).length < 2 ^ (prefixWord ++ tailWord_5610365).sum := by decide
  have hdescent : baseEnd_5610365 < baseStart_5610365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610372 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_5610372 : Nat := 118140960795 + 5610372 * 2 ^ 59
def prefixEnd_5610372 : Nat := 4983230072969 + 3 ^ 40 * 5610372 * 2
def baseEnd_5610372 : Nat := 2880817486526628627448375

theorem tailTrace_5610372 : CollatzResearch.WordTrace tailWord_5610372 prefixEnd_5610372 2880817486526628627448375 := by
  unfold tailWord_5610372
  simp only [CollatzResearch.WordTrace]
  refine ⟨102313538815293947049240685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136418051753725262732320913 102313538815293947049240685)
  ·
    refine ⟨38367577055735230143465257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102313538815293947049240685 38367577055735230143465257)
    ·
      refine ⟨28775682791801422607598943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38367577055735230143465257 28775682791801422607598943)
      ·
        refine ⟨43163524187702133911398415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28775682791801422607598943 43163524187702133911398415)
        ·
          refine ⟨64745286281553200867097623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43163524187702133911398415 64745286281553200867097623)
          ·
            refine ⟨97117929422329801300646435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64745286281553200867097623 97117929422329801300646435)
            ·
              refine ⟨145676894133494701950969653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97117929422329801300646435 145676894133494701950969653)
              ·
                refine ⟨13657208825015128307903405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145676894133494701950969653 13657208825015128307903405)
                ·
                  refine ⟨5121453309380673115463777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13657208825015128307903405 5121453309380673115463777)
                  ·
                    refine ⟨3841089982035504836597833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5121453309380673115463777 3841089982035504836597833)
                    ·
                      refine ⟨2880817486526628627448375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841089982035504836597833 2880817486526628627448375)
                      ·
                        rfl

theorem cell23_5610372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_5610372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610372 prefixEnd_5610372 := by exact prefixLift 5610372
  have htrace : WordTrace (prefixWord ++ tailWord_5610372) baseStart_5610372 baseEnd_5610372 := by
    simpa [prefixWord, tailWord_5610372, baseEnd_5610372] using wordTrace_append hprefix tailTrace_5610372
  have hstable : (prefixWord ++ tailWord_5610372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610372).length < 2 ^ (prefixWord ++ tailWord_5610372).sum := by decide
  have hdescent : baseEnd_5610372 < baseStart_5610372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610375 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3]
def baseStart_5610375 : Nat := 118140960795 + 5610375 * 2 ^ 59
def prefixEnd_5610375 : Nat := 4983230072969 + 3 ^ 40 * 5610375 * 2
def baseEnd_5610375 : Nat := 2880819026968592115710861

theorem tailTrace_5610375 : CollatzResearch.WordTrace tailWord_5610375 prefixEnd_5610375 2880819026968592115710861 := by
  unfold tailWord_5610375
  simp only [CollatzResearch.WordTrace]
  refine ⟨204627187049577025610840579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136418124699718017073893719 204627187049577025610840579)
  ·
    refine ⟨306940780574365538416260869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204627187049577025610840579 306940780574365538416260869)
    ·
      refine ⟨57551396357693538453048913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306940780574365538416260869 57551396357693538453048913)
      ·
        refine ⟨43163547268270153839786685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57551396357693538453048913 43163547268270153839786685)
        ·
          refine ⟨16186330225601307689920007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43163547268270153839786685 16186330225601307689920007)
          ·
            refine ⟨24279495338401961534880011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186330225601307689920007 24279495338401961534880011)
            ·
              refine ⟨36419243007602942302320017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24279495338401961534880011 36419243007602942302320017)
              ·
                refine ⟨27314432255702206726740013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36419243007602942302320017 27314432255702206726740013)
                ·
                  refine ⟨10242912095888327522527505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27314432255702206726740013 10242912095888327522527505)
                  ·
                    refine ⟨7682184071916245641895629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10242912095888327522527505 7682184071916245641895629)
                    ·
                      refine ⟨2880819026968592115710861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682184071916245641895629 2880819026968592115710861)
                      ·
                        rfl

theorem cell23_5610375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_5610375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610375 prefixEnd_5610375 := by exact prefixLift 5610375
  have htrace : WordTrace (prefixWord ++ tailWord_5610375) baseStart_5610375 baseEnd_5610375 := by
    simpa [prefixWord, tailWord_5610375, baseEnd_5610375] using wordTrace_append hprefix tailTrace_5610375
  have hstable : (prefixWord ++ tailWord_5610375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610375).length < 2 ^ (prefixWord ++ tailWord_5610375).sum := by decide
  have hdescent : baseEnd_5610375 < baseStart_5610375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610415 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 5, 3, 2]
def baseStart_5610415 : Nat := 118140960795 + 5610415 * 2 ^ 59
def prefixEnd_5610415 : Nat := 4983230072969 + 3 ^ 40 * 5610415 * 2
def baseEnd_5610415 : Nat := 2880839566194771959210677

theorem tailTrace_5610415 : CollatzResearch.WordTrace tailWord_5610415 prefixEnd_5610415 2880839566194771959210677 := by
  unfold tailWord_5610415
  simp only [CollatzResearch.WordTrace]
  refine ⟨204628645969432112442296699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136419097312954741628197799 204628645969432112442296699)
  ·
    refine ⟨306942968954148168663445049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204628645969432112442296699 306942968954148168663445049)
    ·
      refine ⟨230207226715611126497583787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306942968954148168663445049 230207226715611126497583787)
      ·
        refine ⟨345310840073416689746375681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230207226715611126497583787 345310840073416689746375681)
        ·
          refine ⟨258983130055062517309781761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345310840073416689746375681 258983130055062517309781761)
          ·
            refine ⟨194237347541296887982336321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258983130055062517309781761 194237347541296887982336321)
            ·
              refine ⟨145678010655972665986752241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194237347541296887982336321 145678010655972665986752241)
              ·
                refine ⟨109258507991979499490064181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145678010655972665986752241 109258507991979499490064181)
                ·
                  refine ⟨10242985124248078077193517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109258507991979499490064181 10242985124248078077193517)
                  ·
                    refine ⟨3841119421593029278947569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10242985124248078077193517 3841119421593029278947569)
                    ·
                      refine ⟨2880839566194771959210677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841119421593029278947569 2880839566194771959210677)
                      ·
                        rfl

theorem cell23_5610415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 3, 2].length) (baseStart_5610415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610415 prefixEnd_5610415 := by exact prefixLift 5610415
  have htrace : WordTrace (prefixWord ++ tailWord_5610415) baseStart_5610415 baseEnd_5610415 := by
    simpa [prefixWord, tailWord_5610415, baseEnd_5610415] using wordTrace_append hprefix tailTrace_5610415
  have hstable : (prefixWord ++ tailWord_5610415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610415).length < 2 ^ (prefixWord ++ tailWord_5610415).sum := by decide
  have hdescent : baseEnd_5610415 < baseStart_5610415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610436 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_5610436 : Nat := 118140960795 + 5610436 * 2 ^ 59
def prefixEnd_5610436 : Nat := 4983230072969 + 3 ^ 40 * 5610436 * 2
def baseEnd_5610436 : Nat := 2880850349288516377048081

theorem tailTrace_5610436 : CollatzResearch.WordTrace tailWord_5610436 prefixEnd_5610436 2880850349288516377048081 := by
  unfold tailWord_5610436
  simp only [CollatzResearch.WordTrace]
  refine ⟨102314705951178016514405581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136419607934904022019207441 102314705951178016514405581)
  ·
    refine ⟨38368014731691756192902093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102314705951178016514405581 38368014731691756192902093)
    ·
      refine ⟨14388005524384408572338285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38368014731691756192902093 14388005524384408572338285)
      ·
        refine ⟨5395502071644153214626857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14388005524384408572338285 5395502071644153214626857)
        ·
          refine ⟨4046626553733114910970143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5395502071644153214626857 4046626553733114910970143)
          ·
            refine ⟨6069939830599672366455215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046626553733114910970143 6069939830599672366455215)
            ·
              refine ⟨9104909745899508549682823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6069939830599672366455215 9104909745899508549682823)
              ·
                refine ⟨13657364618849262824524235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9104909745899508549682823 13657364618849262824524235)
                ·
                  refine ⟨20486046928273894236786353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13657364618849262824524235 20486046928273894236786353)
                  ·
                    refine ⟨15364535196205420677589765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20486046928273894236786353 15364535196205420677589765)
                    ·
                      refine ⟨2880850349288516377048081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15364535196205420677589765 2880850349288516377048081)
                      ·
                        rfl

theorem cell23_5610436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_5610436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610436 prefixEnd_5610436 := by exact prefixLift 5610436
  have htrace : WordTrace (prefixWord ++ tailWord_5610436) baseStart_5610436 baseEnd_5610436 := by
    simpa [prefixWord, tailWord_5610436, baseEnd_5610436] using wordTrace_append hprefix tailTrace_5610436
  have hstable : (prefixWord ++ tailWord_5610436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610436).length < 2 ^ (prefixWord ++ tailWord_5610436).sum := by decide
  have hdescent : baseEnd_5610436 < baseStart_5610436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610448 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_5610448 : Nat := 118140960795 + 5610448 * 2 ^ 59
def prefixEnd_5610448 : Nat := 4983230072969 + 3 ^ 40 * 5610448 * 2
def baseEnd_5610448 : Nat := 2880856511056370330098025

theorem tailTrace_5610448 : CollatzResearch.WordTrace tailWord_5610448 prefixEnd_5610448 2880856511056370330098025 := by
  unfold tailWord_5610448
  simp only [CollatzResearch.WordTrace]
  refine ⟨102314924789156279539123999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136419899718875039385498665 102314924789156279539123999)
  ·
    refine ⟨153472387183734419308685999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102314924789156279539123999 153472387183734419308685999)
    ·
      refine ⟨230208580775601628963028999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153472387183734419308685999 230208580775601628963028999)
      ·
        refine ⟨345312871163402443444543499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230208580775601628963028999 345312871163402443444543499)
        ·
          refine ⟨517969306745103665166815249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345312871163402443444543499 517969306745103665166815249)
          ·
            refine ⟨388476980058827748875111437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 517969306745103665166815249 388476980058827748875111437)
            ·
              refine ⟨145678867522060405828166789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388476980058827748875111437 145678867522060405828166789)
              ·
                refine ⟨27314787660386326092781273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145678867522060405828166789 27314787660386326092781273)
                ·
                  refine ⟨20486090745289744569585955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27314787660386326092781273 20486090745289744569585955)
                  ·
                    refine ⟨30729136117934616854378933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20486090745289744569585955 30729136117934616854378933)
                    ·
                      refine ⟨2880856511056370330098025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30729136117934616854378933 2880856511056370330098025)
                      ·
                        rfl

theorem cell23_5610448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_5610448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610448 prefixEnd_5610448 := by exact prefixLift 5610448
  have htrace : WordTrace (prefixWord ++ tailWord_5610448) baseStart_5610448 baseEnd_5610448 := by
    simpa [prefixWord, tailWord_5610448, baseEnd_5610448] using wordTrace_append hprefix tailTrace_5610448
  have hstable : (prefixWord ++ tailWord_5610448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610448).length < 2 ^ (prefixWord ++ tailWord_5610448).sum := by decide
  have hdescent : baseEnd_5610448 < baseStart_5610448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610466 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_5610466 : Nat := 118140960795 + 5610466 * 2 ^ 59
def prefixEnd_5610466 : Nat := 4983230072969 + 3 ^ 40 * 5610466 * 2
def baseEnd_5610466 : Nat := 2880865753708151259672943

theorem tailTrace_5610466 : CollatzResearch.WordTrace tailWord_5610466 prefixEnd_5610466 2880865753708151259672943 := by
  unfold tailWord_5610466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51157626523061837038100813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136420337394831565434935501 51157626523061837038100813)
  ·
    refine ⟨19184109946148188889287805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51157626523061837038100813 19184109946148188889287805)
    ·
      refine ⟨7194041229805570833482927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19184109946148188889287805 7194041229805570833482927)
      ·
        refine ⟨10791061844708356250224391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194041229805570833482927 10791061844708356250224391)
        ·
          refine ⟨16186592767062534375336587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10791061844708356250224391 16186592767062534375336587)
          ·
            refine ⟨24279889150593801563004881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186592767062534375336587 24279889150593801563004881)
            ·
              refine ⟨18209916862945351172253661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24279889150593801563004881 18209916862945351172253661)
              ·
                refine ⟨6828718823604506689595123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18209916862945351172253661 6828718823604506689595123)
                ·
                  refine ⟨10243078235406760034392685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828718823604506689595123 10243078235406760034392685)
                  ·
                    refine ⟨3841154338277535012897257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10243078235406760034392685 3841154338277535012897257)
                    ·
                      refine ⟨2880865753708151259672943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841154338277535012897257 2880865753708151259672943)
                      ·
                        rfl

theorem cell23_5610466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_5610466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610466 prefixEnd_5610466 := by exact prefixLift 5610466
  have htrace : WordTrace (prefixWord ++ tailWord_5610466) baseStart_5610466 baseEnd_5610466 := by
    simpa [prefixWord, tailWord_5610466, baseEnd_5610466] using wordTrace_append hprefix tailTrace_5610466
  have hstable : (prefixWord ++ tailWord_5610466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610466).length < 2 ^ (prefixWord ++ tailWord_5610466).sum := by decide
  have hdescent : baseEnd_5610466 < baseStart_5610466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610532 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_5610532 : Nat := 118140960795 + 5610532 * 2 ^ 59
def prefixEnd_5610532 : Nat := 4983230072969 + 3 ^ 40 * 5610532 * 2
def baseEnd_5610532 : Nat := 960299881143782667149213

theorem tailTrace_5610532 : CollatzResearch.WordTrace tailWord_5610532 prefixEnd_5610532 960299881143782667149213 := by
  unfold tailWord_5610532
  simp only [CollatzResearch.WordTrace]
  refine ⟨102316456655004120712152925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136421942206672160949537233 102316456655004120712152925)
  ·
    refine ⟨38368671245626545267057347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102316456655004120712152925 38368671245626545267057347)
    ·
      refine ⟨57553006868439817900586021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38368671245626545267057347 57553006868439817900586021)
      ·
        refine ⟨10791188787832465856359879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57553006868439817900586021 10791188787832465856359879)
        ·
          refine ⟨16186783181748698784539819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10791188787832465856359879 16186783181748698784539819)
          ·
            refine ⟨24280174772623048176809729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186783181748698784539819 24280174772623048176809729)
            ·
              refine ⟨18210131079467286132607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24280174772623048176809729 18210131079467286132607297)
              ·
                refine ⟨13657598309600464599455473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18210131079467286132607297 13657598309600464599455473)
                ·
                  refine ⟨10243198732200348449591605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13657598309600464599455473 10243198732200348449591605)
                  ·
                    refine ⟨960299881143782667149213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10243198732200348449591605 960299881143782667149213)
                    ·
                      rfl

theorem cell23_5610532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_5610532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610532 prefixEnd_5610532 := by exact prefixLift 5610532
  have htrace : WordTrace (prefixWord ++ tailWord_5610532) baseStart_5610532 baseEnd_5610532 := by
    simpa [prefixWord, tailWord_5610532, baseEnd_5610532] using wordTrace_append hprefix tailTrace_5610532
  have hstable : (prefixWord ++ tailWord_5610532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610532).length < 2 ^ (prefixWord ++ tailWord_5610532).sum := by decide
  have hdescent : baseEnd_5610532 < baseStart_5610532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610552 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_5610552 : Nat := 118140960795 + 5610552 * 2 ^ 59
def prefixEnd_5610552 : Nat := 4983230072969 + 3 ^ 40 * 5610552 * 2
def baseEnd_5610552 : Nat := 2880909913044437923197547

theorem tailTrace_5610552 : CollatzResearch.WordTrace tailWord_5610552 prefixEnd_5610552 2880909913044437923197547 := by
  unfold tailWord_5610552
  simp only [CollatzResearch.WordTrace]
  refine ⟨102316821384967892420016955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136422428513290523226689273 102316821384967892420016955)
  ·
    refine ⟨153475232077451838630025433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102316821384967892420016955 153475232077451838630025433)
    ·
      refine ⟨115106424058088878972519075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153475232077451838630025433 115106424058088878972519075)
      ·
        refine ⟨172659636087133318458778613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115106424058088878972519075 172659636087133318458778613)
        ·
          refine ⟨16186840883168748605510495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172659636087133318458778613 16186840883168748605510495)
          ·
            refine ⟨24280261324753122908265743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16186840883168748605510495 24280261324753122908265743)
            ·
              refine ⟨36420391987129684362398615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24280261324753122908265743 36420391987129684362398615)
              ·
                refine ⟨54630587980694526543597923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36420391987129684362398615 54630587980694526543597923)
                ·
                  refine ⟨81945881971041789815396885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54630587980694526543597923 81945881971041789815396885)
                  ·
                    refine ⟨3841213217392583897596729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81945881971041789815396885 3841213217392583897596729)
                    ·
                      refine ⟨2880909913044437923197547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841213217392583897596729 2880909913044437923197547)
                      ·
                        rfl

theorem cell23_5610552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_5610552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610552 prefixEnd_5610552 := by exact prefixLift 5610552
  have htrace : WordTrace (prefixWord ++ tailWord_5610552) baseStart_5610552 baseEnd_5610552 := by
    simpa [prefixWord, tailWord_5610552, baseEnd_5610552] using wordTrace_append hprefix tailTrace_5610552
  have hstable : (prefixWord ++ tailWord_5610552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610552).length < 2 ^ (prefixWord ++ tailWord_5610552).sum := by decide
  have hdescent : baseEnd_5610552 < baseStart_5610552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610566 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_5610566 : Nat := 118140960795 + 5610566 * 2 ^ 59
def prefixEnd_5610566 : Nat := 4983230072969 + 3 ^ 40 * 5610566 * 2
def baseEnd_5610566 : Nat := 960305700591200289474161

theorem tailTrace_5610566 : CollatzResearch.WordTrace tailWord_5610566 prefixEnd_5610566 960305700591200289474161 := by
  unfold tailWord_5610566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6394817293496408288470111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136422768927923376820695701 6394817293496408288470111)
  ·
    refine ⟨9592225940244612432705167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6394817293496408288470111 9592225940244612432705167)
    ·
      refine ⟨14388338910366918649057751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9592225940244612432705167 14388338910366918649057751)
      ·
        refine ⟨21582508365550377973586627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14388338910366918649057751 21582508365550377973586627)
        ·
          refine ⟨32373762548325566960379941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21582508365550377973586627 32373762548325566960379941)
          ·
            refine ⟨6070080477811043805071239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32373762548325566960379941 6070080477811043805071239)
            ·
              refine ⟨9105120716716565707606859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070080477811043805071239 9105120716716565707606859)
              ·
                refine ⟨13657681075074848561410289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105120716716565707606859 13657681075074848561410289)
                ·
                  refine ⟨10243260806306136421057717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13657681075074848561410289 10243260806306136421057717)
                  ·
                    refine ⟨960305700591200289474161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10243260806306136421057717 960305700591200289474161)
                    ·
                      rfl

theorem cell23_5610566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_5610566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610566 prefixEnd_5610566 := by exact prefixLift 5610566
  have htrace : WordTrace (prefixWord ++ tailWord_5610566) baseStart_5610566 baseEnd_5610566 := by
    simpa [prefixWord, tailWord_5610566, baseEnd_5610566] using wordTrace_append hprefix tailTrace_5610566
  have hstable : (prefixWord ++ tailWord_5610566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610566).length < 2 ^ (prefixWord ++ tailWord_5610566).sum := by decide
  have hdescent : baseEnd_5610566 < baseStart_5610566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610635 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 6]
def baseStart_5610635 : Nat := 118140960795 + 5610635 * 2 ^ 59
def prefixEnd_5610635 : Nat := 4983230072969 + 3 ^ 40 * 5610635 * 2
def baseEnd_5610635 : Nat := 960317510646253699486555

theorem tailTrace_5610635 : CollatzResearch.WordTrace tailWord_5610635 prefixEnd_5610635 960317510646253699486555 := by
  unfold tailWord_5610635
  simp only [CollatzResearch.WordTrace]
  refine ⟨204636670028635090015305359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136424446685756726676870239 204636670028635090015305359)
  ·
    refine ⟨306955005042952635022958039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204636670028635090015305359 306955005042952635022958039)
    ·
      refine ⟨460432507564428952534437059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306955005042952635022958039 460432507564428952534437059)
      ·
        refine ⟨690648761346643428801655589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460432507564428952534437059 690648761346643428801655589)
        ·
          refine ⟨129496642752495642900310423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 690648761346643428801655589 129496642752495642900310423)
          ·
            refine ⟨194244964128743464350465635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129496642752495642900310423 194244964128743464350465635)
            ·
              refine ⟨291367446193115196525698453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194244964128743464350465635 291367446193115196525698453)
              ·
                refine ⟨13657849040302274837142115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291367446193115196525698453 13657849040302274837142115)
                ·
                  refine ⟨20486773560453412255713173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13657849040302274837142115 20486773560453412255713173)
                  ·
                    refine ⟨960317510646253699486555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20486773560453412255713173 960317510646253699486555)
                    ·
                      rfl

theorem cell23_5610635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 6].length) (baseStart_5610635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610635 prefixEnd_5610635 := by exact prefixLift 5610635
  have htrace : WordTrace (prefixWord ++ tailWord_5610635) baseStart_5610635 baseEnd_5610635 := by
    simpa [prefixWord, tailWord_5610635, baseEnd_5610635] using wordTrace_append hprefix tailTrace_5610635
  have hstable : (prefixWord ++ tailWord_5610635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610635).length < 2 ^ (prefixWord ++ tailWord_5610635).sum := by decide
  have hdescent : baseEnd_5610635 < baseStart_5610635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610653 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_5610653 : Nat := 118140960795 + 5610653 * 2 ^ 59
def prefixEnd_5610653 : Nat := 4983230072969 + 3 ^ 40 * 5610653 * 2
def baseEnd_5610653 : Nat := 2880961774590542028034583

theorem tailTrace_5610653 : CollatzResearch.WordTrace tailWord_5610653 prefixEnd_5610653 2880961774590542028034583 := by
  unfold tailWord_5610653
  simp only [CollatzResearch.WordTrace]
  refine ⟨204637326542569879089460613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136424884361713252726307075 204637326542569879089460613)
  ·
    refine ⟨38369498726731852329273865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204637326542569879089460613 38369498726731852329273865)
    ·
      refine ⟨28777124045048889246955399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38369498726731852329273865 28777124045048889246955399)
      ·
        refine ⟨43165686067573333870433099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28777124045048889246955399 43165686067573333870433099)
        ·
          refine ⟨64748529101360000805649649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43165686067573333870433099 64748529101360000805649649)
          ·
            refine ⟨48561396826020000604237237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64748529101360000805649649 48561396826020000604237237)
            ·
              refine ⟨4552630952439375056647241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48561396826020000604237237 4552630952439375056647241)
              ·
                refine ⟨3414473214329531292485431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552630952439375056647241 3414473214329531292485431)
                ·
                  refine ⟨5121709821494296938728147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414473214329531292485431 5121709821494296938728147)
                  ·
                    refine ⟨7682564732241445408092221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121709821494296938728147 7682564732241445408092221)
                    ·
                      refine ⟨2880961774590542028034583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682564732241445408092221 2880961774590542028034583)
                      ·
                        rfl

theorem cell23_5610653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_5610653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610653 prefixEnd_5610653 := by exact prefixLift 5610653
  have htrace : WordTrace (prefixWord ++ tailWord_5610653) baseStart_5610653 baseEnd_5610653 := by
    simpa [prefixWord, tailWord_5610653, baseEnd_5610653] using wordTrace_append hprefix tailTrace_5610653
  have hstable : (prefixWord ++ tailWord_5610653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610653).length < 2 ^ (prefixWord ++ tailWord_5610653).sum := by decide
  have hdescent : baseEnd_5610653 < baseStart_5610653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610689 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5610689 : Nat := 118140960795 + 5610689 * 2 ^ 59
def prefixEnd_5610689 : Nat := 4983230072969 + 3 ^ 40 * 5610689 * 2
def baseEnd_5610689 : Nat := 2880980259894103887184417

theorem tailTrace_5610689 : CollatzResearch.WordTrace tailWord_5610689 prefixEnd_5610689 2880980259894103887184417 := by
  unfold tailWord_5610689
  simp only [CollatzResearch.WordTrace]
  refine ⟨204638639570439457237771121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136425759713626304825180747 204638639570439457237771121)
  ·
    refine ⟨153478979677829592928328341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204638639570439457237771121 153478979677829592928328341)
    ·
      refine ⟨7194327172398262168515391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153478979677829592928328341 7194327172398262168515391)
      ·
        refine ⟨10791490758597393252773087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194327172398262168515391 10791490758597393252773087)
        ·
          refine ⟨16187236137896089879159631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10791490758597393252773087 16187236137896089879159631)
          ·
            refine ⟨24280854206844134818739447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16187236137896089879159631 24280854206844134818739447)
            ·
              refine ⟨36421281310266202228109171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24280854206844134818739447 36421281310266202228109171)
              ·
                refine ⟨54631921965399303342163757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36421281310266202228109171 54631921965399303342163757)
                ·
                  refine ⟨20486970737024738753311409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54631921965399303342163757 20486970737024738753311409)
                  ·
                    refine ⟨15365228052768554064983557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20486970737024738753311409 15365228052768554064983557)
                    ·
                      refine ⟨2880980259894103887184417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15365228052768554064983557 2880980259894103887184417)
                      ·
                        rfl

theorem cell23_5610689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5610689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610689 prefixEnd_5610689 := by exact prefixLift 5610689
  have htrace : WordTrace (prefixWord ++ tailWord_5610689) baseStart_5610689 baseEnd_5610689 := by
    simpa [prefixWord, tailWord_5610689, baseEnd_5610689] using wordTrace_append hprefix tailTrace_5610689
  have hstable : (prefixWord ++ tailWord_5610689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610689).length < 2 ^ (prefixWord ++ tailWord_5610689).sum := by decide
  have hdescent : baseEnd_5610689 < baseStart_5610689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610690 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5610690 : Nat := 118140960795 + 5610690 * 2 ^ 59
def prefixEnd_5610690 : Nat := 4983230072969 + 3 ^ 40 * 5610690 * 2
def baseEnd_5610690 : Nat := 960326924458252794423971

theorem tailTrace_5610690 : CollatzResearch.WordTrace tailWord_5610690 prefixEnd_5610690 960326924458252794423971 := by
  unfold tailWord_5610690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51159669010858958602139381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136425784028957222939038349 51159669010858958602139381)
  ·
    refine ⟨4796218969768027368950567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51159669010858958602139381 4796218969768027368950567)
    ·
      refine ⟨7194328454652041053425851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796218969768027368950567 7194328454652041053425851)
      ·
        refine ⟨10791492681978061580138777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194328454652041053425851 10791492681978061580138777)
        ·
          refine ⟨8093619511483546185104083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10791492681978061580138777 8093619511483546185104083)
          ·
            refine ⟨12140429267225319277656125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093619511483546185104083 12140429267225319277656125)
            ·
              refine ⟨4552660975209494729121047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12140429267225319277656125 4552660975209494729121047)
              ·
                refine ⟨6828991462814242093681571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552660975209494729121047 6828991462814242093681571)
                ·
                  refine ⟨10243487194221363140522357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828991462814242093681571 10243487194221363140522357)
                  ·
                    refine ⟨960326924458252794423971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10243487194221363140522357 960326924458252794423971)
                    ·
                      rfl

theorem cell23_5610690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5610690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610690 prefixEnd_5610690 := by exact prefixLift 5610690
  have htrace : WordTrace (prefixWord ++ tailWord_5610690) baseStart_5610690 baseEnd_5610690 := by
    simpa [prefixWord, tailWord_5610690, baseEnd_5610690] using wordTrace_append hprefix tailTrace_5610690
  have hstable : (prefixWord ++ tailWord_5610690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610690).length < 2 ^ (prefixWord ++ tailWord_5610690).sum := by decide
  have hdescent : baseEnd_5610690 < baseStart_5610690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610695 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 7]
def baseStart_5610695 : Nat := 118140960795 + 5610695 * 2 ^ 59
def prefixEnd_5610695 : Nat := 4983230072969 + 3 ^ 40 * 5610695 * 2
def baseEnd_5610695 : Nat := 960327780259343621236463

theorem tailTrace_5610695 : CollatzResearch.WordTrace tailWord_5610695 prefixEnd_5610695 960327780259343621236463 := by
  unfold tailWord_5610695
  simp only [CollatzResearch.WordTrace]
  refine ⟨204638858408417720262489539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136425905605611813508326359 204638858408417720262489539)
  ·
    refine ⟨306958287612626580393734309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204638858408417720262489539 306958287612626580393734309)
    ·
      refine ⟨57554678927367483823825183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 306958287612626580393734309 57554678927367483823825183)
      ·
        refine ⟨86332018391051225735737775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57554678927367483823825183 86332018391051225735737775)
        ·
          refine ⟨129498027586576838603606663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86332018391051225735737775 129498027586576838603606663)
          ·
            refine ⟨194247041379865257905409995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129498027586576838603606663 194247041379865257905409995)
            ·
              refine ⟨291370562069797886858114993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194247041379865257905409995 291370562069797886858114993)
              ·
                refine ⟨218527921552348415143586245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291370562069797886858114993 218527921552348415143586245)
                ·
                  refine ⟨40973985291065327839422421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218527921552348415143586245 40973985291065327839422421)
                  ·
                    refine ⟨960327780259343621236463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40973985291065327839422421 960327780259343621236463)
                    ·
                      rfl

theorem cell23_5610695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_5610695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610695 prefixEnd_5610695 := by exact prefixLift 5610695
  have htrace : WordTrace (prefixWord ++ tailWord_5610695) baseStart_5610695 baseEnd_5610695 := by
    simpa [prefixWord, tailWord_5610695, baseEnd_5610695] using wordTrace_append hprefix tailTrace_5610695
  have hstable : (prefixWord ++ tailWord_5610695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610695).length < 2 ^ (prefixWord ++ tailWord_5610695).sum := by decide
  have hdescent : baseEnd_5610695 < baseStart_5610695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610719 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 3, 3, 2]
def baseStart_5610719 : Nat := 118140960795 + 5610719 * 2 ^ 59
def prefixEnd_5610719 : Nat := 4983230072969 + 3 ^ 40 * 5610719 * 2
def baseEnd_5610719 : Nat := 2880995664313738769809279

theorem tailTrace_5610719 : CollatzResearch.WordTrace tailWord_5610719 prefixEnd_5610719 2880995664313738769809279 := by
  unfold tailWord_5610719
  simp only [CollatzResearch.WordTrace]
  refine ⟨204639733760330772361363211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136426489173553848240908807 204639733760330772361363211)
  ·
    refine ⟨306959600640496158542044817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204639733760330772361363211 306959600640496158542044817)
    ·
      refine ⟨230219700480372118906533613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306959600640496158542044817 230219700480372118906533613)
      ·
        refine ⟨86332387680139544589950105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230219700480372118906533613 86332387680139544589950105)
        ·
          refine ⟨64749290760104658442462579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86332387680139544589950105 64749290760104658442462579)
          ·
            refine ⟨97123936140156987663693869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64749290760104658442462579 97123936140156987663693869)
            ·
              refine ⟨36421476052558870373885201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97123936140156987663693869 36421476052558870373885201)
              ·
                refine ⟨27316107039419152780413901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36421476052558870373885201 27316107039419152780413901)
                ·
                  refine ⟨10243540139782182292655213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27316107039419152780413901 10243540139782182292655213)
                  ·
                    refine ⟨3841327552418318359745705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10243540139782182292655213 3841327552418318359745705)
                    ·
                      refine ⟨2880995664313738769809279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841327552418318359745705 2880995664313738769809279)
                      ·
                        rfl

theorem cell23_5610719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_5610719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610719 prefixEnd_5610719 := by exact prefixLift 5610719
  have htrace : WordTrace (prefixWord ++ tailWord_5610719) baseStart_5610719 baseEnd_5610719 := by
    simpa [prefixWord, tailWord_5610719, baseEnd_5610719] using wordTrace_append hprefix tailTrace_5610719
  have hstable : (prefixWord ++ tailWord_5610719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610719).length < 2 ^ (prefixWord ++ tailWord_5610719).sum := by decide
  have hdescent : baseEnd_5610719 < baseStart_5610719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610742 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_5610742 : Nat := 118140960795 + 5610742 * 2 ^ 59
def prefixEnd_5610742 : Nat := 4983230072969 + 3 ^ 40 * 5610742 * 2
def baseEnd_5610742 : Nat := 960335824789597393273891

theorem tailTrace_5610742 : CollatzResearch.WordTrace tailWord_5610742 prefixEnd_5610742 960335824789597393273891 := by
  unfold tailWord_5610742
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790035789952965455590655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136427048426164964859633653 12790035789952965455590655)
  ·
    refine ⟨19185053684929448183385983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12790035789952965455590655 19185053684929448183385983)
    ·
      refine ⟨28777580527394172275078975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19185053684929448183385983 28777580527394172275078975)
      ·
        refine ⟨43166370791091258412618463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28777580527394172275078975 43166370791091258412618463)
        ·
          refine ⟨64749556186636887618927695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43166370791091258412618463 64749556186636887618927695)
          ·
            refine ⟨97124334279955331428391543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64749556186636887618927695 97124334279955331428391543)
            ·
              refine ⟨145686501419932997142587315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97124334279955331428391543 145686501419932997142587315)
              ·
                refine ⟨218529752129899495713880973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145686501419932997142587315 218529752129899495713880973)
                ·
                  refine ⟨81948657048712310892705365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218529752129899495713880973 81948657048712310892705365)
                  ·
                    refine ⟨960335824789597393273891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 81948657048712310892705365 960335824789597393273891)
                    ·
                      rfl

theorem cell23_5610742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_5610742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610742 prefixEnd_5610742 := by exact prefixLift 5610742
  have htrace : WordTrace (prefixWord ++ tailWord_5610742) baseStart_5610742 baseEnd_5610742 := by
    simpa [prefixWord, tailWord_5610742, baseEnd_5610742] using wordTrace_append hprefix tailTrace_5610742
  have hstable : (prefixWord ++ tailWord_5610742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610742).length < 2 ^ (prefixWord ++ tailWord_5610742).sum := by decide
  have hdescent : baseEnd_5610742 < baseStart_5610742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610753 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_5610753 : Nat := 118140960795 + 5610753 * 2 ^ 59
def prefixEnd_5610753 : Nat := 4983230072969 + 3 ^ 40 * 5610753 * 2
def baseEnd_5610753 : Nat := 2881013122655991636784123

theorem tailTrace_5610753 : CollatzResearch.WordTrace tailWord_5610753 prefixEnd_5610753 2881013122655991636784123 := by
  unfold tailWord_5610753
  simp only [CollatzResearch.WordTrace]
  refine ⟨204640973842207596168100913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136427315894805064112067275 204640973842207596168100913)
  ·
    refine ⟨153480730381655697126075685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204640973842207596168100913 153480730381655697126075685)
    ·
      refine ⟨28777636946560443211139191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153480730381655697126075685 28777636946560443211139191)
      ·
        refine ⟨43166455419840664816708787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28777636946560443211139191 43166455419840664816708787)
        ·
          refine ⟨64749683129760997225063181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43166455419840664816708787 64749683129760997225063181)
          ·
            refine ⟨24281131173660373959398693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64749683129760997225063181 24281131173660373959398693)
            ·
              refine ⟨4552712095061320117387255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24281131173660373959398693 4552712095061320117387255)
              ·
                refine ⟨6829068142591980176080883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4552712095061320117387255 6829068142591980176080883)
                ·
                  refine ⟨10243602213887970264121325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829068142591980176080883 10243602213887970264121325)
                  ·
                    refine ⟨3841350830207988849045497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10243602213887970264121325 3841350830207988849045497)
                    ·
                      refine ⟨2881013122655991636784123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841350830207988849045497 2881013122655991636784123)
                      ·
                        rfl

theorem cell23_5610753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_5610753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610753 prefixEnd_5610753 := by exact prefixLift 5610753
  have htrace : WordTrace (prefixWord ++ tailWord_5610753) baseStart_5610753 baseEnd_5610753 := by
    simpa [prefixWord, tailWord_5610753, baseEnd_5610753] using wordTrace_append hprefix tailTrace_5610753
  have hstable : (prefixWord ++ tailWord_5610753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610753).length < 2 ^ (prefixWord ++ tailWord_5610753).sum := by decide
  have hdescent : baseEnd_5610753 < baseStart_5610753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610760 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_5610760 : Nat := 118140960795 + 5610760 * 2 ^ 59
def prefixEnd_5610760 : Nat := 4983230072969 + 3 ^ 40 * 5610760 * 2
def baseEnd_5610760 : Nat := 2881016717020573109396591

theorem tailTrace_5610760 : CollatzResearch.WordTrace tailWord_5610760 prefixEnd_5610760 2881016717020573109396591 := by
  unfold tailWord_5610760
  simp only [CollatzResearch.WordTrace]
  refine ⟨102320614576591118181802867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136427486102121490909070489 102320614576591118181802867)
  ·
    refine ⟨153480921864886677272704301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102320614576591118181802867 153480921864886677272704301)
    ·
      refine ⟨57555345699332503977264113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153480921864886677272704301 57555345699332503977264113)
      ·
        refine ⟨43166509274499377982948085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57555345699332503977264113 43166509274499377982948085)
        ·
          refine ⟨4046860244484316685901383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43166509274499377982948085 4046860244484316685901383)
          ·
            refine ⟨6070290366726475028852075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046860244484316685901383 6070290366726475028852075)
            ·
              refine ⟨9105435550089712543278113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070290366726475028852075 9105435550089712543278113)
              ·
                refine ⟨6829076662567284407458585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9105435550089712543278113 6829076662567284407458585)
                ·
                  refine ⟨5121807496925463305593939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6829076662567284407458585 5121807496925463305593939)
                  ·
                    refine ⟨7682711245388194958390909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121807496925463305593939 7682711245388194958390909)
                    ·
                      refine ⟨2881016717020573109396591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682711245388194958390909 2881016717020573109396591)
                      ·
                        rfl

theorem cell23_5610760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_5610760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610760 prefixEnd_5610760 := by exact prefixLift 5610760
  have htrace : WordTrace (prefixWord ++ tailWord_5610760) baseStart_5610760 baseEnd_5610760 := by
    simpa [prefixWord, tailWord_5610760, baseEnd_5610760] using wordTrace_append hprefix tailTrace_5610760
  have hstable : (prefixWord ++ tailWord_5610760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610760).length < 2 ^ (prefixWord ++ tailWord_5610760).sum := by decide
  have hdescent : baseEnd_5610760 < baseStart_5610760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610783 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 4, 2]
def baseStart_5610783 : Nat := 118140960795 + 5610783 * 2 ^ 59
def prefixEnd_5610783 : Nat := 4983230072969 + 3 ^ 40 * 5610783 * 2
def baseEnd_5610783 : Nat := 2881028527075626519408985

theorem tailTrace_5610783 : CollatzResearch.WordTrace tailWord_5610783 prefixEnd_5610783 2881028527075626519408985 := by
  unfold tailWord_5610783
  simp only [CollatzResearch.WordTrace]
  refine ⟨204642068032098911291693003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136428045354732607527795335 204642068032098911291693003)
  ·
    refine ⟨306963102048148366937539505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204642068032098911291693003 306963102048148366937539505)
    ·
      refine ⟨230222326536111275203154629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306963102048148366937539505 230222326536111275203154629)
      ·
        refine ⟨43166686225520864100591493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230222326536111275203154629 43166686225520864100591493)
        ·
          refine ⟨8093753667285162018860905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43166686225520864100591493 8093753667285162018860905)
          ·
            refine ⟨6070315250463871514145679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8093753667285162018860905 6070315250463871514145679)
            ·
              refine ⟨9105472875695807271218519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070315250463871514145679 9105472875695807271218519)
              ·
                refine ⟨13658209313543710906827779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105472875695807271218519 13658209313543710906827779)
                ·
                  refine ⟨20487313970315566360241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13658209313543710906827779 20487313970315566360241669)
                  ·
                    refine ⟨3841371369434168692545313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20487313970315566360241669 3841371369434168692545313)
                    ·
                      refine ⟨2881028527075626519408985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841371369434168692545313 2881028527075626519408985)
                      ·
                        rfl

theorem cell23_5610783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_5610783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610783 prefixEnd_5610783 := by exact prefixLift 5610783
  have htrace : WordTrace (prefixWord ++ tailWord_5610783) baseStart_5610783 baseEnd_5610783 := by
    simpa [prefixWord, tailWord_5610783, baseEnd_5610783] using wordTrace_append hprefix tailTrace_5610783
  have hstable : (prefixWord ++ tailWord_5610783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610783).length < 2 ^ (prefixWord ++ tailWord_5610783).sum := by decide
  have hdescent : baseEnd_5610783 < baseStart_5610783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610849 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 3, 4]
def baseStart_5610849 : Nat := 118140960795 + 5610849 * 2 ^ 59
def prefixEnd_5610849 : Nat := 4983230072969 + 3 ^ 40 * 5610849 * 2
def baseEnd_5610849 : Nat := 960354138932941087061227

theorem tailTrace_5610849 : CollatzResearch.WordTrace tailWord_5610849 prefixEnd_5610849 960354138932941087061227 := by
  unfold tailWord_5610849
  simp only [CollatzResearch.WordTrace]
  refine ⟨204644475249859804563595601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136429650166573203042397067 204644475249859804563595601)
  ·
    refine ⟨153483356437394853422696701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204644475249859804563595601 153483356437394853422696701)
    ·
      refine ⟨57556258664023070033511263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153483356437394853422696701 57556258664023070033511263)
      ·
        refine ⟨86334387996034605050266895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57556258664023070033511263 86334387996034605050266895)
        ·
          refine ⟨129501581994051907575400343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86334387996034605050266895 129501581994051907575400343)
          ·
            refine ⟨194252372991077861363100515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129501581994051907575400343 194252372991077861363100515)
            ·
              refine ⟨291378559486616792044650773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194252372991077861363100515 291378559486616792044650773)
              ·
                refine ⟨13658369975935162127093005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291378559486616792044650773 13658369975935162127093005)
                ·
                  refine ⟨5121888740975685797659877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13658369975935162127093005 5121888740975685797659877)
                  ·
                    refine ⟨960354138932941087061227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121888740975685797659877 960354138932941087061227)
                    ·
                      rfl

theorem cell23_5610849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_5610849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610849 prefixEnd_5610849 := by exact prefixLift 5610849
  have htrace : WordTrace (prefixWord ++ tailWord_5610849) baseStart_5610849 baseEnd_5610849 := by
    simpa [prefixWord, tailWord_5610849, baseEnd_5610849] using wordTrace_append hprefix tailTrace_5610849
  have hstable : (prefixWord ++ tailWord_5610849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610849).length < 2 ^ (prefixWord ++ tailWord_5610849).sum := by decide
  have hdescent : baseEnd_5610849 < baseStart_5610849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610883 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 1, 4]
def baseStart_5610883 : Nat := 118140960795 + 5610883 * 2 ^ 59
def prefixEnd_5610883 : Nat := 4983230072969 + 3 ^ 40 * 5610883 * 2
def baseEnd_5610883 : Nat := 960359958380358709386175

theorem tailTrace_5610883 : CollatzResearch.WordTrace tailWord_5610883 prefixEnd_5610883 960359958380358709386175 := by
  unfold tailWord_5610883
  simp only [CollatzResearch.WordTrace]
  refine ⟨204645715331736628370333303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136430476887824418913555535 204645715331736628370333303)
  ·
    refine ⟨306968572997604942555499955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204645715331736628370333303 306968572997604942555499955)
    ·
      refine ⟨460452859496407413833249933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306968572997604942555499955 460452859496407413833249933)
      ·
        refine ⟨172669822311152780187468725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460452859496407413833249933 172669822311152780187468725)
        ·
          refine ⟨16187795841670573142575193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172669822311152780187468725 16187795841670573142575193)
          ·
            refine ⟨12140846881252929856931395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16187795841670573142575193 12140846881252929856931395)
            ·
              refine ⟨18211270321879394785397093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12140846881252929856931395 18211270321879394785397093)
              ·
                refine ⟨3414613185352386522261955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18211270321879394785397093 3414613185352386522261955)
                ·
                  refine ⟨5121919778028579783392933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414613185352386522261955 5121919778028579783392933)
                  ·
                    refine ⟨960359958380358709386175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5121919778028579783392933 960359958380358709386175)
                    ·
                      rfl

theorem cell23_5610883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 4].length) (baseStart_5610883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610883 prefixEnd_5610883 := by exact prefixLift 5610883
  have htrace : WordTrace (prefixWord ++ tailWord_5610883) baseStart_5610883 baseEnd_5610883 := by
    simpa [prefixWord, tailWord_5610883, baseEnd_5610883] using wordTrace_append hprefix tailTrace_5610883
  have hstable : (prefixWord ++ tailWord_5610883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610883).length < 2 ^ (prefixWord ++ tailWord_5610883).sum := by decide
  have hdescent : baseEnd_5610883 < baseStart_5610883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610940 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_5610940 : Nat := 118140960795 + 5610940 * 2 ^ 59
def prefixEnd_5610940 : Nat := 4983230072969 + 3 ^ 40 * 5610940 * 2
def baseEnd_5610940 : Nat := 2881109143538382405145763

theorem tailTrace_5610940 : CollatzResearch.WordTrace tailWord_5610940 prefixEnd_5610940 2881109143538382405145763 := by
  unfold tailWord_5610940
  simp only [CollatzResearch.WordTrace]
  refine ⟨102323897146265063552579137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136431862861686751403438849 102323897146265063552579137)
  ·
    refine ⟨76742922859698797664434353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102323897146265063552579137 76742922859698797664434353)
    ·
      refine ⟨57557192144774098248325765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76742922859698797664434353 57557192144774098248325765)
      ·
        refine ⟨10791973527145143421561081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57557192144774098248325765 10791973527145143421561081)
        ·
          refine ⟨8093980145358857566170811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10791973527145143421561081 8093980145358857566170811)
          ·
            refine ⟨12140970218038286349256217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8093980145358857566170811 12140970218038286349256217)
            ·
              refine ⟨9105727663528714761942163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12140970218038286349256217 9105727663528714761942163)
              ·
                refine ⟨13658591495293072142913245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105727663528714761942163 13658591495293072142913245)
                ·
                  refine ⟨5121971810734902053592467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13658591495293072142913245 5121971810734902053592467)
                  ·
                    refine ⟨7682957716102353080388701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5121971810734902053592467 7682957716102353080388701)
                    ·
                      refine ⟨2881109143538382405145763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7682957716102353080388701 2881109143538382405145763)
                      ·
                        rfl

theorem cell23_5610940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_5610940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610940 prefixEnd_5610940 := by exact prefixLift 5610940
  have htrace : WordTrace (prefixWord ++ tailWord_5610940) baseStart_5610940 baseEnd_5610940 := by
    simpa [prefixWord, tailWord_5610940, baseEnd_5610940] using wordTrace_append hprefix tailTrace_5610940
  have hstable : (prefixWord ++ tailWord_5610940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610940).length < 2 ^ (prefixWord ++ tailWord_5610940).sum := by decide
  have hdescent : baseEnd_5610940 < baseStart_5610940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610956 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_5610956 : Nat := 118140960795 + 5610956 * 2 ^ 59
def prefixEnd_5610956 : Nat := 4983230072969 + 3 ^ 40 * 5610956 * 2
def baseEnd_5610956 : Nat := 960372453076284780848563

theorem tailTrace_5610956 : CollatzResearch.WordTrace tailWord_5610956 prefixEnd_5610956 960372453076284780848563 := by
  unfold tailWord_5610956
  simp only [CollatzResearch.WordTrace]
  refine ⟨102324188930236080918870361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136432251906981441225160481 102324188930236080918870361)
  ·
    refine ⟨76743141697677060689152771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102324188930236080918870361 76743141697677060689152771)
    ·
      refine ⟨115114712546515591033729157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76743141697677060689152771 115114712546515591033729157)
      ·
        refine ⟨21584008602471673318824217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115114712546515591033729157 21584008602471673318824217)
        ·
          refine ⟨16188006451853754989118163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21584008602471673318824217 16188006451853754989118163)
          ·
            refine ⟨24282009677780632483677245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16188006451853754989118163 24282009677780632483677245)
            ·
              refine ⟨9105753629167737181378967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24282009677780632483677245 9105753629167737181378967)
              ·
                refine ⟨13658630443751605772068451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105753629167737181378967 13658630443751605772068451)
                ·
                  refine ⟨20487945665627408658102677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13658630443751605772068451 20487945665627408658102677)
                  ·
                    refine ⟨960372453076284780848563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20487945665627408658102677 960372453076284780848563)
                    ·
                      rfl

theorem cell23_5610956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_5610956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610956 prefixEnd_5610956 := by exact prefixLift 5610956
  have htrace : WordTrace (prefixWord ++ tailWord_5610956) baseStart_5610956 baseEnd_5610956 := by
    simpa [prefixWord, tailWord_5610956, baseEnd_5610956] using wordTrace_append hprefix tailTrace_5610956
  have hstable : (prefixWord ++ tailWord_5610956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610956).length < 2 ^ (prefixWord ++ tailWord_5610956).sum := by decide
  have hdescent : baseEnd_5610956 < baseStart_5610956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610969 : List Nat := [1, 2, 1, 2, 4, 3, 1, 9]
def baseStart_5610969 : Nat := 118140960795 + 5610969 * 2 ^ 59
def prefixEnd_5610969 : Nat := 4983230072969 + 3 ^ 40 * 5610969 * 2
def baseEnd_5610969 : Nat := 106708297573235658951227

theorem tailTrace_5610969 : CollatzResearch.WordTrace tailWord_5610969 prefixEnd_5610969 106708297573235658951227 := by
  unfold tailWord_5610969
  simp only [CollatzResearch.WordTrace]
  refine ⟨204648852009425065057963961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136432568006283376705309307 204648852009425065057963961)
  ·
    refine ⟨153486639007068798793472971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204648852009425065057963961 153486639007068798793472971)
    ·
      refine ⟨230229958510603198190209457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153486639007068798793472971 230229958510603198190209457)
      ·
        refine ⟨172672468882952398642657093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230229958510603198190209457 172672468882952398642657093)
        ·
          refine ⟨32376087915553574745498205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172672468882952398642657093 32376087915553574745498205)
          ·
            refine ⟨12141032968332590529561827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32376087915553574745498205 12141032968332590529561827)
            ·
              refine ⟨18211549452498885794342741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12141032968332590529561827 18211549452498885794342741)
              ·
                refine ⟨106708297573235658951227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18211549452498885794342741 106708297573235658951227)
                ·
                  rfl

theorem cell23_5610969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 9].length) (baseStart_5610969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610969 prefixEnd_5610969 := by exact prefixLift 5610969
  have htrace : WordTrace (prefixWord ++ tailWord_5610969) baseStart_5610969 baseEnd_5610969 := by
    simpa [prefixWord, tailWord_5610969, baseEnd_5610969] using wordTrace_append hprefix tailTrace_5610969
  have hstable : (prefixWord ++ tailWord_5610969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610969).length < 2 ^ (prefixWord ++ tailWord_5610969).sum := by decide
  have hdescent : baseEnd_5610969 < baseStart_5610969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610983 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 3]
def baseStart_5610983 : Nat := 118140960795 + 5610983 * 2 ^ 59
def prefixEnd_5610983 : Nat := 4983230072969 + 3 ^ 40 * 5610983 * 2
def baseEnd_5610983 : Nat := 2881131223206525736908065

theorem tailTrace_5610983 : CollatzResearch.WordTrace tailWord_5610983 prefixEnd_5610983 2881131223206525736908065 := by
  unfold tailWord_5610983
  simp only [CollatzResearch.WordTrace]
  refine ⟨204649362631374345448973603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136432908420916230299315735 204649362631374345448973603)
  ·
    refine ⟨306974043947061518173460405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204649362631374345448973603 306974043947061518173460405)
    ·
      refine ⟨28778816620037017328761913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 306974043947061518173460405 28778816620037017328761913)
      ·
        refine ⟨21584112465027762996571435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28778816620037017328761913 21584112465027762996571435)
        ·
          refine ⟨32376168697541644494857153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21584112465027762996571435 32376168697541644494857153)
          ·
            refine ⟨24282126523156233371142865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32376168697541644494857153 24282126523156233371142865)
            ·
              refine ⟨18211594892367175028357149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24282126523156233371142865 18211594892367175028357149)
              ·
                refine ⟨6829348084637690635633931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18211594892367175028357149 6829348084637690635633931)
                ·
                  refine ⟨10244022126956535953450897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829348084637690635633931 10244022126956535953450897)
                  ·
                    refine ⟨7683016595217401965088173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10244022126956535953450897 7683016595217401965088173)
                    ·
                      refine ⟨2881131223206525736908065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683016595217401965088173 2881131223206525736908065)
                      ·
                        rfl

theorem cell23_5610983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_5610983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610983 prefixEnd_5610983 := by exact prefixLift 5610983
  have htrace : WordTrace (prefixWord ++ tailWord_5610983) baseStart_5610983 baseEnd_5610983 := by
    simpa [prefixWord, tailWord_5610983, baseEnd_5610983] using wordTrace_append hprefix tailTrace_5610983
  have hstable : (prefixWord ++ tailWord_5610983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610983).length < 2 ^ (prefixWord ++ tailWord_5610983).sum := by decide
  have hdescent : baseEnd_5610983 < baseStart_5610983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610986 : List Nat := [3, 1, 3, 1, 4, 2, 9]
def baseStart_5610986 : Nat := 118140960795 + 5610986 * 2 ^ 59
def prefixEnd_5610986 : Nat := 4983230072969 + 3 ^ 40 * 5610986 * 2
def baseEnd_5610986 : Nat := 35569540291956657100871

theorem tailTrace_5610986 : CollatzResearch.WordTrace tailWord_5610986 prefixEnd_5610986 35569540291956657100871 := by
  unfold tailWord_5610986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51162368012590869240333203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136432981366908984640888541 51162368012590869240333203)
  ·
    refine ⟨76743552018886303860499805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51162368012590869240333203 76743552018886303860499805)
    ·
      refine ⟨28778832007082363947687427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76743552018886303860499805 28778832007082363947687427)
      ·
        refine ⟨43168248010623545921531141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28778832007082363947687427 43168248010623545921531141)
        ·
          refine ⟨8094046501991914860287089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43168248010623545921531141 8094046501991914860287089)
          ·
            refine ⟨6070534876493936145215317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8094046501991914860287089 6070534876493936145215317)
            ·
              refine ⟨35569540291956657100871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6070534876493936145215317 35569540291956657100871)
              ·
                rfl

theorem cell23_5610986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 9].length) (baseStart_5610986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610986 prefixEnd_5610986 := by exact prefixLift 5610986
  have htrace : WordTrace (prefixWord ++ tailWord_5610986) baseStart_5610986 baseEnd_5610986 := by
    simpa [prefixWord, tailWord_5610986, baseEnd_5610986] using wordTrace_append hprefix tailTrace_5610986
  have hstable : (prefixWord ++ tailWord_5610986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610986).length < 2 ^ (prefixWord ++ tailWord_5610986).sum := by decide
  have hdescent : baseEnd_5610986 < baseStart_5610986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5610997 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_5610997 : Nat := 118140960795 + 5610997 * 2 ^ 59
def prefixEnd_5610997 : Nat := 4983230072969 + 3 ^ 40 * 5610997 * 2
def baseEnd_5610997 : Nat := 2881138411935688682133001

theorem tailTrace_5610997 : CollatzResearch.WordTrace tailWord_5610997 prefixEnd_5610997 2881138411935688682133001 := by
  unfold tailWord_5610997
  simp only [CollatzResearch.WordTrace]
  refine ⟨204649873253323625839983245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136433248835549083893322163 204649873253323625839983245)
  ·
    refine ⟨76743702469996359689993717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204649873253323625839983245 76743702469996359689993717)
    ·
      refine ⟨7194722106562158720936911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76743702469996359689993717 7194722106562158720936911)
      ·
        refine ⟨10792083159843238081405367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7194722106562158720936911 10792083159843238081405367)
        ·
          refine ⟨16188124739764857122108051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792083159843238081405367 16188124739764857122108051)
          ·
            refine ⟨24282187109647285683162077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16188124739764857122108051 24282187109647285683162077)
            ·
              refine ⟨9105820166117732131185779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24282187109647285683162077 9105820166117732131185779)
              ·
                refine ⟨13658730249176598196778669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9105820166117732131185779 13658730249176598196778669)
                ·
                  refine ⟨5122023843441224323792001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13658730249176598196778669 5122023843441224323792001)
                  ·
                    refine ⟨3841517882580918242844001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122023843441224323792001 3841517882580918242844001)
                    ·
                      refine ⟨2881138411935688682133001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841517882580918242844001 2881138411935688682133001)
                      ·
                        rfl

theorem cell23_5610997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_5610997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5610997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5610997 prefixEnd_5610997 := by exact prefixLift 5610997
  have htrace : WordTrace (prefixWord ++ tailWord_5610997) baseStart_5610997 baseEnd_5610997 := by
    simpa [prefixWord, tailWord_5610997, baseEnd_5610997] using wordTrace_append hprefix tailTrace_5610997
  have hstable : (prefixWord ++ tailWord_5610997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5610997).length < 2 ^ (prefixWord ++ tailWord_5610997).sum := by decide
  have hdescent : baseEnd_5610997 < baseStart_5610997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5610997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611048 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_5611048 : Nat := 118140960795 + 5611048 * 2 ^ 59
def prefixEnd_5611048 : Nat := 4983230072969 + 3 ^ 40 * 5611048 * 2
def baseEnd_5611048 : Nat := 2881164599449067982595267

theorem tailTrace_5611048 : CollatzResearch.WordTrace tailWord_5611048 prefixEnd_5611048 2881164599449067982595267 := by
  unfold tailWord_5611048
  simp only [CollatzResearch.WordTrace]
  refine ⟨102325866688069430775044899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136434488917425907700059865 102325866688069430775044899)
  ·
    refine ⟨153488800032104146162567349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102325866688069430775044899 153488800032104146162567349)
    ·
      refine ⟨14389575003009763702740689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153488800032104146162567349 14389575003009763702740689)
      ·
        refine ⟨10792181252257322777055517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14389575003009763702740689 10792181252257322777055517)
        ·
          refine ⟨4047067969596496041395819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10792181252257322777055517 4047067969596496041395819)
          ·
            refine ⟨6070601954394744062093729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047067969596496041395819 6070601954394744062093729)
            ·
              refine ⟨4552951465796058046570297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070601954394744062093729 4552951465796058046570297)
              ·
                refine ⟨3414713599347043534927723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552951465796058046570297 3414713599347043534927723)
                ·
                  refine ⟨5122070399020565302391585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414713599347043534927723 5122070399020565302391585)
                  ·
                    refine ⟨3841552799265423976793689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122070399020565302391585 3841552799265423976793689)
                    ·
                      refine ⟨2881164599449067982595267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841552799265423976793689 2881164599449067982595267)
                      ·
                        rfl

theorem cell23_5611048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_5611048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611048 prefixEnd_5611048 := by exact prefixLift 5611048
  have htrace : WordTrace (prefixWord ++ tailWord_5611048) baseStart_5611048 baseEnd_5611048 := by
    simpa [prefixWord, tailWord_5611048, baseEnd_5611048] using wordTrace_append hprefix tailTrace_5611048
  have hstable : (prefixWord ++ tailWord_5611048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611048).length < 2 ^ (prefixWord ++ tailWord_5611048).sum := by decide
  have hdescent : baseEnd_5611048 < baseStart_5611048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611066 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_5611066 : Nat := 118140960795 + 5611066 * 2 ^ 59
def prefixEnd_5611066 : Nat := 4983230072969 + 3 ^ 40 * 5611066 * 2
def baseEnd_5611066 : Nat := 2881173842100848912170183

theorem tailTrace_5611066 : CollatzResearch.WordTrace tailWord_5611066 prefixEnd_5611066 2881173842100848912170183 := by
  unfold tailWord_5611066
  simp only [CollatzResearch.WordTrace]
  refine ⟨51163097472518412656061263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136434926593382433749496701 51163097472518412656061263)
  ·
    refine ⟨76744646208777618984091895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51163097472518412656061263 76744646208777618984091895)
    ·
      refine ⟨115116969313166428476137843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76744646208777618984091895 115116969313166428476137843)
      ·
        refine ⟨172675453969749642714206765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115116969313166428476137843 172675453969749642714206765)
        ·
          refine ⟨64753295238656116017827537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172675453969749642714206765 64753295238656116017827537)
          ·
            refine ⟨48564971428992087013370653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64753295238656116017827537 48564971428992087013370653)
            ·
              refine ⟨18211864285872032630013995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48564971428992087013370653 18211864285872032630013995)
              ·
                refine ⟨27317796428808048945020993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18211864285872032630013995 27317796428808048945020993)
                ·
                  refine ⟨20488347321606036708765745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27317796428808048945020993 20488347321606036708765745)
                  ·
                    refine ⟨15366260491204527531574309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20488347321606036708765745 15366260491204527531574309)
                    ·
                      refine ⟨2881173842100848912170183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15366260491204527531574309 2881173842100848912170183)
                      ·
                        rfl

theorem cell23_5611066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_5611066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611066 prefixEnd_5611066 := by exact prefixLift 5611066
  have htrace : WordTrace (prefixWord ++ tailWord_5611066) baseStart_5611066 baseEnd_5611066 := by
    simpa [prefixWord, tailWord_5611066, baseEnd_5611066] using wordTrace_append hprefix tailTrace_5611066
  have hstable : (prefixWord ++ tailWord_5611066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611066).length < 2 ^ (prefixWord ++ tailWord_5611066).sum := by decide
  have hdescent : baseEnd_5611066 < baseStart_5611066 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611086 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_5611086 : Nat := 118140960795 + 5611086 * 2 ^ 59
def prefixEnd_5611086 : Nat := 4983230072969 + 3 ^ 40 * 5611086 * 2
def baseEnd_5611086 : Nat := 2881184111713938833920091

theorem tailTrace_5611086 : CollatzResearch.WordTrace tailWord_5611086 prefixEnd_5611086 2881184111713938833920091 := by
  unfold tailWord_5611086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25581639918750149254996639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136435412900000796026648741 25581639918750149254996639)
  ·
    refine ⟨38372459878125223882494959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25581639918750149254996639 38372459878125223882494959)
    ·
      refine ⟨57558689817187835823742439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38372459878125223882494959 57558689817187835823742439)
      ·
        refine ⟨86338034725781753735613659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57558689817187835823742439 86338034725781753735613659)
        ·
          refine ⟨129507052088672630603420489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86338034725781753735613659 129507052088672630603420489)
          ·
            refine ⟨97130289066504472952565367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129507052088672630603420489 97130289066504472952565367)
            ·
              refine ⟨145695433599756709428848051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97130289066504472952565367 145695433599756709428848051)
              ·
                refine ⟨218543150399635064143272077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145695433599756709428848051 218543150399635064143272077)
                ·
                  refine ⟨81953681399863149053727029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218543150399635064143272077 81953681399863149053727029)
                  ·
                    refine ⟨7683157631237170223786909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81953681399863149053727029 7683157631237170223786909)
                    ·
                      refine ⟨2881184111713938833920091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683157631237170223786909 2881184111713938833920091)
                      ·
                        rfl

theorem cell23_5611086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_5611086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611086 prefixEnd_5611086 := by exact prefixLift 5611086
  have htrace : WordTrace (prefixWord ++ tailWord_5611086) baseStart_5611086 baseEnd_5611086 := by
    simpa [prefixWord, tailWord_5611086, baseEnd_5611086] using wordTrace_append hprefix tailTrace_5611086
  have hstable : (prefixWord ++ tailWord_5611086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611086).length < 2 ^ (prefixWord ++ tailWord_5611086).sum := by decide
  have hdescent : baseEnd_5611086 < baseStart_5611086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611144 : List Nat := [2, 1, 3, 5, 2, 1, 1, 3, 5]
def baseStart_5611144 : Nat := 118140960795 + 5611144 * 2 ^ 59
def prefixEnd_5611144 : Nat := 4983230072969 + 3 ^ 40 * 5611144 * 2
def baseEnd_5611144 : Nat := 320134877065766622999425

theorem tailTrace_5611144 : CollatzResearch.WordTrace tailWord_5611144 prefixEnd_5611144 320134877065766622999425 := by
  unfold tailWord_5611144
  simp only [CollatzResearch.WordTrace]
  refine ⟨102327617391895534972792243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136436823189194046630389657 102327617391895534972792243)
  ·
    refine ⟨153491426087843302459188365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102327617391895534972792243 153491426087843302459188365)
    ·
      refine ⟨57559284782941238422195637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153491426087843302459188365 57559284782941238422195637)
      ·
        refine ⟨5396182948400741102080841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57559284782941238422195637 5396182948400741102080841)
        ·
          refine ⟨4047137211300555826560631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5396182948400741102080841 4047137211300555826560631)
          ·
            refine ⟨6070705816950833739840947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047137211300555826560631 6070705816950833739840947)
            ·
              refine ⟨9106058725426250609761421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070705816950833739840947 9106058725426250609761421)
              ·
                refine ⟨3414772022034843978660533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9106058725426250609761421 3414772022034843978660533)
                ·
                  refine ⟨320134877065766622999425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3414772022034843978660533 320134877065766622999425)
                  ·
                    rfl

theorem cell23_5611144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 5].length) (baseStart_5611144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611144 prefixEnd_5611144 := by exact prefixLift 5611144
  have htrace : WordTrace (prefixWord ++ tailWord_5611144) baseStart_5611144 baseEnd_5611144 := by
    simpa [prefixWord, tailWord_5611144, baseEnd_5611144] using wordTrace_append hprefix tailTrace_5611144
  have hstable : (prefixWord ++ tailWord_5611144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611144).length < 2 ^ (prefixWord ++ tailWord_5611144).sum := by decide
  have hdescent : baseEnd_5611144 < baseStart_5611144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611186 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5611186 : Nat := 118140960795 + 5611186 * 2 ^ 59
def prefixEnd_5611186 : Nat := 4983230072969 + 3 ^ 40 * 5611186 * 2
def baseEnd_5611186 : Nat := 2881235459779388442669631

theorem tailTrace_5611186 : CollatzResearch.WordTrace tailWord_5611186 prefixEnd_5611186 2881235459779388442669631 := by
  unfold tailWord_5611186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51164191662409727779653353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136437844433092607412408941 51164191662409727779653353)
  ·
    refine ⟨38373143746807295834740015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51164191662409727779653353 38373143746807295834740015)
    ·
      refine ⟨57559715620210943752110023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38373143746807295834740015 57559715620210943752110023)
      ·
        refine ⟨86339573430316415628165035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57559715620210943752110023 86339573430316415628165035)
        ·
          refine ⟨129509360145474623442247553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86339573430316415628165035 129509360145474623442247553)
          ·
            refine ⟨97132020109105967581685665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129509360145474623442247553 97132020109105967581685665)
            ·
              refine ⟨72849015081829475686264249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97132020109105967581685665 72849015081829475686264249)
              ·
                refine ⟨54636761311372106764698187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72849015081829475686264249 54636761311372106764698187)
                ·
                  refine ⟨81955141967058160147047281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54636761311372106764698187 81955141967058160147047281)
                  ·
                    refine ⟨61466356475293620110285461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81955141967058160147047281 61466356475293620110285461)
                    ·
                      refine ⟨2881235459779388442669631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61466356475293620110285461 2881235459779388442669631)
                      ·
                        rfl

theorem cell23_5611186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5611186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611186 prefixEnd_5611186 := by exact prefixLift 5611186
  have htrace : WordTrace (prefixWord ++ tailWord_5611186) baseStart_5611186 baseEnd_5611186 := by
    simpa [prefixWord, tailWord_5611186, baseEnd_5611186] using wordTrace_append hprefix tailTrace_5611186
  have hstable : (prefixWord ++ tailWord_5611186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611186).length < 2 ^ (prefixWord ++ tailWord_5611186).sum := by decide
  have hdescent : baseEnd_5611186 < baseStart_5611186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611250 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_5611250 : Nat := 118140960795 + 5611250 * 2 ^ 59
def prefixEnd_5611250 : Nat := 4983230072969 + 3 ^ 40 * 5611250 * 2
def baseEnd_5611250 : Nat := 2881268322541276192269337

theorem tailTrace_5611250 : CollatzResearch.WordTrace tailWord_5611250 prefixEnd_5611250 2881268322541276192269337 := by
  unfold tailWord_5611250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51164775230351762512235801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136439400614271366699295469 51164775230351762512235801)
  ·
    refine ⟨38373581422763821884176851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51164775230351762512235801 38373581422763821884176851)
    ·
      refine ⟨57560372134145732826265277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38373581422763821884176851 57560372134145732826265277)
      ·
        refine ⟨21585139550304649809849479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57560372134145732826265277 21585139550304649809849479)
        ·
          refine ⟨32377709325456974714774219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21585139550304649809849479 32377709325456974714774219)
          ·
            refine ⟨48566563988185462072161329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32377709325456974714774219 48566563988185462072161329)
            ·
              refine ⟨36424922991139096554120997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48566563988185462072161329 36424922991139096554120997)
              ·
                refine ⟨6829673060838580603897687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36424922991139096554120997 6829673060838580603897687)
                ·
                  refine ⟨10244509591257870905846531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6829673060838580603897687 10244509591257870905846531)
                  ·
                    refine ⟨15366764386886806358769797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10244509591257870905846531 15366764386886806358769797)
                    ·
                      refine ⟨2881268322541276192269337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15366764386886806358769797 2881268322541276192269337)
                      ·
                        rfl

theorem cell23_5611250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_5611250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611250 prefixEnd_5611250 := by exact prefixLift 5611250
  have htrace : WordTrace (prefixWord ++ tailWord_5611250) baseStart_5611250 baseEnd_5611250 := by
    simpa [prefixWord, tailWord_5611250, baseEnd_5611250] using wordTrace_append hprefix tailTrace_5611250
  have hstable : (prefixWord ++ tailWord_5611250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611250).length < 2 ^ (prefixWord ++ tailWord_5611250).sum := by decide
  have hdescent : baseEnd_5611250 < baseStart_5611250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611254 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5611254 : Nat := 118140960795 + 5611254 * 2 ^ 59
def prefixEnd_5611254 : Nat := 4983230072969 + 3 ^ 40 * 5611254 * 2
def baseEnd_5611254 : Nat := 2881270376463894176619319

theorem tailTrace_5611254 : CollatzResearch.WordTrace tailWord_5611254 prefixEnd_5611254 2881270376463894176619319 := by
  unfold tailWord_5611254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12791202925837034920755551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136439497875595039154725877 12791202925837034920755551)
  ·
    refine ⟨19186804388755552381133327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12791202925837034920755551 19186804388755552381133327)
    ·
      refine ⟨28780206583133328571699991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19186804388755552381133327 28780206583133328571699991)
      ·
        refine ⟨43170309874699992857549987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28780206583133328571699991 43170309874699992857549987)
        ·
          refine ⟨64755464812049989286324981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43170309874699992857549987 64755464812049989286324981)
          ·
            refine ⟨6070824826129686495592967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64755464812049989286324981 6070824826129686495592967)
            ·
              refine ⟨9106237239194529743389451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6070824826129686495592967 9106237239194529743389451)
              ·
                refine ⟨13659355858791794615084177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9106237239194529743389451 13659355858791794615084177)
                ·
                  refine ⟨10244516894093845961313133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13659355858791794615084177 10244516894093845961313133)
                  ·
                    refine ⟨3841693835285192235492425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10244516894093845961313133 3841693835285192235492425)
                    ·
                      refine ⟨2881270376463894176619319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841693835285192235492425 2881270376463894176619319)
                      ·
                        rfl

theorem cell23_5611254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5611254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611254 prefixEnd_5611254 := by exact prefixLift 5611254
  have htrace : WordTrace (prefixWord ++ tailWord_5611254) baseStart_5611254 baseEnd_5611254 := by
    simpa [prefixWord, tailWord_5611254, baseEnd_5611254] using wordTrace_append hprefix tailTrace_5611254
  have hstable : (prefixWord ++ tailWord_5611254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611254).length < 2 ^ (prefixWord ++ tailWord_5611254).sum := by decide
  have hdescent : baseEnd_5611254 < baseStart_5611254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611263 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_5611263 : Nat := 118140960795 + 5611263 * 2 ^ 59
def prefixEnd_5611263 : Nat := 4983230072969 + 3 ^ 40 * 5611263 * 2
def baseEnd_5611263 : Nat := 2881274997789784641406777

theorem tailTrace_5611263 : CollatzResearch.WordTrace tailWord_5611263 prefixEnd_5611263 2881274997789784641406777 := by
  unfold tailWord_5611263
  simp only [CollatzResearch.WordTrace]
  refine ⟨204659575070359953269166443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136439716713573302179444295 204659575070359953269166443)
  ·
    refine ⟨306989362605539929903749665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204659575070359953269166443 306989362605539929903749665)
    ·
      refine ⟨230242021954154947427812249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 306989362605539929903749665 230242021954154947427812249)
      ·
        refine ⟨172681516465616210570859187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230242021954154947427812249 172681516465616210570859187)
        ·
          refine ⟨259022274698424315856288781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172681516465616210570859187 259022274698424315856288781)
          ·
            refine ⟨97133353011909118446108293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259022274698424315856288781 97133353011909118446108293)
            ·
              refine ⟨18212503689732959708645305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97133353011909118446108293 18212503689732959708645305)
              ·
                refine ⟨13659377767299719781483979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18212503689732959708645305 13659377767299719781483979)
                ·
                  refine ⟨20489066650949579672225969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13659377767299719781483979 20489066650949579672225969)
                  ·
                    refine ⟨15366799988212184754169477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20489066650949579672225969 15366799988212184754169477)
                    ·
                      refine ⟨2881274997789784641406777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15366799988212184754169477 2881274997789784641406777)
                      ·
                        rfl

theorem cell23_5611263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_5611263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611263 prefixEnd_5611263 := by exact prefixLift 5611263
  have htrace : WordTrace (prefixWord ++ tailWord_5611263) baseStart_5611263 baseEnd_5611263 := by
    simpa [prefixWord, tailWord_5611263, baseEnd_5611263] using wordTrace_append hprefix tailTrace_5611263
  have hstable : (prefixWord ++ tailWord_5611263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611263).length < 2 ^ (prefixWord ++ tailWord_5611263).sum := by decide
  have hdescent : baseEnd_5611263 < baseStart_5611263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611313 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5611313 : Nat := 118140960795 + 5611313 * 2 ^ 59
def prefixEnd_5611313 : Nat := 4983230072969 + 3 ^ 40 * 5611313 * 2
def baseEnd_5611313 : Nat := 2881300671822509445781547

theorem tailTrace_5611313 : CollatzResearch.WordTrace tailWord_5611313 prefixEnd_5611313 2881300671822509445781547 := by
  unfold tailWord_5611313
  simp only [CollatzResearch.WordTrace]
  refine ⟨204661398720178811808486593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136440932480119207872324395 204661398720178811808486593)
  ·
    refine ⟨153496049040134108856364945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204661398720178811808486593 153496049040134108856364945)
    ·
      refine ⟨115122036780100581642273709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153496049040134108856364945 115122036780100581642273709)
      ·
        refine ⟨43170763792537718115852641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115122036780100581642273709 43170763792537718115852641)
        ·
          refine ⟨32378072844403288586889481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43170763792537718115852641 32378072844403288586889481)
          ·
            refine ⟨24283554633302466440167111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32378072844403288586889481 24283554633302466440167111)
            ·
              refine ⟨36425331949953699660250667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24283554633302466440167111 36425331949953699660250667)
              ·
                refine ⟨54637997924930549490376001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36425331949953699660250667 54637997924930549490376001)
                ·
                  refine ⟨40978498443697912117782001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54637997924930549490376001 40978498443697912117782001)
                  ·
                    refine ⟨30733873832773434088336501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40978498443697912117782001 30733873832773434088336501)
                    ·
                      refine ⟨2881300671822509445781547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30733873832773434088336501 2881300671822509445781547)
                      ·
                        rfl

theorem cell23_5611313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5611313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611313 prefixEnd_5611313 := by exact prefixLift 5611313
  have htrace : WordTrace (prefixWord ++ tailWord_5611313) baseStart_5611313 baseEnd_5611313 := by
    simpa [prefixWord, tailWord_5611313, baseEnd_5611313] using wordTrace_append hprefix tailTrace_5611313
  have hstable : (prefixWord ++ tailWord_5611313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611313).length < 2 ^ (prefixWord ++ tailWord_5611313).sum := by decide
  have hdescent : baseEnd_5611313 < baseStart_5611313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611318 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_5611318 : Nat := 118140960795 + 5611318 * 2 ^ 59
def prefixEnd_5611318 : Nat := 4983230072969 + 3 ^ 40 * 5611318 * 2
def baseEnd_5611318 : Nat := 2881303239225781926219025

theorem tailTrace_5611318 : CollatzResearch.WordTrace tailWord_5611318 prefixEnd_5611318 2881303239225781926219025 := by
  unfold tailWord_5611318
  simp only [CollatzResearch.WordTrace]
  refine ⟨12791348817822543603901163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136441054056773798441612405 12791348817822543603901163)
  ·
    refine ⟨19187023226733815405851745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12791348817822543603901163 19187023226733815405851745)
    ·
      refine ⟨14390267420050361554388809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19187023226733815405851745 14390267420050361554388809)
      ·
        refine ⟨10792700565037771165791607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14390267420050361554388809 10792700565037771165791607)
        ·
          refine ⟨16189050847556656748687411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792700565037771165791607 16189050847556656748687411)
          ·
            refine ⟨24283576271334985123031117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16189050847556656748687411 24283576271334985123031117)
            ·
              refine ⟨9106341101750619421136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24283576271334985123031117 9106341101750619421136669)
              ·
                refine ⟨3414877913156482282926251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9106341101750619421136669 3414877913156482282926251)
                ·
                  refine ⟨5122316869734723424389377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414877913156482282926251 5122316869734723424389377)
                  ·
                    refine ⟨3841737652301042568292033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122316869734723424389377 3841737652301042568292033)
                    ·
                      refine ⟨2881303239225781926219025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841737652301042568292033 2881303239225781926219025)
                      ·
                        rfl

theorem cell23_5611318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_5611318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611318 prefixEnd_5611318 := by exact prefixLift 5611318
  have htrace : WordTrace (prefixWord ++ tailWord_5611318) baseStart_5611318 baseEnd_5611318 := by
    simpa [prefixWord, tailWord_5611318, baseEnd_5611318] using wordTrace_append hprefix tailTrace_5611318
  have hstable : (prefixWord ++ tailWord_5611318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611318).length < 2 ^ (prefixWord ++ tailWord_5611318).sum := by decide
  have hdescent : baseEnd_5611318 < baseStart_5611318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611351 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 2, 1, 3]
def baseStart_5611351 : Nat := 118140960795 + 5611351 * 2 ^ 59
def prefixEnd_5611351 : Nat := 4983230072969 + 3 ^ 40 * 5611351 * 2
def baseEnd_5611351 : Nat := 2881320184087380297106373

theorem tailTrace_5611351 : CollatzResearch.WordTrace tailWord_5611351 prefixEnd_5611351 2881320184087380297106373 := by
  unfold tailWord_5611351
  simp only [CollatzResearch.WordTrace]
  refine ⟨204662784694041144298369907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136441856462694096198913271 204662784694041144298369907)
  ·
    refine ⟨306994177041061716447554861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204662784694041144298369907 306994177041061716447554861)
    ·
      refine ⟨115122816390398143667833073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 306994177041061716447554861 115122816390398143667833073)
      ·
        refine ⟨86342112292798607750874805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115122816390398143667833073 86342112292798607750874805)
        ·
          refine ⟨8094573027449869476644513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86342112292798607750874805 8094573027449869476644513)
          ·
            refine ⟨6070929770587402107483385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8094573027449869476644513 6070929770587402107483385)
            ·
              refine ⟨4553197327940551580612539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6070929770587402107483385 4553197327940551580612539)
              ·
                refine ⟨6829795991910827370918809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553197327940551580612539 6829795991910827370918809)
                ·
                  refine ⟨5122346993933120528189107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6829795991910827370918809 5122346993933120528189107)
                  ·
                    refine ⟨7683520490899680792283661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5122346993933120528189107 7683520490899680792283661)
                    ·
                      refine ⟨2881320184087380297106373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683520490899680792283661 2881320184087380297106373)
                      ·
                        rfl

theorem cell23_5611351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_5611351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611351 prefixEnd_5611351 := by exact prefixLift 5611351
  have htrace : WordTrace (prefixWord ++ tailWord_5611351) baseStart_5611351 baseEnd_5611351 := by
    simpa [prefixWord, tailWord_5611351, baseEnd_5611351] using wordTrace_append hprefix tailTrace_5611351
  have hstable : (prefixWord ++ tailWord_5611351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611351).length < 2 ^ (prefixWord ++ tailWord_5611351).sum := by decide
  have hdescent : baseEnd_5611351 < baseStart_5611351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611353 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_5611353 : Nat := 118140960795 + 5611353 * 2 ^ 59
def prefixEnd_5611353 : Nat := 4983230072969 + 3 ^ 40 * 5611353 * 2
def baseEnd_5611353 : Nat := 2881321211048689289281363

theorem tailTrace_5611353 : CollatzResearch.WordTrace tailWord_5611353 prefixEnd_5611353 2881321211048689289281363 := by
  unfold tailWord_5611353
  simp only [CollatzResearch.WordTrace]
  refine ⟨204662857640033898639942713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136441905093355932426628475 204662857640033898639942713)
  ·
    refine ⟨153497143230025423979957035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204662857640033898639942713 153497143230025423979957035)
    ·
      refine ⟨230245714845038135969935553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153497143230025423979957035 230245714845038135969935553)
      ·
        refine ⟨172684286133778601977451665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230245714845038135969935553 172684286133778601977451665)
        ·
          refine ⟨129513214600333951483088749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172684286133778601977451665 129513214600333951483088749)
          ·
            refine ⟨48567455475125231806158281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129513214600333951483088749 48567455475125231806158281)
            ·
              refine ⟨36425591606343923854618711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48567455475125231806158281 36425591606343923854618711)
              ·
                refine ⟨54638387409515885781928067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36425591606343923854618711 54638387409515885781928067)
                ·
                  refine ⟨81957581114273828672892101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54638387409515885781928067 81957581114273828672892101)
                  ·
                    refine ⟨15367046458926342876167269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81957581114273828672892101 15367046458926342876167269)
                    ·
                      refine ⟨2881321211048689289281363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15367046458926342876167269 2881321211048689289281363)
                      ·
                        rfl

theorem cell23_5611353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_5611353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611353 prefixEnd_5611353 := by exact prefixLift 5611353
  have htrace : WordTrace (prefixWord ++ tailWord_5611353) baseStart_5611353 baseEnd_5611353 := by
    simpa [prefixWord, tailWord_5611353, baseEnd_5611353] using wordTrace_append hprefix tailTrace_5611353
  have hstable : (prefixWord ++ tailWord_5611353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611353).length < 2 ^ (prefixWord ++ tailWord_5611353).sum := by decide
  have hdescent : baseEnd_5611353 < baseStart_5611353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611374 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_5611374 : Nat := 118140960795 + 5611374 * 2 ^ 59
def prefixEnd_5611374 : Nat := 4983230072969 + 3 ^ 40 * 5611374 * 2
def baseEnd_5611374 : Nat := 2881331994142433707118767

theorem tailTrace_5611374 : CollatzResearch.WordTrace tailWord_5611374 prefixEnd_5611374 2881331994142433707118767 := by
  unfold tailWord_5611374
  simp only [CollatzResearch.WordTrace]
  refine ⟨25582952946619727403307147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136442415715305212817638117 25582952946619727403307147)
  ·
    refine ⟨38374429419929591104960721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25582952946619727403307147 38374429419929591104960721)
    ·
      refine ⟨28780822064947193328720541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38374429419929591104960721 28780822064947193328720541)
      ·
        refine ⟨10792808274355197498270203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28780822064947193328720541 10792808274355197498270203)
        ·
          refine ⟨16189212411532796247405305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10792808274355197498270203 16189212411532796247405305)
          ·
            refine ⟨12141909308649597185553979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16189212411532796247405305 12141909308649597185553979)
            ·
              refine ⟨18212863962974395778330969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12141909308649597185553979 18212863962974395778330969)
              ·
                refine ⟨13659647972230796833748227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18212863962974395778330969 13659647972230796833748227)
                ·
                  refine ⟨20489471958346195250622341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13659647972230796833748227 20489471958346195250622341)
                  ·
                    refine ⟨3841775992189911609491689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20489471958346195250622341 3841775992189911609491689)
                    ·
                      refine ⟨2881331994142433707118767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841775992189911609491689 2881331994142433707118767)
                      ·
                        rfl

theorem cell23_5611374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_5611374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611374 prefixEnd_5611374 := by exact prefixLift 5611374
  have htrace : WordTrace (prefixWord ++ tailWord_5611374) baseStart_5611374 baseEnd_5611374 := by
    simpa [prefixWord, tailWord_5611374, baseEnd_5611374] using wordTrace_append hprefix tailTrace_5611374
  have hstable : (prefixWord ++ tailWord_5611374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611374).length < 2 ^ (prefixWord ++ tailWord_5611374).sum := by decide
  have hdescent : baseEnd_5611374 < baseStart_5611374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611433 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_5611433 : Nat := 118140960795 + 5611433 * 2 ^ 59
def prefixEnd_5611433 : Nat := 4983230072969 + 3 ^ 40 * 5611433 * 2
def baseEnd_5611433 : Nat := 2881362289501048976280995

theorem tailTrace_5611433 : CollatzResearch.WordTrace tailWord_5611433 prefixEnd_5611433 2881362289501048976280995 := by
  unfold tailWord_5611433
  simp only [CollatzResearch.WordTrace]
  refine ⟨204665775479744072302854953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136443850319829381535236635 204665775479744072302854953)
  ·
    refine ⟨153499331609808054227141215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204665775479744072302854953 153499331609808054227141215)
    ·
      refine ⟨230248997414712081340711823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153499331609808054227141215 230248997414712081340711823)
      ·
        refine ⟨345373496122068122011067735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230248997414712081340711823 345373496122068122011067735)
        ·
          refine ⟨518060244183102183016601603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345373496122068122011067735 518060244183102183016601603)
          ·
            refine ⟨777090366274653274524902405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518060244183102183016601603 777090366274653274524902405)
            ·
              refine ⟨145704443676497488973419201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 777090366274653274524902405 145704443676497488973419201)
              ·
                refine ⟨109278332757373116730064401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145704443676497488973419201 109278332757373116730064401)
                ·
                  refine ⟨81958749568029837547548301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109278332757373116730064401 81958749568029837547548301)
                  ·
                    refine ⟨30734531088011189080330613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81958749568029837547548301 30734531088011189080330613)
                    ·
                      refine ⟨2881362289501048976280995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30734531088011189080330613 2881362289501048976280995)
                      ·
                        rfl

theorem cell23_5611433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_5611433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611433 prefixEnd_5611433 := by exact prefixLift 5611433
  have htrace : WordTrace (prefixWord ++ tailWord_5611433) baseStart_5611433 baseEnd_5611433 := by
    simpa [prefixWord, tailWord_5611433, baseEnd_5611433] using wordTrace_append hprefix tailTrace_5611433
  have hstable : (prefixWord ++ tailWord_5611433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611433).length < 2 ^ (prefixWord ++ tailWord_5611433).sum := by decide
  have hdescent : baseEnd_5611433 < baseStart_5611433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611443 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6]
def baseStart_5611443 : Nat := 118140960795 + 5611443 * 2 ^ 59
def prefixEnd_5611443 : Nat := 4983230072969 + 3 ^ 40 * 5611443 * 2
def baseEnd_5611443 : Nat := 2881367424307593937155949

theorem tailTrace_5611443 : CollatzResearch.WordTrace tailWord_5611443 prefixEnd_5611443 2881367424307593937155949 := by
  unfold tailWord_5611443
  simp only [CollatzResearch.WordTrace]
  refine ⟨204666140209707844010718983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136444093473138562673812655 204666140209707844010718983)
  ·
    refine ⟨306999210314561766016078475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204666140209707844010718983 306999210314561766016078475)
    ·
      refine ⟨460498815471842649024117713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306999210314561766016078475 460498815471842649024117713)
      ·
        refine ⟨345374111603881986768088285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460498815471842649024117713 345374111603881986768088285)
        ·
          refine ⟨129515291851455745038033107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345374111603881986768088285 129515291851455745038033107)
          ·
            refine ⟨194272937777183617557049661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129515291851455745038033107 194272937777183617557049661)
            ·
              refine ⟨72852351666443856583893623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194272937777183617557049661 72852351666443856583893623)
              ·
                refine ⟨109278527499665784875840435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72852351666443856583893623 109278527499665784875840435)
                ·
                  refine ⟨163917791249498677313760653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109278527499665784875840435 163917791249498677313760653)
                  ·
                    refine ⟨61469171718562003992660245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 163917791249498677313760653 61469171718562003992660245)
                    ·
                      refine ⟨2881367424307593937155949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61469171718562003992660245 2881367424307593937155949)
                      ·
                        rfl

theorem cell23_5611443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 6].length) (baseStart_5611443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611443 prefixEnd_5611443 := by exact prefixLift 5611443
  have htrace : WordTrace (prefixWord ++ tailWord_5611443) baseStart_5611443 baseEnd_5611443 := by
    simpa [prefixWord, tailWord_5611443, baseEnd_5611443] using wordTrace_append hprefix tailTrace_5611443
  have hstable : (prefixWord ++ tailWord_5611443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611443).length < 2 ^ (prefixWord ++ tailWord_5611443).sum := by decide
  have hdescent : baseEnd_5611443 < baseStart_5611443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611480 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_5611480 : Nat := 118140960795 + 5611480 * 2 ^ 59
def prefixEnd_5611480 : Nat := 4983230072969 + 3 ^ 40 * 5611480 * 2
def baseEnd_5611480 : Nat := 2881386423091810292393279

theorem tailTrace_5611480 : CollatzResearch.WordTrace tailWord_5611480 prefixEnd_5611480 2881386423091810292393279 := by
  unfold tailWord_5611480
  simp only [CollatzResearch.WordTrace]
  refine ⟨102333744855286899664907947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136444993140382532886543929 102333744855286899664907947)
  ·
    refine ⟨153500617282930349497361921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102333744855286899664907947 153500617282930349497361921)
    ·
      refine ⟨115125462962197762123021441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153500617282930349497361921 115125462962197762123021441)
      ·
        refine ⟨86344097221648321592266081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115125462962197762123021441 86344097221648321592266081)
        ·
          refine ⟨64758072916236241194199561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86344097221648321592266081 64758072916236241194199561)
          ·
            refine ⟨48568554687177180895649671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64758072916236241194199561 48568554687177180895649671)
            ·
              refine ⟨72852832030765771343474507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48568554687177180895649671 72852832030765771343474507)
              ·
                refine ⟨109279248046148657015211761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72852832030765771343474507 109279248046148657015211761)
                ·
                  refine ⟨81959436034611492761408821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109279248046148657015211761 81959436034611492761408821)
                  ·
                    refine ⟨7683697128244827446382077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 81959436034611492761408821 7683697128244827446382077)
                    ·
                      refine ⟨2881386423091810292393279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683697128244827446382077 2881386423091810292393279)
                      ·
                        rfl

theorem cell23_5611480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_5611480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611480 prefixEnd_5611480 := by exact prefixLift 5611480
  have htrace : WordTrace (prefixWord ++ tailWord_5611480) baseStart_5611480 baseEnd_5611480 := by
    simpa [prefixWord, tailWord_5611480, baseEnd_5611480] using wordTrace_append hprefix tailTrace_5611480
  have hstable : (prefixWord ++ tailWord_5611480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611480).length < 2 ^ (prefixWord ++ tailWord_5611480).sum := by decide
  have hdescent : baseEnd_5611480 < baseStart_5611480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611491 : List Nat := [1, 1, 1, 6, 1, 4, 1, 3, 1, 4]
def baseStart_5611491 : Nat := 118140960795 + 5611491 * 2 ^ 59
def prefixEnd_5611491 : Nat := 4983230072969 + 3 ^ 40 * 5611491 * 2
def baseEnd_5611491 : Nat := 960464023793003249785243

theorem tailTrace_5611491 : CollatzResearch.WordTrace tailWord_5611491 prefixEnd_5611491 960464023793003249785243 := by
  unfold tailWord_5611491
  simp only [CollatzResearch.WordTrace]
  refine ⟨204667890913533948208466327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136445260609022632138977551 204667890913533948208466327)
  ·
    refine ⟨307001836370300922312699491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204667890913533948208466327 307001836370300922312699491)
    ·
      refine ⟨460502754555451383469049237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307001836370300922312699491 460502754555451383469049237)
      ·
        refine ⟨21586066619786783600111683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 460502754555451383469049237 21586066619786783600111683)
        ·
          refine ⟨32379099929680175400167525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21586066619786783600111683 32379099929680175400167525)
          ·
            refine ⟨6071081236815032887531411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32379099929680175400167525 6071081236815032887531411)
            ·
              refine ⟨9106621855222549331297117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6071081236815032887531411 9106621855222549331297117)
              ·
                refine ⟨3414983195708455999236419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9106621855222549331297117 3414983195708455999236419)
                ·
                  refine ⟨5122474793562683998854629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3414983195708455999236419 5122474793562683998854629)
                  ·
                    refine ⟨960464023793003249785243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122474793562683998854629 960464023793003249785243)
                    ·
                      rfl

theorem cell23_5611491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 1, 4].length) (baseStart_5611491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611491 prefixEnd_5611491 := by exact prefixLift 5611491
  have htrace : WordTrace (prefixWord ++ tailWord_5611491) baseStart_5611491 baseEnd_5611491 := by
    simpa [prefixWord, tailWord_5611491, baseEnd_5611491] using wordTrace_append hprefix tailTrace_5611491
  have hstable : (prefixWord ++ tailWord_5611491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611491).length < 2 ^ (prefixWord ++ tailWord_5611491).sum := by decide
  have hdescent : baseEnd_5611491 < baseStart_5611491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611501 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5611501 : Nat := 118140960795 + 5611501 * 2 ^ 59
def prefixEnd_5611501 : Nat := 4983230072969 + 3 ^ 40 * 5611501 * 2
def baseEnd_5611501 : Nat := 2881397206185554710230683

theorem tailTrace_5611501 : CollatzResearch.WordTrace tailWord_5611501 prefixEnd_5611501 2881397206185554710230683 := by
  unfold tailWord_5611501
  simp only [CollatzResearch.WordTrace]
  refine ⟨204668255643497719916330357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136445503762331813277553571 204668255643497719916330357)
  ·
    refine ⟨19187648966577911242155971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204668255643497719916330357 19187648966577911242155971)
    ·
      refine ⟨28781473449866866863233957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19187648966577911242155971 28781473449866866863233957)
      ·
        refine ⟨5396526271850037536856367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28781473449866866863233957 5396526271850037536856367)
        ·
          refine ⟨8094789407775056305284551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396526271850037536856367 8094789407775056305284551)
          ·
            refine ⟨12142184111662584457926827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8094789407775056305284551 12142184111662584457926827)
            ·
              refine ⟨18213276167493876686890241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12142184111662584457926827 18213276167493876686890241)
              ·
                refine ⟨13659957125620407515167681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18213276167493876686890241 13659957125620407515167681)
                ·
                  refine ⟨10244967844215305636375761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13659957125620407515167681 10244967844215305636375761)
                  ·
                    refine ⟨7683725883161479227281821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10244967844215305636375761 7683725883161479227281821)
                    ·
                      refine ⟨2881397206185554710230683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683725883161479227281821 2881397206185554710230683)
                      ·
                        rfl

theorem cell23_5611501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5611501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611501 prefixEnd_5611501 := by exact prefixLift 5611501
  have htrace : WordTrace (prefixWord ++ tailWord_5611501) baseStart_5611501 baseEnd_5611501 := by
    simpa [prefixWord, tailWord_5611501, baseEnd_5611501] using wordTrace_append hprefix tailTrace_5611501
  have hstable : (prefixWord ++ tailWord_5611501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611501).length < 2 ^ (prefixWord ++ tailWord_5611501).sum := by decide
  have hdescent : baseEnd_5611501 < baseStart_5611501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611541 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 2, 3, 2]
def baseStart_5611541 : Nat := 118140960795 + 5611541 * 2 ^ 59
def prefixEnd_5611541 : Nat := 4983230072969 + 3 ^ 40 * 5611541 * 2
def baseEnd_5611541 : Nat := 2881417745411734553730499

theorem tailTrace_5611541 : CollatzResearch.WordTrace tailWord_5611541 prefixEnd_5611541 2881417745411734553730499 := by
  unfold tailWord_5611541
  simp only [CollatzResearch.WordTrace]
  refine ⟨204669714563352806747786477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136446476375568537831857651 204669714563352806747786477)
  ·
    refine ⟨76751142961257302530419929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204669714563352806747786477 76751142961257302530419929)
    ·
      refine ⟨57563357220942976897814947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76751142961257302530419929 57563357220942976897814947)
      ·
        refine ⟨86345035831414465346722421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57563357220942976897814947 86345035831414465346722421)
        ·
          refine ⟨8094847109195106126255227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86345035831414465346722421 8094847109195106126255227)
          ·
            refine ⟨12142270663792659189382841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8094847109195106126255227 12142270663792659189382841)
            ·
              refine ⟨9106702997844494392037131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12142270663792659189382841 9106702997844494392037131)
              ·
                refine ⟨13660054496766741588055697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9106702997844494392037131 13660054496766741588055697)
                ·
                  refine ⟨10245040872575056191041773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13660054496766741588055697 10245040872575056191041773)
                  ·
                    refine ⟨3841890327215646071640665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10245040872575056191041773 3841890327215646071640665)
                    ·
                      refine ⟨2881417745411734553730499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841890327215646071640665 2881417745411734553730499)
                      ·
                        rfl

theorem cell23_5611541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 3, 2].length) (baseStart_5611541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611541 prefixEnd_5611541 := by exact prefixLift 5611541
  have htrace : WordTrace (prefixWord ++ tailWord_5611541) baseStart_5611541 baseEnd_5611541 := by
    simpa [prefixWord, tailWord_5611541, baseEnd_5611541] using wordTrace_append hprefix tailTrace_5611541
  have hstable : (prefixWord ++ tailWord_5611541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611541).length < 2 ^ (prefixWord ++ tailWord_5611541).sum := by decide
  have hdescent : baseEnd_5611541 < baseStart_5611541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611557 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 5]
def baseStart_5611557 : Nat := 118140960795 + 5611557 * 2 ^ 59
def prefixEnd_5611557 : Nat := 4983230072969 + 3 ^ 40 * 5611557 * 2
def baseEnd_5611557 : Nat := 2881425961102206491130425

theorem tailTrace_5611557 : CollatzResearch.WordTrace tailWord_5611557 prefixEnd_5611557 2881425961102206491130425 := by
  unfold tailWord_5611557
  simp only [CollatzResearch.WordTrace]
  refine ⟨204670298131294841480368925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136446865420863227653579283 204670298131294841480368925)
  ·
    refine ⟨76751361799235565555138347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204670298131294841480368925 76751361799235565555138347)
    ·
      refine ⟨115127042698853348332707521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76751361799235565555138347 115127042698853348332707521)
      ·
        refine ⟨86345282024140011249530641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115127042698853348332707521 86345282024140011249530641)
        ·
          refine ⟨64758961518105008437147981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86345282024140011249530641 64758961518105008437147981)
          ·
            refine ⟨24284610569289378163930493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64758961518105008437147981 24284610569289378163930493)
            ·
              refine ⟨9106728963483516811473935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24284610569289378163930493 9106728963483516811473935)
              ·
                refine ⟨13660093445225275217210903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9106728963483516811473935 13660093445225275217210903)
                ·
                  refine ⟨20490140167837912825816355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13660093445225275217210903 20490140167837912825816355)
                  ·
                    refine ⟨30735210251756869238724533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20490140167837912825816355 30735210251756869238724533)
                    ·
                      refine ⟨2881425961102206491130425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30735210251756869238724533 2881425961102206491130425)
                      ·
                        rfl

theorem cell23_5611557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_5611557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611557 prefixEnd_5611557 := by exact prefixLift 5611557
  have htrace : WordTrace (prefixWord ++ tailWord_5611557) baseStart_5611557 baseEnd_5611557 := by
    simpa [prefixWord, tailWord_5611557, baseEnd_5611557] using wordTrace_append hprefix tailTrace_5611557
  have hstable : (prefixWord ++ tailWord_5611557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611557).length < 2 ^ (prefixWord ++ tailWord_5611557).sum := by decide
  have hdescent : baseEnd_5611557 < baseStart_5611557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611574 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_5611574 : Nat := 118140960795 + 5611574 * 2 ^ 59
def prefixEnd_5611574 : Nat := 4983230072969 + 3 ^ 40 * 5611574 * 2
def baseEnd_5611574 : Nat := 2881434690273332924617847

theorem tailTrace_5611574 : CollatzResearch.WordTrace tailWord_5611574 prefixEnd_5611574 2881434690273332924617847 := by
  unfold tailWord_5611574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12791932385764578336483611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136447278781488835589158517 12791932385764578336483611)
  ·
    refine ⟨19187898578646867504725417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12791932385764578336483611 19187898578646867504725417)
    ·
      refine ⟨14390923933985150628544063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19187898578646867504725417 14390923933985150628544063)
      ·
        refine ⟨21586385900977725942816095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14390923933985150628544063 21586385900977725942816095)
        ·
          refine ⟨32379578851466588914224143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21586385900977725942816095 32379578851466588914224143)
          ·
            refine ⟨48569368277199883371336215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32379578851466588914224143 48569368277199883371336215)
            ·
              refine ⟨72854052415799825057004323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48569368277199883371336215 72854052415799825057004323)
              ·
                refine ⟨109281078623699737585506485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72854052415799825057004323 109281078623699737585506485)
                ·
                  refine ⟨10245101120971850398641233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109281078623699737585506485 10245101120971850398641233)
                  ·
                    refine ⟨7683825840728887798980925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10245101120971850398641233 7683825840728887798980925)
                    ·
                      refine ⟨2881434690273332924617847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683825840728887798980925 2881434690273332924617847)
                      ·
                        rfl

theorem cell23_5611574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_5611574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611574 prefixEnd_5611574 := by exact prefixLift 5611574
  have htrace : WordTrace (prefixWord ++ tailWord_5611574) baseStart_5611574 baseEnd_5611574 := by
    simpa [prefixWord, tailWord_5611574, baseEnd_5611574] using wordTrace_append hprefix tailTrace_5611574
  have hstable : (prefixWord ++ tailWord_5611574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611574).length < 2 ^ (prefixWord ++ tailWord_5611574).sum := by decide
  have hdescent : baseEnd_5611574 < baseStart_5611574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611604 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_5611604 : Nat := 118140960795 + 5611604 * 2 ^ 59
def prefixEnd_5611604 : Nat := 4983230072969 + 3 ^ 40 * 5611604 * 2
def baseEnd_5611604 : Nat := 2881450094692967807242709

theorem tailTrace_5611604 : CollatzResearch.WordTrace tailWord_5611604 prefixEnd_5611604 2881450094692967807242709 := by
  unfold tailWord_5611604
  simp only [CollatzResearch.WordTrace]
  refine ⟨102336006181062284253664933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136448008241416379004886577 102336006181062284253664933)
  ·
    refine ⟨19188001158949178297562175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102336006181062284253664933 19188001158949178297562175)
    ·
      refine ⟨28782001738423767446343263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19188001158949178297562175 28782001738423767446343263)
      ·
        refine ⟨43173002607635651169514895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28782001738423767446343263 43173002607635651169514895)
        ·
          refine ⟨64759503911453476754272343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43173002607635651169514895 64759503911453476754272343)
          ·
            refine ⟨97139255867180215131408515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64759503911453476754272343 97139255867180215131408515)
            ·
              refine ⟨145708883800770322697112773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97139255867180215131408515 145708883800770322697112773)
              ·
                refine ⟨27320415712644435505708645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145708883800770322697112773 27320415712644435505708645)
                ·
                  refine ⟨5122577946120831657320371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27320415712644435505708645 5122577946120831657320371)
                  ·
                    refine ⟨7683866919181247485980557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5122577946120831657320371 7683866919181247485980557)
                    ·
                      refine ⟨2881450094692967807242709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683866919181247485980557 2881450094692967807242709)
                      ·
                        rfl

theorem cell23_5611604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_5611604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611604 prefixEnd_5611604 := by exact prefixLift 5611604
  have htrace : WordTrace (prefixWord ++ tailWord_5611604) baseStart_5611604 baseEnd_5611604 := by
    simpa [prefixWord, tailWord_5611604, baseEnd_5611604] using wordTrace_append hprefix tailTrace_5611604
  have hstable : (prefixWord ++ tailWord_5611604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611604).length < 2 ^ (prefixWord ++ tailWord_5611604).sum := by decide
  have hdescent : baseEnd_5611604 < baseStart_5611604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611621 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 3]
def baseStart_5611621 : Nat := 118140960795 + 5611621 * 2 ^ 59
def prefixEnd_5611621 : Nat := 4983230072969 + 3 ^ 40 * 5611621 * 2
def baseEnd_5611621 : Nat := 2881458823864094240730131

theorem tailTrace_5611621 : CollatzResearch.WordTrace tailWord_5611621 prefixEnd_5611621 2881458823864094240730131 := by
  unfold tailWord_5611621
  simp only [CollatzResearch.WordTrace]
  refine ⟨204672632403062980410698717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136448421602041986940465811 204672632403062980410698717)
  ·
    refine ⟨76752237151148617654012019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204672632403062980410698717 76752237151148617654012019)
    ·
      refine ⟨115128355726722926481018029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76752237151148617654012019 115128355726722926481018029)
      ·
        refine ⟨43173133397521097430381761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115128355726722926481018029 43173133397521097430381761)
        ·
          refine ⟨32379850048140823072786321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43173133397521097430381761 32379850048140823072786321)
          ·
            refine ⟨24284887536105617304589741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32379850048140823072786321 24284887536105617304589741)
            ·
              refine ⟨9106832826039606489221153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24284887536105617304589741 9106832826039606489221153)
              ·
                refine ⟨6830124619529704866915865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9106832826039606489221153 6830124619529704866915865)
                ·
                  refine ⟨5122593464647278650186899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830124619529704866915865 5122593464647278650186899)
                  ·
                    refine ⟨7683890196970917975280349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5122593464647278650186899 7683890196970917975280349)
                    ·
                      refine ⟨2881458823864094240730131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7683890196970917975280349 2881458823864094240730131)
                      ·
                        rfl

theorem cell23_5611621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_5611621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611621 prefixEnd_5611621 := by exact prefixLift 5611621
  have htrace : WordTrace (prefixWord ++ tailWord_5611621) baseStart_5611621 baseEnd_5611621 := by
    simpa [prefixWord, tailWord_5611621, baseEnd_5611621] using wordTrace_append hprefix tailTrace_5611621
  have hstable : (prefixWord ++ tailWord_5611621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611621).length < 2 ^ (prefixWord ++ tailWord_5611621).sum := by decide
  have hdescent : baseEnd_5611621 < baseStart_5611621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611627 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 10, 2]
def baseStart_5611627 : Nat := 118140960795 + 5611627 * 2 ^ 59
def prefixEnd_5611627 : Nat := 4983230072969 + 3 ^ 40 * 5611627 * 2
def baseEnd_5611627 : Nat := 2881461904748021217255103

theorem tailTrace_5611627 : CollatzResearch.WordTrace tailWord_5611627 prefixEnd_5611627 2881461904748021217255103 := by
  unfold tailWord_5611627
  simp only [CollatzResearch.WordTrace]
  refine ⟨204672851241041243435417135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136448567494027495623611423 204672851241041243435417135)
  ·
    refine ⟨307009276861561865153125703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204672851241041243435417135 307009276861561865153125703)
    ·
      refine ⟨460513915292342797729688555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307009276861561865153125703 460513915292342797729688555)
      ·
        refine ⟨690770872938514196594532833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460513915292342797729688555 690770872938514196594532833)
        ·
          refine ⟨518078154703885647445899625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690770872938514196594532833 518078154703885647445899625)
          ·
            refine ⟨388558616027914235584424719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518078154703885647445899625 388558616027914235584424719)
            ·
              refine ⟨582837924041871353376637079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388558616027914235584424719 582837924041871353376637079)
              ·
                refine ⟨874256886062807030064955619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582837924041871353376637079 874256886062807030064955619)
                ·
                  refine ⟨1311385329094210545097433429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874256886062807030064955619 1311385329094210545097433429)
                  ·
                    refine ⟨3841949206330694956340137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1311385329094210545097433429 3841949206330694956340137)
                    ·
                      refine ⟨2881461904748021217255103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3841949206330694956340137 2881461904748021217255103)
                      ·
                        rfl

theorem cell23_5611627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 10, 2].length) (baseStart_5611627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611627 prefixEnd_5611627 := by exact prefixLift 5611627
  have htrace : WordTrace (prefixWord ++ tailWord_5611627) baseStart_5611627 baseEnd_5611627 := by
    simpa [prefixWord, tailWord_5611627, baseEnd_5611627] using wordTrace_append hprefix tailTrace_5611627
  have hstable : (prefixWord ++ tailWord_5611627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611627).length < 2 ^ (prefixWord ++ tailWord_5611627).sum := by decide
  have hdescent : baseEnd_5611627 < baseStart_5611627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611717 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 4]
def baseStart_5611717 : Nat := 118140960795 + 5611717 * 2 ^ 59
def prefixEnd_5611717 : Nat := 4983230072969 + 3 ^ 40 * 5611717 * 2
def baseEnd_5611717 : Nat := 2881508118006925865129689

theorem tailTrace_5611717 : CollatzResearch.WordTrace tailWord_5611717 prefixEnd_5611717 2881508118006925865129689 := by
  unfold tailWord_5611717
  simp only [CollatzResearch.WordTrace]
  refine ⟨204676133810715188806193405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136450755873810125870795603 204676133810715188806193405)
  ·
    refine ⟨76753550179018195802322527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204676133810715188806193405 76753550179018195802322527)
    ·
      refine ⟨115130325268527293703483791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76753550179018195802322527 115130325268527293703483791)
      ·
        refine ⟨172695487902790940555225687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115130325268527293703483791 172695487902790940555225687)
        ·
          refine ⟨259043231854186410832838531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172695487902790940555225687 259043231854186410832838531)
          ·
            refine ⟨388564847781279616249257797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259043231854186410832838531 388564847781279616249257797)
            ·
              refine ⟨72855908958989928046735837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 388564847781279616249257797 72855908958989928046735837)
              ·
                refine ⟨27320965859621223017525939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72855908958989928046735837 27320965859621223017525939)
                ·
                  refine ⟨40981448789431834526288909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27320965859621223017525939 40981448789431834526288909)
                  ·
                    refine ⟨15368043296036937947358341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40981448789431834526288909 15368043296036937947358341)
                    ·
                      refine ⟨2881508118006925865129689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15368043296036937947358341 2881508118006925865129689)
                      ·
                        rfl

theorem cell23_5611717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_5611717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611717 prefixEnd_5611717 := by exact prefixLift 5611717
  have htrace : WordTrace (prefixWord ++ tailWord_5611717) baseStart_5611717 baseEnd_5611717 := by
    simpa [prefixWord, tailWord_5611717, baseEnd_5611717] using wordTrace_append hprefix tailTrace_5611717
  have hstable : (prefixWord ++ tailWord_5611717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611717).length < 2 ^ (prefixWord ++ tailWord_5611717).sum := by decide
  have hdescent : baseEnd_5611717 < baseStart_5611717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611744 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_5611744 : Nat := 118140960795 + 5611744 * 2 ^ 59
def prefixEnd_5611744 : Nat := 4983230072969 + 3 ^ 40 * 5611744 * 2
def baseEnd_5611744 : Nat := 960507327328199086497355

theorem tailTrace_5611744 : CollatzResearch.WordTrace tailWord_5611744 prefixEnd_5611744 960507327328199086497355 := by
  unfold tailWord_5611744
  simp only [CollatzResearch.WordTrace]
  refine ⟨102338559290808686208713143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136451412387744914944950857 102338559290808686208713143)
  ·
    refine ⟨153507838936213029313069715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102338559290808686208713143 153507838936213029313069715)
    ·
      refine ⟨230261758404319543969604573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153507838936213029313069715 230261758404319543969604573)
      ·
        refine ⟨86348159401619828988601715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230261758404319543969604573 86348159401619828988601715)
        ·
          refine ⟨129522239102429743482902573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86348159401619828988601715 129522239102429743482902573)
          ·
            refine ⟨48570839663411153806088465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129522239102429743482902573 48570839663411153806088465)
            ·
              refine ⟨36428129747558365354566349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48570839663411153806088465 36428129747558365354566349)
              ·
                refine ⟨13660548655334387007962381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36428129747558365354566349 13660548655334387007962381)
                ·
                  refine ⟨5122705745750395127985893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13660548655334387007962381 5122705745750395127985893)
                  ·
                    refine ⟨960507327328199086497355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122705745750395127985893 960507327328199086497355)
                    ·
                      rfl

theorem cell23_5611744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_5611744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611744 prefixEnd_5611744 := by exact prefixLift 5611744
  have htrace : WordTrace (prefixWord ++ tailWord_5611744) baseStart_5611744 baseEnd_5611744 := by
    simpa [prefixWord, tailWord_5611744, baseEnd_5611744] using wordTrace_append hprefix tailTrace_5611744
  have hstable : (prefixWord ++ tailWord_5611744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611744).length < 2 ^ (prefixWord ++ tailWord_5611744).sum := by decide
  have hdescent : baseEnd_5611744 < baseStart_5611744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
