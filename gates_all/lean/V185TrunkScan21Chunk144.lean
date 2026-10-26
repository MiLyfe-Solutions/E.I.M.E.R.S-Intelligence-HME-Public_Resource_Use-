import V185TrunkScan21Chunk143

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1755293 : List Nat := [1, 4, 2, 1, 1, 5, 7]
def baseStart_1755293 : Nat := 118140960795 + 1755293 * 2 ^ 59
def prefixEnd_1755293 : Nat := 4983230072969 + 3 ^ 40 * 1755293 * 2
def baseEnd_1755293 : Nat := 44509086344321290951361

theorem tailTrace_1755293 : CollatzResearch.WordTrace tailWord_1755293 prefixEnd_1755293 44509086344321290951361 := by
  unfold tailWord_1755293
  simp only [CollatzResearch.WordTrace]
  refine ⟨64020795229880716022790533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42680530153253810681860355 64020795229880716022790533)
  ·
    refine ⟨12003899105602634254273225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64020795229880716022790533 12003899105602634254273225)
    ·
      refine ⟨9002924329201975690704919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12003899105602634254273225 9002924329201975690704919)
      ·
        refine ⟨13504386493802963536057379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9002924329201975690704919 13504386493802963536057379)
        ·
          refine ⟨20256579740704445304086069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13504386493802963536057379 20256579740704445304086069)
          ·
            refine ⟨1899054350691041747258069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20256579740704445304086069 1899054350691041747258069)
            ·
              refine ⟨44509086344321290951361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1899054350691041747258069 44509086344321290951361)
              ·
                rfl

theorem cell21_1755293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 7].length) (baseStart_1755293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755293 prefixEnd_1755293 := by exact prefixLift 1755293
  have htrace : WordTrace (prefixWord ++ tailWord_1755293) baseStart_1755293 baseEnd_1755293 := by
    simpa [prefixWord, tailWord_1755293, baseEnd_1755293] using wordTrace_append hprefix tailTrace_1755293
  have hstable : (prefixWord ++ tailWord_1755293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755293).length < 2 ^ (prefixWord ++ tailWord_1755293).sum := by decide
  have hdescent : baseEnd_1755293 < baseStart_1755293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755313 : List Nat := [1, 2, 2, 5, 2, 2, 2, 1, 4]
def baseStart_1755313 : Nat := 118140960795 + 1755313 * 2 ^ 59
def prefixEnd_1755313 : Nat := 4983230072969 + 3 ^ 40 * 1755313 * 2
def baseEnd_1755313 : Nat := 400586341371376028228875

theorem tailTrace_1755313 : CollatzResearch.WordTrace tailWord_1755313 prefixEnd_1755313 400586341371376028228875 := by
  unfold tailWord_1755313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64021524689808259438518593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42681016459872172959012395 64021524689808259438518593)
  ·
    refine ⟨48016143517356194578888945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64021524689808259438518593 48016143517356194578888945)
    ·
      refine ⟨36012107638017145934166709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48016143517356194578888945 36012107638017145934166709)
      ·
        refine ⟨3376135091064107431328129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36012107638017145934166709 3376135091064107431328129)
        ·
          refine ⟨2532101318298080573496097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376135091064107431328129 2532101318298080573496097)
          ·
            refine ⟨1899075988723560430122073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532101318298080573496097 1899075988723560430122073)
            ·
              refine ⟨1424306991542670322591555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899075988723560430122073 1424306991542670322591555)
              ·
                refine ⟨2136460487314005483887333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424306991542670322591555 2136460487314005483887333)
                ·
                  refine ⟨400586341371376028228875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136460487314005483887333 400586341371376028228875)
                  ·
                    rfl

theorem cell21_1755313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_1755313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755313 prefixEnd_1755313 := by exact prefixLift 1755313
  have htrace : WordTrace (prefixWord ++ tailWord_1755313) baseStart_1755313 baseEnd_1755313 := by
    simpa [prefixWord, tailWord_1755313, baseEnd_1755313] using wordTrace_append hprefix tailTrace_1755313
  have hstable : (prefixWord ++ tailWord_1755313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755313).length < 2 ^ (prefixWord ++ tailWord_1755313).sum := by decide
  have hdescent : baseEnd_1755313 < baseStart_1755313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755352 : List Nat := [2, 1, 2, 2, 4, 10]
def baseStart_1755352 : Nat := 118140960795 + 1755352 * 2 ^ 59
def prefixEnd_1755352 : Nat := 4983230072969 + 3 ^ 40 * 1755352 * 2
def baseEnd_1755352 : Nat := 14836860803804467669585

theorem tailTrace_1755352 : CollatzResearch.WordTrace tailWord_1755352 prefixEnd_1755352 14836860803804467669585 := by
  unfold tailWord_1755352
  simp only [CollatzResearch.WordTrace]
  refine ⟨32011473568333484549594155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42681964757777979399458873 32011473568333484549594155)
  ·
    refine ⟨48017210352500226824391233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32011473568333484549594155 48017210352500226824391233)
    ·
      refine ⟨36012907764375170118293425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48017210352500226824391233 36012907764375170118293425)
      ·
        refine ⟨27009680823281377588720069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36012907764375170118293425 27009680823281377588720069)
        ·
          refine ⟨5064315154365258297885013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27009680823281377588720069 5064315154365258297885013)
          ·
            refine ⟨14836860803804467669585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5064315154365258297885013 14836860803804467669585)
            ·
              rfl

theorem cell21_1755352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 10].length) (baseStart_1755352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755352 prefixEnd_1755352 := by exact prefixLift 1755352
  have htrace : WordTrace (prefixWord ++ tailWord_1755352) baseStart_1755352 baseEnd_1755352 := by
    simpa [prefixWord, tailWord_1755352, baseEnd_1755352] using wordTrace_append hprefix tailTrace_1755352
  have hstable : (prefixWord ++ tailWord_1755352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755352).length < 2 ^ (prefixWord ++ tailWord_1755352).sum := by decide
  have hdescent : baseEnd_1755352 < baseStart_1755352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755476 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1755476 : Nat := 118140960795 + 1755476 * 2 ^ 59
def prefixEnd_1755476 : Nat := 4983230072969 + 3 ^ 40 * 1755476 * 2
def baseEnd_1755476 : Nat := 400623540192123967011875

theorem tailTrace_1755476 : CollatzResearch.WordTrace tailWord_1755476 prefixEnd_1755476 400623540192123967011875 := by
  unfold tailWord_1755476
  simp only [CollatzResearch.WordTrace]
  refine ⟨32013734894108869138351141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42684979858811825517801521 32013734894108869138351141)
  ·
    refine ⟨6002575292645412963440839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32013734894108869138351141 6002575292645412963440839)
    ·
      refine ⟨9003862938968119445161259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6002575292645412963440839 9003862938968119445161259)
      ·
        refine ⟨13505794408452179167741889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9003862938968119445161259 13505794408452179167741889)
        ·
          refine ⟨10129345806339134375806417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13505794408452179167741889 10129345806339134375806417)
          ·
            refine ⟨7597009354754350781854813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10129345806339134375806417 7597009354754350781854813)
            ·
              refine ⟨2848878508032881543195555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7597009354754350781854813 2848878508032881543195555)
              ·
                refine ⟨4273317762049322314793333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2848878508032881543195555 4273317762049322314793333)
                ·
                  refine ⟨400623540192123967011875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273317762049322314793333 400623540192123967011875)
                  ·
                    rfl

theorem cell21_1755476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1755476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755476 prefixEnd_1755476 := by exact prefixLift 1755476
  have htrace : WordTrace (prefixWord ++ tailWord_1755476) baseStart_1755476 baseEnd_1755476 := by
    simpa [prefixWord, tailWord_1755476, baseEnd_1755476] using wordTrace_append hprefix tailTrace_1755476
  have hstable : (prefixWord ++ tailWord_1755476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755476).length < 2 ^ (prefixWord ++ tailWord_1755476).sum := by decide
  have hdescent : baseEnd_1755476 < baseStart_1755476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755504 : List Nat := [2, 1, 1, 1, 4, 3, 2, 7]
def baseStart_1755504 : Nat := 118140960795 + 1755504 * 2 ^ 59
def prefixEnd_1755504 : Nat := 4983230072969 + 3 ^ 40 * 1755504 * 2
def baseEnd_1755504 : Nat := 133543310057867380181717

theorem tailTrace_1755504 : CollatzResearch.WordTrace tailWord_1755504 prefixEnd_1755504 133543310057867380181717 := by
  unfold tailWord_1755504
  simp only [CollatzResearch.WordTrace]
  refine ⟨32014245516058149529360783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42685660688077532705814377 32014245516058149529360783)
  ·
    refine ⟨48021368274087224294041175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32014245516058149529360783 48021368274087224294041175)
    ·
      refine ⟨72032052411130836441061763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48021368274087224294041175 72032052411130836441061763)
      ·
        refine ⟨108048078616696254661592645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72032052411130836441061763 108048078616696254661592645)
        ·
          refine ⟨20259014740630547749048621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108048078616696254661592645 20259014740630547749048621)
          ·
            refine ⟨7597130527736455405893233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20259014740630547749048621 7597130527736455405893233)
            ·
              refine ⟨5697847895802341554419925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7597130527736455405893233 5697847895802341554419925)
              ·
                refine ⟨133543310057867380181717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5697847895802341554419925 133543310057867380181717)
                ·
                  rfl

theorem cell21_1755504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_1755504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755504 prefixEnd_1755504 := by exact prefixLift 1755504
  have htrace : WordTrace (prefixWord ++ tailWord_1755504) baseStart_1755504 baseEnd_1755504 := by
    simpa [prefixWord, tailWord_1755504, baseEnd_1755504] using wordTrace_append hprefix tailTrace_1755504
  have hstable : (prefixWord ++ tailWord_1755504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755504).length < 2 ^ (prefixWord ++ tailWord_1755504).sum := by decide
  have hdescent : baseEnd_1755504 < baseStart_1755504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755569 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 3]
def baseStart_1755569 : Nat := 118140960795 + 1755569 * 2 ^ 59
def prefixEnd_1755569 : Nat := 4983230072969 + 3 ^ 40 * 1755569 * 2
def baseEnd_1755569 : Nat := 400644764059176471961685

theorem tailTrace_1755569 : CollatzResearch.WordTrace tailWord_1755569 prefixEnd_1755569 400644764059176471961685 := by
  unfold tailWord_1755569
  simp only [CollatzResearch.WordTrace]
  refine ⟨64030861776880815159837761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42687241184587210106558507 64030861776880815159837761)
  ·
    refine ⟨48023146332660611369878321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64030861776880815159837761 48023146332660611369878321)
    ·
      refine ⟨36017359749495458527408741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48023146332660611369878321 36017359749495458527408741)
      ·
        refine ⟨6753254953030398473889139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36017359749495458527408741 6753254953030398473889139)
        ·
          refine ⟨10129882429545597710833709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6753254953030398473889139 10129882429545597710833709)
          ·
            refine ⟨3798705911079599141562641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10129882429545597710833709 3798705911079599141562641)
            ·
              refine ⟨2849029433309699356171981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798705911079599141562641 2849029433309699356171981)
              ·
                refine ⟨1068386037491137258564493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849029433309699356171981 1068386037491137258564493)
                ·
                  refine ⟨400644764059176471961685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068386037491137258564493 400644764059176471961685)
                  ·
                    rfl

theorem cell21_1755569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 3].length) (baseStart_1755569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755569 prefixEnd_1755569 := by exact prefixLift 1755569
  have htrace : WordTrace (prefixWord ++ tailWord_1755569) baseStart_1755569 baseEnd_1755569 := by
    simpa [prefixWord, tailWord_1755569, baseEnd_1755569] using wordTrace_append hprefix tailTrace_1755569
  have hstable : (prefixWord ++ tailWord_1755569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755569).length < 2 ^ (prefixWord ++ tailWord_1755569).sum := by decide
  have hdescent : baseEnd_1755569 < baseStart_1755569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755645 : List Nat := [1, 4, 1, 1, 1, 3, 5, 2, 3]
def baseStart_1755645 : Nat := 118140960795 + 1755645 * 2 ^ 59
def prefixEnd_1755645 : Nat := 4983230072969 + 3 ^ 40 * 1755645 * 2
def baseEnd_1755645 : Nat := 400662108294617228694863

theorem tailTrace_1755645 : CollatzResearch.WordTrace tailWord_1755645 prefixEnd_1755645 400662108294617228694863 := by
  unfold tailWord_1755645
  simp only [CollatzResearch.WordTrace]
  refine ⟨64033633724605480139604389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42689089149736986759736259 64033633724605480139604389)
  ·
    refine ⟨12006306323363527526175823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64033633724605480139604389 12006306323363527526175823)
    ·
      refine ⟨18009459485045291289263735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006306323363527526175823 18009459485045291289263735)
      ·
        refine ⟨27014189227567936933895603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18009459485045291289263735 27014189227567936933895603)
        ·
          refine ⟨40521283841351905400843405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27014189227567936933895603 40521283841351905400843405)
          ·
            refine ⟨15195481440506964525316277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40521283841351905400843405 15195481440506964525316277)
            ·
              refine ⟨1424576385047527924248401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15195481440506964525316277 1424576385047527924248401)
              ·
                refine ⟨1068432288785645943186301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424576385047527924248401 1068432288785645943186301)
                ·
                  refine ⟨400662108294617228694863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068432288785645943186301 400662108294617228694863)
                  ·
                    rfl

theorem cell21_1755645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_1755645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755645 prefixEnd_1755645 := by exact prefixLift 1755645
  have htrace : WordTrace (prefixWord ++ tailWord_1755645) baseStart_1755645 baseEnd_1755645 := by
    simpa [prefixWord, tailWord_1755645, baseEnd_1755645] using wordTrace_append hprefix tailTrace_1755645
  have hstable : (prefixWord ++ tailWord_1755645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755645).length < 2 ^ (prefixWord ++ tailWord_1755645).sum := by decide
  have hdescent : baseEnd_1755645 < baseStart_1755645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755659 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 4]
def baseStart_1755659 : Nat := 118140960795 + 1755659 * 2 ^ 59
def prefixEnd_1755659 : Nat := 4983230072969 + 3 ^ 40 * 1755659 * 2
def baseEnd_1755659 : Nat := 400665303285356315461501

theorem tailTrace_1755659 : CollatzResearch.WordTrace tailWord_1755659 prefixEnd_1755659 400665303285356315461501 := by
  unfold tailWord_1755659
  simp only [CollatzResearch.WordTrace]
  refine ⟨64034144346554760530614031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42689429564369840353742687 64034144346554760530614031)
  ·
    refine ⟨96051216519832140795921047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64034144346554760530614031 96051216519832140795921047)
    ·
      refine ⟨144076824779748211193881571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96051216519832140795921047 144076824779748211193881571)
      ·
        refine ⟨216115237169622316790822357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144076824779748211193881571 216115237169622316790822357)
        ·
          refine ⟨5065200871163023049784899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 216115237169622316790822357 5065200871163023049784899)
          ·
            refine ⟨7597801306744534574677349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065200871163023049784899 7597801306744534574677349)
            ·
              refine ⟨1424587745014600232752003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7597801306744534574677349 1424587745014600232752003)
              ·
                refine ⟨2136881617521900349128005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424587745014600232752003 2136881617521900349128005)
                ·
                  refine ⟨400665303285356315461501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136881617521900349128005 400665303285356315461501)
                  ·
                    rfl

theorem cell21_1755659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_1755659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755659 prefixEnd_1755659 := by exact prefixLift 1755659
  have htrace : WordTrace (prefixWord ++ tailWord_1755659) baseStart_1755659 baseEnd_1755659 := by
    simpa [prefixWord, tailWord_1755659, baseEnd_1755659] using wordTrace_append hprefix tailTrace_1755659
  have hstable : (prefixWord ++ tailWord_1755659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755659).length < 2 ^ (prefixWord ++ tailWord_1755659).sum := by decide
  have hdescent : baseEnd_1755659 < baseStart_1755659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755704 : List Nat := [2, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_1755704 : Nat := 118140960795 + 1755704 * 2 ^ 59
def prefixEnd_1755704 : Nat := 4983230072969 + 3 ^ 40 * 1755704 * 2
def baseEnd_1755704 : Nat := 400675572898446237211409

theorem tailTrace_1755704 : CollatzResearch.WordTrace tailWord_1755704 prefixEnd_1755704 400675572898446237211409 := by
  unfold tailWord_1755704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017892815695866608001083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42690523754261155477334777 32017892815695866608001083)
  ·
    refine ⟨48026839223543799912001625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32017892815695866608001083 48026839223543799912001625)
    ·
      refine ⟨36020129417657849934001219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48026839223543799912001625 36020129417657849934001219)
      ·
        refine ⟨54030194126486774901001829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36020129417657849934001219 54030194126486774901001829)
        ·
          refine ⟨10130661398716270293937843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54030194126486774901001829 10130661398716270293937843)
          ·
            refine ⟨15195992098074405440906765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10130661398716270293937843 15195992098074405440906765)
            ·
              refine ⟨5698497036777902040340037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15195992098074405440906765 5698497036777902040340037)
              ·
                refine ⟨1068468194395856632563757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5698497036777902040340037 1068468194395856632563757)
                ·
                  refine ⟨400675572898446237211409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068468194395856632563757 400675572898446237211409)
                  ·
                    rfl

theorem cell21_1755704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_1755704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755704 prefixEnd_1755704 := by exact prefixLift 1755704
  have htrace : WordTrace (prefixWord ++ tailWord_1755704) baseStart_1755704 baseEnd_1755704 := by
    simpa [prefixWord, tailWord_1755704, baseEnd_1755704] using wordTrace_append hprefix tailTrace_1755704
  have hstable : (prefixWord ++ tailWord_1755704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755704).length < 2 ^ (prefixWord ++ tailWord_1755704).sum := by decide
  have hdescent : baseEnd_1755704 < baseStart_1755704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755752 : List Nat := [2, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_1755752 : Nat := 118140960795 + 1755752 * 2 ^ 59
def prefixEnd_1755752 : Nat := 4983230072969 + 3 ^ 40 * 1755752 * 2
def baseEnd_1755752 : Nat := 400686527152408820411311

theorem tailTrace_1755752 : CollatzResearch.WordTrace tailWord_1755752 prefixEnd_1755752 400686527152408820411311 := by
  unfold tailWord_1755752
  simp only [CollatzResearch.WordTrace]
  refine ⟨32018768167608918706874755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42691690890145224942499673 32018768167608918706874755)
  ·
    refine ⟨48028152251413378060312133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32018768167608918706874755 48028152251413378060312133)
    ·
      refine ⟨9005278547140008386308525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48028152251413378060312133 9005278547140008386308525)
      ·
        refine ⟨3376979455177503144865697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9005278547140008386308525 3376979455177503144865697)
        ·
          refine ⟨2532734591383127358649273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376979455177503144865697 2532734591383127358649273)
          ·
            refine ⟨1899550943537345518986955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2532734591383127358649273 1899550943537345518986955)
            ·
              refine ⟨2849326415306018278480433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899550943537345518986955 2849326415306018278480433)
              ·
                refine ⟨2136994811479513708860325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849326415306018278480433 2136994811479513708860325)
                ·
                  refine ⟨400686527152408820411311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136994811479513708860325 400686527152408820411311)
                  ·
                    rfl

theorem cell21_1755752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_1755752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755752 prefixEnd_1755752 := by exact prefixLift 1755752
  have htrace : WordTrace (prefixWord ++ tailWord_1755752) baseStart_1755752 baseEnd_1755752 := by
    simpa [prefixWord, tailWord_1755752, baseEnd_1755752] using wordTrace_append hprefix tailTrace_1755752
  have hstable : (prefixWord ++ tailWord_1755752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755752).length < 2 ^ (prefixWord ++ tailWord_1755752).sum := by decide
  have hdescent : baseEnd_1755752 < baseStart_1755752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755791 : List Nat := [1, 1, 2, 1, 1, 1, 1, 13]
def baseStart_1755791 : Nat := 118140960795 + 1755791 * 2 ^ 59
def prefixEnd_1755791 : Nat := 4983230072969 + 3 ^ 40 * 1755791 * 2
def baseEnd_1755791 : Nat := 133565142494584473087077

theorem tailTrace_1755791 : CollatzResearch.WordTrace tailWord_1755791 prefixEnd_1755791 133565142494584473087077 := by
  unfold tailWord_1755791
  simp only [CollatzResearch.WordTrace]
  refine ⟨64038958782076547074419227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42692639188051031382946151 64038958782076547074419227)
  ·
    refine ⟨96058438173114820611628841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64038958782076547074419227 96058438173114820611628841)
    ·
      refine ⟨72043828629836115458721631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96058438173114820611628841 72043828629836115458721631)
      ·
        refine ⟨108065742944754173188082447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72043828629836115458721631 108065742944754173188082447)
        ·
          refine ⟨162098614417131259782123671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108065742944754173188082447 162098614417131259782123671)
          ·
            refine ⟨243147921625696889673185507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162098614417131259782123671 243147921625696889673185507)
            ·
              refine ⟨364721882438545334509778261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243147921625696889673185507 364721882438545334509778261)
              ·
                refine ⟨133565142494584473087077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 364721882438545334509778261 133565142494584473087077)
                ·
                  rfl

theorem cell21_1755791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_1755791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755791 prefixEnd_1755791 := by exact prefixLift 1755791
  have htrace : WordTrace (prefixWord ++ tailWord_1755791) baseStart_1755791 baseEnd_1755791 := by
    simpa [prefixWord, tailWord_1755791, baseEnd_1755791] using wordTrace_append hprefix tailTrace_1755791
  have hstable : (prefixWord ++ tailWord_1755791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755791).length < 2 ^ (prefixWord ++ tailWord_1755791).sum := by decide
  have hdescent : baseEnd_1755791 < baseStart_1755791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755794 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1755794 : Nat := 118140960795 + 1755794 * 2 ^ 59
def prefixEnd_1755794 : Nat := 4983230072969 + 3 ^ 40 * 1755794 * 2
def baseEnd_1755794 : Nat := 400696112124626080711225

theorem tailTrace_1755794 : CollatzResearch.WordTrace tailWord_1755794 prefixEnd_1755794 400696112124626080711225 := by
  unfold tailWord_1755794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16009767050266419646694609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42692712134043785724518957 16009767050266419646694609)
  ·
    refine ⟨12007325287699814735020957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16009767050266419646694609 12007325287699814735020957)
    ·
      refine ⟨4502746982887430525632859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12007325287699814735020957 4502746982887430525632859)
      ·
        refine ⟨6754120474331145788449289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4502746982887430525632859 6754120474331145788449289)
        ·
          refine ⟨5065590355748359341336967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6754120474331145788449289 5065590355748359341336967)
          ·
            refine ⟨7598385533622539012005451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065590355748359341336967 7598385533622539012005451)
            ·
              refine ⟨11397578300433808518008177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7598385533622539012005451 11397578300433808518008177)
              ·
                refine ⟨8548183725325356388506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11397578300433808518008177 8548183725325356388506133)
                ·
                  refine ⟨400696112124626080711225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8548183725325356388506133 400696112124626080711225)
                  ·
                    rfl

theorem cell21_1755794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1755794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755794 prefixEnd_1755794 := by exact prefixLift 1755794
  have htrace : WordTrace (prefixWord ++ tailWord_1755794) baseStart_1755794 baseEnd_1755794 := by
    simpa [prefixWord, tailWord_1755794, baseEnd_1755794] using wordTrace_append hprefix tailTrace_1755794
  have hstable : (prefixWord ++ tailWord_1755794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755794).length < 2 ^ (prefixWord ++ tailWord_1755794).sum := by decide
  have hdescent : baseEnd_1755794 < baseStart_1755794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755873 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 3]
def baseStart_1755873 : Nat := 118140960795 + 1755873 * 2 ^ 59
def prefixEnd_1755873 : Nat := 4983230072969 + 3 ^ 40 * 1755873 * 2
def baseEnd_1755873 : Nat := 400714141000939498894397

theorem tailTrace_1755873 : CollatzResearch.WordTrace tailWord_1755873 prefixEnd_1755873 400714141000939498894397 := by
  unfold tailWord_1755873
  simp only [CollatzResearch.WordTrace]
  refine ⟨64041949567779475078904273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42694633045186316719269515 64041949567779475078904273)
  ·
    refine ⟨48031462175834606309178205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64041949567779475078904273 48031462175834606309178205)
    ·
      refine ⟨18011798315937977365941827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48031462175834606309178205 18011798315937977365941827)
      ·
        refine ⟨27017697473906966048912741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18011798315937977365941827 27017697473906966048912741)
        ·
          refine ⟨5065818276357556134171139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27017697473906966048912741 5065818276357556134171139)
          ·
            refine ⟨7598727414536334201256709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5065818276357556134171139 7598727414536334201256709)
            ·
              refine ⟨1424761390225562662735633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7598727414536334201256709 1424761390225562662735633)
              ·
                refine ⟨1068571042669171997051725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424761390225562662735633 1068571042669171997051725)
                ·
                  refine ⟨400714141000939498894397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068571042669171997051725 400714141000939498894397)
                  ·
                    rfl

theorem cell21_1755873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_1755873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755873 prefixEnd_1755873 := by exact prefixLift 1755873
  have htrace : WordTrace (prefixWord ++ tailWord_1755873) baseStart_1755873 baseEnd_1755873 := by
    simpa [prefixWord, tailWord_1755873, baseEnd_1755873] using wordTrace_append hprefix tailTrace_1755873
  have hstable : (prefixWord ++ tailWord_1755873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755873).length < 2 ^ (prefixWord ++ tailWord_1755873).sum := by decide
  have hdescent : baseEnd_1755873 < baseStart_1755873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755898 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1755898 : Nat := 118140960795 + 1755898 * 2 ^ 59
def prefixEnd_1755898 : Nat := 4983230072969 + 3 ^ 40 * 1755898 * 2
def baseEnd_1755898 : Nat := 400719846341545010977679

theorem tailTrace_1755898 : CollatzResearch.WordTrace tailWord_1755898 prefixEnd_1755898 400719846341545010977679 := by
  unfold tailWord_1755898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010715348172226087141087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42695240928459269565709565 16010715348172226087141087)
  ·
    refine ⟨24016073022258339130711631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16010715348172226087141087 24016073022258339130711631)
    ·
      refine ⟨36024109533387508696067447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24016073022258339130711631 36024109533387508696067447)
      ·
        refine ⟨54036164300081263044101171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36024109533387508696067447 54036164300081263044101171)
        ·
          refine ⟨81054246450121894566151757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54036164300081263044101171 81054246450121894566151757)
          ·
            refine ⟨30395342418795710462306909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81054246450121894566151757 30395342418795710462306909)
            ·
              refine ⟨11398253407048391423365091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30395342418795710462306909 11398253407048391423365091)
              ·
                refine ⟨17097380110572587135047637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11398253407048391423365091 17097380110572587135047637)
                ·
                  refine ⟨400719846341545010977679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17097380110572587135047637 400719846341545010977679)
                  ·
                    rfl

theorem cell21_1755898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1755898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755898 prefixEnd_1755898 := by exact prefixLift 1755898
  have htrace : WordTrace (prefixWord ++ tailWord_1755898) baseStart_1755898 baseEnd_1755898 := by
    simpa [prefixWord, tailWord_1755898, baseEnd_1755898] using wordTrace_append hprefix tailTrace_1755898
  have hstable : (prefixWord ++ tailWord_1755898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755898).length < 2 ^ (prefixWord ++ tailWord_1755898).sum := by decide
  have hdescent : baseEnd_1755898 < baseStart_1755898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755929 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_1755929 : Nat := 118140960795 + 1755929 * 2 ^ 59
def prefixEnd_1755929 : Nat := 4983230072969 + 3 ^ 40 * 1755929 * 2
def baseEnd_1755929 : Nat := 400726920963895845960949

theorem tailTrace_1755929 : CollatzResearch.WordTrace tailWord_1755929 prefixEnd_1755929 400726920963895845960949 := by
  unfold tailWord_1755929
  simp only [CollatzResearch.WordTrace]
  refine ⟨64043992055576596642942841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42695994703717731095295227 64043992055576596642942841)
  ·
    refine ⟨48032994041682447482207131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64043992055576596642942841 48032994041682447482207131)
    ·
      refine ⟨72049491062523671223310697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48032994041682447482207131 72049491062523671223310697)
      ·
        refine ⟨54037118296892753417483023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72049491062523671223310697 54037118296892753417483023)
        ·
          refine ⟨81055677445339130126224535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54037118296892753417483023 81055677445339130126224535)
          ·
            refine ⟨121583516168008695189336803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81055677445339130126224535 121583516168008695189336803)
            ·
              refine ⟨182375274252013042784005205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121583516168008695189336803 182375274252013042784005205)
              ·
                refine ⟨2137210245140777845125061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 182375274252013042784005205 2137210245140777845125061)
                ·
                  refine ⟨400726920963895845960949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137210245140777845125061 400726920963895845960949)
                  ·
                    rfl

theorem cell21_1755929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_1755929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755929 prefixEnd_1755929 := by exact prefixLift 1755929
  have htrace : WordTrace (prefixWord ++ tailWord_1755929) baseStart_1755929 baseEnd_1755929 := by
    simpa [prefixWord, tailWord_1755929, baseEnd_1755929] using wordTrace_append hprefix tailTrace_1755929
  have hstable : (prefixWord ++ tailWord_1755929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755929).length < 2 ^ (prefixWord ++ tailWord_1755929).sum := by decide
  have hdescent : baseEnd_1755929 < baseStart_1755929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755932 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_1755932 : Nat := 118140960795 + 1755932 * 2 ^ 59
def prefixEnd_1755932 : Nat := 4983230072969 + 3 ^ 40 * 1755932 * 2
def baseEnd_1755932 : Nat := 400727605604768507410943

theorem tailTrace_1755932 : CollatzResearch.WordTrace tailWord_1755932 prefixEnd_1755932 400727605604768507410943 := by
  unfold tailWord_1755932
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022050737282864077651025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42696067649710485436868033 32022050737282864077651025)
  ·
    refine ⟨24016538052962148058238269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32022050737282864077651025 24016538052962148058238269)
    ·
      refine ⟨9006201769860805521839351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24016538052962148058238269 9006201769860805521839351)
      ·
        refine ⟨13509302654791208282759027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9006201769860805521839351 13509302654791208282759027)
        ·
          refine ⟨20263953982186812424138541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13509302654791208282759027 20263953982186812424138541)
          ·
            refine ⟨7598982743320054659051953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20263953982186812424138541 7598982743320054659051953)
            ·
              refine ⟨5699237057490040994288965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598982743320054659051953 5699237057490040994288965)
              ·
                refine ⟨1068606948279382686429181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5699237057490040994288965 1068606948279382686429181)
                ·
                  refine ⟨400727605604768507410943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068606948279382686429181 400727605604768507410943)
                  ·
                    rfl

theorem cell21_1755932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_1755932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755932 prefixEnd_1755932 := by exact prefixLift 1755932
  have htrace : WordTrace (prefixWord ++ tailWord_1755932) baseStart_1755932 baseEnd_1755932 := by
    simpa [prefixWord, tailWord_1755932, baseEnd_1755932] using wordTrace_append hprefix tailTrace_1755932
  have hstable : (prefixWord ++ tailWord_1755932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755932).length < 2 ^ (prefixWord ++ tailWord_1755932).sum := by decide
  have hdescent : baseEnd_1755932 < baseStart_1755932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755966 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 3]
def baseStart_1755966 : Nat := 118140960795 + 1755966 * 2 ^ 59
def prefixEnd_1755966 : Nat := 4983230072969 + 3 ^ 40 * 1755966 * 2
def baseEnd_1755966 : Nat := 400735364867992003844207

theorem tailTrace_1755966 : CollatzResearch.WordTrace tailWord_1755966 prefixEnd_1755966 400735364867992003844207 := by
  unfold tailWord_1755966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8005667694555318995254969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42696894370961701308026501 8005667694555318995254969)
  ·
    refine ⟨6004250770916489246441227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8005667694555318995254969 6004250770916489246441227)
    ·
      refine ⟨9006376156374733869661841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004250770916489246441227 9006376156374733869661841)
      ·
        refine ⟨6754782117281050402246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006376156374733869661841 6754782117281050402246381)
        ·
          refine ⟨2533043293980393900842393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6754782117281050402246381 2533043293980393900842393)
          ·
            refine ⟨1899782470485295425631795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533043293980393900842393 1899782470485295425631795)
            ·
              refine ⟨2849673705727943138447693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899782470485295425631795 2849673705727943138447693)
              ·
                refine ⟨1068627639647978676917885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2849673705727943138447693 1068627639647978676917885)
                ·
                  refine ⟨400735364867992003844207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068627639647978676917885 400735364867992003844207)
                  ·
                    rfl

theorem cell21_1755966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_1755966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755966 prefixEnd_1755966 := by exact prefixLift 1755966
  have htrace : WordTrace (prefixWord ++ tailWord_1755966) baseStart_1755966 baseEnd_1755966 := by
    simpa [prefixWord, tailWord_1755966, baseEnd_1755966] using wordTrace_append hprefix tailTrace_1755966
  have hstable : (prefixWord ++ tailWord_1755966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755966).length < 2 ^ (prefixWord ++ tailWord_1755966).sum := by decide
  have hdescent : baseEnd_1755966 < baseStart_1755966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1755991 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_1755991 : Nat := 118140960795 + 1755991 * 2 ^ 59
def prefixEnd_1755991 : Nat := 4983230072969 + 3 ^ 40 * 1755991 * 2
def baseEnd_1755991 : Nat := 400741070208597515927489

theorem tailTrace_1755991 : CollatzResearch.WordTrace tailWord_1755991 prefixEnd_1755991 400741070208597515927489 := by
  unfold tailWord_1755991
  simp only [CollatzResearch.WordTrace]
  refine ⟨64046253381351981231699827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42697502254234654154466551 64046253381351981231699827)
  ·
    refine ⟨96069380072027971847549741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64046253381351981231699827 96069380072027971847549741)
    ·
      refine ⟨36026017527010489442831153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96069380072027971847549741 36026017527010489442831153)
      ·
        refine ⟨27019513145257867082123365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36026017527010489442831153 27019513145257867082123365)
        ·
          refine ⟨5066158714735850077898131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27019513145257867082123365 5066158714735850077898131)
          ·
            refine ⟨7599238072103775116847197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066158714735850077898131 7599238072103775116847197)
            ·
              refine ⟨2849714277038915668817699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7599238072103775116847197 2849714277038915668817699)
              ·
                refine ⟨4274571415558373503226549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849714277038915668817699 4274571415558373503226549)
                ·
                  refine ⟨400741070208597515927489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4274571415558373503226549 400741070208597515927489)
                  ·
                    rfl

theorem cell21_1755991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_1755991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1755991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1755991 prefixEnd_1755991 := by exact prefixLift 1755991
  have htrace : WordTrace (prefixWord ++ tailWord_1755991) baseStart_1755991 baseEnd_1755991 := by
    simpa [prefixWord, tailWord_1755991, baseEnd_1755991] using wordTrace_append hprefix tailTrace_1755991
  have hstable : (prefixWord ++ tailWord_1755991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1755991).length < 2 ^ (prefixWord ++ tailWord_1755991).sum := by decide
  have hdescent : baseEnd_1755991 < baseStart_1755991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1755991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756019 : List Nat := [1, 1, 1, 2, 2, 1, 6, 7]
def baseStart_1756019 : Nat := 118140960795 + 1756019 * 2 ^ 59
def prefixEnd_1756019 : Nat := 4983230072969 + 3 ^ 40 * 1756019 * 2
def baseEnd_1756019 : Nat := 133582486730025229820255

theorem tailTrace_1756019 : CollatzResearch.WordTrace tailWord_1756019 prefixEnd_1756019 133582486730025229820255 := by
  unfold tailWord_1756019
  simp only [CollatzResearch.WordTrace]
  refine ⟨64047274625250542013719111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42698183083500361342479407 64047274625250542013719111)
  ·
    refine ⟨96070911937875813020578667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64047274625250542013719111 96070911937875813020578667)
    ·
      refine ⟨144106367906813719530868001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96070911937875813020578667 144106367906813719530868001)
      ·
        refine ⟨108079775930110289648151001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144106367906813719530868001 108079775930110289648151001)
        ·
          refine ⟨81059831947582717236113251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108079775930110289648151001 81059831947582717236113251)
          ·
            refine ⟨121589747921374075854169877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81059831947582717236113251 121589747921374075854169877)
            ·
              refine ⟨5699519433814409805664213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121589747921374075854169877 5699519433814409805664213)
              ·
                refine ⟨133582486730025229820255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5699519433814409805664213 133582486730025229820255)
                ·
                  rfl

theorem cell21_1756019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_1756019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756019 prefixEnd_1756019 := by exact prefixLift 1756019
  have htrace : WordTrace (prefixWord ++ tailWord_1756019) baseStart_1756019 baseEnd_1756019 := by
    simpa [prefixWord, tailWord_1756019, baseEnd_1756019] using wordTrace_append hprefix tailTrace_1756019
  have hstable : (prefixWord ++ tailWord_1756019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756019).length < 2 ^ (prefixWord ++ tailWord_1756019).sum := by decide
  have hdescent : baseEnd_1756019 < baseStart_1756019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756042 : List Nat := [3, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1756042 : Nat := 118140960795 + 1756042 * 2 ^ 59
def prefixEnd_1756042 : Nat := 4983230072969 + 3 ^ 40 * 1756042 * 2
def baseEnd_1756042 : Nat := 400752709103432760577385

theorem tailTrace_1756042 : CollatzResearch.WordTrace tailWord_1756042 prefixEnd_1756042 400752709103432760577385 := by
  unfold tailWord_1756042
  simp only [CollatzResearch.WordTrace]
  refine ⟨16012028376041804235451595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42698742336111477961204253 16012028376041804235451595)
  ·
    refine ⟨24018042564062706353177393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16012028376041804235451595 24018042564062706353177393)
    ·
      refine ⟨18013531923047029764883045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24018042564062706353177393 18013531923047029764883045)
      ·
        refine ⟨3377537235571318080915571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18013531923047029764883045 3377537235571318080915571)
        ·
          refine ⟨5066305853356977121373357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377537235571318080915571 5066305853356977121373357)
          ·
            refine ⟨1899864695008866420515009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5066305853356977121373357 1899864695008866420515009)
            ·
              refine ⟨1424898521256649815386257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1899864695008866420515009 1424898521256649815386257)
              ·
                refine ⟨1068673890942487361539693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424898521256649815386257 1068673890942487361539693)
                ·
                  refine ⟨400752709103432760577385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068673890942487361539693 400752709103432760577385)
                  ·
                    rfl

theorem cell21_1756042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1756042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756042 prefixEnd_1756042 := by exact prefixLift 1756042
  have htrace : WordTrace (prefixWord ++ tailWord_1756042) baseStart_1756042 baseEnd_1756042 := by
    simpa [prefixWord, tailWord_1756042, baseEnd_1756042] using wordTrace_append hprefix tailTrace_1756042
  have hstable : (prefixWord ++ tailWord_1756042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756042).length < 2 ^ (prefixWord ++ tailWord_1756042).sum := by decide
  have hdescent : baseEnd_1756042 < baseStart_1756042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756146 : List Nat := [3, 2, 1, 5, 2, 1, 7]
def baseStart_1756146 : Nat := 118140960795 + 1756146 * 2 ^ 59
def prefixEnd_1756146 : Nat := 4983230072969 + 3 ^ 40 * 1756146 * 2
def baseEnd_1756146 : Nat := 44530715924483521204871

theorem tailTrace_1756146 : CollatzResearch.WordTrace tailWord_1756146 prefixEnd_1756146 44530715924483521204871 := by
  unfold tailWord_1756146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16012976673947610675898073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42701271130526961802394861 16012976673947610675898073)
  ·
    refine ⟨12009732505460708006923555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16012976673947610675898073 12009732505460708006923555)
    ·
      refine ⟨18014598758191062010385333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12009732505460708006923555 18014598758191062010385333)
      ·
        refine ⟨1688868633580412063473625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18014598758191062010385333 1688868633580412063473625)
        ·
          refine ⟨1266651475185309047605219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688868633580412063473625 1266651475185309047605219)
          ·
            refine ⟨1899977212777963571407829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266651475185309047605219 1899977212777963571407829)
            ·
              refine ⟨44530715924483521204871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1899977212777963571407829 44530715924483521204871)
              ·
                rfl

theorem cell21_1756146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 7].length) (baseStart_1756146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756146 prefixEnd_1756146 := by exact prefixLift 1756146
  have htrace : WordTrace (prefixWord ++ tailWord_1756146) baseStart_1756146 baseEnd_1756146 := by
    simpa [prefixWord, tailWord_1756146, baseEnd_1756146] using wordTrace_append hprefix tailTrace_1756146
  have hstable : (prefixWord ++ tailWord_1756146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756146).length < 2 ^ (prefixWord ++ tailWord_1756146).sum := by decide
  have hdescent : baseEnd_1756146 < baseStart_1756146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756157 : List Nat := [1, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1756157 : Nat := 118140960795 + 1756157 * 2 ^ 59
def prefixEnd_1756157 : Nat := 4983230072969 + 3 ^ 40 * 1756157 * 2
def baseEnd_1756157 : Nat := 400778953670218116160483

theorem tailTrace_1756157 : CollatzResearch.WordTrace tailWord_1756157 prefixEnd_1756157 400778953670218116160483 := by
  unfold tailWord_1756157
  simp only [CollatzResearch.WordTrace]
  refine ⟨64052307898750591582242725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42701538599167061054828483 64052307898750591582242725)
  ·
    refine ⟨12009807731015735921670511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64052307898750591582242725 12009807731015735921670511)
    ·
      refine ⟨18014711596523603882505767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12009807731015735921670511 18014711596523603882505767)
      ·
        refine ⟨27022067394785405823758651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18014711596523603882505767 27022067394785405823758651)
        ·
          refine ⟨40533101092178108735637977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27022067394785405823758651 40533101092178108735637977)
          ·
            refine ⟨30399825819133581551728483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40533101092178108735637977 30399825819133581551728483)
            ·
              refine ⟨45599738728700372327592725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30399825819133581551728483 45599738728700372327592725)
              ·
                refine ⟨2137487752907829952855909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45599738728700372327592725 2137487752907829952855909)
                ·
                  refine ⟨400778953670218116160483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137487752907829952855909 400778953670218116160483)
                  ·
                    rfl

theorem cell21_1756157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1756157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756157 prefixEnd_1756157 := by exact prefixLift 1756157
  have htrace : WordTrace (prefixWord ++ tailWord_1756157) baseStart_1756157 baseEnd_1756157 := by
    simpa [prefixWord, tailWord_1756157, baseEnd_1756157] using wordTrace_append hprefix tailTrace_1756157
  have hstable : (prefixWord ++ tailWord_1756157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756157).length < 2 ^ (prefixWord ++ tailWord_1756157).sum := by decide
  have hdescent : baseEnd_1756157 < baseStart_1756157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756171 : List Nat := [1, 1, 1, 1, 6, 2, 1, 8]
def baseStart_1756171 : Nat := 118140960795 + 1756171 * 2 ^ 59
def prefixEnd_1756171 : Nat := 4983230072969 + 3 ^ 40 * 1756171 * 2
def baseEnd_1756171 : Nat := 133594049553652400975707

theorem tailTrace_1756171 : CollatzResearch.WordTrace tailWord_1756171 prefixEnd_1756171 133594049553652400975707 := by
  unfold tailWord_1756171
  simp only [CollatzResearch.WordTrace]
  refine ⟨64052818520699871973252367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42701879013799914648834911 64052818520699871973252367)
  ·
    refine ⟨96079227781049807959878551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64052818520699871973252367 96079227781049807959878551)
    ·
      refine ⟨144118841671574711939817827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96079227781049807959878551 144118841671574711939817827)
      ·
        refine ⟨216178262507362067909726741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144118841671574711939817827 216178262507362067909726741)
        ·
          refine ⟨10133356055032596933268441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216178262507362067909726741 10133356055032596933268441)
          ·
            refine ⟨7600017041274447699951331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133356055032596933268441 7600017041274447699951331)
            ·
              refine ⟨11400025561911671549926997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600017041274447699951331 11400025561911671549926997)
              ·
                refine ⟨133594049553652400975707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11400025561911671549926997 133594049553652400975707)
                ·
                  rfl

theorem cell21_1756171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_1756171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756171 prefixEnd_1756171 := by exact prefixLift 1756171
  have htrace : WordTrace (prefixWord ++ tailWord_1756171) baseStart_1756171 baseEnd_1756171 := by
    simpa [prefixWord, tailWord_1756171, baseEnd_1756171] using wordTrace_append hprefix tailTrace_1756171
  have hstable : (prefixWord ++ tailWord_1756171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756171).length < 2 ^ (prefixWord ++ tailWord_1756171).sum := by decide
  have hdescent : baseEnd_1756171 < baseStart_1756171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756174 : List Nat := [4, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1756174 : Nat := 118140960795 + 1756174 * 2 ^ 59
def prefixEnd_1756174 : Nat := 4983230072969 + 3 ^ 40 * 1756174 * 2
def baseEnd_1756174 : Nat := 400782833301829864377115

theorem tailTrace_1756174 : CollatzResearch.WordTrace tailWord_1756174 prefixEnd_1756174 400782833301829864377115 := by
  unfold tailWord_1756174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006615992461125435701447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42701951959792668990407717 8006615992461125435701447)
  ·
    refine ⟨12009923988691688153552171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8006615992461125435701447 12009923988691688153552171)
    ·
      refine ⟨18014885983037532230328257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12009923988691688153552171 18014885983037532230328257)
      ·
        refine ⟨13511164487278149172746193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18014885983037532230328257 13511164487278149172746193)
        ·
          refine ⟨10133373365458611879559645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13511164487278149172746193 10133373365458611879559645)
          ·
            refine ⟨3800015012046979454834867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10133373365458611879559645 3800015012046979454834867)
            ·
              refine ⟨5700022518070469182252301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800015012046979454834867 5700022518070469182252301)
              ·
                refine ⟨2137508444276425943344613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5700022518070469182252301 2137508444276425943344613)
                ·
                  refine ⟨400782833301829864377115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137508444276425943344613 400782833301829864377115)
                  ·
                    rfl

theorem cell21_1756174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1756174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756174 prefixEnd_1756174 := by exact prefixLift 1756174
  have htrace : WordTrace (prefixWord ++ tailWord_1756174) baseStart_1756174 baseEnd_1756174 := by
    simpa [prefixWord, tailWord_1756174, baseEnd_1756174] using wordTrace_append hprefix tailTrace_1756174
  have hstable : (prefixWord ++ tailWord_1756174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756174).length < 2 ^ (prefixWord ++ tailWord_1756174).sum := by decide
  have hdescent : baseEnd_1756174 < baseStart_1756174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756312 : List Nat := [2, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_1756312 : Nat := 118140960795 + 1756312 * 2 ^ 59
def prefixEnd_1756312 : Nat := 4983230072969 + 3 ^ 40 * 1756312 * 2
def baseEnd_1756312 : Nat := 400814326781972291076833

theorem tailTrace_1756312 : CollatzResearch.WordTrace tailWord_1756312 prefixEnd_1756312 400814326781972291076833 := by
  unfold tailWord_1756312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32028980606594526527067595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42705307475459368702756793 32028980606594526527067595)
  ·
    refine ⟨48043470909891789790601393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32028980606594526527067595 48043470909891789790601393)
    ·
      refine ⟨36032603182418842342951045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48043470909891789790601393 36032603182418842342951045)
      ·
        refine ⟨6756113096703532939303321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36032603182418842342951045 6756113096703532939303321)
        ·
          refine ⟨5067084822527649704477491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756113096703532939303321 5067084822527649704477491)
          ·
            refine ⟨7600627233791474556716237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067084822527649704477491 7600627233791474556716237)
            ·
              refine ⟨2850235212671802958768589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7600627233791474556716237 2850235212671802958768589)
              ·
                refine ⟨1068838204751926109538221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850235212671802958768589 1068838204751926109538221)
                ·
                  refine ⟨400814326781972291076833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068838204751926109538221 400814326781972291076833)
                  ·
                    rfl

theorem cell21_1756312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_1756312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756312 prefixEnd_1756312 := by exact prefixLift 1756312
  have htrace : WordTrace (prefixWord ++ tailWord_1756312) baseStart_1756312 baseEnd_1756312 := by
    simpa [prefixWord, tailWord_1756312, baseEnd_1756312] using wordTrace_append hprefix tailTrace_1756312
  have hstable : (prefixWord ++ tailWord_1756312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756312).length < 2 ^ (prefixWord ++ tailWord_1756312).sum := by decide
  have hdescent : baseEnd_1756312 < baseStart_1756312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756385 : List Nat := [1, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_1756385 : Nat := 118140960795 + 1756385 * 2 ^ 59
def prefixEnd_1756385 : Nat := 4983230072969 + 3 ^ 40 * 1756385 * 2
def baseEnd_1756385 : Nat := 400830986376540386360017

theorem tailTrace_1756385 : CollatzResearch.WordTrace tailWord_1756385 prefixEnd_1756385 400830986376540386360017 := by
  unfold tailWord_1756385
  simp only [CollatzResearch.WordTrace]
  refine ⟨64060623741924586521542609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42707082494616391014361739 64060623741924586521542609)
  ·
    refine ⟨48045467806443439891156957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64060623741924586521542609 48045467806443439891156957)
    ·
      refine ⟨18017050427416289959183859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48045467806443439891156957 18017050427416289959183859)
      ·
        refine ⟨27025575641124434938775789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18017050427416289959183859 27025575641124434938775789)
        ·
          refine ⟨10134590865421663102040921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27025575641124434938775789 10134590865421663102040921)
          ·
            refine ⟨7600943149066247326530691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10134590865421663102040921 7600943149066247326530691)
            ·
              refine ⟨11401414723599370989796037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600943149066247326530691 11401414723599370989796037)
              ·
                refine ⟨2137765260674882060586757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11401414723599370989796037 2137765260674882060586757)
                ·
                  refine ⟨400830986376540386360017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137765260674882060586757 400830986376540386360017)
                  ·
                    rfl

theorem cell21_1756385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_1756385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756385 prefixEnd_1756385 := by exact prefixLift 1756385
  have htrace : WordTrace (prefixWord ++ tailWord_1756385) baseStart_1756385 baseEnd_1756385 := by
    simpa [prefixWord, tailWord_1756385, baseEnd_1756385] using wordTrace_append hprefix tailTrace_1756385
  have hstable : (prefixWord ++ tailWord_1756385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756385).length < 2 ^ (prefixWord ++ tailWord_1756385).sum := by decide
  have hdescent : baseEnd_1756385 < baseStart_1756385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756388 : List Nat := [2, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_1756388 : Nat := 118140960795 + 1756388 * 2 ^ 59
def prefixEnd_1756388 : Nat := 4983230072969 + 3 ^ 40 * 1756388 * 2
def baseEnd_1756388 : Nat := 400831671017413047810011

theorem tailTrace_1756388 : CollatzResearch.WordTrace tailWord_1756388 prefixEnd_1756388 400831671017413047810011 := by
  unfold tailWord_1756388
  simp only [CollatzResearch.WordTrace]
  refine ⟨32030366580456859016950909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42707155440609145355934545 32030366580456859016950909)
  ·
    refine ⟨12011387467671322131356591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32030366580456859016950909 12011387467671322131356591)
    ·
      refine ⟨18017081201506983197034887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12011387467671322131356591 18017081201506983197034887)
      ·
        refine ⟨27025621802260474795552331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18017081201506983197034887 27025621802260474795552331)
        ·
          refine ⟨40538432703390712193328497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27025621802260474795552331 40538432703390712193328497)
          ·
            refine ⟨30403824527543034144996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40538432703390712193328497 30403824527543034144996373)
            ·
              refine ⟨1425179274728579725546705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30403824527543034144996373 1425179274728579725546705)
              ·
                refine ⟨1068884456046434794160029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425179274728579725546705 1068884456046434794160029)
                ·
                  refine ⟨400831671017413047810011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068884456046434794160029 400831671017413047810011)
                  ·
                    rfl

theorem cell21_1756388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_1756388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756388 prefixEnd_1756388 := by exact prefixLift 1756388
  have htrace : WordTrace (prefixWord ++ tailWord_1756388) baseStart_1756388 baseEnd_1756388 := by
    simpa [prefixWord, tailWord_1756388, baseEnd_1756388] using wordTrace_append hprefix tailTrace_1756388
  have hstable : (prefixWord ++ tailWord_1756388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756388).length < 2 ^ (prefixWord ++ tailWord_1756388).sum := by decide
  have hdescent : baseEnd_1756388 < baseStart_1756388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756447 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 5]
def baseStart_1756447 : Nat := 118140960795 + 1756447 * 2 ^ 59
def prefixEnd_1756447 : Nat := 4983230072969 + 3 ^ 40 * 1756447 * 2
def baseEnd_1756447 : Nat := 400845135621242056326557

theorem tailTrace_1756447 : CollatzResearch.WordTrace tailWord_1756447 prefixEnd_1756447 400845135621242056326557 := by
  unfold tailWord_1756447
  simp only [CollatzResearch.WordTrace]
  refine ⟨64062885067699971110299595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42708590045133314073533063 64062885067699971110299595)
  ·
    refine ⟨96094327601549956665449393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64062885067699971110299595 96094327601549956665449393)
    ·
      refine ⟨72070745701162467499087045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96094327601549956665449393 72070745701162467499087045)
      ·
        refine ⟨13513264818967962656078821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72070745701162467499087045 13513264818967962656078821)
        ·
          refine ⟨2533737153556492998014779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13513264818967962656078821 2533737153556492998014779)
          ·
            refine ⟨3800605730334739497022169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533737153556492998014779 3800605730334739497022169)
            ·
              refine ⟨2850454297751054622766627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3800605730334739497022169 2850454297751054622766627)
              ·
                refine ⟨4275681446626581934149941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850454297751054622766627 4275681446626581934149941)
                ·
                  refine ⟨400845135621242056326557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4275681446626581934149941 400845135621242056326557)
                  ·
                    rfl

theorem cell21_1756447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_1756447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756447 prefixEnd_1756447 := by exact prefixLift 1756447
  have htrace : WordTrace (prefixWord ++ tailWord_1756447) baseStart_1756447 baseEnd_1756447 := by
    simpa [prefixWord, tailWord_1756447, baseEnd_1756447] using wordTrace_append hprefix tailTrace_1756447
  have hstable : (prefixWord ++ tailWord_1756447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756447).length < 2 ^ (prefixWord ++ tailWord_1756447).sum := by decide
  have hdescent : baseEnd_1756447 < baseStart_1756447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756481 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 3]
def baseStart_1756481 : Nat := 118140960795 + 1756481 * 2 ^ 59
def prefixEnd_1756481 : Nat := 4983230072969 + 3 ^ 40 * 1756481 * 2
def baseEnd_1756481 : Nat := 400852894884465552759821

theorem tailTrace_1756481 : CollatzResearch.WordTrace tailWord_1756481 prefixEnd_1756481 400852894884465552759821 := by
  unfold tailWord_1756481
  simp only [CollatzResearch.WordTrace]
  refine ⟨64064125149576794917037297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42709416766384529944691531 64064125149576794917037297)
  ·
    refine ⟨48048093862182596187777973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64064125149576794917037297 48048093862182596187777973)
    ·
      refine ⟨4504508799579618392604185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48048093862182596187777973 4504508799579618392604185)
      ·
        refine ⟨3378381599684713794453139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504508799579618392604185 3378381599684713794453139)
        ·
          refine ⟨5067572399527070691679709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378381599684713794453139 5067572399527070691679709)
          ·
            refine ⟨1900339649822651509379891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5067572399527070691679709 1900339649822651509379891)
            ·
              refine ⟨2850509474733977264069837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900339649822651509379891 2850509474733977264069837)
              ·
                refine ⟨1068941053025241474026189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850509474733977264069837 1068941053025241474026189)
                ·
                  refine ⟨400852894884465552759821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068941053025241474026189 400852894884465552759821)
                  ·
                    rfl

theorem cell21_1756481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 3].length) (baseStart_1756481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756481 prefixEnd_1756481 := by exact prefixLift 1756481
  have htrace : WordTrace (prefixWord ++ tailWord_1756481) baseStart_1756481 baseEnd_1756481 := by
    simpa [prefixWord, tailWord_1756481, baseEnd_1756481] using wordTrace_append hprefix tailTrace_1756481
  have hstable : (prefixWord ++ tailWord_1756481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756481).length < 2 ^ (prefixWord ++ tailWord_1756481).sum := by decide
  have hdescent : baseEnd_1756481 < baseStart_1756481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756489 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 7]
def baseStart_1756489 : Nat := 118140960795 + 1756489 * 2 ^ 59
def prefixEnd_1756489 : Nat := 4983230072969 + 3 ^ 40 * 1756489 * 2
def baseEnd_1756489 : Nat := 400854720593459316626471

theorem tailTrace_1756489 : CollatzResearch.WordTrace tailWord_1756489 prefixEnd_1756489 400854720593459316626471 := by
  unfold tailWord_1756489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64064416933547812283328521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42709611289031874855552347 64064416933547812283328521)
  ·
    refine ⟨48048312700160859212496391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64064416933547812283328521 48048312700160859212496391)
    ·
      refine ⟨72072469050241288818744587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48048312700160859212496391 72072469050241288818744587)
      ·
        refine ⟨108108703575361933228116881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72072469050241288818744587 108108703575361933228116881)
        ·
          refine ⟨81081527681521449921087661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108108703575361933228116881 81081527681521449921087661)
          ·
            refine ⟨30405572880570543720407873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81081527681521449921087661 30405572880570543720407873)
            ·
              refine ⟨22804179660427907790305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30405572880570543720407873 22804179660427907790305905)
              ·
                refine ⟨17103134745320930842729429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22804179660427907790305905 17103134745320930842729429)
                ·
                  refine ⟨400854720593459316626471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17103134745320930842729429 400854720593459316626471)
                  ·
                    rfl

theorem cell21_1756489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_1756489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756489 prefixEnd_1756489 := by exact prefixLift 1756489
  have htrace : WordTrace (prefixWord ++ tailWord_1756489) baseStart_1756489 baseEnd_1756489 := by
    simpa [prefixWord, tailWord_1756489, baseEnd_1756489] using wordTrace_append hprefix tailTrace_1756489
  have hstable : (prefixWord ++ tailWord_1756489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756489).length < 2 ^ (prefixWord ++ tailWord_1756489).sum := by decide
  have hdescent : baseEnd_1756489 < baseStart_1756489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756506 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 5]
def baseStart_1756506 : Nat := 118140960795 + 1756506 * 2 ^ 59
def prefixEnd_1756506 : Nat := 4983230072969 + 3 ^ 40 * 1756506 * 2
def baseEnd_1756506 : Nat := 400858600225071064843103

theorem tailTrace_1756506 : CollatzResearch.WordTrace tailWord_1756506 prefixEnd_1756506 400858600225071064843103 := by
  unfold tailWord_1756506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16016259243621556046674343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42710024649657482791131581 16016259243621556046674343)
  ·
    refine ⟨24024388865432334070011515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16016259243621556046674343 24024388865432334070011515)
    ·
      refine ⟨36036583298148501105017273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24024388865432334070011515 36036583298148501105017273)
      ·
        refine ⟨27027437473611375828762955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36036583298148501105017273 27027437473611375828762955)
        ·
          refine ⟨40541156210417063743144433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27027437473611375828762955 40541156210417063743144433)
          ·
            refine ⟨30405867157812797807358325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40541156210417063743144433 30405867157812797807358325)
            ·
              refine ⟨2850550046044949794439843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30405867157812797807358325 2850550046044949794439843)
              ·
                refine ⟨4275825069067424691659765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850550046044949794439843 4275825069067424691659765)
                ·
                  refine ⟨400858600225071064843103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4275825069067424691659765 400858600225071064843103)
                  ·
                    rfl

theorem cell21_1756506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 5].length) (baseStart_1756506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756506 prefixEnd_1756506 := by exact prefixLift 1756506
  have htrace : WordTrace (prefixWord ++ tailWord_1756506) baseStart_1756506 baseEnd_1756506 := by
    simpa [prefixWord, tailWord_1756506, baseEnd_1756506] using wordTrace_append hprefix tailTrace_1756506
  have hstable : (prefixWord ++ tailWord_1756506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756506).length < 2 ^ (prefixWord ++ tailWord_1756506).sum := by decide
  have hdescent : baseEnd_1756506 < baseStart_1756506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756599 : List Nat := [1, 1, 3, 1, 3, 2, 4, 3, 3]
def baseStart_1756599 : Nat := 118140960795 + 1756599 * 2 ^ 59
def prefixEnd_1756599 : Nat := 4983230072969 + 3 ^ 40 * 1756599 * 2
def baseEnd_1756599 : Nat := 400879824092123569792913

theorem tailTrace_1756599 : CollatzResearch.WordTrace tailWord_1756599 prefixEnd_1756599 400879824092123569792913 := by
  unfold tailWord_1756599
  simp only [CollatzResearch.WordTrace]
  refine ⟨64068428963149301069832851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42712285975432867379888567 64068428963149301069832851)
  ·
    refine ⟨96102643444723951604749277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64068428963149301069832851 96102643444723951604749277)
    ·
      refine ⟨36038491291771481851780979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96102643444723951604749277 36038491291771481851780979)
      ·
        refine ⟨54057736937657222777671469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36038491291771481851780979 54057736937657222777671469)
        ·
          refine ⟨20271651351621458541626801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54057736937657222777671469 20271651351621458541626801)
          ·
            refine ⟨15203738513716093906220101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20271651351621458541626801 15203738513716093906220101)
            ·
              refine ⟨2850700971321767607416269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15203738513716093906220101 2850700971321767607416269)
              ·
                refine ⟨1069012864245662852781101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2850700971321767607416269 1069012864245662852781101)
                ·
                  refine ⟨400879824092123569792913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069012864245662852781101 400879824092123569792913)
                  ·
                    rfl

theorem cell21_1756599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3, 3].length) (baseStart_1756599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756599 prefixEnd_1756599 := by exact prefixLift 1756599
  have htrace : WordTrace (prefixWord ++ tailWord_1756599) baseStart_1756599 baseEnd_1756599 := by
    simpa [prefixWord, tailWord_1756599, baseEnd_1756599] using wordTrace_append hprefix tailTrace_1756599
  have hstable : (prefixWord ++ tailWord_1756599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756599).length < 2 ^ (prefixWord ++ tailWord_1756599).sum := by decide
  have hdescent : baseEnd_1756599 < baseStart_1756599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756726 : List Nat := [5, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1756726 : Nat := 118140960795 + 1756726 * 2 ^ 59
def prefixEnd_1756726 : Nat := 4983230072969 + 3 ^ 40 * 1756726 * 2
def baseEnd_1756726 : Nat := 400908807222399571175987

theorem tailTrace_1756726 : CollatzResearch.WordTrace tailWord_1756726 prefixEnd_1756726 400908807222399571175987 := by
  unfold tailWord_1756726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004566314605575109981627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42715374022459467839804021 4004566314605575109981627)
  ·
    refine ⟨6006849471908362664972441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004566314605575109981627 6006849471908362664972441)
    ·
      refine ⟨4505137103931271998729331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6006849471908362664972441 4505137103931271998729331)
      ·
        refine ⟨6757705655896907998093997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505137103931271998729331 6757705655896907998093997)
        ·
          refine ⟨2534139620961340499285249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6757705655896907998093997 2534139620961340499285249)
          ·
            refine ⟨1900604715721005374463937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534139620961340499285249 1900604715721005374463937)
            ·
              refine ⟨1425453536790754030847953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900604715721005374463937 1425453536790754030847953)
              ·
                refine ⟨1069090152593065523135965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425453536790754030847953 1069090152593065523135965)
                ·
                  refine ⟨400908807222399571175987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069090152593065523135965 400908807222399571175987)
                  ·
                    rfl

theorem cell21_1756726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1756726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756726 prefixEnd_1756726 := by exact prefixLift 1756726
  have htrace : WordTrace (prefixWord ++ tailWord_1756726) baseStart_1756726 baseEnd_1756726 := by
    simpa [prefixWord, tailWord_1756726, baseEnd_1756726] using wordTrace_append hprefix tailTrace_1756726
  have hstable : (prefixWord ++ tailWord_1756726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756726).length < 2 ^ (prefixWord ++ tailWord_1756726).sum := by decide
  have hdescent : baseEnd_1756726 < baseStart_1756726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756762 : List Nat := [3, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1756762 : Nat := 118140960795 + 1756762 * 2 ^ 59
def prefixEnd_1756762 : Nat := 4983230072969 + 3 ^ 40 * 1756762 * 2
def baseEnd_1756762 : Nat := 133639007637623836191971

theorem tailTrace_1756762 : CollatzResearch.WordTrace tailWord_1756762 prefixEnd_1756762 133639007637623836191971 := by
  unfold tailWord_1756762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018593515389694977004135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42716249374372519938677693 16018593515389694977004135)
  ·
    refine ⟨24027890273084542465506203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16018593515389694977004135 24027890273084542465506203)
    ·
      refine ⟨36041835409626813698259305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24027890273084542465506203 36041835409626813698259305)
      ·
        refine ⟨27031376557220110273694479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36041835409626813698259305 27031376557220110273694479)
        ·
          refine ⟨40547064835830165410541719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27031376557220110273694479 40547064835830165410541719)
          ·
            refine ⟨60820597253745248115812579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40547064835830165410541719 60820597253745248115812579)
            ·
              refine ⟨91230895880617872173718869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60820597253745248115812579 91230895880617872173718869)
              ·
                refine ⟨133639007637623836191971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91230895880617872173718869 133639007637623836191971)
                ·
                  rfl

theorem cell21_1756762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1756762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756762 prefixEnd_1756762 := by exact prefixLift 1756762
  have htrace : WordTrace (prefixWord ++ tailWord_1756762) baseStart_1756762 baseEnd_1756762 := by
    simpa [prefixWord, tailWord_1756762, baseEnd_1756762] using wordTrace_append hprefix tailTrace_1756762
  have hstable : (prefixWord ++ tailWord_1756762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756762).length < 2 ^ (prefixWord ++ tailWord_1756762).sum := by decide
  have hdescent : baseEnd_1756762 < baseStart_1756762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756810 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1756810 : Nat := 118140960795 + 1756810 * 2 ^ 59
def prefixEnd_1756810 : Nat := 4983230072969 + 3 ^ 40 * 1756810 * 2
def baseEnd_1756810 : Nat := 400927977166834091775815

theorem tailTrace_1756810 : CollatzResearch.WordTrace tailWord_1756810 prefixEnd_1756810 400927977166834091775815 := by
  unfold tailWord_1756810
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019031191346221026440971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42717416510256589403842589 16019031191346221026440971)
  ·
    refine ⟨24028546787019331539661457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16019031191346221026440971 24028546787019331539661457)
    ·
      refine ⟨18021410090264498654746093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24028546787019331539661457 18021410090264498654746093)
      ·
        refine ⟨6758028783849186995529785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18021410090264498654746093 6758028783849186995529785)
        ·
          refine ⟨5068521587886890246647339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758028783849186995529785 5068521587886890246647339)
          ·
            refine ⟨7602782381830335369971009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068521587886890246647339 7602782381830335369971009)
            ·
              refine ⟨5702086786372751527478257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7602782381830335369971009 5702086786372751527478257)
              ·
                refine ⟨4276565089779563645608693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5702086786372751527478257 4276565089779563645608693)
                ·
                  refine ⟨400927977166834091775815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4276565089779563645608693 400927977166834091775815)
                  ·
                    rfl

theorem cell21_1756810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1756810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756810 prefixEnd_1756810 := by exact prefixLift 1756810
  have htrace : WordTrace (prefixWord ++ tailWord_1756810) baseStart_1756810 baseEnd_1756810 := by
    simpa [prefixWord, tailWord_1756810, baseEnd_1756810] using wordTrace_append hprefix tailTrace_1756810
  have hstable : (prefixWord ++ tailWord_1756810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756810).length < 2 ^ (prefixWord ++ tailWord_1756810).sum := by decide
  have hdescent : baseEnd_1756810 < baseStart_1756810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756824 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_1756824 : Nat := 118140960795 + 1756824 * 2 ^ 59
def prefixEnd_1756824 : Nat := 4983230072969 + 3 ^ 40 * 1756824 * 2
def baseEnd_1756824 : Nat := 400931172157573178542453

theorem tailTrace_1756824 : CollatzResearch.WordTrace tailWord_1756824 prefixEnd_1756824 400931172157573178542453 := by
  unfold tailWord_1756824
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038317693667082248386763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42717756924889442997849017 32038317693667082248386763)
  ·
    refine ⟨48057476540500623372580145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32038317693667082248386763 48057476540500623372580145)
    ·
      refine ⟨36043107405375467529435109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48057476540500623372580145 36043107405375467529435109)
      ·
        refine ⟨6758082638507900161769083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36043107405375467529435109 6758082638507900161769083)
        ·
          refine ⟨10137123957761850242653625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758082638507900161769083 10137123957761850242653625)
          ·
            refine ⟨7602842968321387681990219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137123957761850242653625 7602842968321387681990219)
            ·
              refine ⟨11404264452482081522985329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7602842968321387681990219 11404264452482081522985329)
              ·
                refine ⟨8553198339361561142238997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11404264452482081522985329 8553198339361561142238997)
                ·
                  refine ⟨400931172157573178542453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8553198339361561142238997 400931172157573178542453)
                  ·
                    rfl

theorem cell21_1756824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_1756824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756824 prefixEnd_1756824 := by exact prefixLift 1756824
  have htrace : WordTrace (prefixWord ++ tailWord_1756824) baseStart_1756824 baseEnd_1756824 := by
    simpa [prefixWord, tailWord_1756824, baseEnd_1756824] using wordTrace_append hprefix tailTrace_1756824
  have hstable : (prefixWord ++ tailWord_1756824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756824).length < 2 ^ (prefixWord ++ tailWord_1756824).sum := by decide
  have hdescent : baseEnd_1756824 < baseStart_1756824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756855 : List Nat := [1, 1, 3, 1, 5, 2, 2, 6]
def baseStart_1756855 : Nat := 118140960795 + 1756855 * 2 ^ 59
def prefixEnd_1756855 : Nat := 4983230072969 + 3 ^ 40 * 1756855 * 2
def baseEnd_1756855 : Nat := 133646082259974671175241

theorem tailTrace_1756855 : CollatzResearch.WordTrace tailWord_1756855 prefixEnd_1756855 133646082259974671175241 := by
  unfold tailWord_1756855
  simp only [CollatzResearch.WordTrace]
  refine ⟨64077766050221856791152019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42718510700147904527434679 64077766050221856791152019)
  ·
    refine ⟨96116649075332785186728029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64077766050221856791152019 96116649075332785186728029)
    ·
      refine ⟨36043743403249794445023011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96116649075332785186728029 36043743403249794445023011)
      ·
        refine ⟨54065615104874691667534517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36043743403249794445023011 54065615104874691667534517)
        ·
          refine ⟨5068651416082002343831361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54065615104874691667534517 5068651416082002343831361)
          ·
            refine ⟨3801488562061501757873521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5068651416082002343831361 3801488562061501757873521)
            ·
              refine ⟨2851116421546126318405141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3801488562061501757873521 2851116421546126318405141)
              ·
                refine ⟨133646082259974671175241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2851116421546126318405141 133646082259974671175241)
                ·
                  rfl

theorem cell21_1756855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 6].length) (baseStart_1756855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756855 prefixEnd_1756855 := by exact prefixLift 1756855
  have htrace : WordTrace (prefixWord ++ tailWord_1756855) baseStart_1756855 baseEnd_1756855 := by
    simpa [prefixWord, tailWord_1756855, baseEnd_1756855] using wordTrace_append hprefix tailTrace_1756855
  have hstable : (prefixWord ++ tailWord_1756855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756855).length < 2 ^ (prefixWord ++ tailWord_1756855).sum := by decide
  have hdescent : baseEnd_1756855 < baseStart_1756855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756858 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1756858 : Nat := 118140960795 + 1756858 * 2 ^ 59
def prefixEnd_1756858 : Nat := 4983230072969 + 3 ^ 40 * 1756858 * 2
def baseEnd_1756858 : Nat := 400938931420796674975717

theorem tailTrace_1756858 : CollatzResearch.WordTrace tailWord_1756858 prefixEnd_1756858 400938931420796674975717 := by
  unfold tailWord_1756858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16019468867302747075877807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42718583646140658869007485 16019468867302747075877807)
  ·
    refine ⟨24029203300954120613816711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16019468867302747075877807 24029203300954120613816711)
    ·
      refine ⟨36043804951431180920725067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24029203300954120613816711 36043804951431180920725067)
      ·
        refine ⟨54065707427146771381087601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36043804951431180920725067 54065707427146771381087601)
        ·
          refine ⟨40549280570360078535815701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54065707427146771381087601 40549280570360078535815701)
          ·
            refine ⟨1900747526735628681366361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40549280570360078535815701 1900747526735628681366361)
            ·
              refine ⟨1425560645051721511024771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900747526735628681366361 1425560645051721511024771)
              ·
                refine ⟨2138340967577582266537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425560645051721511024771 2138340967577582266537157)
                ·
                  refine ⟨400938931420796674975717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138340967577582266537157 400938931420796674975717)
                  ·
                    rfl

theorem cell21_1756858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1756858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756858 prefixEnd_1756858 := by exact prefixLift 1756858
  have htrace : WordTrace (prefixWord ++ tailWord_1756858) baseStart_1756858 baseEnd_1756858 := by
    simpa [prefixWord, tailWord_1756858, baseEnd_1756858] using wordTrace_append hprefix tailTrace_1756858
  have hstable : (prefixWord ++ tailWord_1756858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756858).length < 2 ^ (prefixWord ++ tailWord_1756858).sum := by decide
  have hdescent : baseEnd_1756858 < baseStart_1756858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1756962 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1756962 : Nat := 118140960795 + 1756962 * 2 ^ 59
def prefixEnd_1756962 : Nat := 4983230072969 + 3 ^ 40 * 1756962 * 2
def baseEnd_1756962 : Nat := 400962665637715605242171

theorem tailTrace_1756962 : CollatzResearch.WordTrace tailWord_1756962 prefixEnd_1756962 400962665637715605242171 := by
  unfold tailWord_1756962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020417165208553516324285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42721112440556142710198093 16020417165208553516324285)
  ·
    refine ⟨6007656436953207568621607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16020417165208553516324285 6007656436953207568621607)
    ·
      refine ⟨9011484655429811352932411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007656436953207568621607 9011484655429811352932411)
      ·
        refine ⟨13517226983144717029398617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9011484655429811352932411 13517226983144717029398617)
        ·
          refine ⟨10137920237358537772048963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13517226983144717029398617 10137920237358537772048963)
          ·
            refine ⟨15206880356037806658073445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10137920237358537772048963 15206880356037806658073445)
            ·
              refine ⟨2851290066757088748388771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15206880356037806658073445 2851290066757088748388771)
              ·
                refine ⟨4276935100135633122583157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2851290066757088748388771 4276935100135633122583157)
                ·
                  refine ⟨400962665637715605242171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4276935100135633122583157 400962665637715605242171)
                  ·
                    rfl

theorem cell21_1756962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1756962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1756962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1756962 prefixEnd_1756962 := by exact prefixLift 1756962
  have htrace : WordTrace (prefixWord ++ tailWord_1756962) baseStart_1756962 baseEnd_1756962 := by
    simpa [prefixWord, tailWord_1756962, baseEnd_1756962] using wordTrace_append hprefix tailTrace_1756962
  have hstable : (prefixWord ++ tailWord_1756962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1756962).length < 2 ^ (prefixWord ++ tailWord_1756962).sum := by decide
  have hdescent : baseEnd_1756962 < baseStart_1756962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1756962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757027 : List Nat := [1, 1, 1, 5, 5, 1, 2, 1, 4]
def baseStart_1757027 : Nat := 118140960795 + 1757027 * 2 ^ 59
def prefixEnd_1757027 : Nat := 4983230072969 + 3 ^ 40 * 1757027 * 2
def baseEnd_1757027 : Nat := 400977499523289936658705

theorem tailTrace_1757027 : CollatzResearch.WordTrace tailWord_1757027 prefixEnd_1757027 400977499523289936658705 := by
  unfold tailWord_1757027
  simp only [CollatzResearch.WordTrace]
  refine ⟨64084039405598730166413335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42722692937065820110942223 64084039405598730166413335)
  ·
    refine ⟨96126059108398095249620003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64084039405598730166413335 96126059108398095249620003)
    ·
      refine ⟨144189088662597142874430005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96126059108398095249620003 144189088662597142874430005)
      ·
        refine ⟨13517727062118482144477813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144189088662597142874430005 13517727062118482144477813)
        ·
          refine ⟨1267286912073607701044795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13517727062118482144477813 1267286912073607701044795)
          ·
            refine ⟨1900930368110411551567193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267286912073607701044795 1900930368110411551567193)
            ·
              refine ⟨1425697776082808663675395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900930368110411551567193 1425697776082808663675395)
              ·
                refine ⟨2138546664124212995513093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425697776082808663675395 2138546664124212995513093)
                ·
                  refine ⟨400977499523289936658705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138546664124212995513093 400977499523289936658705)
                  ·
                    rfl

theorem cell21_1757027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 1, 4].length) (baseStart_1757027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757027 prefixEnd_1757027 := by exact prefixLift 1757027
  have htrace : WordTrace (prefixWord ++ tailWord_1757027) baseStart_1757027 baseEnd_1757027 := by
    simpa [prefixWord, tailWord_1757027, baseEnd_1757027] using wordTrace_append hprefix tailTrace_1757027
  have hstable : (prefixWord ++ tailWord_1757027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757027).length < 2 ^ (prefixWord ++ tailWord_1757027).sum := by decide
  have hdescent : baseEnd_1757027 < baseStart_1757027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757066 : List Nat := [3, 1, 2, 4, 11]
def baseStart_1757066 : Nat := 118140960795 + 1757066 * 2 ^ 59
def prefixEnd_1757066 : Nat := 4983230072969 + 3 ^ 40 * 1757066 * 2
def baseEnd_1757066 : Nat := 4950449380921414018625

theorem tailTrace_1757066 : CollatzResearch.WordTrace tailWord_1757066 prefixEnd_1757066 4950449380921414018625 := by
  unfold tailWord_1757066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021365463114359956770763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42723641234971626551388701 16021365463114359956770763)
  ·
    refine ⟨24032048194671539935156145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16021365463114359956770763 24032048194671539935156145)
    ·
      refine ⟨18024036146003654951367109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24032048194671539935156145 18024036146003654951367109)
      ·
        refine ⟨3379506777375685303381333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18024036146003654951367109 3379506777375685303381333)
        ·
          refine ⟨4950449380921414018625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3379506777375685303381333 4950449380921414018625)
          ·
            rfl

theorem cell21_1757066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 11].length) (baseStart_1757066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757066 prefixEnd_1757066 := by exact prefixLift 1757066
  have htrace : WordTrace (prefixWord ++ tailWord_1757066) baseStart_1757066 baseEnd_1757066 := by
    simpa [prefixWord, tailWord_1757066, baseEnd_1757066] using wordTrace_append hprefix tailTrace_1757066
  have hstable : (prefixWord ++ tailWord_1757066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757066).length < 2 ^ (prefixWord ++ tailWord_1757066).sum := by decide
  have hdescent : baseEnd_1757066 < baseStart_1757066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757111 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_1757111 : Nat := 118140960795 + 1757111 * 2 ^ 59
def prefixEnd_1757111 : Nat := 4983230072969 + 3 ^ 40 * 1757111 * 2
def baseEnd_1757111 : Nat := 400996669467724457258533

theorem tailTrace_1757111 : CollatzResearch.WordTrace tailWord_1757111 prefixEnd_1757111 400996669467724457258533 := by
  unfold tailWord_1757111
  simp only [CollatzResearch.WordTrace]
  refine ⟨64087103137294412512471187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42724735424862941674980791 64087103137294412512471187)
  ·
    refine ⟨96130654705941618768706781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64087103137294412512471187 96130654705941618768706781)
    ·
      refine ⟨36048995514728107038265043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96130654705941618768706781 36048995514728107038265043)
      ·
        refine ⟨54073493272092160557397565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36048995514728107038265043 54073493272092160557397565)
        ·
          refine ⟨20277559977034560209024087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54073493272092160557397565 20277559977034560209024087)
          ·
            refine ⟨30416339965551840313536131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20277559977034560209024087 30416339965551840313536131)
            ·
              refine ⟨45624509948327760470304197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30416339965551840313536131 45624509948327760470304197)
              ·
                refine ⟨8554595615311455088182037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45624509948327760470304197 8554595615311455088182037)
                ·
                  refine ⟨400996669467724457258533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8554595615311455088182037 400996669467724457258533)
                  ·
                    rfl

theorem cell21_1757111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_1757111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757111 prefixEnd_1757111 := by exact prefixLift 1757111
  have htrace : WordTrace (prefixWord ++ tailWord_1757111) baseStart_1757111 baseEnd_1757111 := by
    simpa [prefixWord, tailWord_1757111, baseEnd_1757111] using wordTrace_append hprefix tailTrace_1757111
  have hstable : (prefixWord ++ tailWord_1757111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757111).length < 2 ^ (prefixWord ++ tailWord_1757111).sum := by decide
  have hdescent : baseEnd_1757111 < baseStart_1757111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757128 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_1757128 : Nat := 118140960795 + 1757128 * 2 ^ 59
def prefixEnd_1757128 : Nat := 4983230072969 + 3 ^ 40 * 1757128 * 2
def baseEnd_1757128 : Nat := 401000549099336205475165

theorem tailTrace_1757128 : CollatzResearch.WordTrace tailWord_1757128 prefixEnd_1757128 401000549099336205475165 := by
  unfold tailWord_1757128
  simp only [CollatzResearch.WordTrace]
  refine ⟨32043861589116412207920019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42725148785488549610560025 32043861589116412207920019)
  ·
    refine ⟨48065792383674618311880029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32043861589116412207920019 48065792383674618311880029)
    ·
      refine ⟨18024672143877981866955011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48065792383674618311880029 18024672143877981866955011)
      ·
        refine ⟨27037008215816972800432517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18024672143877981866955011 27037008215816972800432517)
        ·
          refine ⟨5069439040465682400081097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27037008215816972800432517 5069439040465682400081097)
          ·
            refine ⟨3802079280349261800060823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069439040465682400081097 3802079280349261800060823)
            ·
              refine ⟨5703118920523892700091235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802079280349261800060823 5703118920523892700091235)
              ·
                refine ⟨8554678380785839050136853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5703118920523892700091235 8554678380785839050136853)
                ·
                  refine ⟨401000549099336205475165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8554678380785839050136853 401000549099336205475165)
                  ·
                    rfl

theorem cell21_1757128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_1757128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757128 prefixEnd_1757128 := by exact prefixLift 1757128
  have htrace : WordTrace (prefixWord ++ tailWord_1757128) baseStart_1757128 baseEnd_1757128 := by
    simpa [prefixWord, tailWord_1757128, baseEnd_1757128] using wordTrace_append hprefix tailTrace_1757128
  have hstable : (prefixWord ++ tailWord_1757128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757128).length < 2 ^ (prefixWord ++ tailWord_1757128).sum := by decide
  have hdescent : baseEnd_1757128 < baseStart_1757128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757159 : List Nat := [1, 1, 5, 2, 3, 1, 1, 7]
def baseStart_1757159 : Nat := 118140960795 + 1757159 * 2 ^ 59
def prefixEnd_1757159 : Nat := 4983230072969 + 3 ^ 40 * 1757159 * 2
def baseEnd_1757159 : Nat := 133669207907229013486145

theorem tailTrace_1757159 : CollatzResearch.WordTrace tailWord_1757159 prefixEnd_1757159 133669207907229013486145 := by
  unfold tailWord_1757159
  simp only [CollatzResearch.WordTrace]
  refine ⟨64088853841120516710218531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42725902560747011140145687 64088853841120516710218531)
  ·
    refine ⟨96133280761680775065327797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64088853841120516710218531 96133280761680775065327797)
    ·
      refine ⟨9012495071407572662374481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96133280761680775065327797 9012495071407572662374481)
      ·
        refine ⟨6759371303555679496780861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9012495071407572662374481 6759371303555679496780861)
        ·
          refine ⟨2534764238833379811292823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6759371303555679496780861 2534764238833379811292823)
          ·
            refine ⟨3802146358250069716939235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534764238833379811292823 3802146358250069716939235)
            ·
              refine ⟨5703219537375104575408853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802146358250069716939235 5703219537375104575408853)
              ·
                refine ⟨133669207907229013486145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5703219537375104575408853 133669207907229013486145)
                ·
                  rfl

theorem cell21_1757159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_1757159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757159 prefixEnd_1757159 := by exact prefixLift 1757159
  have htrace : WordTrace (prefixWord ++ tailWord_1757159) baseStart_1757159 baseEnd_1757159 := by
    simpa [prefixWord, tailWord_1757159, baseEnd_1757159] using wordTrace_append hprefix tailTrace_1757159
  have hstable : (prefixWord ++ tailWord_1757159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757159).length < 2 ^ (prefixWord ++ tailWord_1757159).sum := by decide
  have hdescent : baseEnd_1757159 < baseStart_1757159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757165 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1757165 : Nat := 118140960795 + 1757165 * 2 ^ 59
def prefixEnd_1757165 : Nat := 4983230072969 + 3 ^ 40 * 1757165 * 2
def baseEnd_1757165 : Nat := 401008993003432363358423

theorem tailTrace_1757165 : CollatzResearch.WordTrace tailWord_1757165 prefixEnd_1757165 401008993003432363358423 := by
  unfold tailWord_1757165
  simp only [CollatzResearch.WordTrace]
  refine ⟨64089072679098779734936949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42726048452732519823291299 64089072679098779734936949)
  ·
    refine ⟨6008350563665510600150339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64089072679098779734936949 6008350563665510600150339)
    ·
      refine ⟨9012525845498265900225509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008350563665510600150339 9012525845498265900225509)
      ·
        refine ⟨1689848596030924856292283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9012525845498265900225509 1689848596030924856292283)
        ·
          refine ⟨2534772894046387284438425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689848596030924856292283 2534772894046387284438425)
          ·
            refine ⟨1901079670534790463328819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534772894046387284438425 1901079670534790463328819)
            ·
              refine ⟨2851619505802185694993229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901079670534790463328819 2851619505802185694993229)
              ·
                refine ⟨1069357314675819635622461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2851619505802185694993229 1069357314675819635622461)
                ·
                  refine ⟨401008993003432363358423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069357314675819635622461 401008993003432363358423)
                  ·
                    rfl

theorem cell21_1757165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1757165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757165 prefixEnd_1757165 := by exact prefixLift 1757165
  have htrace : WordTrace (prefixWord ++ tailWord_1757165) baseStart_1757165 baseEnd_1757165 := by
    simpa [prefixWord, tailWord_1757165, baseEnd_1757165] using wordTrace_append hprefix tailTrace_1757165
  have hstable : (prefixWord ++ tailWord_1757165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757165).length < 2 ^ (prefixWord ++ tailWord_1757165).sum := by decide
  have hdescent : baseEnd_1757165 < baseStart_1757165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757218 : List Nat := [3, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1757218 : Nat := 118140960795 + 1757218 * 2 ^ 59
def prefixEnd_1757218 : Nat := 4983230072969 + 3 ^ 40 * 1757218 * 2
def baseEnd_1757218 : Nat := 133673696108505349658327

theorem tailTrace_1757218 : CollatzResearch.WordTrace tailWord_1757218 prefixEnd_1757218 133673696108505349658327 := by
  unfold tailWord_1757218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16022751436976692446654077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42727337165271179857744205 16022751436976692446654077)
  ·
    refine ⟨6008531788866259667495279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16022751436976692446654077 6008531788866259667495279)
    ·
      refine ⟨9012797683299389501242919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008531788866259667495279 9012797683299389501242919)
      ·
        refine ⟨13519196524949084251864379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9012797683299389501242919 13519196524949084251864379)
        ·
          refine ⟨20278794787423626377796569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13519196524949084251864379 20278794787423626377796569)
          ·
            refine ⟨15209096090567719783347427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20278794787423626377796569 15209096090567719783347427)
            ·
              refine ⟨22813644135851579675021141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15209096090567719783347427 22813644135851579675021141)
              ·
                refine ⟨133673696108505349658327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22813644135851579675021141 133673696108505349658327)
                ·
                  rfl

theorem cell21_1757218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1757218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757218 prefixEnd_1757218 := by exact prefixLift 1757218
  have htrace : WordTrace (prefixWord ++ tailWord_1757218) baseStart_1757218 baseEnd_1757218 := by
    simpa [prefixWord, tailWord_1757218, baseEnd_1757218] using wordTrace_append hprefix tailTrace_1757218
  have hstable : (prefixWord ++ tailWord_1757218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757218).length < 2 ^ (prefixWord ++ tailWord_1757218).sum := by decide
  have hdescent : baseEnd_1757218 < baseStart_1757218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757241 : List Nat := [1, 2, 1, 5, 4, 1, 2, 2, 3]
def baseStart_1757241 : Nat := 118140960795 + 1757241 * 2 ^ 59
def prefixEnd_1757241 : Nat := 4983230072969 + 3 ^ 40 * 1757241 * 2
def baseEnd_1757241 : Nat := 401026337238873120091601

theorem tailTrace_1757241 : CollatzResearch.WordTrace tailWord_1757241 prefixEnd_1757241 401026337238873120091601 := by
  unfold tailWord_1757241
  simp only [CollatzResearch.WordTrace]
  refine ⟨64091844626823444714703577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42727896417882296476469051 64091844626823444714703577)
  ·
    refine ⟨48068883470117583536027683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64091844626823444714703577 48068883470117583536027683)
    ·
      refine ⟨72103325205176375304041525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48068883470117583536027683 72103325205176375304041525)
      ·
        refine ⟨6759686737985285184753893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72103325205176375304041525 6759686737985285184753893)
        ·
          refine ⟨1267441263372240972141355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6759686737985285184753893 1267441263372240972141355)
          ·
            refine ⟨1901161895058361458212033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267441263372240972141355 1901161895058361458212033)
            ·
              refine ⟨1425871421293771093659025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901161895058361458212033 1425871421293771093659025)
              ·
                refine ⟨1069403565970328320244269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1425871421293771093659025 1069403565970328320244269)
                ·
                  refine ⟨401026337238873120091601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069403565970328320244269 401026337238873120091601)
                  ·
                    rfl

theorem cell21_1757241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_1757241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757241 prefixEnd_1757241 := by exact prefixLift 1757241
  have htrace : WordTrace (prefixWord ++ tailWord_1757241) baseStart_1757241 baseEnd_1757241 := by
    simpa [prefixWord, tailWord_1757241, baseEnd_1757241] using wordTrace_append hprefix tailTrace_1757241
  have hstable : (prefixWord ++ tailWord_1757241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757241).length < 2 ^ (prefixWord ++ tailWord_1757241).sum := by decide
  have hdescent : baseEnd_1757241 < baseStart_1757241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757266 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1757266 : Nat := 118140960795 + 1757266 * 2 ^ 59
def prefixEnd_1757266 : Nat := 4983230072969 + 3 ^ 40 * 1757266 * 2
def baseEnd_1757266 : Nat := 401032042579478632174883

theorem tailTrace_1757266 : CollatzResearch.WordTrace tailWord_1757266 prefixEnd_1757266 401032042579478632174883 := by
  unfold tailWord_1757266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023189112933218496090913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42728504301155249322909101 16023189112933218496090913)
  ·
    refine ⟨12017391834699913872068185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16023189112933218496090913 12017391834699913872068185)
    ·
      refine ⟨9013043876024935404051139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12017391834699913872068185 9013043876024935404051139)
      ·
        refine ⟨13519565814037403106076709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013043876024935404051139 13519565814037403106076709)
        ·
          refine ⟨2534918590132013082389383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13519565814037403106076709 2534918590132013082389383)
          ·
            refine ⟨3802377885198019623584075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534918590132013082389383 3802377885198019623584075)
            ·
              refine ⟨5703566827797029435376113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802377885198019623584075 5703566827797029435376113)
              ·
                refine ⟨4277675120847772076532085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703566827797029435376113 4277675120847772076532085)
                ·
                  refine ⟨401032042579478632174883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4277675120847772076532085 401032042579478632174883)
                  ·
                    rfl

theorem cell21_1757266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1757266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757266 prefixEnd_1757266 := by exact prefixLift 1757266
  have htrace : WordTrace (prefixWord ++ tailWord_1757266) baseStart_1757266 baseEnd_1757266 := by
    simpa [prefixWord, tailWord_1757266, baseEnd_1757266] using wordTrace_append hprefix tailTrace_1757266
  have hstable : (prefixWord ++ tailWord_1757266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757266).length < 2 ^ (prefixWord ++ tailWord_1757266).sum := by decide
  have hdescent : baseEnd_1757266 < baseStart_1757266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757294 : List Nat := [4, 1, 2, 2, 1, 1, 10]
def baseStart_1757294 : Nat := 118140960795 + 1757294 * 2 ^ 59
def prefixEnd_1757294 : Nat := 4983230072969 + 3 ^ 40 * 1757294 * 2
def baseEnd_1757294 : Nat := 44559825840106311745351

theorem tailTrace_1757294 : CollatzResearch.WordTrace tailWord_1757294 prefixEnd_1757294 44559825840106311745351 := by
  unfold tailWord_1757294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011722211953929345797867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42729185130420956510921957 8011722211953929345797867)
  ·
    refine ⟨12017583317930894018696801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8011722211953929345797867 12017583317930894018696801)
    ·
      refine ⟨9013187488448170514022601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12017583317930894018696801 9013187488448170514022601)
      ·
        refine ⟨6759890616336127885516951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9013187488448170514022601 6759890616336127885516951)
        ·
          refine ⟨10139835924504191828275427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6759890616336127885516951 10139835924504191828275427)
          ·
            refine ⟨15209753886756287742413141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10139835924504191828275427 15209753886756287742413141)
            ·
              refine ⟨44559825840106311745351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15209753886756287742413141 44559825840106311745351)
              ·
                rfl

theorem cell21_1757294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 10].length) (baseStart_1757294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757294 prefixEnd_1757294 := by exact prefixLift 1757294
  have htrace : WordTrace (prefixWord ++ tailWord_1757294) baseStart_1757294 baseEnd_1757294 := by
    simpa [prefixWord, tailWord_1757294, baseEnd_1757294] using wordTrace_append hprefix tailTrace_1757294
  have hstable : (prefixWord ++ tailWord_1757294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757294).length < 2 ^ (prefixWord ++ tailWord_1757294).sum := by decide
  have hdescent : baseEnd_1757294 < baseStart_1757294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757384 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_1757384 : Nat := 118140960795 + 1757384 * 2 ^ 59
def prefixEnd_1757384 : Nat := 4983230072969 + 3 ^ 40 * 1757384 * 2
def baseEnd_1757384 : Nat := 401058971787136649207975

theorem tailTrace_1757384 : CollatzResearch.WordTrace tailWord_1757384 prefixEnd_1757384 401058971787136649207975 := by
  unfold tailWord_1757384
  simp only [CollatzResearch.WordTrace]
  refine ⟨32048530132652690068579603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42731373510203586758106137 32048530132652690068579603)
  ·
    refine ⟨48072795198979035102869405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32048530132652690068579603 48072795198979035102869405)
    ·
      refine ⟨18027298199617138163576027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48072795198979035102869405 18027298199617138163576027)
      ·
        refine ⟨27040947299425707245364041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18027298199617138163576027 27040947299425707245364041)
        ·
          refine ⟨20280710474569280434023031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27040947299425707245364041 20280710474569280434023031)
          ·
            refine ⟨30421065711853920651034547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20280710474569280434023031 30421065711853920651034547)
            ·
              refine ⟨45631598567780880976551821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30421065711853920651034547 45631598567780880976551821)
              ·
                refine ⟨17111849462917830366206933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45631598567780880976551821 17111849462917830366206933)
                ·
                  refine ⟨401058971787136649207975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17111849462917830366206933 401058971787136649207975)
                  ·
                    rfl

theorem cell21_1757384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_1757384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757384 prefixEnd_1757384 := by exact prefixLift 1757384
  have htrace : WordTrace (prefixWord ++ tailWord_1757384) baseStart_1757384 baseEnd_1757384 := by
    simpa [prefixWord, tailWord_1757384, baseEnd_1757384] using wordTrace_append hprefix tailTrace_1757384
  have hstable : (prefixWord ++ tailWord_1757384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757384).length < 2 ^ (prefixWord ++ tailWord_1757384).sum := by decide
  have hdescent : baseEnd_1757384 < baseStart_1757384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757404 : List Nat := [2, 2, 5, 2, 2, 8]
def baseStart_1757404 : Nat := 118140960795 + 1757404 * 2 ^ 59
def prefixEnd_1757404 : Nat := 4983230072969 + 3 ^ 40 * 1757404 * 2
def baseEnd_1757404 : Nat := 14854205039245224402763

theorem tailTrace_1757404 : CollatzResearch.WordTrace tailWord_1757404 prefixEnd_1757404 14854205039245224402763 := by
  unfold tailWord_1757404
  simp only [CollatzResearch.WordTrace]
  refine ⟨32048894862616461776443633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42731859816821949035258177 32048894862616461776443633)
  ·
    refine ⟨24036671146962346332332725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32048894862616461776443633 24036671146962346332332725)
    ·
      refine ⟨2253437920027719968656193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24036671146962346332332725 2253437920027719968656193)
      ·
        refine ⟨1690078440020789976492145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253437920027719968656193 1690078440020789976492145)
        ·
          refine ⟨1267558830015592482369109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690078440020789976492145 1267558830015592482369109)
          ·
            refine ⟨14854205039245224402763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1267558830015592482369109 14854205039245224402763)
            ·
              rfl

theorem cell21_1757404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 8].length) (baseStart_1757404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757404 prefixEnd_1757404 := by exact prefixLift 1757404
  have htrace : WordTrace (prefixWord ++ tailWord_1757404) baseStart_1757404 baseEnd_1757404 := by
    simpa [prefixWord, tailWord_1757404, baseEnd_1757404] using wordTrace_append hprefix tailTrace_1757404
  have hstable : (prefixWord ++ tailWord_1757404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757404).length < 2 ^ (prefixWord ++ tailWord_1757404).sum := by decide
  have hdescent : baseEnd_1757404 < baseStart_1757404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757418 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 3]
def baseStart_1757418 : Nat := 118140960795 + 1757418 * 2 ^ 59
def prefixEnd_1757418 : Nat := 4983230072969 + 3 ^ 40 * 1757418 * 2
def baseEnd_1757418 : Nat := 401066731050360145641239

theorem tailTrace_1757418 : CollatzResearch.WordTrace tailWord_1757418 prefixEnd_1757418 401066731050360145641239 := by
  unfold tailWord_1757418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024575086795550985974227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42732200231454802629264605 16024575086795550985974227)
  ·
    refine ⟨24036862630193326478961341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16024575086795550985974227 24036862630193326478961341)
    ·
      refine ⟨9013823486322497429610503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24036862630193326478961341 9013823486322497429610503)
      ·
        refine ⟨13520735229483746144415755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013823486322497429610503 13520735229483746144415755)
        ·
          refine ⟨20281102844225619216623633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13520735229483746144415755 20281102844225619216623633)
          ·
            refine ⟨15210827133169214412467725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20281102844225619216623633 15210827133169214412467725)
            ·
              refine ⟨5704060174938455404675397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15210827133169214412467725 5704060174938455404675397)
              ·
                refine ⟨1069511282800960388376637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5704060174938455404675397 1069511282800960388376637)
                ·
                  refine ⟨401066731050360145641239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069511282800960388376637 401066731050360145641239)
                  ·
                    rfl

theorem cell21_1757418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 3].length) (baseStart_1757418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757418 prefixEnd_1757418 := by exact prefixLift 1757418
  have htrace : WordTrace (prefixWord ++ tailWord_1757418) baseStart_1757418 baseEnd_1757418 := by
    simpa [prefixWord, tailWord_1757418, baseEnd_1757418] using wordTrace_append hprefix tailTrace_1757418
  have hstable : (prefixWord ++ tailWord_1757418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757418).length < 2 ^ (prefixWord ++ tailWord_1757418).sum := by decide
  have hdescent : baseEnd_1757418 < baseStart_1757418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757466 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1757466 : Nat := 118140960795 + 1757466 * 2 ^ 59
def prefixEnd_1757466 : Nat := 4983230072969 + 3 ^ 40 * 1757466 * 2
def baseEnd_1757466 : Nat := 401077685304322728841141

theorem tailTrace_1757466 : CollatzResearch.WordTrace tailWord_1757466 prefixEnd_1757466 401077685304322728841141 := by
  unfold tailWord_1757466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16025012762752077035411063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42733367367338872094429501 16025012762752077035411063)
  ·
    refine ⟨24037519144128115553116595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16025012762752077035411063 24037519144128115553116595)
    ·
      refine ⟨36056278716192173329674893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24037519144128115553116595 36056278716192173329674893)
      ·
        refine ⟨13521104518572064998628085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36056278716192173329674893 13521104518572064998628085)
        ·
          refine ⟨1267603548616131093621383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13521104518572064998628085 1267603548616131093621383)
          ·
            refine ⟨1901405322924196640432075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267603548616131093621383 1901405322924196640432075)
            ·
              refine ⟨2852107984386294960648113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901405322924196640432075 2852107984386294960648113)
              ·
                refine ⟨2139080988289721220486085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852107984386294960648113 2139080988289721220486085)
                ·
                  refine ⟨401077685304322728841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139080988289721220486085 401077685304322728841141)
                  ·
                    rfl

theorem cell21_1757466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1757466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757466 prefixEnd_1757466 := by exact prefixLift 1757466
  have htrace : WordTrace (prefixWord ++ tailWord_1757466) baseStart_1757466 baseEnd_1757466 := by
    simpa [prefixWord, tailWord_1757466, baseEnd_1757466] using wordTrace_append hprefix tailTrace_1757466
  have hstable : (prefixWord ++ tailWord_1757466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757466).length < 2 ^ (prefixWord ++ tailWord_1757466).sum := by decide
  have hdescent : baseEnd_1757466 < baseStart_1757466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757534 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1757534 : Nat := 118140960795 + 1757534 * 2 ^ 59
def prefixEnd_1757534 : Nat := 4983230072969 + 3 ^ 40 * 1757534 * 2
def baseEnd_1757534 : Nat := 401093203830769721707669

theorem tailTrace_1757534 : CollatzResearch.WordTrace tailWord_1757534 prefixEnd_1757534 401093203830769721707669 := by
  unfold tailWord_1757534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012816401845244469389957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42735020809841303836746437 8012816401845244469389957)
  ·
    refine ⟨1502403075345983338010617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8012816401845244469389957 1502403075345983338010617)
    ·
      refine ⟨1126802306509487503507963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502403075345983338010617 1126802306509487503507963)
      ·
        refine ⟨1690203459764231255261945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126802306509487503507963 1690203459764231255261945)
        ·
          refine ⟨1267652594823173441446459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690203459764231255261945 1267652594823173441446459)
          ·
            refine ⟨1901478892234760162169689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267652594823173441446459 1901478892234760162169689)
            ·
              refine ⟨1426109169176070121627267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901478892234760162169689 1426109169176070121627267)
              ·
                refine ⟨2139163753764105182440901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426109169176070121627267 2139163753764105182440901)
                ·
                  refine ⟨401093203830769721707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139163753764105182440901 401093203830769721707669)
                  ·
                    rfl

theorem cell21_1757534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1757534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757534 prefixEnd_1757534 := by exact prefixLift 1757534
  have htrace : WordTrace (prefixWord ++ tailWord_1757534) baseStart_1757534 baseEnd_1757534 := by
    simpa [prefixWord, tailWord_1757534, baseEnd_1757534] using wordTrace_append hprefix tailTrace_1757534
  have hstable : (prefixWord ++ tailWord_1757534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757534).length < 2 ^ (prefixWord ++ tailWord_1757534).sum := by decide
  have hdescent : baseEnd_1757534 < baseStart_1757534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757590 : List Nat := [5, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1757590 : Nat := 118140960795 + 1757590 * 2 ^ 59
def prefixEnd_1757590 : Nat := 4983230072969 + 3 ^ 40 * 1757590 * 2
def baseEnd_1757590 : Nat := 133701994597908689591407

theorem tailTrace_1757590 : CollatzResearch.WordTrace tailWord_1757590 prefixEnd_1757590 133701994597908689591407 := by
  unfold tailWord_1757590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006535856409942332447389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42736382468372718212772149 4006535856409942332447389)
  ·
    refine ⟨1502450946153728374667771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4006535856409942332447389 1502450946153728374667771)
    ·
      refine ⟨2253676419230592562001657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502450946153728374667771 2253676419230592562001657)
      ·
        refine ⟨1690257314422944421501243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253676419230592562001657 1690257314422944421501243)
        ·
          refine ⟨2535385971634416632251865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690257314422944421501243 2535385971634416632251865)
          ·
            refine ⟨1901539478725812474188899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535385971634416632251865 1901539478725812474188899)
            ·
              refine ⟨2852309218088718711283349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901539478725812474188899 2852309218088718711283349)
              ·
                refine ⟨133701994597908689591407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2852309218088718711283349 133701994597908689591407)
                ·
                  rfl

theorem cell21_1757590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1757590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757590 prefixEnd_1757590 := by exact prefixLift 1757590
  have htrace : WordTrace (prefixWord ++ tailWord_1757590) baseStart_1757590 baseEnd_1757590 := by
    simpa [prefixWord, tailWord_1757590, baseEnd_1757590] using wordTrace_append hprefix tailTrace_1757590
  have hstable : (prefixWord ++ tailWord_1757590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757590).length < 2 ^ (prefixWord ++ tailWord_1757590).sum := by decide
  have hdescent : baseEnd_1757590 < baseStart_1757590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757657 : List Nat := [1, 2, 1, 2, 4, 1, 2, 8]
def baseStart_1757657 : Nat := 118140960795 + 1757657 * 2 ^ 59
def prefixEnd_1757657 : Nat := 4983230072969 + 3 ^ 40 * 1757657 * 2
def baseEnd_1757657 : Nat := 133707091368849613719139

theorem tailTrace_1757657 : CollatzResearch.WordTrace tailWord_1757657 prefixEnd_1757657 133707091368849613719139 := by
  unfold tailWord_1757657
  simp only [CollatzResearch.WordTrace]
  refine ⟨64107017393316347761847225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42738011595544231841231483 64107017393316347761847225)
  ·
    refine ⟨48080263044987260821385419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64107017393316347761847225 48080263044987260821385419)
    ·
      refine ⟨72120394567480891232078129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48080263044987260821385419 72120394567480891232078129)
      ·
        refine ⟨54090295925610668424058597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72120394567480891232078129 54090295925610668424058597)
        ·
          refine ⟨10141930486052000329510987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54090295925610668424058597 10141930486052000329510987)
          ·
            refine ⟨15212895729078000494266481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10141930486052000329510987 15212895729078000494266481)
            ·
              refine ⟨11409671796808500370699861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15212895729078000494266481 11409671796808500370699861)
              ·
                refine ⟨133707091368849613719139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11409671796808500370699861 133707091368849613719139)
                ·
                  rfl

theorem cell21_1757657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_1757657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757657 prefixEnd_1757657 := by exact prefixLift 1757657
  have htrace : WordTrace (prefixWord ++ tailWord_1757657) baseStart_1757657 baseEnd_1757657 := by
    simpa [prefixWord, tailWord_1757657, baseEnd_1757657] using wordTrace_append hprefix tailTrace_1757657
  have hstable : (prefixWord ++ tailWord_1757657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757657).length < 2 ^ (prefixWord ++ tailWord_1757657).sum := by decide
  have hdescent : baseEnd_1757657 < baseStart_1757657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757666 : List Nat := [3, 3, 3, 2, 2, 1, 2, 5]
def baseStart_1757666 : Nat := 118140960795 + 1757666 * 2 ^ 59
def prefixEnd_1757666 : Nat := 4983230072969 + 3 ^ 40 * 1757666 * 2
def baseEnd_1757666 : Nat := 133707776009722275169133

theorem tailTrace_1757666 : CollatzResearch.WordTrace tailWord_1757666 prefixEnd_1757666 133707776009722275169133 := by
  unfold tailWord_1757666
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026836412570935574731213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42738230433522494865949901 16026836412570935574731213)
  ·
    refine ⟨6010063654714100840524205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16026836412570935574731213 6010063654714100840524205)
    ·
      refine ⟨2253773870517787815196577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6010063654714100840524205 2253773870517787815196577)
      ·
        refine ⟨1690330402888340861397433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253773870517787815196577 1690330402888340861397433)
        ·
          refine ⟨1267747802166255646048075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690330402888340861397433 1267747802166255646048075)
          ·
            refine ⟨1901621703249383469072113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267747802166255646048075 1901621703249383469072113)
            ·
              refine ⟨1426216277437037601804085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901621703249383469072113 1426216277437037601804085)
              ·
                refine ⟨133707776009722275169133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1426216277437037601804085 133707776009722275169133)
                ·
                  rfl

theorem cell21_1757666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_1757666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757666 prefixEnd_1757666 := by exact prefixLift 1757666
  have htrace : WordTrace (prefixWord ++ tailWord_1757666) baseStart_1757666 baseEnd_1757666 := by
    simpa [prefixWord, tailWord_1757666, baseEnd_1757666] using wordTrace_append hprefix tailTrace_1757666
  have hstable : (prefixWord ++ tailWord_1757666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757666).length < 2 ^ (prefixWord ++ tailWord_1757666).sum := by decide
  have hdescent : baseEnd_1757666 < baseStart_1757666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757674 : List Nat := [3, 1, 3, 1, 3, 2, 1, 7]
def baseStart_1757674 : Nat := 118140960795 + 1757674 * 2 ^ 59
def prefixEnd_1757674 : Nat := 4983230072969 + 3 ^ 40 * 1757674 * 2
def baseEnd_1757674 : Nat := 133708384579386863124683

theorem tailTrace_1757674 : CollatzResearch.WordTrace tailWord_1757674 prefixEnd_1757674 133708384579386863124683 := by
  unfold tailWord_1757674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026909358563689916304019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42738424956169839776810717 16026909358563689916304019)
  ·
    refine ⟨24040364037845534874456029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16026909358563689916304019 24040364037845534874456029)
    ·
      refine ⟨9015136514192075577921011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24040364037845534874456029 9015136514192075577921011)
      ·
        refine ⟨13522704771288113366881517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015136514192075577921011 13522704771288113366881517)
        ·
          refine ⟨5071014289233042512580569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13522704771288113366881517 5071014289233042512580569)
          ·
            refine ⟨3803260716924781884435427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5071014289233042512580569 3803260716924781884435427)
            ·
              refine ⟨5704891075387172826653141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803260716924781884435427 5704891075387172826653141)
              ·
                refine ⟨133708384579386863124683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5704891075387172826653141 133708384579386863124683)
                ·
                  rfl

theorem cell21_1757674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 7].length) (baseStart_1757674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757674 prefixEnd_1757674 := by exact prefixLift 1757674
  have htrace : WordTrace (prefixWord ++ tailWord_1757674) baseStart_1757674 baseEnd_1757674 := by
    simpa [prefixWord, tailWord_1757674, baseEnd_1757674] using wordTrace_append hprefix tailTrace_1757674
  have hstable : (prefixWord ++ tailWord_1757674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757674).length < 2 ^ (prefixWord ++ tailWord_1757674).sum := by decide
  have hdescent : baseEnd_1757674 < baseStart_1757674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757733 : List Nat := [1, 3, 1, 2, 2, 1, 4, 7]
def baseStart_1757733 : Nat := 118140960795 + 1757733 * 2 ^ 59
def prefixEnd_1757733 : Nat := 4983230072969 + 3 ^ 40 * 1757733 * 2
def baseEnd_1757733 : Nat := 133712872780663199296865

theorem tailTrace_1757733 : CollatzResearch.WordTrace tailWord_1757733 prefixEnd_1757733 133712872780663199296865 := by
  unfold tailWord_1757733
  simp only [CollatzResearch.WordTrace]
  refine ⟨64109789341041012741613853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42739859560694008494409235 64109789341041012741613853)
  ·
    refine ⟨24041171002890379778105195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64109789341041012741613853 24041171002890379778105195)
    ·
      refine ⟨36061756504335569667157793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24041171002890379778105195 36061756504335569667157793)
      ·
        refine ⟨27046317378251677250368345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36061756504335569667157793 27046317378251677250368345)
        ·
          refine ⟨20284738033688757937776259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27046317378251677250368345 20284738033688757937776259)
          ·
            refine ⟨30427107050533136906664389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284738033688757937776259 30427107050533136906664389)
            ·
              refine ⟨5705082571974963169999573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30427107050533136906664389 5705082571974963169999573)
              ·
                refine ⟨133712872780663199296865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5705082571974963169999573 133712872780663199296865)
                ·
                  rfl

theorem cell21_1757733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 7].length) (baseStart_1757733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757733 prefixEnd_1757733 := by exact prefixLift 1757733
  have htrace : WordTrace (prefixWord ++ tailWord_1757733) baseStart_1757733 baseEnd_1757733 := by
    simpa [prefixWord, tailWord_1757733, baseEnd_1757733] using wordTrace_append hprefix tailTrace_1757733
  have hstable : (prefixWord ++ tailWord_1757733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757733).length < 2 ^ (prefixWord ++ tailWord_1757733).sum := by decide
  have hdescent : baseEnd_1757733 < baseStart_1757733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757750 : List Nat := [5, 1, 2, 1, 2, 10]
def baseStart_1757750 : Nat := 118140960795 + 1757750 * 2 ^ 59
def prefixEnd_1757750 : Nat := 4983230072969 + 3 ^ 40 * 1757750 * 2
def baseEnd_1757750 : Nat := 14857129554577827633601

theorem tailTrace_1757750 : CollatzResearch.WordTrace tailWord_1757750 prefixEnd_1757750 14857129554577827633601 := by
  unfold tailWord_1757750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006900586373714040311419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42740272921319616429988469 4006900586373714040311419)
  ·
    refine ⟨6010350879560571060467129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4006900586373714040311419 6010350879560571060467129)
    ·
      refine ⟨4507763159670428295350347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6010350879560571060467129 4507763159670428295350347)
      ·
        refine ⟨6761644739505642443025521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507763159670428295350347 6761644739505642443025521)
        ·
          refine ⟨5071233554629231832269141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6761644739505642443025521 5071233554629231832269141)
          ·
            refine ⟨14857129554577827633601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5071233554629231832269141 14857129554577827633601)
            ·
              rfl

theorem cell21_1757750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 10].length) (baseStart_1757750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757750 prefixEnd_1757750 := by exact prefixLift 1757750
  have htrace : WordTrace (prefixWord ++ tailWord_1757750) baseStart_1757750 baseEnd_1757750 := by
    simpa [prefixWord, tailWord_1757750, baseEnd_1757750] using wordTrace_append hprefix tailTrace_1757750
  have hstable : (prefixWord ++ tailWord_1757750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757750).length < 2 ^ (prefixWord ++ tailWord_1757750).sum := by decide
  have hdescent : baseEnd_1757750 < baseStart_1757750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757885 : List Nat := [1, 4, 1, 2, 1, 3, 1, 8]
def baseStart_1757885 : Nat := 118140960795 + 1757885 * 2 ^ 59
def prefixEnd_1757885 : Nat := 4983230072969 + 3 ^ 40 * 1757885 * 2
def baseEnd_1757885 : Nat := 133724435604290370452317

theorem tailTrace_1757885 : CollatzResearch.WordTrace tailWord_1757885 prefixEnd_1757885 133724435604290370452317 := by
  unfold tailWord_1757885
  simp only [CollatzResearch.WordTrace]
  refine ⟨64115333236490342701147109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42743555490993561800764739 64115333236490342701147109)
  ·
    refine ⟨12021624981841939256465083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64115333236490342701147109 12021624981841939256465083)
    ·
      refine ⟨18032437472762908884697625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12021624981841939256465083 18032437472762908884697625)
      ·
        refine ⟨13524328104572181663523219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18032437472762908884697625 13524328104572181663523219)
        ·
          refine ⟨20286492156858272495284829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524328104572181663523219 20286492156858272495284829)
          ·
            refine ⟨7607434558821852185731811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20286492156858272495284829 7607434558821852185731811)
            ·
              refine ⟨11411151838232778278597717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607434558821852185731811 11411151838232778278597717)
              ·
                refine ⟨133724435604290370452317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11411151838232778278597717 133724435604290370452317)
                ·
                  rfl

theorem cell21_1757885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_1757885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757885 prefixEnd_1757885 := by exact prefixLift 1757885
  have htrace : WordTrace (prefixWord ++ tailWord_1757885) baseStart_1757885 baseEnd_1757885 := by
    simpa [prefixWord, tailWord_1757885, baseEnd_1757885] using wordTrace_append hprefix tailTrace_1757885
  have hstable : (prefixWord ++ tailWord_1757885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757885).length < 2 ^ (prefixWord ++ tailWord_1757885).sum := by decide
  have hdescent : baseEnd_1757885 < baseStart_1757885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1757888 : List Nat := [2, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_1757888 : Nat := 118140960795 + 1757888 * 2 ^ 59
def prefixEnd_1757888 : Nat := 4983230072969 + 3 ^ 40 * 1757888 * 2
def baseEnd_1757888 : Nat := 401173991453743772806945

theorem tailTrace_1757888 : CollatzResearch.WordTrace tailWord_1757888 prefixEnd_1757888 401173991453743772806945 := by
  unfold tailWord_1757888
  simp only [CollatzResearch.WordTrace]
  refine ⟨32057721327739737106753159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42743628436986316142337545 32057721327739737106753159)
  ·
    refine ⟨48086581991609605660129739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32057721327739737106753159 48086581991609605660129739)
    ·
      refine ⟨72129872987414408490194609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48086581991609605660129739 72129872987414408490194609)
      ·
        refine ⟨54097404740560806367645957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72129872987414408490194609 54097404740560806367645957)
        ·
          refine ⟨10143263388855151193933617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54097404740560806367645957 10143263388855151193933617)
          ·
            refine ⟨7607447541641363395450213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10143263388855151193933617 7607447541641363395450213)
            ·
              refine ⟨1426396414057755636646915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7607447541641363395450213 1426396414057755636646915)
              ·
                refine ⟨2139594621086633454970373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426396414057755636646915 2139594621086633454970373)
                ·
                  refine ⟨401173991453743772806945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139594621086633454970373 401173991453743772806945)
                  ·
                    rfl

theorem cell21_1757888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_1757888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1757888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1757888 prefixEnd_1757888 := by exact prefixLift 1757888
  have htrace : WordTrace (prefixWord ++ tailWord_1757888) baseStart_1757888 baseEnd_1757888 := by
    simpa [prefixWord, tailWord_1757888, baseEnd_1757888] using wordTrace_append hprefix tailTrace_1757888
  have hstable : (prefixWord ++ tailWord_1757888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1757888).length < 2 ^ (prefixWord ++ tailWord_1757888).sum := by decide
  have hdescent : baseEnd_1757888 < baseStart_1757888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1757888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758220 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_1758220 : Nat := 118140960795 + 1758220 * 2 ^ 59
def prefixEnd_1758220 : Nat := 4983230072969 + 3 ^ 40 * 1758220 * 2
def baseEnd_1758220 : Nat := 401249758376984973272933

theorem tailTrace_1758220 : CollatzResearch.WordTrace tailWord_1758220 prefixEnd_1758220 401249758376984973272933 := by
  unfold tailWord_1758220
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063775845138347457296057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42751701126851129943061409 32063775845138347457296057)
  ·
    refine ⟨24047831883853760592972043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32063775845138347457296057 24047831883853760592972043)
    ·
      refine ⟨36071747825780640889458065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24047831883853760592972043 36071747825780640889458065)
      ·
        refine ⟨27053810869335480667093549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36071747825780640889458065 27053810869335480667093549)
        ·
          refine ⟨10145179076000805250160081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27053810869335480667093549 10145179076000805250160081)
          ·
            refine ⟨7608884307000603937620061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10145179076000805250160081 7608884307000603937620061)
            ·
              refine ⟨2853331615125226476607523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7608884307000603937620061 2853331615125226476607523)
              ·
                refine ⟨4279997422687839714911285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2853331615125226476607523 4279997422687839714911285)
                ·
                  refine ⟨401249758376984973272933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4279997422687839714911285 401249758376984973272933)
                  ·
                    rfl

theorem cell21_1758220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_1758220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758220 prefixEnd_1758220 := by exact prefixLift 1758220
  have htrace : WordTrace (prefixWord ++ tailWord_1758220) baseStart_1758220 baseEnd_1758220 := by
    simpa [prefixWord, tailWord_1758220, baseEnd_1758220] using wordTrace_append hprefix tailTrace_1758220
  have hstable : (prefixWord ++ tailWord_1758220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758220).length < 2 ^ (prefixWord ++ tailWord_1758220).sum := by decide
  have hdescent : baseEnd_1758220 < baseStart_1758220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758226 : List Nat := [3, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1758226 : Nat := 118140960795 + 1758226 * 2 ^ 59
def prefixEnd_1758226 : Nat := 4983230072969 + 3 ^ 40 * 1758226 * 2
def baseEnd_1758226 : Nat := 401251127658730296172921

theorem tailTrace_1758226 : CollatzResearch.WordTrace tailWord_1758226 prefixEnd_1758226 401251127658730296172921 := by
  unfold tailWord_1758226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031942632063739484827633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42751847018836638626207021 16031942632063739484827633)
  ·
    refine ⟨12023956974047804613620725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16031942632063739484827633 12023956974047804613620725)
    ·
      refine ⟨1127245966316981682526943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12023956974047804613620725 1127245966316981682526943)
      ·
        refine ⟨1690868949475472523790415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127245966316981682526943 1690868949475472523790415)
        ·
          refine ⟨2536303424213208785685623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690868949475472523790415 2536303424213208785685623)
          ·
            refine ⟨3804455136319813178528435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536303424213208785685623 3804455136319813178528435)
            ·
              refine ⟨5706682704479719767792653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804455136319813178528435 5706682704479719767792653)
              ·
                refine ⟨2140006014179894912922245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5706682704479719767792653 2140006014179894912922245)
                ·
                  refine ⟨401251127658730296172921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140006014179894912922245 401251127658730296172921)
                  ·
                    rfl

theorem cell21_1758226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1758226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758226 prefixEnd_1758226 := by exact prefixLift 1758226
  have htrace : WordTrace (prefixWord ++ tailWord_1758226) baseStart_1758226 baseEnd_1758226 := by
    simpa [prefixWord, tailWord_1758226, baseEnd_1758226] using wordTrace_append hprefix tailTrace_1758226
  have hstable : (prefixWord ++ tailWord_1758226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758226).length < 2 ^ (prefixWord ++ tailWord_1758226).sum := by decide
  have hdescent : baseEnd_1758226 < baseStart_1758226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758313 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 3]
def baseStart_1758313 : Nat := 118140960795 + 1758313 * 2 ^ 59
def prefixEnd_1758313 : Nat := 4983230072969 + 3 ^ 40 * 1758313 * 2
def baseEnd_1758313 : Nat := 401270982244037478222743

theorem tailTrace_1758313 : CollatzResearch.WordTrace tailWord_1758313 prefixEnd_1758313 401270982244037478222743 := by
  unfold tailWord_1758313
  simp only [CollatzResearch.WordTrace]
  refine ⟨64130943678939771797727593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42753962452626514531818395 64130943678939771797727593)
  ·
    refine ⟨48098207759204828848295695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64130943678939771797727593 48098207759204828848295695)
    ·
      refine ⟨72147311638807243272443543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48098207759204828848295695 72147311638807243272443543)
      ·
        refine ⟨108220967458210864908665315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72147311638807243272443543 108220967458210864908665315)
        ·
          refine ⟨162331451187316297362997973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108220967458210864908665315 162331451187316297362997973)
          ·
            refine ⟨3804643387202725719445265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 162331451187316297362997973 3804643387202725719445265)
            ·
              refine ⟨2853482540402044289583949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804643387202725719445265 2853482540402044289583949)
              ·
                refine ⟨1070055952650766608593981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853482540402044289583949 1070055952650766608593981)
                ·
                  refine ⟨401270982244037478222743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070055952650766608593981 401270982244037478222743)
                  ·
                    rfl

theorem cell21_1758313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 3].length) (baseStart_1758313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758313 prefixEnd_1758313 := by exact prefixLift 1758313
  have htrace : WordTrace (prefixWord ++ tailWord_1758313) baseStart_1758313 baseEnd_1758313 := by
    simpa [prefixWord, tailWord_1758313, baseEnd_1758313] using wordTrace_append hprefix tailTrace_1758313
  have hstable : (prefixWord ++ tailWord_1758313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758313).length < 2 ^ (prefixWord ++ tailWord_1758313).sum := by decide
  have hdescent : baseEnd_1758313 < baseStart_1758313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758355 : List Nat := [1, 1, 1, 2, 1, 2, 6, 2, 5]
def baseStart_1758355 : Nat := 118140960795 + 1758355 * 2 ^ 59
def prefixEnd_1758355 : Nat := 4983230072969 + 3 ^ 40 * 1758355 * 2
def baseEnd_1758355 : Nat := 401280567216254738522657

theorem tailTrace_1758355 : CollatzResearch.WordTrace tailWord_1758355 prefixEnd_1758355 401280567216254738522657 := by
  unfold tailWord_1758355
  simp only [CollatzResearch.WordTrace]
  refine ⟨64132475544787612970756519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42754983696525075313837679 64132475544787612970756519)
  ·
    refine ⟨96198713317181419456134779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64132475544787612970756519 96198713317181419456134779)
    ·
      refine ⟨144298069975772129184202169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96198713317181419456134779 144298069975772129184202169)
      ·
        refine ⟨108223552481829096888151627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144298069975772129184202169 108223552481829096888151627)
        ·
          refine ⟨162335328722743645332227441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108223552481829096888151627 162335328722743645332227441)
          ·
            refine ⟨121751496542057733999170581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162335328722743645332227441 121751496542057733999170581)
            ·
              refine ⟨5707101400408956281211121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121751496542057733999170581 5707101400408956281211121)
              ·
                refine ⟨4280326050306717210908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707101400408956281211121 4280326050306717210908341)
                ·
                  refine ⟨401280567216254738522657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280326050306717210908341 401280567216254738522657)
                  ·
                    rfl

theorem cell21_1758355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_1758355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758355 prefixEnd_1758355 := by exact prefixLift 1758355
  have htrace : WordTrace (prefixWord ++ tailWord_1758355) baseStart_1758355 baseEnd_1758355 := by
    simpa [prefixWord, tailWord_1758355, baseEnd_1758355] using wordTrace_append hprefix tailTrace_1758355
  have hstable : (prefixWord ++ tailWord_1758355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758355).length < 2 ^ (prefixWord ++ tailWord_1758355).sum := by decide
  have hdescent : baseEnd_1758355 < baseStart_1758355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758386 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1758386 : Nat := 118140960795 + 1758386 * 2 ^ 59
def prefixEnd_1758386 : Nat := 4983230072969 + 3 ^ 40 * 1758386 * 2
def baseEnd_1758386 : Nat := 401287641838605573505927

theorem tailTrace_1758386 : CollatzResearch.WordTrace tailWord_1758386 prefixEnd_1758386 401287641838605573505927 := by
  unfold tailWord_1758386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16033401551918826316283753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42755737471783536843423341 16033401551918826316283753)
  ·
    refine ⟨12025051163939119737212815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16033401551918826316283753 12025051163939119737212815)
    ·
      refine ⟨18037576745908679605819223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025051163939119737212815 18037576745908679605819223)
      ·
        refine ⟨27056365118863019408728835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18037576745908679605819223 27056365118863019408728835)
        ·
          refine ⟨40584547678294529113093253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27056365118863019408728835 40584547678294529113093253)
          ·
            refine ⟨7609602689680224208704985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40584547678294529113093253 7609602689680224208704985)
            ·
              refine ⟨5707202017260168156528739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609602689680224208704985 5707202017260168156528739)
              ·
                refine ⟨8560803025890252234793109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707202017260168156528739 8560803025890252234793109)
                ·
                  refine ⟨401287641838605573505927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8560803025890252234793109 401287641838605573505927)
                  ·
                    rfl

theorem cell21_1758386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1758386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758386 prefixEnd_1758386 := by exact prefixLift 1758386
  have htrace : WordTrace (prefixWord ++ tailWord_1758386) baseStart_1758386 baseEnd_1758386 := by
    simpa [prefixWord, tailWord_1758386, baseEnd_1758386] using wordTrace_append hprefix tailTrace_1758386
  have hstable : (prefixWord ++ tailWord_1758386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758386).length < 2 ^ (prefixWord ++ tailWord_1758386).sum := by decide
  have hdescent : baseEnd_1758386 < baseStart_1758386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758493 : List Nat := [1, 4, 2, 3, 1, 2, 8]
def baseStart_1758493 : Nat := 118140960795 + 1758493 * 2 ^ 59
def prefixEnd_1758493 : Nat := 4983230072969 + 3 ^ 40 * 1758493 * 2
def baseEnd_1758493 : Nat := 44590228966266351691375

theorem tailTrace_1758493 : CollatzResearch.WordTrace tailWord_1758493 prefixEnd_1758493 44590228966266351691375 := by
  unfold tailWord_1758493
  simp only [CollatzResearch.WordTrace]
  refine ⟨64137508818287662539280133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42758339212191775026186755 64137508818287662539280133)
  ·
    refine ⟨12025782903428936726115025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64137508818287662539280133 12025782903428936726115025)
    ·
      refine ⟨9019337177571702544586269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12025782903428936726115025 9019337177571702544586269)
      ·
        refine ⟨3382251441589388454219851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9019337177571702544586269 3382251441589388454219851)
        ·
          refine ⟨5073377162384082681329777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382251441589388454219851 5073377162384082681329777)
          ·
            refine ⟨3805032871788062010997333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073377162384082681329777 3805032871788062010997333)
            ·
              refine ⟨44590228966266351691375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3805032871788062010997333 44590228966266351691375)
              ·
                rfl

theorem cell21_1758493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 8].length) (baseStart_1758493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758493 prefixEnd_1758493 := by exact prefixLift 1758493
  have htrace : WordTrace (prefixWord ++ tailWord_1758493) baseStart_1758493 baseEnd_1758493 := by
    simpa [prefixWord, tailWord_1758493, baseEnd_1758493] using wordTrace_append hprefix tailTrace_1758493
  have hstable : (prefixWord ++ tailWord_1758493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758493).length < 2 ^ (prefixWord ++ tailWord_1758493).sum := by decide
  have hdescent : baseEnd_1758493 < baseStart_1758493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758496 : List Nat := [2, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_1758496 : Nat := 118140960795 + 1758496 * 2 ^ 59
def prefixEnd_1758496 : Nat := 4983230072969 + 3 ^ 40 * 1758496 * 2
def baseEnd_1758496 : Nat := 401312745337269826672369

theorem tailTrace_1758496 : CollatzResearch.WordTrace tailWord_1758496 prefixEnd_1758496 401312745337269826672369 := by
  unfold tailWord_1758496
  simp only [CollatzResearch.WordTrace]
  refine ⟨32068809118638397025819671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42758412158184529367759561 32068809118638397025819671)
  ·
    refine ⟨48103213677957595538729507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32068809118638397025819671 48103213677957595538729507)
    ·
      refine ⟨72154820516936393308094261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48103213677957595538729507 72154820516936393308094261)
      ·
        refine ⟨6764514423462786872633837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72154820516936393308094261 6764514423462786872633837)
        ·
          refine ⟨2536692908798545077237689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6764514423462786872633837 2536692908798545077237689)
          ·
            refine ⟨1902519681598908807928267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2536692908798545077237689 1902519681598908807928267)
            ·
              refine ⟨2853779522398363211892401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902519681598908807928267 2853779522398363211892401)
              ·
                refine ⟨2140334641798772408919301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853779522398363211892401 2140334641798772408919301)
                ·
                  refine ⟨401312745337269826672369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140334641798772408919301 401312745337269826672369)
                  ·
                    rfl

theorem cell21_1758496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_1758496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758496 prefixEnd_1758496 := by exact prefixLift 1758496
  have htrace : WordTrace (prefixWord ++ tailWord_1758496) baseStart_1758496 baseEnd_1758496 := by
    simpa [prefixWord, tailWord_1758496, baseEnd_1758496] using wordTrace_append hprefix tailTrace_1758496
  have hstable : (prefixWord ++ tailWord_1758496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758496).length < 2 ^ (prefixWord ++ tailWord_1758496).sum := by decide
  have hdescent : baseEnd_1758496 < baseStart_1758496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758572 : List Nat := [2, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1758572 : Nat := 118140960795 + 1758572 * 2 ^ 59
def prefixEnd_1758572 : Nat := 4983230072969 + 3 ^ 40 * 1758572 * 2
def baseEnd_1758572 : Nat := 401330089572710583405547

theorem tailTrace_1758572 : CollatzResearch.WordTrace tailWord_1758572 prefixEnd_1758572 401330089572710583405547 := by
  unfold tailWord_1758572
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070195092500729515702985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42760260123334306020937313 32070195092500729515702985)
  ·
    refine ⟨24052646319375547136777239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32070195092500729515702985 24052646319375547136777239)
    ·
      refine ⟨36078969479063320705165859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24052646319375547136777239 36078969479063320705165859)
      ·
        refine ⟨54118454218594981057748789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36078969479063320705165859 54118454218594981057748789)
        ·
          refine ⟨5073605082993279474163949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54118454218594981057748789 5073605082993279474163949)
          ·
            refine ⟨1902601906122479802811481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5073605082993279474163949 1902601906122479802811481)
            ·
              refine ⟨1426951429591859852108611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902601906122479802811481 1426951429591859852108611)
              ·
                refine ⟨2140427144387789778162917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1426951429591859852108611 2140427144387789778162917)
                ·
                  refine ⟨401330089572710583405547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140427144387789778162917 401330089572710583405547)
                  ·
                    rfl

theorem cell21_1758572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1758572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758572 prefixEnd_1758572 := by exact prefixLift 1758572
  have htrace : WordTrace (prefixWord ++ tailWord_1758572) baseStart_1758572 baseEnd_1758572 := by
    simpa [prefixWord, tailWord_1758572, baseEnd_1758572] using wordTrace_append hprefix tailTrace_1758572
  have hstable : (prefixWord ++ tailWord_1758572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758572).length < 2 ^ (prefixWord ++ tailWord_1758572).sum := by decide
  have hdescent : baseEnd_1758572 < baseStart_1758572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758597 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 8]
def baseStart_1758597 : Nat := 118140960795 + 1758597 * 2 ^ 59
def prefixEnd_1758597 : Nat := 4983230072969 + 3 ^ 40 * 1758597 * 2
def baseEnd_1758597 : Nat := 401335794913316095488829

theorem tailTrace_1758597 : CollatzResearch.WordTrace tailWord_1758597 prefixEnd_1758597 401335794913316095488829 := by
  unfold tailWord_1758597
  simp only [CollatzResearch.WordTrace]
  refine ⟨64141302009910888301066045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42760868006607258867377363 64141302009910888301066045)
  ·
    refine ⟨24052988253716583112899767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64141302009910888301066045 24052988253716583112899767)
    ·
      refine ⟨36079482380574874669349651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24052988253716583112899767 36079482380574874669349651)
      ·
        refine ⟨54119223570862312004024477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36079482380574874669349651 54119223570862312004024477)
        ·
          refine ⟨20294708839073367001509179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54119223570862312004024477 20294708839073367001509179)
          ·
            refine ⟨30442063258610050502263769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20294708839073367001509179 30442063258610050502263769)
            ·
              refine ⟨22831547443957537876697827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30442063258610050502263769 22831547443957537876697827)
              ·
                refine ⟨34247321165936306815046741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22831547443957537876697827 34247321165936306815046741)
                ·
                  refine ⟨401335794913316095488829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34247321165936306815046741 401335794913316095488829)
                  ·
                    rfl

theorem cell21_1758597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_1758597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758597 prefixEnd_1758597 := by exact prefixLift 1758597
  have htrace : WordTrace (prefixWord ++ tailWord_1758597) baseStart_1758597 baseEnd_1758597 := by
    simpa [prefixWord, tailWord_1758597, baseEnd_1758597] using wordTrace_append hprefix tailTrace_1758597
  have hstable : (prefixWord ++ tailWord_1758597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758597).length < 2 ^ (prefixWord ++ tailWord_1758597).sum := by decide
  have hdescent : baseEnd_1758597 < baseStart_1758597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758617 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 3]
def baseStart_1758617 : Nat := 118140960795 + 1758617 * 2 ^ 59
def prefixEnd_1758617 : Nat := 4983230072969 + 3 ^ 40 * 1758617 * 2
def baseEnd_1758617 : Nat := 401340359185800505155455

theorem tailTrace_1758617 : CollatzResearch.WordTrace tailWord_1758617 prefixEnd_1758617 401340359185800505155455 := by
  unfold tailWord_1758617
  simp only [CollatzResearch.WordTrace]
  refine ⟨64142031469838431716794105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42761354313225621144529403 64142031469838431716794105)
  ·
    refine ⟨48106523602378823787595579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64142031469838431716794105 48106523602378823787595579)
    ·
      refine ⟨72159785403568235681393369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48106523602378823787595579 72159785403568235681393369)
      ·
        refine ⟨54119839052676176761045027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72159785403568235681393369 54119839052676176761045027)
        ·
          refine ⟨81179758579014265141567541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54119839052676176761045027 81179758579014265141567541)
          ·
            refine ⟨7610602366782587357021957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81179758579014265141567541 7610602366782587357021957)
            ·
              refine ⟨1426987943771735129441617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7610602366782587357021957 1426987943771735129441617)
              ·
                refine ⟨1070240957828801347081213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1426987943771735129441617 1070240957828801347081213)
                ·
                  refine ⟨401340359185800505155455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070240957828801347081213 401340359185800505155455)
                  ·
                    rfl

theorem cell21_1758617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_1758617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758617 prefixEnd_1758617 := by exact prefixLift 1758617
  have htrace : WordTrace (prefixWord ++ tailWord_1758617) baseStart_1758617 baseEnd_1758617 := by
    simpa [prefixWord, tailWord_1758617, baseEnd_1758617] using wordTrace_append hprefix tailTrace_1758617
  have hstable : (prefixWord ++ tailWord_1758617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758617).length < 2 ^ (prefixWord ++ tailWord_1758617).sum := by decide
  have hdescent : baseEnd_1758617 < baseStart_1758617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758704 : List Nat := [2, 1, 1, 1, 3, 5, 1, 7]
def baseStart_1758704 : Nat := 118140960795 + 1758704 * 2 ^ 59
def prefixEnd_1758704 : Nat := 4983230072969 + 3 ^ 40 * 1758704 * 2
def baseEnd_1758704 : Nat := 133786737923702562401759

theorem tailTrace_1758704 : CollatzResearch.WordTrace tailWord_1758704 prefixEnd_1758704 133786737923702562401759 := by
  unfold tailWord_1758704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32072602310261622787605583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42763469747015497050140777 32072602310261622787605583)
  ·
    refine ⟨48108903465392434181408375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32072602310261622787605583 48108903465392434181408375)
    ·
      refine ⟨72163355198088651272112563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48108903465392434181408375 72163355198088651272112563)
      ·
        refine ⟨108245032797132976908168845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72163355198088651272112563 108245032797132976908168845)
        ·
          refine ⟨40591887298924866340563317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108245032797132976908168845 40591887298924866340563317)
          ·
            refine ⟨3805489434274206219427811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40591887298924866340563317 3805489434274206219427811)
            ·
              refine ⟨5708234151411309329141717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805489434274206219427811 5708234151411309329141717)
              ·
                refine ⟨133786737923702562401759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5708234151411309329141717 133786737923702562401759)
                ·
                  rfl

theorem cell21_1758704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_1758704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758704 prefixEnd_1758704 := by exact prefixLift 1758704
  have htrace : WordTrace (prefixWord ++ tailWord_1758704) baseStart_1758704 baseEnd_1758704 := by
    simpa [prefixWord, tailWord_1758704, baseEnd_1758704] using wordTrace_append hprefix tailTrace_1758704
  have hstable : (prefixWord ++ tailWord_1758704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758704).length < 2 ^ (prefixWord ++ tailWord_1758704).sum := by decide
  have hdescent : baseEnd_1758704 < baseStart_1758704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758710 : List Nat := [5, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1758710 : Nat := 118140960795 + 1758710 * 2 ^ 59
def prefixEnd_1758710 : Nat := 4983230072969 + 3 ^ 40 * 1758710 * 2
def baseEnd_1758710 : Nat := 401361583052853010105265

theorem tailTrace_1758710 : CollatzResearch.WordTrace tailWord_1758710 prefixEnd_1758710 401361583052853010105265 := by
  unfold tailWord_1758710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009088966156344287495599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42763615639001005733286389 4009088966156344287495599)
  ·
    refine ⟨6013633449234516431243399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009088966156344287495599 6013633449234516431243399)
    ·
      refine ⟨9020450173851774646865099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6013633449234516431243399 9020450173851774646865099)
      ·
        refine ⟨13530675260777661970297649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020450173851774646865099 13530675260777661970297649)
        ·
          refine ⟨10148006445583246477723237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13530675260777661970297649 10148006445583246477723237)
          ·
            refine ⟨1902751208546858714573107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10148006445583246477723237 1902751208546858714573107)
            ·
              refine ⟨2854126812820288071859661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902751208546858714573107 2854126812820288071859661)
              ·
                refine ⟨1070297554807608026947373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2854126812820288071859661 1070297554807608026947373)
                ·
                  refine ⟨401361583052853010105265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070297554807608026947373 401361583052853010105265)
                  ·
                    rfl

theorem cell21_1758710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1758710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758710 prefixEnd_1758710 := by exact prefixLift 1758710
  have htrace : WordTrace (prefixWord ++ tailWord_1758710) baseStart_1758710 baseEnd_1758710 := by
    simpa [prefixWord, tailWord_1758710, baseEnd_1758710] using wordTrace_append hprefix tailTrace_1758710
  have hstable : (prefixWord ++ tailWord_1758710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758710).length < 2 ^ (prefixWord ++ tailWord_1758710).sum := by decide
  have hdescent : baseEnd_1758710 < baseStart_1758710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758721 : List Nat := [1, 2, 4, 1, 4, 2, 7]
def baseStart_1758721 : Nat := 118140960795 + 1758721 * 2 ^ 59
def prefixEnd_1758721 : Nat := 4983230072969 + 3 ^ 40 * 1758721 * 2
def baseEnd_1758721 : Nat := 44596010378079937269101

theorem tailTrace_1758721 : CollatzResearch.WordTrace tailWord_1758721 prefixEnd_1758721 44596010378079937269101 := by
  unfold tailWord_1758721
  simp only [CollatzResearch.WordTrace]
  refine ⟨64145824661461657478580017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42763883107641104985720011 64145824661461657478580017)
  ·
    refine ⟨48109368496096243108935013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64145824661461657478580017 48109368496096243108935013)
    ·
      refine ⟨9020506593018045582925315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48109368496096243108935013 9020506593018045582925315)
      ·
        refine ⟨13530759889527068374387973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9020506593018045582925315 13530759889527068374387973)
        ·
          refine ⟨2537017479286325320197745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13530759889527068374387973 2537017479286325320197745)
          ·
            refine ⟨1902763109464743990148309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537017479286325320197745 1902763109464743990148309)
            ·
              refine ⟨44596010378079937269101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1902763109464743990148309 44596010378079937269101)
              ·
                rfl

theorem cell21_1758721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 7].length) (baseStart_1758721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758721 prefixEnd_1758721 := by exact prefixLift 1758721
  have htrace : WordTrace (prefixWord ++ tailWord_1758721) baseStart_1758721 baseEnd_1758721 := by
    simpa [prefixWord, tailWord_1758721, baseEnd_1758721] using wordTrace_append hprefix tailTrace_1758721
  have hstable : (prefixWord ++ tailWord_1758721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758721).length < 2 ^ (prefixWord ++ tailWord_1758721).sum := by decide
  have hdescent : baseEnd_1758721 < baseStart_1758721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758780 : List Nat := [2, 2, 2, 2, 4, 9]
def baseStart_1758780 : Nat := 118140960795 + 1758780 * 2 ^ 59
def prefixEnd_1758780 : Nat := 4983230072969 + 3 ^ 40 * 1758780 * 2
def baseEnd_1758780 : Nat := 14865835481724016442165

theorem tailTrace_1758780 : CollatzResearch.WordTrace tailWord_1758780 prefixEnd_1758780 14865835481724016442165 := by
  unfold tailWord_1758780
  simp only [CollatzResearch.WordTrace]
  refine ⟨32073988284123955277488897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42765317712165273703318529 32073988284123955277488897)
  ·
    refine ⟨24055491213092966458116673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32073988284123955277488897 24055491213092966458116673)
    ·
      refine ⟨18041618409819724843587505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24055491213092966458116673 18041618409819724843587505)
      ·
        refine ⟨13531213807364793632690629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18041618409819724843587505 13531213807364793632690629)
        ·
          refine ⟨2537102588880898806129493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13531213807364793632690629 2537102588880898806129493)
          ·
            refine ⟨14865835481724016442165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2537102588880898806129493 14865835481724016442165)
            ·
              rfl

theorem cell21_1758780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 9].length) (baseStart_1758780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758780 prefixEnd_1758780 := by exact prefixLift 1758780
  have htrace : WordTrace (prefixWord ++ tailWord_1758780) baseStart_1758780 baseEnd_1758780 := by
    simpa [prefixWord, tailWord_1758780, baseEnd_1758780] using wordTrace_append hprefix tailTrace_1758780
  have hstable : (prefixWord ++ tailWord_1758780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758780).length < 2 ^ (prefixWord ++ tailWord_1758780).sum := by decide
  have hdescent : baseEnd_1758780 < baseStart_1758780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1758879 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 3]
def baseStart_1758879 : Nat := 118140960795 + 1758879 * 2 ^ 59
def prefixEnd_1758879 : Nat := 4983230072969 + 3 ^ 40 * 1758879 * 2
def baseEnd_1758879 : Nat := 401400151155346271788253

theorem tailTrace_1758879 : CollatzResearch.WordTrace tailWord_1758879 prefixEnd_1758879 401400151155346271788253 := by
  unfold tailWord_1758879
  simp only [CollatzResearch.WordTrace]
  refine ⟨64151587394889250462831691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42767724929926166975221127 64151587394889250462831691)
  ·
    refine ⟨96227381092333875694247537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64151587394889250462831691 96227381092333875694247537)
    ·
      refine ⟨72170535819250406770685653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96227381092333875694247537 72170535819250406770685653)
      ·
        refine ⟨1691496933263681408687945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 72170535819250406770685653 1691496933263681408687945)
        ·
          refine ⟨1268622699947761056515959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1691496933263681408687945 1268622699947761056515959)
          ·
            refine ⟨1902934049921641584773939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268622699947761056515959 1902934049921641584773939)
            ·
              refine ⟨2854401074882462377160909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902934049921641584773939 2854401074882462377160909)
              ·
                refine ⟨1070400403080923391435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2854401074882462377160909 1070400403080923391435341)
                ·
                  refine ⟨401400151155346271788253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070400403080923391435341 401400151155346271788253)
                  ·
                    rfl

theorem cell21_1758879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 3].length) (baseStart_1758879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1758879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1758879 prefixEnd_1758879 := by exact prefixLift 1758879
  have htrace : WordTrace (prefixWord ++ tailWord_1758879) baseStart_1758879 baseEnd_1758879 := by
    simpa [prefixWord, tailWord_1758879, baseEnd_1758879] using wordTrace_append hprefix tailTrace_1758879
  have hstable : (prefixWord ++ tailWord_1758879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1758879).length < 2 ^ (prefixWord ++ tailWord_1758879).sum := by decide
  have hdescent : baseEnd_1758879 < baseStart_1758879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1758879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759028 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1759028 : Nat := 118140960795 + 1759028 * 2 ^ 59
def prefixEnd_1759028 : Nat := 4983230072969 + 3 ^ 40 * 1759028 * 2
def baseEnd_1759028 : Nat := 401434154985355123804615

theorem tailTrace_1759028 : CollatzResearch.WordTrace tailWord_1759028 prefixEnd_1759028 401434154985355123804615 := by
  unfold tailWord_1759028
  simp only [CollatzResearch.WordTrace]
  refine ⟨32078510935674724455002869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42771347914232965940003825 32078510935674724455002869)
  ·
    refine ⟨3007360400219505417656519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32078510935674724455002869 3007360400219505417656519)
    ·
      refine ⟨4511040600329258126484779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3007360400219505417656519 4511040600329258126484779)
      ·
        refine ⟨6766560900493887189727169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4511040600329258126484779 6766560900493887189727169)
        ·
          refine ⟨5074920675370415392295377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6766560900493887189727169 5074920675370415392295377)
          ·
            refine ⟨3806190506527811544221533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5074920675370415392295377 3806190506527811544221533)
            ·
              refine ⟨1427321439947929329083075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3806190506527811544221533 1427321439947929329083075)
              ·
                refine ⟨2140982159921893993624613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427321439947929329083075 2140982159921893993624613)
                ·
                  refine ⟨401434154985355123804615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140982159921893993624613 401434154985355123804615)
                  ·
                    rfl

theorem cell21_1759028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1759028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759028 prefixEnd_1759028 := by exact prefixLift 1759028
  have htrace : WordTrace (prefixWord ++ tailWord_1759028) baseStart_1759028 baseEnd_1759028 := by
    simpa [prefixWord, tailWord_1759028, baseEnd_1759028] using wordTrace_append hprefix tailTrace_1759028
  have hstable : (prefixWord ++ tailWord_1759028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759028).length < 2 ^ (prefixWord ++ tailWord_1759028).sum := by decide
  have hdescent : baseEnd_1759028 < baseStart_1759028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759084 : List Nat := [2, 2, 1, 1, 4, 3, 2, 6]
def baseStart_1759084 : Nat := 118140960795 + 1759084 * 2 ^ 59
def prefixEnd_1759084 : Nat := 4983230072969 + 3 ^ 40 * 1759084 * 2
def baseEnd_1759084 : Nat := 133815644982770490290389

theorem tailTrace_1759084 : CollatzResearch.WordTrace tailWord_1759084 prefixEnd_1759084 133815644982770490290389 := by
  unfold tailWord_1759084
  simp only [CollatzResearch.WordTrace]
  refine ⟨32079532179573285237022153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42772709572764380316029537 32079532179573285237022153)
  ·
    refine ⟨24059649134679963927766615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32079532179573285237022153 24059649134679963927766615)
    ·
      refine ⟨36089473702019945891649923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24059649134679963927766615 36089473702019945891649923)
      ·
        refine ⟨54134210553029918837474885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36089473702019945891649923 54134210553029918837474885)
        ·
          refine ⟨10150164478693109782026541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54134210553029918837474885 10150164478693109782026541)
          ·
            refine ⟨3806311679509916168259953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10150164478693109782026541 3806311679509916168259953)
            ·
              refine ⟨2854733759632437126194965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806311679509916168259953 2854733759632437126194965)
              ·
                refine ⟨133815644982770490290389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2854733759632437126194965 133815644982770490290389)
                ·
                  rfl

theorem cell21_1759084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_1759084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759084 prefixEnd_1759084 := by exact prefixLift 1759084
  have htrace : WordTrace (prefixWord ++ tailWord_1759084) baseStart_1759084 baseEnd_1759084 := by
    simpa [prefixWord, tailWord_1759084, baseEnd_1759084] using wordTrace_append hprefix tailTrace_1759084
  have hstable : (prefixWord ++ tailWord_1759084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759084).length < 2 ^ (prefixWord ++ tailWord_1759084).sum := by decide
  have hdescent : baseEnd_1759084 < baseStart_1759084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759098 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1759098 : Nat := 118140960795 + 1759098 * 2 ^ 59
def prefixEnd_1759098 : Nat := 4983230072969 + 3 ^ 40 * 1759098 * 2
def baseEnd_1759098 : Nat := 401450129939050557637805

theorem tailTrace_1759098 : CollatzResearch.WordTrace tailWord_1759098 prefixEnd_1759098 401450129939050557637805 := by
  unfold tailWord_1759098
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039893745273962716263487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42773049987397233910035965 16039893745273962716263487)
  ·
    refine ⟨24059840617910944074395231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16039893745273962716263487 24059840617910944074395231)
    ·
      refine ⟨36089760926866416111592847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24059840617910944074395231 36089760926866416111592847)
      ·
        refine ⟨54134641390299624167389271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36089760926866416111592847 54134641390299624167389271)
        ·
          refine ⟨81201962085449436251083907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54134641390299624167389271 81201962085449436251083907)
          ·
            refine ⟨121802943128174154376625861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81201962085449436251083907 121802943128174154376625861)
            ·
              refine ⟨22838051836532653945617349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121802943128174154376625861 22838051836532653945617349)
              ·
                refine ⟨4282134719349872614803253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22838051836532653945617349 4282134719349872614803253)
                ·
                  refine ⟨401450129939050557637805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4282134719349872614803253 401450129939050557637805)
                  ·
                    rfl

theorem cell21_1759098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1759098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759098 prefixEnd_1759098 := by exact prefixLift 1759098
  have htrace : WordTrace (prefixWord ++ tailWord_1759098) baseStart_1759098 baseEnd_1759098 := by
    simpa [prefixWord, tailWord_1759098, baseEnd_1759098] using wordTrace_append hprefix tailTrace_1759098
  have hstable : (prefixWord ++ tailWord_1759098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759098).length < 2 ^ (prefixWord ++ tailWord_1759098).sum := by decide
  have hdescent : baseEnd_1759098 < baseStart_1759098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759115 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 3]
def baseStart_1759115 : Nat := 118140960795 + 1759115 * 2 ^ 59
def prefixEnd_1759115 : Nat := 4983230072969 + 3 ^ 40 * 1759115 * 2
def baseEnd_1759115 : Nat := 401454009570662305854437

theorem tailTrace_1759115 : CollatzResearch.WordTrace tailWord_1759115 prefixEnd_1759115 401454009570662305854437 := by
  unfold tailWord_1759115
  simp only [CollatzResearch.WordTrace]
  refine ⟨64160195022034262768422799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42773463348022841845615199 64160195022034262768422799)
  ·
    refine ⟨96240292533051394152634199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64160195022034262768422799 96240292533051394152634199)
    ·
      refine ⟨144360438799577091228951299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96240292533051394152634199 144360438799577091228951299)
      ·
        refine ⟨216540658199365636843426949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144360438799577091228951299 216540658199365636843426949)
        ·
          refine ⟨40601373412381056908142553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216540658199365636843426949 40601373412381056908142553)
          ·
            refine ⟨30451030059285792681106915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40601373412381056908142553 30451030059285792681106915)
            ·
              refine ⟨45676545088928689021660373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30451030059285792681106915 45676545088928689021660373)
              ·
                refine ⟨1070544025521766148945165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45676545088928689021660373 1070544025521766148945165)
                ·
                  refine ⟨401454009570662305854437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070544025521766148945165 401454009570662305854437)
                  ·
                    rfl

theorem cell21_1759115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 3].length) (baseStart_1759115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759115 prefixEnd_1759115 := by exact prefixLift 1759115
  have htrace : WordTrace (prefixWord ++ tailWord_1759115) baseStart_1759115 baseEnd_1759115 := by
    simpa [prefixWord, tailWord_1759115, baseEnd_1759115] using wordTrace_append hprefix tailTrace_1759115
  have hstable : (prefixWord ++ tailWord_1759115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759115).length < 2 ^ (prefixWord ++ tailWord_1759115).sum := by decide
  have hdescent : baseEnd_1759115 < baseStart_1759115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759129 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 4]
def baseStart_1759129 : Nat := 118140960795 + 1759129 * 2 ^ 59
def prefixEnd_1759129 : Nat := 4983230072969 + 3 ^ 40 * 1759129 * 2
def baseEnd_1759129 : Nat := 401457204561401392621075

theorem tailTrace_1759129 : CollatzResearch.WordTrace tailWord_1759129 prefixEnd_1759129 401457204561401392621075 := by
  unfold tailWord_1759129
  simp only [CollatzResearch.WordTrace]
  refine ⟨64160705643983543159432441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42773803762655695439621627 64160705643983543159432441)
  ·
    refine ⟨48120529232987657369574331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64160705643983543159432441 48120529232987657369574331)
    ·
      refine ⟨72180793849481486054361497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48120529232987657369574331 72180793849481486054361497)
      ·
        refine ⟨54135595387111114540771123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72180793849481486054361497 54135595387111114540771123)
        ·
          refine ⟨81203393080666671811156685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54135595387111114540771123 81203393080666671811156685)
          ·
            refine ⟨30451272405250001929183757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81203393080666671811156685 30451272405250001929183757)
            ·
              refine ⟨11419227151968750723443909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30451272405250001929183757 11419227151968750723443909)
              ·
                refine ⟨2141105090994140760645733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11419227151968750723443909 2141105090994140760645733)
                ·
                  refine ⟨401457204561401392621075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141105090994140760645733 401457204561401392621075)
                  ·
                    rfl

theorem cell21_1759129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_1759129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759129 prefixEnd_1759129 := by exact prefixLift 1759129
  have htrace : WordTrace (prefixWord ++ tailWord_1759129) baseStart_1759129 baseEnd_1759129 := by
    simpa [prefixWord, tailWord_1759129, baseEnd_1759129] using wordTrace_append hprefix tailTrace_1759129
  have hstable : (prefixWord ++ tailWord_1759129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759129).length < 2 ^ (prefixWord ++ tailWord_1759129).sum := by decide
  have hdescent : baseEnd_1759129 < baseStart_1759129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759160 : List Nat := [2, 1, 2, 1, 2, 3, 5, 5]
def baseStart_1759160 : Nat := 118140960795 + 1759160 * 2 ^ 59
def prefixEnd_1759160 : Nat := 4983230072969 + 3 ^ 40 * 1759160 * 2
def baseEnd_1759160 : Nat := 133821426394584075868115

theorem tailTrace_1759160 : CollatzResearch.WordTrace tailWord_1759160 prefixEnd_1759160 133821426394584075868115 := by
  unfold tailWord_1759160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32080918153435617726905467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42774557537914156969207289 32080918153435617726905467)
  ·
    refine ⟨48121377230153426590358201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32080918153435617726905467 48121377230153426590358201)
    ·
      refine ⟨36091032922615069942768651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48121377230153426590358201 36091032922615069942768651)
      ·
        refine ⟨54136549383922604914152977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091032922615069942768651 54136549383922604914152977)
        ·
          refine ⟨40602412037941953685614733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54136549383922604914152977 40602412037941953685614733)
          ·
            refine ⟨15225904514228232632105525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40602412037941953685614733 15225904514228232632105525)
            ·
              refine ⟨1427428548208896809259893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15225904514228232632105525 1427428548208896809259893)
              ·
                refine ⟨133821426394584075868115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427428548208896809259893 133821426394584075868115)
                ·
                  rfl

theorem cell21_1759160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_1759160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759160 prefixEnd_1759160 := by exact prefixLift 1759160
  have htrace : WordTrace (prefixWord ++ tailWord_1759160) baseStart_1759160 baseEnd_1759160 := by
    simpa [prefixWord, tailWord_1759160, baseEnd_1759160] using wordTrace_append hprefix tailTrace_1759160
  have hstable : (prefixWord ++ tailWord_1759160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759160).length < 2 ^ (prefixWord ++ tailWord_1759160).sum := by decide
  have hdescent : baseEnd_1759160 < baseStart_1759160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759191 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 3]
def baseStart_1759191 : Nat := 118140960795 + 1759191 * 2 ^ 59
def prefixEnd_1759191 : Nat := 4983230072969 + 3 ^ 40 * 1759191 * 2
def baseEnd_1759191 : Nat := 401471353806103062587615

theorem tailTrace_1759191 : CollatzResearch.WordTrace tailWord_1759191 prefixEnd_1759191 401471353806103062587615 := by
  unfold tailWord_1759191
  simp only [CollatzResearch.WordTrace]
  refine ⟨64162966969758927748189427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42775311313172618498792951 64162966969758927748189427)
  ·
    refine ⟨96244450454638391622284141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64162966969758927748189427 96244450454638391622284141)
    ·
      refine ⟨36091668920489396858356553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96244450454638391622284141 36091668920489396858356553)
      ·
        refine ⟨27068751690367047643767415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36091668920489396858356553 27068751690367047643767415)
        ·
          refine ⟨40603127535550571465651123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27068751690367047643767415 40603127535550571465651123)
          ·
            refine ⟨60904691303325857198476685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40603127535550571465651123 60904691303325857198476685)
            ·
              refine ⟨22839259238747196449428757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60904691303325857198476685 22839259238747196449428757)
              ·
                refine ⟨1070590276816274833566973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22839259238747196449428757 1070590276816274833566973)
                ·
                  refine ⟨401471353806103062587615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070590276816274833566973 401471353806103062587615)
                  ·
                    rfl

theorem cell21_1759191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 3].length) (baseStart_1759191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759191 prefixEnd_1759191 := by exact prefixLift 1759191
  have htrace : WordTrace (prefixWord ++ tailWord_1759191) baseStart_1759191 baseEnd_1759191 := by
    simpa [prefixWord, tailWord_1759191, baseEnd_1759191] using wordTrace_append hprefix tailTrace_1759191
  have hstable : (prefixWord ++ tailWord_1759191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759191).length < 2 ^ (prefixWord ++ tailWord_1759191).sum := by decide
  have hdescent : baseEnd_1759191 < baseStart_1759191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759343 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 3]
def baseStart_1759343 : Nat := 118140960795 + 1759343 * 2 ^ 59
def prefixEnd_1759343 : Nat := 4983230072969 + 3 ^ 40 * 1759343 * 2
def baseEnd_1759343 : Nat := 401506042276984576053971

theorem tailTrace_1759343 : CollatzResearch.WordTrace tailWord_1759343 prefixEnd_1759343 401506042276984576053971 := by
  unfold tailWord_1759343
  simp only [CollatzResearch.WordTrace]
  refine ⟨64168510865208257707722683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42779007243472171805148455 64168510865208257707722683)
  ·
    refine ⟨96252766297812386561584025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64168510865208257707722683 96252766297812386561584025)
    ·
      refine ⟨72189574723359289921188019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96252766297812386561584025 72189574723359289921188019)
      ·
        refine ⟨108284362085038934881782029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72189574723359289921188019 108284362085038934881782029)
        ·
          refine ⟨40606635781889600580668261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108284362085038934881782029 40606635781889600580668261)
          ·
            refine ⟨7613744209104300108875299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40606635781889600580668261 7613744209104300108875299)
            ·
              refine ⟨11420616313656450163312949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613744209104300108875299 11420616313656450163312949)
              ·
                refine ⟨1070682779405292202810589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11420616313656450163312949 1070682779405292202810589)
                ·
                  refine ⟨401506042276984576053971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070682779405292202810589 401506042276984576053971)
                  ·
                    rfl

theorem cell21_1759343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 3].length) (baseStart_1759343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759343 prefixEnd_1759343 := by exact prefixLift 1759343
  have htrace : WordTrace (prefixWord ++ tailWord_1759343) baseStart_1759343 baseEnd_1759343 := by
    simpa [prefixWord, tailWord_1759343, baseEnd_1759343] using wordTrace_append hprefix tailTrace_1759343
  have hstable : (prefixWord ++ tailWord_1759343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759343).length < 2 ^ (prefixWord ++ tailWord_1759343).sum := by decide
  have hdescent : baseEnd_1759343 < baseStart_1759343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759357 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 6]
def baseStart_1759357 : Nat := 118140960795 + 1759357 * 2 ^ 59
def prefixEnd_1759357 : Nat := 4983230072969 + 3 ^ 40 * 1759357 * 2
def baseEnd_1759357 : Nat := 401509237267723662820609

theorem tailTrace_1759357 : CollatzResearch.WordTrace tailWord_1759357 prefixEnd_1759357 401509237267723662820609 := by
  unfold tailWord_1759357
  simp only [CollatzResearch.WordTrace]
  refine ⟨64169021487157538098732325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42779347658105025399154883 64169021487157538098732325)
  ·
    refine ⟨12031691528842038393512311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64169021487157538098732325 12031691528842038393512311)
    ·
      refine ⟨18047537293263057590268467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031691528842038393512311 18047537293263057590268467)
      ·
        refine ⟨27071305939894586385402701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18047537293263057590268467 27071305939894586385402701)
        ·
          refine ⟨10151739727460469894526013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27071305939894586385402701 10151739727460469894526013)
          ·
            refine ⟨3806902397797676210447255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10151739727460469894526013 3806902397797676210447255)
            ·
              refine ⟨5710353596696514315670883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806902397797676210447255 5710353596696514315670883)
              ·
                refine ⟨8565530395044771473506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710353596696514315670883 8565530395044771473506325)
                ·
                  refine ⟨401509237267723662820609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8565530395044771473506325 401509237267723662820609)
                  ·
                    rfl

theorem cell21_1759357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_1759357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759357 prefixEnd_1759357 := by exact prefixLift 1759357
  have htrace : WordTrace (prefixWord ++ tailWord_1759357) baseStart_1759357 baseEnd_1759357 := by
    simpa [prefixWord, tailWord_1759357, baseEnd_1759357] using wordTrace_append hprefix tailTrace_1759357
  have hstable : (prefixWord ++ tailWord_1759357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759357).length < 2 ^ (prefixWord ++ tailWord_1759357).sum := by decide
  have hdescent : baseEnd_1759357 < baseStart_1759357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759416 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_1759416 : Nat := 118140960795 + 1759416 * 2 ^ 59
def prefixEnd_1759416 : Nat := 4983230072969 + 3 ^ 40 * 1759416 * 2
def baseEnd_1759416 : Nat := 401522701871552671337155

theorem tailTrace_1759416 : CollatzResearch.WordTrace tailWord_1759416 prefixEnd_1759416 401522701871552671337155 := by
  unfold tailWord_1759416
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085586696971895587565051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42780782262629194116753401 32085586696971895587565051)
  ·
    refine ⟨48128380045457843381347577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32085586696971895587565051 48128380045457843381347577)
    ·
      refine ⟨36096285034093382536010683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48128380045457843381347577 36096285034093382536010683)
      ·
        refine ⟨54144427551140073804016025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36096285034093382536010683 54144427551140073804016025)
        ·
          refine ⟨40608320663355055353012019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54144427551140073804016025 40608320663355055353012019)
          ·
            refine ⟨60912480995032583029518029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40608320663355055353012019 60912480995032583029518029)
            ·
              refine ⟨22842180373137218636069261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60912480995032583029518029 22842180373137218636069261)
              ·
                refine ⟨8565817639926456988525973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22842180373137218636069261 8565817639926456988525973)
                ·
                  refine ⟨401522701871552671337155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8565817639926456988525973 401522701871552671337155)
                  ·
                    rfl

theorem cell21_1759416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_1759416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759416 prefixEnd_1759416 := by exact prefixLift 1759416
  have htrace : WordTrace (prefixWord ++ tailWord_1759416) baseStart_1759416 baseEnd_1759416 := by
    simpa [prefixWord, tailWord_1759416, baseEnd_1759416] using wordTrace_append hprefix tailTrace_1759416
  have hstable : (prefixWord ++ tailWord_1759416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759416).length < 2 ^ (prefixWord ++ tailWord_1759416).sum := by decide
  have hdescent : baseEnd_1759416 < baseStart_1759416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759425 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 4]
def baseStart_1759425 : Nat := 118140960795 + 1759425 * 2 ^ 59
def prefixEnd_1759425 : Nat := 4983230072969 + 3 ^ 40 * 1759425 * 2
def baseEnd_1759425 : Nat := 401524755794170655687137

theorem tailTrace_1759425 : CollatzResearch.WordTrace tailWord_1759425 prefixEnd_1759425 401524755794170655687137 := by
  unfold tailWord_1759425
  simp only [CollatzResearch.WordTrace]
  refine ⟨64171501650911185712207729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42781001100607457141471819 64171501650911185712207729)
  ·
    refine ⟨48128626238183389284155797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64171501650911185712207729 48128626238183389284155797)
    ·
      refine ⟨2256029354914846372694803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48128626238183389284155797 2256029354914846372694803)
      ·
        refine ⟨3384044032372269559042205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256029354914846372694803 3384044032372269559042205)
        ·
          refine ⟨1269016512139601084640827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3384044032372269559042205 1269016512139601084640827)
          ·
            refine ⟨1903524768209401626961241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269016512139601084640827 1903524768209401626961241)
            ·
              refine ⟨1427643576157051220220931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903524768209401626961241 1427643576157051220220931)
              ·
                refine ⟨2141465364235576830331397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427643576157051220220931 2141465364235576830331397)
                ·
                  refine ⟨401524755794170655687137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141465364235576830331397 401524755794170655687137)
                  ·
                    rfl

theorem cell21_1759425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_1759425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759425 prefixEnd_1759425 := by exact prefixLift 1759425
  have htrace : WordTrace (prefixWord ++ tailWord_1759425) baseStart_1759425 baseEnd_1759425 := by
    simpa [prefixWord, tailWord_1759425, baseEnd_1759425] using wordTrace_append hprefix tailTrace_1759425
  have hstable : (prefixWord ++ tailWord_1759425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759425).length < 2 ^ (prefixWord ++ tailWord_1759425).sum := by decide
  have hdescent : baseEnd_1759425 < baseStart_1759425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759568 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_1759568 : Nat := 118140960795 + 1759568 * 2 ^ 59
def prefixEnd_1759568 : Nat := 4983230072969 + 3 ^ 40 * 1759568 * 2
def baseEnd_1759568 : Nat := 401557390342434184803511

theorem tailTrace_1759568 : CollatzResearch.WordTrace tailWord_1759568 prefixEnd_1759568 401557390342434184803511 := by
  unfold tailWord_1759568
  simp only [CollatzResearch.WordTrace]
  refine ⟨32088358644696560567331679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42784478192928747423108905 32088358644696560567331679)
  ·
    refine ⟨48132537967044840850997519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32088358644696560567331679 48132537967044840850997519)
    ·
      refine ⟨72198806950567261276496279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48132537967044840850997519 72198806950567261276496279)
      ·
        refine ⟨108298210425850891914744419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72198806950567261276496279 108298210425850891914744419)
        ·
          refine ⟨162447315638776337872116629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108298210425850891914744419 162447315638776337872116629)
          ·
            refine ⟨7614717920567640837755467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162447315638776337872116629 7614717920567640837755467)
            ·
              refine ⟨11422076880851461256633201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614717920567640837755467 11422076880851461256633201)
              ·
                refine ⟨8566557660638595942474901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11422076880851461256633201 8566557660638595942474901)
                ·
                  refine ⟨401557390342434184803511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8566557660638595942474901 401557390342434184803511)
                  ·
                    rfl

theorem cell21_1759568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_1759568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759568 prefixEnd_1759568 := by exact prefixLift 1759568
  have htrace : WordTrace (prefixWord ++ tailWord_1759568) baseStart_1759568 baseEnd_1759568 := by
    simpa [prefixWord, tailWord_1759568, baseEnd_1759568] using wordTrace_append hprefix tailTrace_1759568
  have hstable : (prefixWord ++ tailWord_1759568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759568).length < 2 ^ (prefixWord ++ tailWord_1759568).sum := by decide
  have hdescent : baseEnd_1759568 < baseStart_1759568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759588 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_1759588 : Nat := 118140960795 + 1759588 * 2 ^ 59
def prefixEnd_1759588 : Nat := 4983230072969 + 3 ^ 40 * 1759588 * 2
def baseEnd_1759588 : Nat := 401561954614918594470137

theorem tailTrace_1759588 : CollatzResearch.WordTrace tailWord_1759588 prefixEnd_1759588 401561954614918594470137 := by
  unfold tailWord_1759588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32088723374660332275195709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42784964499547109700260945 32088723374660332275195709)
  ·
    refine ⟨12033271265497624603198391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32088723374660332275195709 12033271265497624603198391)
    ·
      refine ⟨18049906898246436904797587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033271265497624603198391 18049906898246436904797587)
      ·
        refine ⟨27074860347369655357196381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18049906898246436904797587 27074860347369655357196381)
        ·
          refine ⟨10153072630263620758948643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27074860347369655357196381 10153072630263620758948643)
          ·
            refine ⟨15229608945395431138422965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153072630263620758948643 15229608945395431138422965)
            ·
              refine ⟨1427775838630821669227153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15229608945395431138422965 1427775838630821669227153)
              ·
                refine ⟨1070831878973116251920365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427775838630821669227153 1070831878973116251920365)
                ·
                  refine ⟨401561954614918594470137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070831878973116251920365 401561954614918594470137)
                  ·
                    rfl

theorem cell21_1759588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_1759588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759588 prefixEnd_1759588 := by exact prefixLift 1759588
  have htrace : WordTrace (prefixWord ++ tailWord_1759588) baseStart_1759588 baseEnd_1759588 := by
    simpa [prefixWord, tailWord_1759588, baseEnd_1759588] using wordTrace_append hprefix tailTrace_1759588
  have hstable : (prefixWord ++ tailWord_1759588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759588).length < 2 ^ (prefixWord ++ tailWord_1759588).sum := by decide
  have hdescent : baseEnd_1759588 < baseStart_1759588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759602 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1759602 : Nat := 118140960795 + 1759602 * 2 ^ 59
def prefixEnd_1759602 : Nat := 4983230072969 + 3 ^ 40 * 1759602 * 2
def baseEnd_1759602 : Nat := 401565149605657681236775

theorem tailTrace_1759602 : CollatzResearch.WordTrace tailWord_1759602 prefixEnd_1759602 401565149605657681236775 := by
  unfold tailWord_1759602
  simp only [CollatzResearch.WordTrace]
  refine ⟨16044489342817486235350265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42785304914179963294267373 16044489342817486235350265)
  ·
    refine ⟨12033367007113114676512699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16044489342817486235350265 12033367007113114676512699)
    ·
      refine ⟨18050050510669672014769049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033367007113114676512699 18050050510669672014769049)
      ·
        refine ⟨13537537883002254011076787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18050050510669672014769049 13537537883002254011076787)
        ·
          refine ⟨20306306824503381016615181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13537537883002254011076787 20306306824503381016615181)
          ·
            refine ⟨7614865059188767881230693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20306306824503381016615181 7614865059188767881230693)
            ·
              refine ⟨1427787198597893977730755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7614865059188767881230693 1427787198597893977730755)
              ·
                refine ⟨2141680797896840966596133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427787198597893977730755 2141680797896840966596133)
                ·
                  refine ⟨401565149605657681236775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141680797896840966596133 401565149605657681236775)
                  ·
                    rfl

theorem cell21_1759602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1759602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759602 prefixEnd_1759602 := by exact prefixLift 1759602
  have htrace : WordTrace (prefixWord ++ tailWord_1759602) baseStart_1759602 baseEnd_1759602 := by
    simpa [prefixWord, tailWord_1759602, baseEnd_1759602] using wordTrace_append hprefix tailTrace_1759602
  have hstable : (prefixWord ++ tailWord_1759602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759602).length < 2 ^ (prefixWord ++ tailWord_1759602).sum := by decide
  have hdescent : baseEnd_1759602 < baseStart_1759602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759647 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 3]
def baseStart_1759647 : Nat := 118140960795 + 1759647 * 2 ^ 59
def prefixEnd_1759647 : Nat := 4983230072969 + 3 ^ 40 * 1759647 * 2
def baseEnd_1759647 : Nat := 401575419218747602986683

theorem tailTrace_1759647 : CollatzResearch.WordTrace tailWord_1759647 prefixEnd_1759647 401575419218747602986683 := by
  unfold tailWord_1759647
  simp only [CollatzResearch.WordTrace]
  refine ⟨64179598656106917626789195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42786399104071278417859463 64179598656106917626789195)
  ·
    refine ⟨96269397984160376440183793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64179598656106917626789195 96269397984160376440183793)
    ·
      refine ⟨72202048488120282330137845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96269397984160376440183793 72202048488120282330137845)
      ·
        refine ⟨6768942045761276468450423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72202048488120282330137845 6768942045761276468450423)
        ·
          refine ⟨10153413068641914702675635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768942045761276468450423 10153413068641914702675635)
          ·
            refine ⟨15230119602962872054013453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153413068641914702675635 15230119602962872054013453)
            ·
              refine ⟨5711294851111077020255045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15230119602962872054013453 5711294851111077020255045)
              ·
                refine ⟨1070867784583326941297821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5711294851111077020255045 1070867784583326941297821)
                ·
                  refine ⟨401575419218747602986683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070867784583326941297821 401575419218747602986683)
                  ·
                    rfl

theorem cell21_1759647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 3].length) (baseStart_1759647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759647 prefixEnd_1759647 := by exact prefixLift 1759647
  have htrace : WordTrace (prefixWord ++ tailWord_1759647) baseStart_1759647 baseEnd_1759647 := by
    simpa [prefixWord, tailWord_1759647, baseEnd_1759647] using wordTrace_append hprefix tailTrace_1759647
  have hstable : (prefixWord ++ tailWord_1759647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759647).length < 2 ^ (prefixWord ++ tailWord_1759647).sum := by decide
  have hdescent : baseEnd_1759647 < baseStart_1759647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759706 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1759706 : Nat := 118140960795 + 1759706 * 2 ^ 59
def prefixEnd_1759706 : Nat := 4983230072969 + 3 ^ 40 * 1759706 * 2
def baseEnd_1759706 : Nat := 401588883822576611503229

theorem tailTrace_1759706 : CollatzResearch.WordTrace tailWord_1759706 prefixEnd_1759706 401588883822576611503229 := by
  unfold tailWord_1759706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045437640723292675796743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42787833708595447135457981 16045437640723292675796743)
  ·
    refine ⟨24068156461084939013695115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16045437640723292675796743 24068156461084939013695115)
    ·
      refine ⟨36102234691627408520542673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24068156461084939013695115 36102234691627408520542673)
      ·
        refine ⟨27076676018720556390407005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36102234691627408520542673 27076676018720556390407005)
        ·
          refine ⟨10153753507020208646402627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27076676018720556390407005 10153753507020208646402627)
          ·
            refine ⟨15230630260530312969603941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153753507020208646402627 15230630260530312969603941)
            ·
              refine ⟨2855743173849433681800739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15230630260530312969603941 2855743173849433681800739)
              ·
                refine ⟨4283614760774150522701109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855743173849433681800739 4283614760774150522701109)
                ·
                  refine ⟨401588883822576611503229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283614760774150522701109 401588883822576611503229)
                  ·
                    rfl

theorem cell21_1759706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1759706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759706 prefixEnd_1759706 := by exact prefixLift 1759706
  have htrace : WordTrace (prefixWord ++ tailWord_1759706) baseStart_1759706 baseEnd_1759706 := by
    simpa [prefixWord, tailWord_1759706, baseEnd_1759706] using wordTrace_append hprefix tailTrace_1759706
  have hstable : (prefixWord ++ tailWord_1759706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759706).length < 2 ^ (prefixWord ++ tailWord_1759706).sum := by decide
  have hdescent : baseEnd_1759706 < baseStart_1759706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759757 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1759757 : Nat := 118140960795 + 1759757 * 2 ^ 59
def prefixEnd_1759757 : Nat := 4983230072969 + 3 ^ 40 * 1759757 * 2
def baseEnd_1759757 : Nat := 401600522717411856153125

theorem tailTrace_1759757 : CollatzResearch.WordTrace tailWord_1759757 prefixEnd_1759757 401600522717411856153125 := by
  unfold tailWord_1759757
  simp only [CollatzResearch.WordTrace]
  refine ⟨64183610685708406413293525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42789073790472270942195683 64183610685708406413293525)
  ·
    refine ⟨1504303375446290775311567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 64183610685708406413293525 1504303375446290775311567)
    ·
      refine ⟨2256455063169436162967351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504303375446290775311567 2256455063169436162967351)
      ·
        refine ⟨3384682594754154244451027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256455063169436162967351 3384682594754154244451027)
        ·
          refine ⟨5077023892131231366676541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3384682594754154244451027 5077023892131231366676541)
          ·
            refine ⟨1903883959549211762503703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5077023892131231366676541 1903883959549211762503703)
            ·
              refine ⟨2855825939323817643755555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903883959549211762503703 2855825939323817643755555)
              ·
                refine ⟨4283738908985726465633333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855825939323817643755555 4283738908985726465633333)
                ·
                  refine ⟨401600522717411856153125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283738908985726465633333 401600522717411856153125)
                  ·
                    rfl

theorem cell21_1759757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1759757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759757 prefixEnd_1759757 := by exact prefixLift 1759757
  have htrace : WordTrace (prefixWord ++ tailWord_1759757) baseStart_1759757 baseEnd_1759757 := by
    simpa [prefixWord, tailWord_1759757, baseEnd_1759757] using wordTrace_append hprefix tailTrace_1759757
  have hstable : (prefixWord ++ tailWord_1759757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759757).length < 2 ^ (prefixWord ++ tailWord_1759757).sum := by decide
  have hdescent : baseEnd_1759757 < baseStart_1759757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759813 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 4]
def baseStart_1759813 : Nat := 118140960795 + 1759813 * 2 ^ 59
def prefixEnd_1759813 : Nat := 4983230072969 + 3 ^ 40 * 1759813 * 2
def baseEnd_1759813 : Nat := 401613302680368203219677

theorem tailTrace_1759813 : CollatzResearch.WordTrace tailWord_1759813 prefixEnd_1759813 401613302680368203219677 := by
  unfold tailWord_1759813
  simp only [CollatzResearch.WordTrace]
  refine ⟨64185653173505527977332093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42790435449003685318221395 64185653173505527977332093)
  ·
    refine ⟨24069619940064572991499535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64185653173505527977332093 24069619940064572991499535)
    ·
      refine ⟨36104429910096859487249303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24069619940064572991499535 36104429910096859487249303)
      ·
        refine ⟨54156644865145289230873955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36104429910096859487249303 54156644865145289230873955)
        ·
          refine ⟨81234967297717933846310933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54156644865145289230873955 81234967297717933846310933)
          ·
            refine ⟨3807889092080528149045825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81234967297717933846310933 3807889092080528149045825)
            ·
              refine ⟨2855916819060396111784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807889092080528149045825 2855916819060396111784369)
              ·
                refine ⟨2141937614295297083838277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855916819060396111784369 2141937614295297083838277)
                ·
                  refine ⟨401613302680368203219677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141937614295297083838277 401613302680368203219677)
                  ·
                    rfl

theorem cell21_1759813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_1759813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759813 prefixEnd_1759813 := by exact prefixLift 1759813
  have htrace : WordTrace (prefixWord ++ tailWord_1759813) baseStart_1759813 baseEnd_1759813 := by
    simpa [prefixWord, tailWord_1759813, baseEnd_1759813] using wordTrace_append hprefix tailTrace_1759813
  have hstable : (prefixWord ++ tailWord_1759813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759813).length < 2 ^ (prefixWord ++ tailWord_1759813).sum := by decide
  have hdescent : baseEnd_1759813 < baseStart_1759813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759841 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_1759841 : Nat := 118140960795 + 1759841 * 2 ^ 59
def prefixEnd_1759841 : Nat := 4983230072969 + 3 ^ 40 * 1759841 * 2
def baseEnd_1759841 : Nat := 401619692661846376752953

theorem tailTrace_1759841 : CollatzResearch.WordTrace tailWord_1759841 prefixEnd_1759841 401619692661846376752953 := by
  unfold tailWord_1759841
  simp only [CollatzResearch.WordTrace]
  refine ⟨64186674417404088759351377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42791116278269392506234251 64186674417404088759351377)
  ·
    refine ⟨48140005813053066569513533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64186674417404088759351377 48140005813053066569513533)
    ·
      refine ⟨18052502179894899963567575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48140005813053066569513533 18052502179894899963567575)
      ·
        refine ⟨27078753269842349945351363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052502179894899963567575 27078753269842349945351363)
        ·
          refine ⟨40618129904763524918027045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27078753269842349945351363 40618129904763524918027045)
          ·
            refine ⟨7615899357143160922130071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40618129904763524918027045 7615899357143160922130071)
            ·
              refine ⟨11423849035714741383195107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7615899357143160922130071 11423849035714741383195107)
              ·
                refine ⟨17135773553572112074792661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11423849035714741383195107 17135773553572112074792661)
                ·
                  refine ⟨401619692661846376752953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17135773553572112074792661 401619692661846376752953)
                  ·
                    rfl

theorem cell21_1759841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_1759841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759841 prefixEnd_1759841 := by exact prefixLift 1759841
  have htrace : WordTrace (prefixWord ++ tailWord_1759841) baseStart_1759841 baseEnd_1759841 := by
    simpa [prefixWord, tailWord_1759841, baseEnd_1759841] using wordTrace_append hprefix tailTrace_1759841
  have hstable : (prefixWord ++ tailWord_1759841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759841).length < 2 ^ (prefixWord ++ tailWord_1759841).sum := by decide
  have hdescent : baseEnd_1759841 < baseStart_1759841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759872 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1759872 : Nat := 118140960795 + 1759872 * 2 ^ 59
def prefixEnd_1759872 : Nat := 4983230072969 + 3 ^ 40 * 1759872 * 2
def baseEnd_1759872 : Nat := 401626767284197211736223

theorem tailTrace_1759872 : CollatzResearch.WordTrace tailWord_1759872 prefixEnd_1759872 401626767284197211736223 := by
  unfold tailWord_1759872
  simp only [CollatzResearch.WordTrace]
  refine ⟨32093902540145890526864935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42791870053527854035819913 32093902540145890526864935)
  ·
    refine ⟨48140853810218835790297403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32093902540145890526864935 48140853810218835790297403)
    ·
      refine ⟨72211280715328253685446105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48140853810218835790297403 72211280715328253685446105)
      ·
        refine ⟨54158460536496190264084579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72211280715328253685446105 54158460536496190264084579)
        ·
          refine ⟨81237690804744285396126869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54158460536496190264084579 81237690804744285396126869)
          ·
            refine ⟨3808016756472388377943447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81237690804744285396126869 3808016756472388377943447)
            ·
              refine ⟨5712025134708582566915171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808016756472388377943447 5712025134708582566915171)
              ·
                refine ⟨8568037702062873850372757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712025134708582566915171 8568037702062873850372757)
                ·
                  refine ⟨401626767284197211736223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8568037702062873850372757 401626767284197211736223)
                  ·
                    rfl

theorem cell21_1759872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1759872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759872 prefixEnd_1759872 := by exact prefixLift 1759872
  have htrace : WordTrace (prefixWord ++ tailWord_1759872) baseStart_1759872 baseEnd_1759872 := by
    simpa [prefixWord, tailWord_1759872, baseEnd_1759872] using wordTrace_append hprefix tailTrace_1759872
  have hstable : (prefixWord ++ tailWord_1759872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759872).length < 2 ^ (prefixWord ++ tailWord_1759872).sum := by decide
  have hdescent : baseEnd_1759872 < baseStart_1759872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759926 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 3]
def baseStart_1759926 : Nat := 118140960795 + 1759926 * 2 ^ 59
def prefixEnd_1759926 : Nat := 4983230072969 + 3 ^ 40 * 1759926 * 2
def baseEnd_1759926 : Nat := 401639090819905117836113

theorem tailTrace_1759926 : CollatzResearch.WordTrace tailWord_1759926 prefixEnd_1759926 401639090819905117836113 := by
  unfold tailWord_1759926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011860913881009267262227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42793183081397432184130421 4011860913881009267262227)
  ·
    refine ⟨6017791370821513900893341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4011860913881009267262227 6017791370821513900893341)
    ·
      refine ⟨2256671764058067712835003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6017791370821513900893341 2256671764058067712835003)
      ·
        refine ⟨3385007646087101569252505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256671764058067712835003 3385007646087101569252505)
        ·
          refine ⟨2538755734565326176939379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3385007646087101569252505 2538755734565326176939379)
          ·
            refine ⟨3808133601847989265409069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538755734565326176939379 3808133601847989265409069)
            ·
              refine ⟨1428050100692995974528401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3808133601847989265409069 1428050100692995974528401)
              ·
                refine ⟨1071037575519746980896301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428050100692995974528401 1071037575519746980896301)
                ·
                  refine ⟨401639090819905117836113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071037575519746980896301 401639090819905117836113)
                  ·
                    rfl

theorem cell21_1759926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_1759926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759926 prefixEnd_1759926 := by exact prefixLift 1759926
  have htrace : WordTrace (prefixWord ++ tailWord_1759926) baseStart_1759926 baseEnd_1759926 := by
    simpa [prefixWord, tailWord_1759926, baseEnd_1759926] using wordTrace_append hprefix tailTrace_1759926
  have hstable : (prefixWord ++ tailWord_1759926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759926).length < 2 ^ (prefixWord ++ tailWord_1759926).sum := by decide
  have hdescent : baseEnd_1759926 < baseStart_1759926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759937 : List Nat := [1, 2, 6, 2, 1, 1, 2, 6]
def baseStart_1759937 : Nat := 118140960795 + 1759937 * 2 ^ 59
def prefixEnd_1759937 : Nat := 4983230072969 + 3 ^ 40 * 1759937 * 2
def baseEnd_1759937 : Nat := 133880533723257181050919

theorem tailTrace_1759937 : CollatzResearch.WordTrace tailWord_1759937 prefixEnd_1759937 133880533723257181050919 := by
  unfold tailWord_1759937
  simp only [CollatzResearch.WordTrace]
  refine ⟨64190175825056297154846065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42793450550037531436564043 64190175825056297154846065)
  ·
    refine ⟨48142631868792222866134549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64190175825056297154846065 48142631868792222866134549)
    ·
      refine ⟨2256685868849635446850057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48142631868792222866134549 2256685868849635446850057)
      ·
        refine ⟨1692514401637226585137543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256685868849635446850057 1692514401637226585137543)
        ·
          refine ⟨2538771602455839877706315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692514401637226585137543 2538771602455839877706315)
          ·
            refine ⟨3808157403683759816559473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538771602455839877706315 3808157403683759816559473)
            ·
              refine ⟨2856118052762819862419605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808157403683759816559473 2856118052762819862419605)
              ·
                refine ⟨133880533723257181050919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2856118052762819862419605 133880533723257181050919)
                ·
                  rfl

theorem cell21_1759937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 6].length) (baseStart_1759937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759937 prefixEnd_1759937 := by exact prefixLift 1759937
  have htrace : WordTrace (prefixWord ++ tailWord_1759937) baseStart_1759937 baseEnd_1759937 := by
    simpa [prefixWord, tailWord_1759937, baseEnd_1759937] using wordTrace_append hprefix tailTrace_1759937
  have hstable : (prefixWord ++ tailWord_1759937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759937).length < 2 ^ (prefixWord ++ tailWord_1759937).sum := by decide
  have hdescent : baseEnd_1759937 < baseStart_1759937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1759962 : List Nat := [3, 1, 1, 2, 2, 2, 1, 9]
def baseStart_1759962 : Nat := 118140960795 + 1759962 * 2 ^ 59
def prefixEnd_1759962 : Nat := 4983230072969 + 3 ^ 40 * 1759962 * 2
def baseEnd_1759962 : Nat := 133882435503459018412013

theorem tailTrace_1759962 : CollatzResearch.WordTrace tailWord_1759962 prefixEnd_1759962 133882435503459018412013 := by
  unfold tailWord_1759962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16047771912491431606126535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42794058433310484283004093 16047771912491431606126535)
  ·
    refine ⟨24071657868737147409189803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16047771912491431606126535 24071657868737147409189803)
    ·
      refine ⟨36107486803105721113784705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071657868737147409189803 36107486803105721113784705)
      ·
        refine ⟨27080615102329290835338529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36107486803105721113784705 27080615102329290835338529)
        ·
          refine ⟨20310461326746968126503897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27080615102329290835338529 20310461326746968126503897)
          ·
            refine ⟨15232845995060226094877923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20310461326746968126503897 15232845995060226094877923)
            ·
              refine ⟨22849268992590339142316885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15232845995060226094877923 22849268992590339142316885)
              ·
                refine ⟨133882435503459018412013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22849268992590339142316885 133882435503459018412013)
                ·
                  rfl

theorem cell21_1759962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 9].length) (baseStart_1759962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1759962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1759962 prefixEnd_1759962 := by exact prefixLift 1759962
  have htrace : WordTrace (prefixWord ++ tailWord_1759962) baseStart_1759962 baseEnd_1759962 := by
    simpa [prefixWord, tailWord_1759962, baseEnd_1759962] using wordTrace_append hprefix tailTrace_1759962
  have hstable : (prefixWord ++ tailWord_1759962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1759962).length < 2 ^ (prefixWord ++ tailWord_1759962).sum := by decide
  have hdescent : baseEnd_1759962 < baseStart_1759962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1759962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760058 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1760058 : Nat := 118140960795 + 1760058 * 2 ^ 59
def prefixEnd_1760058 : Nat := 4983230072969 + 3 ^ 40 * 1760058 * 2
def baseEnd_1760058 : Nat := 401669215018302221635843

theorem tailTrace_1760058 : CollatzResearch.WordTrace tailWord_1760058 prefixEnd_1760058 401669215018302221635843 := by
  unfold tailWord_1760058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048647264404483705000207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42796392705078623213333885 16048647264404483705000207)
  ·
    refine ⟨24072970896606725557500311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16048647264404483705000207 24072970896606725557500311)
    ·
      refine ⟨36109456344910088336250467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24072970896606725557500311 36109456344910088336250467)
      ·
        refine ⟨54164184517365132504375701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36109456344910088336250467 54164184517365132504375701)
        ·
          refine ⟨2538946149251490586142611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54164184517365132504375701 2538946149251490586142611)
          ·
            refine ⟨3808419223877235879213917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538946149251490586142611 3808419223877235879213917)
            ·
              refine ⟨1428157208953963454705219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3808419223877235879213917 1428157208953963454705219)
              ·
                refine ⟨2142235813430945182057829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428157208953963454705219 2142235813430945182057829)
                ·
                  refine ⟨401669215018302221635843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142235813430945182057829 401669215018302221635843)
                  ·
                    rfl

theorem cell21_1760058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1760058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760058 prefixEnd_1760058 := by exact prefixLift 1760058
  have htrace : WordTrace (prefixWord ++ tailWord_1760058) baseStart_1760058 baseEnd_1760058 := by
    simpa [prefixWord, tailWord_1760058, baseEnd_1760058] using wordTrace_append hprefix tailTrace_1760058
  have hstable : (prefixWord ++ tailWord_1760058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760058).length < 2 ^ (prefixWord ++ tailWord_1760058).sum := by decide
  have hdescent : baseEnd_1760058 < baseStart_1760058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760100 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1760100 : Nat := 118140960795 + 1760100 * 2 ^ 59
def prefixEnd_1760100 : Nat := 4983230072969 + 3 ^ 40 * 1760100 * 2
def baseEnd_1760100 : Nat := 401678799990519481935757

theorem tailTrace_1760100 : CollatzResearch.WordTrace tailWord_1760100 prefixEnd_1760100 401678799990519481935757 := by
  unfold tailWord_1760100
  simp only [CollatzResearch.WordTrace]
  refine ⟨32098060461732887996514877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42797413948977183995353169 32098060461732887996514877)
  ·
    refine ⟨12036772673149832998693079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32098060461732887996514877 12036772673149832998693079)
    ·
      refine ⟨18055159009724749498039619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036772673149832998693079 18055159009724749498039619)
      ·
        refine ⟨27082738514587124247059429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18055159009724749498039619 27082738514587124247059429)
        ·
          refine ⟨5078013471485085796323643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27082738514587124247059429 5078013471485085796323643)
          ·
            refine ⟨7617020207227628694485465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078013471485085796323643 7617020207227628694485465)
            ·
              refine ⟨5712765155420721520864099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7617020207227628694485465 5712765155420721520864099)
              ·
                refine ⟨8569147733131082281296149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712765155420721520864099 8569147733131082281296149)
                ·
                  refine ⟨401678799990519481935757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8569147733131082281296149 401678799990519481935757)
                  ·
                    rfl

theorem cell21_1760100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1760100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760100 prefixEnd_1760100 := by exact prefixLift 1760100
  have htrace : WordTrace (prefixWord ++ tailWord_1760100) baseStart_1760100 baseEnd_1760100 := by
    simpa [prefixWord, tailWord_1760100, baseEnd_1760100] using wordTrace_append hprefix tailTrace_1760100
  have hstable : (prefixWord ++ tailWord_1760100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760100).length < 2 ^ (prefixWord ++ tailWord_1760100).sum := by decide
  have hdescent : baseEnd_1760100 < baseStart_1760100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760114 : List Nat := [3, 2, 1, 2, 1, 1, 3, 8]
def baseStart_1760114 : Nat := 118140960795 + 1760114 * 2 ^ 59
def prefixEnd_1760114 : Nat := 4983230072969 + 3 ^ 40 * 1760114 * 2
def baseEnd_1760114 : Nat := 133893998327086189567465

theorem tailTrace_1760114 : CollatzResearch.WordTrace tailWord_1760114 prefixEnd_1760114 133893998327086189567465 := by
  unfold tailWord_1760114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049157886353764096009849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42797754363610037589359597 16049157886353764096009849)
  ·
    refine ⟨12036868414765323072007387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16049157886353764096009849 12036868414765323072007387)
    ·
      refine ⟨18055302622147984608011081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036868414765323072007387 18055302622147984608011081)
      ·
        refine ⟨13541476966610988456008311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18055302622147984608011081 13541476966610988456008311)
        ·
          refine ⟨20312215449916482684012467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541476966610988456008311 20312215449916482684012467)
          ·
            refine ⟨30468323174874724026018701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20312215449916482684012467 30468323174874724026018701)
            ·
              refine ⟨11425621190578021509757013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30468323174874724026018701 11425621190578021509757013)
              ·
                refine ⟨133893998327086189567465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11425621190578021509757013 133893998327086189567465)
                ·
                  rfl

theorem cell21_1760114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_1760114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760114 prefixEnd_1760114 := by exact prefixLift 1760114
  have htrace : WordTrace (prefixWord ++ tailWord_1760114) baseStart_1760114 baseEnd_1760114 := by
    simpa [prefixWord, tailWord_1760114, baseEnd_1760114] using wordTrace_append hprefix tailTrace_1760114
  have hstable : (prefixWord ++ tailWord_1760114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760114).length < 2 ^ (prefixWord ++ tailWord_1760114).sum := by decide
  have hdescent : baseEnd_1760114 < baseStart_1760114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760117 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 4]
def baseStart_1760117 : Nat := 118140960795 + 1760117 * 2 ^ 59
def prefixEnd_1760117 : Nat := 4983230072969 + 3 ^ 40 * 1760117 * 2
def baseEnd_1760117 : Nat := 401682679622131230152389

theorem tailTrace_1760117 : CollatzResearch.WordTrace tailWord_1760117 prefixEnd_1760117 401682679622131230152389 := by
  unfold tailWord_1760117
  simp only [CollatzResearch.WordTrace]
  refine ⟨64196740964404187896398605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42797827309602791930932403 64196740964404187896398605)
  ·
    refine ⟨24073777861651570461149477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64196740964404187896398605 24073777861651570461149477)
    ·
      refine ⟨4513833349059669461465527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24073777861651570461149477 4513833349059669461465527)
      ·
        refine ⟨6770750023589504192198291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513833349059669461465527 6770750023589504192198291)
        ·
          refine ⟨10156125035384256288297437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770750023589504192198291 10156125035384256288297437)
          ·
            refine ⟨3808546888269096108111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10156125035384256288297437 3808546888269096108111539)
            ·
              refine ⟨5712820332403644162167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808546888269096108111539 5712820332403644162167309)
              ·
                refine ⟨2142307624651366560812741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712820332403644162167309 2142307624651366560812741)
                ·
                  refine ⟨401682679622131230152389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142307624651366560812741 401682679622131230152389)
                  ·
                    rfl

theorem cell21_1760117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_1760117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760117 prefixEnd_1760117 := by exact prefixLift 1760117
  have htrace : WordTrace (prefixWord ++ tailWord_1760117) baseStart_1760117 baseEnd_1760117 := by
    simpa [prefixWord, tailWord_1760117, baseEnd_1760117] using wordTrace_append hprefix tailTrace_1760117
  have hstable : (prefixWord ++ tailWord_1760117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760117).length < 2 ^ (prefixWord ++ tailWord_1760117).sum := by decide
  have hdescent : baseEnd_1760117 < baseStart_1760117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760210 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_1760210 : Nat := 118140960795 + 1760210 * 2 ^ 59
def prefixEnd_1760210 : Nat := 4983230072969 + 3 ^ 40 * 1760210 * 2
def baseEnd_1760210 : Nat := 401703903489183735102199

theorem tailTrace_1760210 : CollatzResearch.WordTrace tailWord_1760210 prefixEnd_1760210 401703903489183735102199 := by
  unfold tailWord_1760210
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050033238266816194883521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42800088635378176519689389 16050033238266816194883521)
  ·
    refine ⟨12037524928700112146162641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16050033238266816194883521 12037524928700112146162641)
    ·
      refine ⟨9028143696525084109621981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12037524928700112146162641 9028143696525084109621981)
      ·
        refine ⟨3385553886196906541108243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9028143696525084109621981 3385553886196906541108243)
        ·
          refine ⟨5078330829295359811662365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385553886196906541108243 5078330829295359811662365)
          ·
            refine ⟨1904374060985759929373387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5078330829295359811662365 1904374060985759929373387)
            ·
              refine ⟨2856561091478639894060081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904374060985759929373387 2856561091478639894060081)
              ·
                refine ⟨2142420818608979920545061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856561091478639894060081 2142420818608979920545061)
                ·
                  refine ⟨401703903489183735102199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142420818608979920545061 401703903489183735102199)
                  ·
                    rfl

theorem cell21_1760210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_1760210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760210 prefixEnd_1760210 := by exact prefixLift 1760210
  have htrace : WordTrace (prefixWord ++ tailWord_1760210) baseStart_1760210 baseEnd_1760210 := by
    simpa [prefixWord, tailWord_1760210, baseEnd_1760210] using wordTrace_append hprefix tailTrace_1760210
  have hstable : (prefixWord ++ tailWord_1760210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760210).length < 2 ^ (prefixWord ++ tailWord_1760210).sum := by decide
  have hdescent : baseEnd_1760210 < baseStart_1760210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760266 : List Nat := [3, 1, 2, 2, 3, 1, 9]
def baseStart_1760266 : Nat := 118140960795 + 1760266 * 2 ^ 59
def prefixEnd_1760266 : Nat := 4983230072969 + 3 ^ 40 * 1760266 * 2
def baseEnd_1760266 : Nat := 44635187050237786907639

theorem tailTrace_1760266 : CollatzResearch.WordTrace tailWord_1760266 prefixEnd_1760266 44635187050237786907639 := by
  unfold tailWord_1760266
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050543860216096585893163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42801450293909590895715101 16050543860216096585893163)
  ·
    refine ⟨24075815790324144878839745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16050543860216096585893163 24075815790324144878839745)
    ·
      refine ⟨18056861842743108659129809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24075815790324144878839745 18056861842743108659129809)
      ·
        refine ⟨13542646382057331494347357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18056861842743108659129809 13542646382057331494347357)
        ·
          refine ⟨5078492393271499310380259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13542646382057331494347357 5078492393271499310380259)
          ·
            refine ⟨7617738589907248965570389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078492393271499310380259 7617738589907248965570389)
            ·
              refine ⟨44635187050237786907639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7617738589907248965570389 44635187050237786907639)
              ·
                rfl

theorem cell21_1760266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 9].length) (baseStart_1760266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760266 prefixEnd_1760266 := by exact prefixLift 1760266
  have htrace : WordTrace (prefixWord ++ tailWord_1760266) baseStart_1760266 baseEnd_1760266 := by
    simpa [prefixWord, tailWord_1760266, baseEnd_1760266] using wordTrace_append hprefix tailTrace_1760266
  have hstable : (prefixWord ++ tailWord_1760266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760266).length < 2 ^ (prefixWord ++ tailWord_1760266).sum := by decide
  have hdescent : baseEnd_1760266 < baseStart_1760266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760328 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_1760328 : Nat := 118140960795 + 1760328 * 2 ^ 59
def prefixEnd_1760328 : Nat := 4983230072969 + 3 ^ 40 * 1760328 * 2
def baseEnd_1760328 : Nat := 401730832696841752135291

theorem tailTrace_1760328 : CollatzResearch.WordTrace tailWord_1760328 prefixEnd_1760328 401730832696841752135291 := by
  unfold tailWord_1760328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32102218383319885466164819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42802957844426513954886425 32102218383319885466164819)
  ·
    refine ⟨48153327574979828199247229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32102218383319885466164819 48153327574979828199247229)
    ·
      refine ⟨18057497840617435574717711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48153327574979828199247229 18057497840617435574717711)
      ·
        refine ⟨27086246760926153362076567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18057497840617435574717711 27086246760926153362076567)
        ·
          refine ⟨40629370141389230043114851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27086246760926153362076567 40629370141389230043114851)
          ·
            refine ⟨60944055212083845064672277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40629370141389230043114851 60944055212083845064672277)
            ·
              refine ⟨2856752588066430237406513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60944055212083845064672277 2856752588066430237406513)
              ·
                refine ⟨2142564441049822678054885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856752588066430237406513 2142564441049822678054885)
                ·
                  refine ⟨401730832696841752135291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142564441049822678054885 401730832696841752135291)
                  ·
                    rfl

theorem cell21_1760328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_1760328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760328 prefixEnd_1760328 := by exact prefixLift 1760328
  have htrace : WordTrace (prefixWord ++ tailWord_1760328) baseStart_1760328 baseEnd_1760328 := by
    simpa [prefixWord, tailWord_1760328, baseEnd_1760328] using wordTrace_append hprefix tailTrace_1760328
  have hstable : (prefixWord ++ tailWord_1760328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760328).length < 2 ^ (prefixWord ++ tailWord_1760328).sum := by decide
  have hdescent : baseEnd_1760328 < baseStart_1760328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760359 : List Nat := [1, 1, 5, 1, 1, 4, 3, 5]
def baseStart_1760359 : Nat := 118140960795 + 1760359 * 2 ^ 59
def prefixEnd_1760359 : Nat := 4983230072969 + 3 ^ 40 * 1760359 * 2
def baseEnd_1760359 : Nat := 133912635773064195706187

theorem tailTrace_1760359 : CollatzResearch.WordTrace tailWord_1760359 prefixEnd_1760359 133912635773064195706187 := by
  unfold tailWord_1760359
  simp only [CollatzResearch.WordTrace]
  refine ⟨64205567429527463226708131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42803711619684975484472087 64205567429527463226708131)
  ·
    refine ⟨96308351144291194840062197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64205567429527463226708131 96308351144291194840062197)
    ·
      refine ⟨9028907919777299516255831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96308351144291194840062197 9028907919777299516255831)
      ·
        refine ⟨13543361879665949274383747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028907919777299516255831 13543361879665949274383747)
        ·
          refine ⟨20315042819498923911575621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543361879665949274383747 20315042819498923911575621)
          ·
            refine ⟨3809070528656048233420429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20315042819498923911575621 3809070528656048233420429)
            ·
              refine ⟨1428401448246018087532661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3809070528656048233420429 1428401448246018087532661)
              ·
                refine ⟨133912635773064195706187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1428401448246018087532661 133912635773064195706187)
                ·
                  rfl

theorem cell21_1760359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 5].length) (baseStart_1760359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760359 prefixEnd_1760359 := by exact prefixLift 1760359
  have htrace : WordTrace (prefixWord ++ tailWord_1760359) baseStart_1760359 baseEnd_1760359 := by
    simpa [prefixWord, tailWord_1760359, baseEnd_1760359] using wordTrace_append hprefix tailTrace_1760359
  have hstable : (prefixWord ++ tailWord_1760359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760359).length < 2 ^ (prefixWord ++ tailWord_1760359).sum := by decide
  have hdescent : baseEnd_1760359 < baseStart_1760359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760387 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 6]
def baseStart_1760387 : Nat := 118140960795 + 1760387 * 2 ^ 59
def prefixEnd_1760387 : Nat := 4983230072969 + 3 ^ 40 * 1760387 * 2
def baseEnd_1760387 : Nat := 401744297300670760651837

theorem tailTrace_1760387 : CollatzResearch.WordTrace tailWord_1760387 prefixEnd_1760387 401744297300670760651837 := by
  unfold tailWord_1760387
  simp only [CollatzResearch.WordTrace]
  refine ⟨64206588673426024008727415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42804392448950682672484943 64206588673426024008727415)
  ·
    refine ⟨96309883010139036013091123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64206588673426024008727415 96309883010139036013091123)
    ·
      refine ⟨144464824515208554019636685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96309883010139036013091123 144464824515208554019636685)
      ·
        refine ⟨54174309193203207757363757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144464824515208554019636685 54174309193203207757363757)
        ·
          refine ⟨20315365947451202909011409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54174309193203207757363757 20315365947451202909011409)
          ·
            refine ⟨15236524460588402181758557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20315365947451202909011409 15236524460588402181758557)
            ·
              refine ⟨5713696672720650818159459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15236524460588402181758557 5713696672720650818159459)
              ·
                refine ⟨8570545009080976227239189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713696672720650818159459 8570545009080976227239189)
                ·
                  refine ⟨401744297300670760651837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8570545009080976227239189 401744297300670760651837)
                  ·
                    rfl

theorem cell21_1760387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_1760387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760387 prefixEnd_1760387 := by exact prefixLift 1760387
  have htrace : WordTrace (prefixWord ++ tailWord_1760387) baseStart_1760387 baseEnd_1760387 := by
    simpa [prefixWord, tailWord_1760387, baseEnd_1760387] using wordTrace_append hprefix tailTrace_1760387
  have hstable : (prefixWord ++ tailWord_1760387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760387).length < 2 ^ (prefixWord ++ tailWord_1760387).sum := by decide
  have hdescent : baseEnd_1760387 < baseStart_1760387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760680 : List Nat := [2, 1, 6, 1, 2, 2, 1, 6]
def baseStart_1760680 : Nat := 118140960795 + 1760680 * 2 ^ 59
def prefixEnd_1760680 : Nat := 4983230072969 + 3 ^ 40 * 1760680 * 2
def baseEnd_1760680 : Nat := 133937054630855787422635

theorem tailTrace_1760680 : CollatzResearch.WordTrace tailWord_1760680 prefixEnd_1760680 133937054630855787422635 := by
  unfold tailWord_1760680
  simp only [CollatzResearch.WordTrace]
  refine ⟨32108637630682267524571747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42811516840909690032762329 32108637630682267524571747)
  ·
    refine ⟨48162956446023401286857621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32108637630682267524571747 48162956446023401286857621)
    ·
      refine ⟨2257638583407346935321451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48162956446023401286857621 2257638583407346935321451)
      ·
        refine ⟨3386457875111020402982177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257638583407346935321451 3386457875111020402982177)
        ·
          refine ⟨2539843406333265302236633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3386457875111020402982177 2539843406333265302236633)
          ·
            refine ⟨1904882554749948976677475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2539843406333265302236633 1904882554749948976677475)
            ·
              refine ⟨2857323832124923465016213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904882554749948976677475 2857323832124923465016213)
              ·
                refine ⟨133937054630855787422635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2857323832124923465016213 133937054630855787422635)
                ·
                  rfl

theorem cell21_1760680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 6].length) (baseStart_1760680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760680 prefixEnd_1760680 := by exact prefixLift 1760680
  have htrace : WordTrace (prefixWord ++ tailWord_1760680) baseStart_1760680 baseEnd_1760680 := by
    simpa [prefixWord, tailWord_1760680, baseEnd_1760680] using wordTrace_append hprefix tailTrace_1760680
  have hstable : (prefixWord ++ tailWord_1760680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760680).length < 2 ^ (prefixWord ++ tailWord_1760680).sum := by decide
  have hdescent : baseEnd_1760680 < baseStart_1760680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760801 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 4]
def baseStart_1760801 : Nat := 118140960795 + 1760801 * 2 ^ 59
def prefixEnd_1760801 : Nat := 4983230072969 + 3 ^ 40 * 1760801 * 2
def baseEnd_1760801 : Nat := 401838777741098040750991

theorem tailTrace_1760801 : CollatzResearch.WordTrace tailWord_1760801 prefixEnd_1760801 401838777741098040750991 := by
  unfold tailWord_1760801
  simp only [CollatzResearch.WordTrace]
  refine ⟨64221688493926172714298257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42814458995950781809532171 64221688493926172714298257)
  ·
    refine ⟨48166266370444629535723693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64221688493926172714298257 48166266370444629535723693)
    ·
      refine ⟨18062349888916736075896385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48166266370444629535723693 18062349888916736075896385)
      ·
        refine ⟨13546762416687552056922289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18062349888916736075896385 13546762416687552056922289)
        ·
          refine ⟨10160071812515664042691717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13546762416687552056922289 10160071812515664042691717)
          ·
            refine ⟨1905013464846687008004697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10160071812515664042691717 1905013464846687008004697)
            ·
              refine ⟨1428760098635015256003523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905013464846687008004697 1428760098635015256003523)
              ·
                refine ⟨2143140147952522884005285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428760098635015256003523 2143140147952522884005285)
                ·
                  refine ⟨401838777741098040750991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143140147952522884005285 401838777741098040750991)
                  ·
                    rfl

theorem cell21_1760801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 4].length) (baseStart_1760801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760801 prefixEnd_1760801 := by exact prefixLift 1760801
  have htrace : WordTrace (prefixWord ++ tailWord_1760801) baseStart_1760801 baseEnd_1760801 := by
    simpa [prefixWord, tailWord_1760801, baseEnd_1760801] using wordTrace_append hprefix tailTrace_1760801
  have hstable : (prefixWord ++ tailWord_1760801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760801).length < 2 ^ (prefixWord ++ tailWord_1760801).sum := by decide
  have hdescent : baseEnd_1760801 < baseStart_1760801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760838 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1760838 : Nat := 118140960795 + 1760838 * 2 ^ 59
def prefixEnd_1760838 : Nat := 4983230072969 + 3 ^ 40 * 1760838 * 2
def baseEnd_1760838 : Nat := 401847221645194198634249

theorem tailTrace_1760838 : CollatzResearch.WordTrace tailWord_1760838 prefixEnd_1760838 401847221645194198634249 := by
  unfold tailWord_1760838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006969937337254001043599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42815358663194752022263445 2006969937337254001043599)
  ·
    refine ⟨3010454906005881001565399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006969937337254001043599 3010454906005881001565399)
    ·
      refine ⟨4515682359008821502348099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010454906005881001565399 4515682359008821502348099)
      ·
        refine ⟨6773523538513232253522149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515682359008821502348099 6773523538513232253522149)
        ·
          refine ⟨1270035663471231047535403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6773523538513232253522149 1270035663471231047535403)
          ·
            refine ⟨1905053495206846571303105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270035663471231047535403 1905053495206846571303105)
            ·
              refine ⟨1428790121405134928477329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905053495206846571303105 1428790121405134928477329)
              ·
                refine ⟨1071592591053851196357997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428790121405134928477329 1071592591053851196357997)
                ·
                  refine ⟨401847221645194198634249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071592591053851196357997 401847221645194198634249)
                  ·
                    rfl

theorem cell21_1760838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1760838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760838 prefixEnd_1760838 := by exact prefixLift 1760838
  have htrace : WordTrace (prefixWord ++ tailWord_1760838) baseStart_1760838 baseEnd_1760838 := by
    simpa [prefixWord, tailWord_1760838, baseEnd_1760838] using wordTrace_append hprefix tailTrace_1760838
  have hstable : (prefixWord ++ tailWord_1760838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760838).length < 2 ^ (prefixWord ++ tailWord_1760838).sum := by decide
  have hdescent : baseEnd_1760838 < baseStart_1760838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760860 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 4]
def baseStart_1760860 : Nat := 118140960795 + 1760860 * 2 ^ 59
def prefixEnd_1760860 : Nat := 4983230072969 + 3 ^ 40 * 1760860 * 2
def baseEnd_1760860 : Nat := 401852242344927049267537

theorem tailTrace_1760860 : CollatzResearch.WordTrace tailWord_1760860 prefixEnd_1760860 401852242344927049267537 := by
  unfold tailWord_1760860
  simp only [CollatzResearch.WordTrace]
  refine ⟨32111920200356212895348017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42815893600474950527130689 32111920200356212895348017)
  ·
    refine ⟨24083940150267159671511013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32111920200356212895348017 24083940150267159671511013)
    ·
      refine ⟨4515738778175092438408315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24083940150267159671511013 4515738778175092438408315)
      ·
        refine ⟨6773608167262638657612473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515738778175092438408315 6773608167262638657612473)
        ·
          refine ⟨5080206125446978993209355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6773608167262638657612473 5080206125446978993209355)
          ·
            refine ⟨7620309188170468489814033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080206125446978993209355 7620309188170468489814033)
            ·
              refine ⟨5715231891127851367360525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620309188170468489814033 5715231891127851367360525)
              ·
                refine ⟨2143211959172944262760197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5715231891127851367360525 2143211959172944262760197)
                ·
                  refine ⟨401852242344927049267537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143211959172944262760197 401852242344927049267537)
                  ·
                    rfl

theorem cell21_1760860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_1760860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760860 prefixEnd_1760860 := by exact prefixLift 1760860
  have htrace : WordTrace (prefixWord ++ tailWord_1760860) baseStart_1760860 baseEnd_1760860 := by
    simpa [prefixWord, tailWord_1760860, baseEnd_1760860] using wordTrace_append hprefix tailTrace_1760860
  have hstable : (prefixWord ++ tailWord_1760860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760860).length < 2 ^ (prefixWord ++ tailWord_1760860).sum := by decide
  have hdescent : baseEnd_1760860 < baseStart_1760860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760905 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 3]
def baseStart_1760905 : Nat := 118140960795 + 1760905 * 2 ^ 59
def prefixEnd_1760905 : Nat := 4983230072969 + 3 ^ 40 * 1760905 * 2
def baseEnd_1760905 : Nat := 401862511958016971017445

theorem tailTrace_1760905 : CollatzResearch.WordTrace tailWord_1760905 prefixEnd_1760905 401862511958016971017445 := by
  unfold tailWord_1760905
  simp only [CollatzResearch.WordTrace]
  refine ⟨64225481685549398476084169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42816987790366265650722779 64225481685549398476084169)
  ·
    refine ⟨48169111264162048857063127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64225481685549398476084169 48169111264162048857063127)
    ·
      refine ⟨72253666896243073285594691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48169111264162048857063127 72253666896243073285594691)
      ·
        refine ⟨108380500344364609928392037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72253666896243073285594691 108380500344364609928392037)
        ·
          refine ⟨20321343814568364361573507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108380500344364609928392037 20321343814568364361573507)
          ·
            refine ⟨30482015721852546542360261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20321343814568364361573507 30482015721852546542360261)
            ·
              refine ⟨5715377947847352476692549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30482015721852546542360261 5715377947847352476692549)
              ·
                refine ⟨1071633365221378589379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5715377947847352476692549 1071633365221378589379853)
                ·
                  refine ⟨401862511958016971017445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071633365221378589379853 401862511958016971017445)
                  ·
                    rfl

theorem cell21_1760905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_1760905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760905 prefixEnd_1760905 := by exact prefixLift 1760905
  have htrace : WordTrace (prefixWord ++ tailWord_1760905) baseStart_1760905 baseEnd_1760905 := by
    simpa [prefixWord, tailWord_1760905, baseEnd_1760905] using wordTrace_append hprefix tailTrace_1760905
  have hstable : (prefixWord ++ tailWord_1760905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760905).length < 2 ^ (prefixWord ++ tailWord_1760905).sum := by decide
  have hdescent : baseEnd_1760905 < baseStart_1760905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1760970 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 4]
def baseStart_1760970 : Nat := 118140960795 + 1760970 * 2 ^ 59
def prefixEnd_1760970 : Nat := 4983230072969 + 3 ^ 40 * 1760970 * 2
def baseEnd_1760970 : Nat := 401877345843591302433979

theorem tailTrace_1760970 : CollatzResearch.WordTrace tailWord_1760970 prefixEnd_1760970 401877345843591302433979 := by
  unfold tailWord_1760970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056963107578478644300091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42818568286875943051466909 16056963107578478644300091)
  ·
    refine ⟨24085444661367717966450137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16056963107578478644300091 24085444661367717966450137)
    ·
      refine ⟨18064083496025788474837603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24085444661367717966450137 18064083496025788474837603)
      ·
        refine ⟨27096125244038682712256405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18064083496025788474837603 27096125244038682712256405)
        ·
          refine ⟨1270130870814313252137019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27096125244038682712256405 1270130870814313252137019)
          ·
            refine ⟨1905196306221469878205529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270130870814313252137019 1905196306221469878205529)
            ·
              refine ⟨1428897229666102408654147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905196306221469878205529 1428897229666102408654147)
              ·
                refine ⟨2143345844499153612981221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428897229666102408654147 2143345844499153612981221)
                ·
                  refine ⟨401877345843591302433979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143345844499153612981221 401877345843591302433979)
                  ·
                    rfl

theorem cell21_1760970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_1760970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1760970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1760970 prefixEnd_1760970 := by exact prefixLift 1760970
  have htrace : WordTrace (prefixWord ++ tailWord_1760970) baseStart_1760970 baseEnd_1760970 := by
    simpa [prefixWord, tailWord_1760970, baseEnd_1760970] using wordTrace_append hprefix tailTrace_1760970
  have hstable : (prefixWord ++ tailWord_1760970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1760970).length < 2 ^ (prefixWord ++ tailWord_1760970).sum := by decide
  have hdescent : baseEnd_1760970 < baseStart_1760970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1760970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761057 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 3]
def baseStart_1761057 : Nat := 118140960795 + 1761057 * 2 ^ 59
def prefixEnd_1761057 : Nat := 4983230072969 + 3 ^ 40 * 1761057 * 2
def baseEnd_1761057 : Nat := 401897200428898484483801

theorem tailTrace_1761057 : CollatzResearch.WordTrace tailWord_1761057 prefixEnd_1761057 401897200428898484483801 := by
  unfold tailWord_1761057
  simp only [CollatzResearch.WordTrace]
  refine ⟨64231025580998728435617425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42820683720665818957078283 64231025580998728435617425)
  ·
    refine ⟨48173269185749046326713069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64231025580998728435617425 48173269185749046326713069)
    ·
      refine ⟨18064975944655892372517401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48173269185749046326713069 18064975944655892372517401)
      ·
        refine ⟨13548731958491919279388051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18064975944655892372517401 13548731958491919279388051)
        ·
          refine ⟨20323097937737878919082077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13548731958491919279388051 20323097937737878919082077)
          ·
            refine ⟨7621161726651704594655779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20323097937737878919082077 7621161726651704594655779)
            ·
              refine ⟨11431742589977556891983669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621161726651704594655779 11431742589977556891983669)
              ·
                refine ⟨1071725867810395958623469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11431742589977556891983669 1071725867810395958623469)
                ·
                  refine ⟨401897200428898484483801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071725867810395958623469 401897200428898484483801)
                  ·
                    rfl

theorem cell21_1761057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_1761057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761057 prefixEnd_1761057 := by exact prefixLift 1761057
  have htrace : WordTrace (prefixWord ++ tailWord_1761057) baseStart_1761057 baseEnd_1761057 := by
    simpa [prefixWord, tailWord_1761057, baseEnd_1761057] using wordTrace_append hprefix tailTrace_1761057
  have hstable : (prefixWord ++ tailWord_1761057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761057).length < 2 ^ (prefixWord ++ tailWord_1761057).sum := by decide
  have hdescent : baseEnd_1761057 < baseStart_1761057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761133 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1761133 : Nat := 118140960795 + 1761133 * 2 ^ 59
def prefixEnd_1761133 : Nat := 4983230072969 + 3 ^ 40 * 1761133 * 2
def baseEnd_1761133 : Nat := 401914544664339241216979

theorem tailTrace_1761133 : CollatzResearch.WordTrace tailWord_1761133 prefixEnd_1761133 401914544664339241216979 := by
  unfold tailWord_1761133
  simp only [CollatzResearch.WordTrace]
  refine ⟨64233797528723393415384053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42822531685815595610256035 64233797528723393415384053)
  ·
    refine ⟨6021918518317818132692255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64233797528723393415384053 6021918518317818132692255)
    ·
      refine ⟨9032877777476727199038383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021918518317818132692255 9032877777476727199038383)
      ·
        refine ⟨13549316666215090798557575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9032877777476727199038383 13549316666215090798557575)
        ·
          refine ⟨20323974999322636197836363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13549316666215090798557575 20323974999322636197836363)
          ·
            refine ⟨30485962498983954296754545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20323974999322636197836363 30485962498983954296754545)
            ·
              refine ⟨22864471874237965722565909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30485962498983954296754545 22864471874237965722565909)
              ·
                refine ⟨1071772119104904643245277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22864471874237965722565909 1071772119104904643245277)
                ·
                  refine ⟨401914544664339241216979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071772119104904643245277 401914544664339241216979)
                  ·
                    rfl

theorem cell21_1761133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1761133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761133 prefixEnd_1761133 := by exact prefixLift 1761133
  have htrace : WordTrace (prefixWord ++ tailWord_1761133) baseStart_1761133 baseEnd_1761133 := by
    simpa [prefixWord, tailWord_1761133, baseEnd_1761133] using wordTrace_append hprefix tailTrace_1761133
  have hstable : (prefixWord ++ tailWord_1761133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761133).length < 2 ^ (prefixWord ++ tailWord_1761133).sum := by decide
  have hdescent : baseEnd_1761133 < baseStart_1761133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761237 : List Nat := [1, 3, 2, 3, 2, 2, 8]
def baseStart_1761237 : Nat := 118140960795 + 1761237 * 2 ^ 59
def prefixEnd_1761237 : Nat := 4983230072969 + 3 ^ 40 * 1761237 * 2
def baseEnd_1761237 : Nat := 44659808764584241275937

theorem tailTrace_1761237 : CollatzResearch.WordTrace tailWord_1761237 prefixEnd_1761237 44659808764584241275937 := by
  unfold tailWord_1761237
  simp only [CollatzResearch.WordTrace]
  refine ⟨64237590720346619177169965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42825060480231079451446643 64237590720346619177169965)
  ·
    refine ⟨24089096520129982191438737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64237590720346619177169965 24089096520129982191438737)
    ·
      refine ⟨18066822390097486643579053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24089096520129982191438737 18066822390097486643579053)
      ·
        refine ⟨6775058396286557491342145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18066822390097486643579053 6775058396286557491342145)
        ·
          refine ⟨5081293797214918118506609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6775058396286557491342145 5081293797214918118506609)
          ·
            refine ⟨3810970347911188588879957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5081293797214918118506609 3810970347911188588879957)
            ·
              refine ⟨44659808764584241275937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3810970347911188588879957 44659808764584241275937)
              ·
                rfl

theorem cell21_1761237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 8].length) (baseStart_1761237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761237 prefixEnd_1761237 := by exact prefixLift 1761237
  have htrace : WordTrace (prefixWord ++ tailWord_1761237) baseStart_1761237 baseEnd_1761237 := by
    simpa [prefixWord, tailWord_1761237, baseEnd_1761237] using wordTrace_append hprefix tailTrace_1761237
  have hstable : (prefixWord ++ tailWord_1761237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761237).length < 2 ^ (prefixWord ++ tailWord_1761237).sum := by decide
  have hdescent : baseEnd_1761237 < baseStart_1761237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761285 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 3]
def baseStart_1761285 : Nat := 118140960795 + 1761285 * 2 ^ 59
def prefixEnd_1761285 : Nat := 4983230072969 + 3 ^ 40 * 1761285 * 2
def baseEnd_1761285 : Nat := 401949233135220754683335

theorem tailTrace_1761285 : CollatzResearch.WordTrace tailWord_1761285 prefixEnd_1761285 401949233135220754683335 := by
  unfold tailWord_1761285
  simp only [CollatzResearch.WordTrace]
  refine ⟨64239341424172723374917309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42826227616115148916611539 64239341424172723374917309)
  ·
    refine ⟨24089753034064771265593991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64239341424172723374917309 24089753034064771265593991)
    ·
      refine ⟨36134629551097156898390987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24089753034064771265593991 36134629551097156898390987)
      ·
        refine ⟨54201944326645735347586481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36134629551097156898390987 54201944326645735347586481)
        ·
          refine ⟨40651458244984301510689861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54201944326645735347586481 40651458244984301510689861)
          ·
            refine ⟨7622148420934556533254349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40651458244984301510689861 7622148420934556533254349)
            ·
              refine ⟨2858305657850458699970381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622148420934556533254349 2858305657850458699970381)
              ·
                refine ⟨1071864621693922012488893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2858305657850458699970381 1071864621693922012488893)
                ·
                  refine ⟨401949233135220754683335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071864621693922012488893 401949233135220754683335)
                  ·
                    rfl

theorem cell21_1761285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_1761285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761285 prefixEnd_1761285 := by exact prefixLift 1761285
  have htrace : WordTrace (prefixWord ++ tailWord_1761285) baseStart_1761285 baseEnd_1761285 := by
    simpa [prefixWord, tailWord_1761285, baseEnd_1761285] using wordTrace_append hprefix tailTrace_1761285
  have hstable : (prefixWord ++ tailWord_1761285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761285).length < 2 ^ (prefixWord ++ tailWord_1761285).sum := by decide
  have hdescent : baseEnd_1761285 < baseStart_1761285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761316 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_1761316 : Nat := 118140960795 + 1761316 * 2 ^ 59
def prefixEnd_1761316 : Nat := 4983230072969 + 3 ^ 40 * 1761316 * 2
def baseEnd_1761316 : Nat := 401956307757571589666605

theorem tailTrace_1761316 : CollatzResearch.WordTrace tailWord_1761316 prefixEnd_1761316 401956307757571589666605 := by
  unfold tailWord_1761316
  simp only [CollatzResearch.WordTrace]
  refine ⟨32120236043530207834647901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42826981391373610446197201 32120236043530207834647901)
  ·
    refine ⟨12045088516323827937992963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32120236043530207834647901 12045088516323827937992963)
    ·
      refine ⟨18067632774485741906989445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12045088516323827937992963 18067632774485741906989445)
      ·
        refine ⟨3387681145216076607560521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18067632774485741906989445 3387681145216076607560521)
        ·
          refine ⟨2540760858912057455670391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3387681145216076607560521 2540760858912057455670391)
          ·
            refine ⟨3811141288368086183505587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540760858912057455670391 3811141288368086183505587)
            ·
              refine ⟨5716711932552129275258381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811141288368086183505587 5716711932552129275258381)
              ·
                refine ⟨2143766974707048478221893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5716711932552129275258381 2143766974707048478221893)
                ·
                  refine ⟨401956307757571589666605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143766974707048478221893 401956307757571589666605)
                  ·
                    rfl

theorem cell21_1761316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_1761316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761316 prefixEnd_1761316 := by exact prefixLift 1761316
  have htrace : WordTrace (prefixWord ++ tailWord_1761316) baseStart_1761316 baseEnd_1761316 := by
    simpa [prefixWord, tailWord_1761316, baseEnd_1761316] using wordTrace_append hprefix tailTrace_1761316
  have hstable : (prefixWord ++ tailWord_1761316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761316).length < 2 ^ (prefixWord ++ tailWord_1761316).sum := by decide
  have hdescent : baseEnd_1761316 < baseStart_1761316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761409 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 4]
def baseStart_1761409 : Nat := 118140960795 + 1761409 * 2 ^ 59
def prefixEnd_1761409 : Nat := 4983230072969 + 3 ^ 40 * 1761409 * 2
def baseEnd_1761409 : Nat := 401977531624624094616415

theorem tailTrace_1761409 : CollatzResearch.WordTrace tailWord_1761409 prefixEnd_1761409 401977531624624094616415 := by
  unfold tailWord_1761409
  simp only [CollatzResearch.WordTrace]
  refine ⟨64243864075723492552431281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42829242717148995034954187 64243864075723492552431281)
  ·
    refine ⟨48182898056792619414323461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64243864075723492552431281 48182898056792619414323461)
    ·
      refine ⟨9034293385648616140185649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48182898056792619414323461 9034293385648616140185649)
      ·
        refine ⟨6775720039236462105139237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9034293385648616140185649 6775720039236462105139237)
        ·
          refine ⟨1270447507356836644713607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6775720039236462105139237 1270447507356836644713607)
          ·
            refine ⟨1905671261035254967070411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270447507356836644713607 1905671261035254967070411)
            ·
              refine ⟨2858506891552882450605617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905671261035254967070411 2858506891552882450605617)
              ·
                refine ⟨2143880168664661837954213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2858506891552882450605617 2143880168664661837954213)
                ·
                  refine ⟨401977531624624094616415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143880168664661837954213 401977531624624094616415)
                  ·
                    rfl

theorem cell21_1761409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_1761409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761409 prefixEnd_1761409 := by exact prefixLift 1761409
  have htrace : WordTrace (prefixWord ++ tailWord_1761409) baseStart_1761409 baseEnd_1761409 := by
    simpa [prefixWord, tailWord_1761409, baseEnd_1761409] using wordTrace_append hprefix tailTrace_1761409
  have hstable : (prefixWord ++ tailWord_1761409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761409).length < 2 ^ (prefixWord ++ tailWord_1761409).sum := by decide
  have hdescent : baseEnd_1761409 < baseStart_1761409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761530 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1761530 : Nat := 118140960795 + 1761530 * 2 ^ 59
def prefixEnd_1761530 : Nat := 4983230072969 + 3 ^ 40 * 1761530 * 2
def baseEnd_1761530 : Nat := 402005145473154773099501

theorem tailTrace_1761530 : CollatzResearch.WordTrace tailWord_1761530 prefixEnd_1761530 402005145473154773099501 := by
  unfold tailWord_1761530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062069327071282554396511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42832184872190086811724029 16062069327071282554396511)
  ·
    refine ⟨24093103990606923831594767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16062069327071282554396511 24093103990606923831594767)
    ·
      refine ⟨36139655985910385747392151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24093103990606923831594767 36139655985910385747392151)
      ·
        refine ⟨54209483978865578621088227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36139655985910385747392151 54209483978865578621088227)
        ·
          refine ⟨81314225968298367931632341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54209483978865578621088227 81314225968298367931632341)
          ·
            refine ⟨1905802171131992998397633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81314225968298367931632341 1905802171131992998397633)
            ·
              refine ⟨1429351628348994748798225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905802171131992998397633 1429351628348994748798225)
              ·
                refine ⟨1072013721261746061598669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429351628348994748798225 1072013721261746061598669)
                ·
                  refine ⟨402005145473154773099501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072013721261746061598669 402005145473154773099501)
                  ·
                    rfl

theorem cell21_1761530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1761530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761530 prefixEnd_1761530 := by exact prefixLift 1761530
  have htrace : WordTrace (prefixWord ++ tailWord_1761530) baseStart_1761530 baseEnd_1761530 := by
    simpa [prefixWord, tailWord_1761530, baseEnd_1761530] using wordTrace_append hprefix tailTrace_1761530
  have hstable : (prefixWord ++ tailWord_1761530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761530).length < 2 ^ (prefixWord ++ tailWord_1761530).sum := by decide
  have hdescent : baseEnd_1761530 < baseStart_1761530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761575 : List Nat := [1, 1, 8, 1, 1, 1, 8]
def baseStart_1761575 : Nat := 118140960795 + 1761575 * 2 ^ 59
def prefixEnd_1761575 : Nat := 4983230072969 + 3 ^ 40 * 1761575 * 2
def baseEnd_1761575 : Nat := 44668379454027188316601

theorem tailTrace_1761575 : CollatzResearch.WordTrace tailWord_1761575 prefixEnd_1761575 44668379454027188316601 := by
  unfold tailWord_1761575
  simp only [CollatzResearch.WordTrace]
  refine ⟨64249918593122102902974179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42833279062081401935316119 64249918593122102902974179)
  ·
    refine ⟨96374877889683154354461269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64249918593122102902974179 96374877889683154354461269)
    ·
      refine ⟨1129393100269724465091343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 96374877889683154354461269 1129393100269724465091343)
      ·
        refine ⟨1694089650404586697637015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129393100269724465091343 1694089650404586697637015)
        ·
          refine ⟨2541134475606880046455523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694089650404586697637015 2541134475606880046455523)
          ·
            refine ⟨3811701713410320069683285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541134475606880046455523 3811701713410320069683285)
            ·
              refine ⟨44668379454027188316601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3811701713410320069683285 44668379454027188316601)
              ·
                rfl

theorem cell21_1761575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 8].length) (baseStart_1761575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761575 prefixEnd_1761575 := by exact prefixLift 1761575
  have htrace : WordTrace (prefixWord ++ tailWord_1761575) baseStart_1761575 baseEnd_1761575 := by
    simpa [prefixWord, tailWord_1761575, baseEnd_1761575] using wordTrace_append hprefix tailTrace_1761575
  have hstable : (prefixWord ++ tailWord_1761575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761575).length < 2 ^ (prefixWord ++ tailWord_1761575).sum := by decide
  have hdescent : baseEnd_1761575 < baseStart_1761575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761617 : List Nat := [1, 2, 2, 1, 4, 2, 4, 5]
def baseStart_1761617 : Nat := 118140960795 + 1761617 * 2 ^ 59
def prefixEnd_1761617 : Nat := 4983230072969 + 3 ^ 40 * 1761617 * 2
def baseEnd_1761617 : Nat := 134008333352820651716441

theorem tailTrace_1761617 : CollatzResearch.WordTrace tailWord_1761617 prefixEnd_1761617 134008333352820651716441 := by
  unfold tailWord_1761617
  simp only [CollatzResearch.WordTrace]
  refine ⟨64251450458969944076003105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42834300305979962717335403 64251450458969944076003105)
  ·
    refine ⟨48188587844227458057002329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64251450458969944076003105 48188587844227458057002329)
    ·
      refine ⟨36141440883170593542751747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48188587844227458057002329 36141440883170593542751747)
      ·
        refine ⟨54212161324755890314127621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36141440883170593542751747 54212161324755890314127621)
        ·
          refine ⟨10164780248391729433898929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54212161324755890314127621 10164780248391729433898929)
          ·
            refine ⟨7623585186293797075424197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10164780248391729433898929 7623585186293797075424197)
            ·
              refine ⟨1429422222430086951642037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7623585186293797075424197 1429422222430086951642037)
              ·
                refine ⟨134008333352820651716441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1429422222430086951642037 134008333352820651716441)
                ·
                  rfl

theorem cell21_1761617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 5].length) (baseStart_1761617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761617 prefixEnd_1761617 := by exact prefixLift 1761617
  have htrace : WordTrace (prefixWord ++ tailWord_1761617) baseStart_1761617 baseEnd_1761617 := by
    simpa [prefixWord, tailWord_1761617, baseEnd_1761617] using wordTrace_append hprefix tailTrace_1761617
  have hstable : (prefixWord ++ tailWord_1761617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761617).length < 2 ^ (prefixWord ++ tailWord_1761617).sum := by decide
  have hdescent : baseEnd_1761617 < baseStart_1761617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761648 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_1761648 : Nat := 118140960795 + 1761648 * 2 ^ 59
def prefixEnd_1761648 : Nat := 4983230072969 + 3 ^ 40 * 1761648 * 2
def baseEnd_1761648 : Nat := 402032074680812790132593

theorem tailTrace_1761648 : CollatzResearch.WordTrace tailWord_1761648 prefixEnd_1761648 402032074680812790132593 := by
  unfold tailWord_1761648
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126290560928818185190799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42835054081238424246921065 32126290560928818185190799)
  ·
    refine ⟨48189435841393227277786199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32126290560928818185190799 48189435841393227277786199)
    ·
      refine ⟨72284153762089840916679299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48189435841393227277786199 72284153762089840916679299)
      ·
        refine ⟨108426230643134761375018949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72284153762089840916679299 108426230643134761375018949)
        ·
          refine ⟨20329918245587767757816053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108426230643134761375018949 20329918245587767757816053)
          ·
            refine ⟨1905929835523853227295255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20329918245587767757816053 1905929835523853227295255)
            ·
              refine ⟨2858894753285779840942883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905929835523853227295255 2858894753285779840942883)
              ·
                refine ⟨4288342129928669761414325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858894753285779840942883 4288342129928669761414325)
                ·
                  refine ⟨402032074680812790132593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4288342129928669761414325 402032074680812790132593)
                  ·
                    rfl

theorem cell21_1761648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_1761648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761648 prefixEnd_1761648 := by exact prefixLift 1761648
  have htrace : WordTrace (prefixWord ++ tailWord_1761648) baseStart_1761648 baseEnd_1761648 := by
    simpa [prefixWord, tailWord_1761648, baseEnd_1761648] using wordTrace_append hprefix tailTrace_1761648
  have hstable : (prefixWord ++ tailWord_1761648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761648).length < 2 ^ (prefixWord ++ tailWord_1761648).sum := by decide
  have hdescent : baseEnd_1761648 < baseStart_1761648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761654 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1761654 : Nat := 118140960795 + 1761654 * 2 ^ 59
def prefixEnd_1761654 : Nat := 4983230072969 + 3 ^ 40 * 1761654 * 2
def baseEnd_1761654 : Nat := 402033443962558113032581

theorem tailTrace_1761654 : CollatzResearch.WordTrace tailWord_1761654 prefixEnd_1761654 402033443962558113032581 := by
  unfold tailWord_1761654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015799997489743712193751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42835199973223932930066677 4015799997489743712193751)
  ·
    refine ⟨6023699996234615568290627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015799997489743712193751 6023699996234615568290627)
    ·
      refine ⟨9035549994351923352435941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023699996234615568290627 9035549994351923352435941)
      ·
        refine ⟨1694165623940985628581739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9035549994351923352435941 1694165623940985628581739)
        ·
          refine ⟨2541248435911478442872609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694165623940985628581739 2541248435911478442872609)
          ·
            refine ⟨1905936326933608832154457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541248435911478442872609 1905936326933608832154457)
            ·
              refine ⟨1429452245200206624115843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905936326933608832154457 1429452245200206624115843)
              ·
                refine ⟨2144178367800309936173765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429452245200206624115843 2144178367800309936173765)
                ·
                  refine ⟨402033443962558113032581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144178367800309936173765 402033443962558113032581)
                  ·
                    rfl

theorem cell21_1761654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1761654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761654 prefixEnd_1761654 := by exact prefixLift 1761654
  have htrace : WordTrace (prefixWord ++ tailWord_1761654) baseStart_1761654 baseEnd_1761654 := by
    simpa [prefixWord, tailWord_1761654, baseEnd_1761654] using wordTrace_append hprefix tailTrace_1761654
  have hstable : (prefixWord ++ tailWord_1761654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761654).length < 2 ^ (prefixWord ++ tailWord_1761654).sum := by decide
  have hdescent : baseEnd_1761654 < baseStart_1761654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761676 : List Nat := [2, 2, 1, 2, 1, 4, 2, 7]
def baseStart_1761676 : Nat := 118140960795 + 1761676 * 2 ^ 59
def prefixEnd_1761676 : Nat := 4983230072969 + 3 ^ 40 * 1761676 * 2
def baseEnd_1761676 : Nat := 134012821554096987888623

theorem tailTrace_1761676 : CollatzResearch.WordTrace tailWord_1761676 prefixEnd_1761676 134012821554096987888623 := by
  unfold tailWord_1761676
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126801182878098576200441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42835734910504131434933921 32126801182878098576200441)
  ·
    refine ⟨24095100887158573932150331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32126801182878098576200441 24095100887158573932150331)
    ·
      refine ⟨36142651330737860898225497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24095100887158573932150331 36142651330737860898225497)
      ·
        refine ⟨27106988498053395673669123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36142651330737860898225497 27106988498053395673669123)
        ·
          refine ⟨40660482747080093510503685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27106988498053395673669123 40660482747080093510503685)
          ·
            refine ⟨7623840515077517533219441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40660482747080093510503685 7623840515077517533219441)
            ·
              refine ⟨5717880386308138149914581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7623840515077517533219441 5717880386308138149914581)
              ·
                refine ⟨134012821554096987888623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5717880386308138149914581 134012821554096987888623)
                ·
                  rfl

theorem cell21_1761676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_1761676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761676 prefixEnd_1761676 := by exact prefixLift 1761676
  have htrace : WordTrace (prefixWord ++ tailWord_1761676) baseStart_1761676 baseEnd_1761676 := by
    simpa [prefixWord, tailWord_1761676, baseEnd_1761676] using wordTrace_append hprefix tailTrace_1761676
  have hstable : (prefixWord ++ tailWord_1761676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761676).length < 2 ^ (prefixWord ++ tailWord_1761676).sum := by decide
  have hdescent : baseEnd_1761676 < baseStart_1761676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761693 : List Nat := [1, 4, 2, 1, 5, 8]
def baseStart_1761693 : Nat := 118140960795 + 1761693 * 2 ^ 59
def prefixEnd_1761693 : Nat := 4983230072969 + 3 ^ 40 * 1761693 * 2
def baseEnd_1761693 : Nat := 14890457196070470810463

theorem tailTrace_1761693 : CollatzResearch.WordTrace tailWord_1761693 prefixEnd_1761693 14890457196070470810463 := by
  unfold tailWord_1761693
  simp only [CollatzResearch.WordTrace]
  refine ⟨64254222406694609055769733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42836148271129739370513155 64254222406694609055769733)
  ·
    refine ⟨12047666701255239197956825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64254222406694609055769733 12047666701255239197956825)
    ·
      refine ⟨9035750025941429398467619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12047666701255239197956825 9035750025941429398467619)
      ·
        refine ⟨13553625038912144097701429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035750025941429398467619 13553625038912144097701429)
        ·
          refine ⟨1270652347398013509159509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13553625038912144097701429 1270652347398013509159509)
          ·
            refine ⟨14890457196070470810463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1270652347398013509159509 14890457196070470810463)
            ·
              rfl

theorem cell21_1761693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 8].length) (baseStart_1761693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761693 prefixEnd_1761693 := by exact prefixLift 1761693
  have htrace : WordTrace (prefixWord ++ tailWord_1761693) baseStart_1761693 baseEnd_1761693 := by
    simpa [prefixWord, tailWord_1761693, baseEnd_1761693] using wordTrace_append hprefix tailTrace_1761693
  have hstable : (prefixWord ++ tailWord_1761693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761693).length < 2 ^ (prefixWord ++ tailWord_1761693).sum := by decide
  have hdescent : baseEnd_1761693 < baseStart_1761693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761724 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1761724 : Nat := 118140960795 + 1761724 * 2 ^ 59
def prefixEnd_1761724 : Nat := 4983230072969 + 3 ^ 40 * 1761724 * 2
def baseEnd_1761724 : Nat := 402049418916253546865771

theorem tailTrace_1761724 : CollatzResearch.WordTrace tailWord_1761724 prefixEnd_1761724 402049418916253546865771 := by
  unfold tailWord_1761724
  simp only [CollatzResearch.WordTrace]
  refine ⟨32127676534791150675074113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42836902046388200900098817 32127676534791150675074113)
  ·
    refine ⟨24095757401093363006305585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32127676534791150675074113 24095757401093363006305585)
    ·
      refine ⟨18071818050820022254729189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24095757401093363006305585 18071818050820022254729189)
      ·
        refine ⟨3388465884528754172761723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18071818050820022254729189 3388465884528754172761723)
        ·
          refine ⟨5082698826793131259142585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388465884528754172761723 5082698826793131259142585)
          ·
            refine ⟨3812024120094848444356939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082698826793131259142585 3812024120094848444356939)
            ·
              refine ⟨5718036180142272666535409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812024120094848444356939 5718036180142272666535409)
              ·
                refine ⟨4288527135106704499901557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5718036180142272666535409 4288527135106704499901557)
                ·
                  refine ⟨402049418916253546865771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4288527135106704499901557 402049418916253546865771)
                  ·
                    rfl

theorem cell21_1761724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1761724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761724 prefixEnd_1761724 := by exact prefixLift 1761724
  have htrace : WordTrace (prefixWord ++ tailWord_1761724) baseStart_1761724 baseEnd_1761724 := by
    simpa [prefixWord, tailWord_1761724, baseEnd_1761724] using wordTrace_append hprefix tailTrace_1761724
  have hstable : (prefixWord ++ tailWord_1761724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761724).length < 2 ^ (prefixWord ++ tailWord_1761724).sum := by decide
  have hdescent : baseEnd_1761724 < baseStart_1761724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761797 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 6]
def baseStart_1761797 : Nat := 118140960795 + 1761797 * 2 ^ 59
def prefixEnd_1761797 : Nat := 4983230072969 + 3 ^ 40 * 1761797 * 2
def baseEnd_1761797 : Nat := 402066078510821642148955

theorem tailTrace_1761797 : CollatzResearch.WordTrace tailWord_1761797 prefixEnd_1761797 402066078510821642148955 := by
  unfold tailWord_1761797
  simp only [CollatzResearch.WordTrace]
  refine ⟨64258015598317834817555645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42838677065545223211703763 64258015598317834817555645)
  ·
    refine ⟨24096755849369188056583367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64258015598317834817555645 24096755849369188056583367)
    ·
      refine ⟨36145133774053782084875051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24096755849369188056583367 36145133774053782084875051)
      ·
        refine ⟨54217700661080673127312577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36145133774053782084875051 54217700661080673127312577)
        ·
          refine ⟨40663275495810504845484433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54217700661080673127312577 40663275495810504845484433)
          ·
            refine ⟨30497456621857878634113325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40663275495810504845484433 30497456621857878634113325)
            ·
              refine ⟨11436546233196704487792497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30497456621857878634113325 11436546233196704487792497)
              ·
                refine ⟨8577409674897528365844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11436546233196704487792497 8577409674897528365844373)
                ·
                  refine ⟨402066078510821642148955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8577409674897528365844373 402066078510821642148955)
                  ·
                    rfl

theorem cell21_1761797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_1761797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761797 prefixEnd_1761797 := by exact prefixLift 1761797
  have htrace : WordTrace (prefixWord ++ tailWord_1761797) baseStart_1761797 baseEnd_1761797 := by
    simpa [prefixWord, tailWord_1761797, baseEnd_1761797] using wordTrace_append hprefix tailTrace_1761797
  have hstable : (prefixWord ++ tailWord_1761797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761797).length < 2 ^ (prefixWord ++ tailWord_1761797).sum := by decide
  have hdescent : baseEnd_1761797 < baseStart_1761797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1761910 : List Nat := [5, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1761910 : Nat := 118140960795 + 1761910 * 2 ^ 59
def prefixEnd_1761910 : Nat := 4983230072969 + 3 ^ 40 * 1761910 * 2
def baseEnd_1761910 : Nat := 402091866650358556765391

theorem tailTrace_1761910 : CollatzResearch.WordTrace tailWord_1761910 prefixEnd_1761910 402091866650358556765391 := by
  unfold tailWord_1761910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016383565431778444776199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42841424697938970077612789 4016383565431778444776199)
  ·
    refine ⟨6024575348147667667164299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4016383565431778444776199 6024575348147667667164299)
    ·
      refine ⟨9036863022221501500746449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024575348147667667164299 9036863022221501500746449)
      ·
        refine ⟨6777647266666126125559837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9036863022221501500746449 6777647266666126125559837)
        ·
          refine ⟨2541617724999797297084939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6777647266666126125559837 2541617724999797297084939)
          ·
            refine ⟨3812426587499695945627409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541617724999797297084939 3812426587499695945627409)
            ·
              refine ⟨2859319940624771959220557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812426587499695945627409 2859319940624771959220557)
              ·
                refine ⟨1072244977734289484707709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2859319940624771959220557 1072244977734289484707709)
                ·
                  refine ⟨402091866650358556765391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072244977734289484707709 402091866650358556765391)
                  ·
                    rfl

theorem cell21_1761910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1761910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1761910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1761910 prefixEnd_1761910 := by exact prefixLift 1761910
  have htrace : WordTrace (prefixWord ++ tailWord_1761910) baseStart_1761910 baseEnd_1761910 := by
    simpa [prefixWord, tailWord_1761910, baseEnd_1761910] using wordTrace_append hprefix tailTrace_1761910
  have hstable : (prefixWord ++ tailWord_1761910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1761910).length < 2 ^ (prefixWord ++ tailWord_1761910).sum := by decide
  have hdescent : baseEnd_1761910 < baseStart_1761910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1761910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762037 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 3]
def baseStart_1762037 : Nat := 118140960795 + 1762037 * 2 ^ 59
def prefixEnd_1762037 : Nat := 4983230072969 + 3 ^ 40 * 1762037 * 2
def baseEnd_1762037 : Nat := 402120849780634558148465

theorem tailTrace_1762037 : CollatzResearch.WordTrace tailWord_1762037 prefixEnd_1762037 402120849780634558148465 := by
  unfold tailWord_1762037
  simp only [CollatzResearch.WordTrace]
  refine ⟨64266769117448355806292365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42844512744965570537528243 64266769117448355806292365)
  ·
    refine ⟨24100038419043133427359637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64266769117448355806292365 24100038419043133427359637)
    ·
      refine ⟨1129689300892646879407483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24100038419043133427359637 1129689300892646879407483)
      ·
        refine ⟨1694533951338970319111225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129689300892646879407483 1694533951338970319111225)
        ·
          refine ⟨1270900463504227739333419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694533951338970319111225 1270900463504227739333419)
          ·
            refine ⟨1906350695256341609000129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270900463504227739333419 1906350695256341609000129)
            ·
              refine ⟨1429763021442256206750097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1906350695256341609000129 1429763021442256206750097)
              ·
                refine ⟨1072322266081692155062573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429763021442256206750097 1072322266081692155062573)
                ·
                  refine ⟨402120849780634558148465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072322266081692155062573 402120849780634558148465)
                  ·
                    rfl

theorem cell21_1762037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_1762037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762037 prefixEnd_1762037 := by exact prefixLift 1762037
  have htrace : WordTrace (prefixWord ++ tailWord_1762037) baseStart_1762037 baseEnd_1762037 := by
    simpa [prefixWord, tailWord_1762037, baseEnd_1762037] using wordTrace_append hprefix tailTrace_1762037
  have hstable : (prefixWord ++ tailWord_1762037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762037).length < 2 ^ (prefixWord ++ tailWord_1762037).sum := by decide
  have hdescent : baseEnd_1762037 < baseStart_1762037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762056 : List Nat := [2, 1, 3, 2, 2, 2, 3, 6]
def baseStart_1762056 : Nat := 118140960795 + 1762056 * 2 ^ 59
def prefixEnd_1762056 : Nat := 4983230072969 + 3 ^ 40 * 1762056 * 2
def baseEnd_1762056 : Nat := 134041728613164915777253

theorem tailTrace_1762056 : CollatzResearch.WordTrace tailWord_1762056 prefixEnd_1762056 134041728613164915777253 := by
  unfold tailWord_1762056
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133731052189761025617011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42844974736253014700822681 32133731052189761025617011)
  ·
    refine ⟨48200596578284641538425517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32133731052189761025617011 48200596578284641538425517)
    ·
      refine ⟨18075223716856740576909569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48200596578284641538425517 18075223716856740576909569)
      ·
        refine ⟨13556417787642555432682177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18075223716856740576909569 13556417787642555432682177)
        ·
          refine ⟨10167313340731916574511633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13556417787642555432682177 10167313340731916574511633)
          ·
            refine ⟨7625485005548937430883725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10167313340731916574511633 7625485005548937430883725)
            ·
              refine ⟨2859556877080851536581397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7625485005548937430883725 2859556877080851536581397)
              ·
                refine ⟨134041728613164915777253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2859556877080851536581397 134041728613164915777253)
                ·
                  rfl

theorem cell21_1762056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_1762056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762056 prefixEnd_1762056 := by exact prefixLift 1762056
  have htrace : WordTrace (prefixWord ++ tailWord_1762056) baseStart_1762056 baseEnd_1762056 := by
    simpa [prefixWord, tailWord_1762056, baseEnd_1762056] using wordTrace_append hprefix tailTrace_1762056
  have hstable : (prefixWord ++ tailWord_1762056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762056).length < 2 ^ (prefixWord ++ tailWord_1762056).sum := by decide
  have hdescent : baseEnd_1762056 < baseStart_1762056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762093 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 4]
def baseStart_1762093 : Nat := 118140960795 + 1762093 * 2 ^ 59
def prefixEnd_1762093 : Nat := 4983230072969 + 3 ^ 40 * 1762093 * 2
def baseEnd_1762093 : Nat := 402133629743590905215017

theorem tailTrace_1762093 : CollatzResearch.WordTrace tailWord_1762093 prefixEnd_1762093 402133629743590905215017 := by
  unfold tailWord_1762093
  simp only [CollatzResearch.WordTrace]
  refine ⟨64268811605245477370330933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42845874403496984913553955 64268811605245477370330933)
  ·
    refine ⟨6025201087991763503468525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64268811605245477370330933 6025201087991763503468525)
    ·
      refine ⟨2259450407996911313800697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6025201087991763503468525 2259450407996911313800697)
      ·
        refine ⟨1694587805997683485350523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2259450407996911313800697 1694587805997683485350523)
        ·
          refine ⟨2541881708996525228025785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694587805997683485350523 2541881708996525228025785)
          ·
            refine ⟨1906411281747393921019339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541881708996525228025785 1906411281747393921019339)
            ·
              refine ⟨2859616922621090881529009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906411281747393921019339 2859616922621090881529009)
              ·
                refine ⟨2144712691965818161146757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859616922621090881529009 2144712691965818161146757)
                ·
                  refine ⟨402133629743590905215017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144712691965818161146757 402133629743590905215017)
                  ·
                    rfl

theorem cell21_1762093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_1762093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762093 prefixEnd_1762093 := by exact prefixLift 1762093
  have htrace : WordTrace (prefixWord ++ tailWord_1762093) baseStart_1762093 baseEnd_1762093 := by
    simpa [prefixWord, tailWord_1762093, baseEnd_1762093] using wordTrace_append hprefix tailTrace_1762093
  have hstable : (prefixWord ++ tailWord_1762093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762093).length < 2 ^ (prefixWord ++ tailWord_1762093).sum := by decide
  have hdescent : baseEnd_1762093 < baseStart_1762093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762115 : List Nat := [1, 1, 1, 3, 1, 4, 2, 8]
def baseStart_1762115 : Nat := 118140960795 + 1762115 * 2 ^ 59
def prefixEnd_1762115 : Nat := 4983230072969 + 3 ^ 40 * 1762115 * 2
def baseEnd_1762115 : Nat := 134046216814441251949435

theorem tailTrace_1762115 : CollatzResearch.WordTrace tailWord_1762115 prefixEnd_1762115 134046216814441251949435 := by
  unfold tailWord_1762115
  simp only [CollatzResearch.WordTrace]
  refine ⟨64269614011165775127631799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42846409340777183418421199 64269614011165775127631799)
  ·
    refine ⟨96404421016748662691447699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64269614011165775127631799 96404421016748662691447699)
    ·
      refine ⟨144606631525122994037171549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96404421016748662691447699 144606631525122994037171549)
      ·
        refine ⟨54227486821921122763939331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144606631525122994037171549 54227486821921122763939331)
        ·
          refine ⟨81341230232881684145908997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54227486821921122763939331 81341230232881684145908997)
          ·
            refine ⟨15251480668665315777357937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81341230232881684145908997 15251480668665315777357937)
            ·
              refine ⟨11438610501498986833018453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15251480668665315777357937 11438610501498986833018453)
              ·
                refine ⟨134046216814441251949435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11438610501498986833018453 134046216814441251949435)
                ·
                  rfl

theorem cell21_1762115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 8].length) (baseStart_1762115 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762115 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762115 prefixEnd_1762115 := by exact prefixLift 1762115
  have htrace : WordTrace (prefixWord ++ tailWord_1762115) baseStart_1762115 baseEnd_1762115 := by
    simpa [prefixWord, tailWord_1762115, baseEnd_1762115] using wordTrace_append hprefix tailTrace_1762115
  have hstable : (prefixWord ++ tailWord_1762115).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762115).length < 2 ^ (prefixWord ++ tailWord_1762115).sum := by decide
  have hdescent : baseEnd_1762115 < baseStart_1762115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762163 : List Nat := [1, 1, 1, 2, 2, 1, 4, 6, 3]
def baseStart_1762163 : Nat := 118140960795 + 1762163 * 2 ^ 59
def prefixEnd_1762163 : Nat := 4983230072969 + 3 ^ 40 * 1762163 * 2
def baseEnd_1762163 : Nat := 402149604697286339048207

theorem tailTrace_1762163 : CollatzResearch.WordTrace tailWord_1762163 prefixEnd_1762163 402149604697286339048207 := by
  unfold tailWord_1762163
  simp only [CollatzResearch.WordTrace]
  refine ⟨64271364714991879325379143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42847576476661252883586095 64271364714991879325379143)
  ·
    refine ⟨96407047072487818988068715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64271364714991879325379143 96407047072487818988068715)
    ·
      refine ⟨144610570608731728482103073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96407047072487818988068715 144610570608731728482103073)
      ·
        refine ⟨108457927956548796361577305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144610570608731728482103073 108457927956548796361577305)
        ·
          refine ⟨81343445967411597271182979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108457927956548796361577305 81343445967411597271182979)
          ·
            refine ⟨122015168951117395906774469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81343445967411597271182979 122015168951117395906774469)
            ·
              refine ⟨22877844178334511732520213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122015168951117395906774469 22877844178334511732520213)
              ·
                refine ⟨1072398945859430237461885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22877844178334511732520213 1072398945859430237461885)
                ·
                  refine ⟨402149604697286339048207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072398945859430237461885 402149604697286339048207)
                  ·
                    rfl

theorem cell21_1762163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].length) (baseStart_1762163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762163 prefixEnd_1762163 := by exact prefixLift 1762163
  have htrace : WordTrace (prefixWord ++ tailWord_1762163) baseStart_1762163 baseEnd_1762163 := by
    simpa [prefixWord, tailWord_1762163, baseEnd_1762163] using wordTrace_append hprefix tailTrace_1762163
  have hstable : (prefixWord ++ tailWord_1762163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762163).length < 2 ^ (prefixWord ++ tailWord_1762163).sum := by decide
  have hdescent : baseEnd_1762163 < baseStart_1762163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762225 : List Nat := [1, 2, 2, 4, 3, 2, 1, 6]
def baseStart_1762225 : Nat := 118140960795 + 1762225 * 2 ^ 59
def prefixEnd_1762225 : Nat := 4983230072969 + 3 ^ 40 * 1762225 * 2
def baseEnd_1762225 : Nat := 134054584647329336338249

theorem tailTrace_1762225 : CollatzResearch.WordTrace tailWord_1762225 prefixEnd_1762225 134054584647329336338249 := by
  unfold tailWord_1762225
  simp only [CollatzResearch.WordTrace]
  refine ⟨64273626040767263914136129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42849084027178175942757419 64273626040767263914136129)
  ·
    refine ⟨48205219530575447935602097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64273626040767263914136129 48205219530575447935602097)
    ·
      refine ⟨36153914647931585951701573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48205219530575447935602097 36153914647931585951701573)
      ·
        refine ⟨6778858996487172365944045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36153914647931585951701573 6778858996487172365944045)
        ·
          refine ⟨2542072123682689637229017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6778858996487172365944045 2542072123682689637229017)
          ·
            refine ⟨1906554092762017227921763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542072123682689637229017 1906554092762017227921763)
            ·
              refine ⟨2859831139143025841882645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906554092762017227921763 2859831139143025841882645)
              ·
                refine ⟨134054584647329336338249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2859831139143025841882645 134054584647329336338249)
                ·
                  rfl

theorem cell21_1762225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 6].length) (baseStart_1762225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762225 prefixEnd_1762225 := by exact prefixLift 1762225
  have htrace : WordTrace (prefixWord ++ tailWord_1762225) baseStart_1762225 baseEnd_1762225 := by
    simpa [prefixWord, tailWord_1762225, baseEnd_1762225] using wordTrace_append hprefix tailTrace_1762225
  have hstable : (prefixWord ++ tailWord_1762225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762225).length < 2 ^ (prefixWord ++ tailWord_1762225).sum := by decide
  have hdescent : baseEnd_1762225 < baseStart_1762225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762332 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1762332 : Nat := 118140960795 + 1762332 * 2 ^ 59
def prefixEnd_1762332 : Nat := 4983230072969 + 3 ^ 40 * 1762332 * 2
def baseEnd_1762332 : Nat := 402188172799779600731195

theorem tailTrace_1762332 : CollatzResearch.WordTrace tailWord_1762332 prefixEnd_1762332 402188172799779600731195 := by
  unfold tailWord_1762332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32138764325689810594140625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42851685767586414125520833 32138764325689810594140625)
  ·
    refine ⟨24104073244267357945605469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32138764325689810594140625 24104073244267357945605469)
    ·
      refine ⟨9039027466600259229602051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24104073244267357945605469 9039027466600259229602051)
      ·
        refine ⟨13558541199900388844403077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9039027466600259229602051 13558541199900388844403077)
        ·
          refine ⟨2542226474981322908325577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13558541199900388844403077 2542226474981322908325577)
          ·
            refine ⟨1906669856235992181244183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542226474981322908325577 1906669856235992181244183)
            ·
              refine ⟨2860004784353988271866275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906669856235992181244183 2860004784353988271866275)
              ·
                refine ⟨4290007176530982407799413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2860004784353988271866275 4290007176530982407799413)
                ·
                  refine ⟨402188172799779600731195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290007176530982407799413 402188172799779600731195)
                  ·
                    rfl

theorem cell21_1762332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1762332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762332 prefixEnd_1762332 := by exact prefixLift 1762332
  have htrace : WordTrace (prefixWord ++ tailWord_1762332) baseStart_1762332 baseEnd_1762332 := by
    simpa [prefixWord, tailWord_1762332, baseEnd_1762332] using wordTrace_append hprefix tailTrace_1762332
  have hstable : (prefixWord ++ tailWord_1762332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762332).length < 2 ^ (prefixWord ++ tailWord_1762332).sum := by decide
  have hdescent : baseEnd_1762332 < baseStart_1762332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762405 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 4]
def baseStart_1762405 : Nat := 118140960795 + 1762405 * 2 ^ 59
def prefixEnd_1762405 : Nat := 4983230072969 + 3 ^ 40 * 1762405 * 2
def baseEnd_1762405 : Nat := 402204832394347696014379

theorem tailTrace_1762405 : CollatzResearch.WordTrace tailWord_1762405 prefixEnd_1762405 402204832394347696014379 := by
  unfold tailWord_1762405
  simp only [CollatzResearch.WordTrace]
  refine ⟨64280191180115154655688669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42853460786743436437125779 64280191180115154655688669)
  ·
    refine ⟨24105071692543182995883251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64280191180115154655688669 24105071692543182995883251)
    ·
      refine ⟨36157607538814774493824877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24105071692543182995883251 36157607538814774493824877)
      ·
        refine ⟨13559102827055540435184329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36157607538814774493824877 13559102827055540435184329)
        ·
          refine ⟨10169327120291655326388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13559102827055540435184329 10169327120291655326388247)
          ·
            refine ⟨15253990680437482989582371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10169327120291655326388247 15253990680437482989582371)
            ·
              refine ⟨22880986020656224484373557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15253990680437482989582371 22880986020656224484373557)
              ·
                refine ⟨2145092439436521045410021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22880986020656224484373557 2145092439436521045410021)
                ·
                  refine ⟨402204832394347696014379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145092439436521045410021 402204832394347696014379)
                  ·
                    rfl

theorem cell21_1762405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_1762405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762405 prefixEnd_1762405 := by exact prefixLift 1762405
  have htrace : WordTrace (prefixWord ++ tailWord_1762405) baseStart_1762405 baseEnd_1762405 := by
    simpa [prefixWord, tailWord_1762405, baseEnd_1762405] using wordTrace_append hprefix tailTrace_1762405
  have hstable : (prefixWord ++ tailWord_1762405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762405).length < 2 ^ (prefixWord ++ tailWord_1762405).sum := by decide
  have hdescent : baseEnd_1762405 < baseStart_1762405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762408 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_1762408 : Nat := 118140960795 + 1762408 * 2 ^ 59
def prefixEnd_1762408 : Nat := 4983230072969 + 3 ^ 40 * 1762408 * 2
def baseEnd_1762408 : Nat := 402205517035220357464373

theorem tailTrace_1762408 : CollatzResearch.WordTrace tailWord_1762408 prefixEnd_1762408 402205517035220357464373 := by
  unfold tailWord_1762408
  simp only [CollatzResearch.WordTrace]
  refine ⟨32140150299552143084023939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42853533732736190778698585 32140150299552143084023939)
  ·
    refine ⟨48210225449328214626035909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32140150299552143084023939 48210225449328214626035909)
    ·
      refine ⟨9039417271749040242381733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48210225449328214626035909 9039417271749040242381733)
      ·
        refine ⟨1694890738452945045446575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9039417271749040242381733 1694890738452945045446575)
        ·
          refine ⟨2542336107679417568169863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694890738452945045446575 2542336107679417568169863)
          ·
            refine ⟨3813504161519126352254795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542336107679417568169863 3813504161519126352254795)
            ·
              refine ⟨5720256242278689528382193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3813504161519126352254795 5720256242278689528382193)
              ·
                refine ⟨4290192181709017146286645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5720256242278689528382193 4290192181709017146286645)
                ·
                  refine ⟨402205517035220357464373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4290192181709017146286645 402205517035220357464373)
                  ·
                    rfl

theorem cell21_1762408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_1762408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762408 prefixEnd_1762408 := by exact prefixLift 1762408
  have htrace : WordTrace (prefixWord ++ tailWord_1762408) baseStart_1762408 baseEnd_1762408 := by
    simpa [prefixWord, tailWord_1762408, baseEnd_1762408] using wordTrace_append hprefix tailTrace_1762408
  have hstable : (prefixWord ++ tailWord_1762408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762408).length < 2 ^ (prefixWord ++ tailWord_1762408).sum := by decide
  have hdescent : baseEnd_1762408 < baseStart_1762408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762481 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1762481 : Nat := 118140960795 + 1762481 * 2 ^ 59
def prefixEnd_1762481 : Nat := 4983230072969 + 3 ^ 40 * 1762481 * 2
def baseEnd_1762481 : Nat := 402222176629788452747557

theorem tailTrace_1762481 : CollatzResearch.WordTrace tailWord_1762481 prefixEnd_1762481 402222176629788452747557 := by
  unfold tailWord_1762481
  simp only [CollatzResearch.WordTrace]
  refine ⟨64282963127839819635455297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42855308751893213090303531 64282963127839819635455297)
  ·
    refine ⟨48212222345879864726591473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64282963127839819635455297 48212222345879864726591473)
    ·
      refine ⟨36159166759409898544943605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48212222345879864726591473 36159166759409898544943605)
      ·
        refine ⟨3389921883694677988588463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36159166759409898544943605 3389921883694677988588463)
        ·
          refine ⟨5084882825542016982882695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389921883694677988588463 5084882825542016982882695)
          ·
            refine ⟨7627324238313025474324043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5084882825542016982882695 7627324238313025474324043)
            ·
              refine ⟨11440986357469538211486065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7627324238313025474324043 11440986357469538211486065)
              ·
                refine ⟨8580739768102153658614549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11440986357469538211486065 8580739768102153658614549)
                ·
                  refine ⟨402222176629788452747557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8580739768102153658614549 402222176629788452747557)
                  ·
                    rfl

theorem cell21_1762481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1762481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762481 prefixEnd_1762481 := by exact prefixLift 1762481
  have htrace : WordTrace (prefixWord ++ tailWord_1762481) baseStart_1762481 baseEnd_1762481 := by
    simpa [prefixWord, tailWord_1762481, baseEnd_1762481] using wordTrace_append hprefix tailTrace_1762481
  have hstable : (prefixWord ++ tailWord_1762481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762481).length < 2 ^ (prefixWord ++ tailWord_1762481).sum := by decide
  have hdescent : baseEnd_1762481 < baseStart_1762481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762571 : List Nat := [1, 1, 1, 1, 5, 3, 3, 6]
def baseStart_1762571 : Nat := 118140960795 + 1762571 * 2 ^ 59
def prefixEnd_1762571 : Nat := 4983230072969 + 3 ^ 40 * 1762571 * 2
def baseEnd_1762571 : Nat := 134080905285322765415791

theorem tailTrace_1762571 : CollatzResearch.WordTrace tailWord_1762571 prefixEnd_1762571 134080905285322765415791 := by
  unfold tailWord_1762571
  simp only [CollatzResearch.WordTrace]
  refine ⟨64286245697513765006231567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42857497131675843337487711 64286245697513765006231567)
  ·
    refine ⟨96429368546270647509347351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64286245697513765006231567 96429368546270647509347351)
    ·
      refine ⟨144644052819405971264021027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96429368546270647509347351 144644052819405971264021027)
      ·
        refine ⟨216966079229108956896031541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144644052819405971264021027 216966079229108956896031541)
        ·
          refine ⟨20340569927728964709002957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216966079229108956896031541 20340569927728964709002957)
          ·
            refine ⟨7627713722898361765876109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20340569927728964709002957 7627713722898361765876109)
            ·
              refine ⟨2860392646086885662203541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7627713722898361765876109 2860392646086885662203541)
              ·
                refine ⟨134080905285322765415791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2860392646086885662203541 134080905285322765415791)
                ·
                  rfl

theorem cell21_1762571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 6].length) (baseStart_1762571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762571 prefixEnd_1762571 := by exact prefixLift 1762571
  have htrace : WordTrace (prefixWord ++ tailWord_1762571) baseStart_1762571 baseEnd_1762571 := by
    simpa [prefixWord, tailWord_1762571, baseEnd_1762571] using wordTrace_append hprefix tailTrace_1762571
  have hstable : (prefixWord ++ tailWord_1762571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762571).length < 2 ^ (prefixWord ++ tailWord_1762571).sum := by decide
  have hdescent : baseEnd_1762571 < baseStart_1762571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762647 : List Nat := [1, 1, 3, 2, 3, 3, 1, 7]
def baseStart_1762647 : Nat := 118140960795 + 1762647 * 2 ^ 59
def prefixEnd_1762647 : Nat := 4983230072969 + 3 ^ 40 * 1762647 * 2
def baseEnd_1762647 : Nat := 134086686697136350993517

theorem tailTrace_1762647 : CollatzResearch.WordTrace tailWord_1762647 prefixEnd_1762647 134086686697136350993517 := by
  unfold tailWord_1762647
  simp only [CollatzResearch.WordTrace]
  refine ⟨64289017645238429985998195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42859345096825619990665463 64289017645238429985998195)
  ·
    refine ⟨96433526467857644978997293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64289017645238429985998195 96433526467857644978997293)
    ·
      refine ⟨36162572425446616867123985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96433526467857644978997293 36162572425446616867123985)
      ·
        refine ⟨27121929319084962650342989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36162572425446616867123985 27121929319084962650342989)
        ·
          refine ⟨10170723494656860993878621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27121929319084962650342989 10170723494656860993878621)
          ·
            refine ⟨3814021310496322872704483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10170723494656860993878621 3814021310496322872704483)
            ·
              refine ⟨5721031965744484309056725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814021310496322872704483 5721031965744484309056725)
              ·
                refine ⟨134086686697136350993517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5721031965744484309056725 134086686697136350993517)
                ·
                  rfl

theorem cell21_1762647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_1762647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762647 prefixEnd_1762647 := by exact prefixLift 1762647
  have htrace : WordTrace (prefixWord ++ tailWord_1762647) baseStart_1762647 baseEnd_1762647 := by
    simpa [prefixWord, tailWord_1762647, baseEnd_1762647] using wordTrace_append hprefix tailTrace_1762647
  have hstable : (prefixWord ++ tailWord_1762647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762647).length < 2 ^ (prefixWord ++ tailWord_1762647).sum := by decide
  have hdescent : baseEnd_1762647 < baseStart_1762647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762664 : List Nat := [2, 1, 4, 2, 3, 2, 7]
def baseStart_1762664 : Nat := 118140960795 + 1762664 * 2 ^ 59
def prefixEnd_1762664 : Nat := 4983230072969 + 3 ^ 40 * 1762664 * 2
def baseEnd_1762664 : Nat := 44695993302557866799687

theorem tailTrace_1762664 : CollatzResearch.WordTrace tailWord_1762664 prefixEnd_1762664 44695993302557866799687 := by
  unfold tailWord_1762664
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144818843088420944683523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42859758457451227926244697 32144818843088420944683523)
  ·
    refine ⟨48217228264632631417025285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32144818843088420944683523 48217228264632631417025285)
    ·
      refine ⟨9040730299618618390692241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48217228264632631417025285 9040730299618618390692241)
      ·
        refine ⟨6780547724713963793019181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9040730299618618390692241 6780547724713963793019181)
        ·
          refine ⟨2542705396767736422382193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6780547724713963793019181 2542705396767736422382193)
          ·
            refine ⟨1907029047575802316786645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542705396767736422382193 1907029047575802316786645)
            ·
              refine ⟨44695993302557866799687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1907029047575802316786645 44695993302557866799687)
              ·
                rfl

theorem cell21_1762664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 7].length) (baseStart_1762664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762664 prefixEnd_1762664 := by exact prefixLift 1762664
  have htrace : WordTrace (prefixWord ++ tailWord_1762664) baseStart_1762664 baseEnd_1762664 := by
    simpa [prefixWord, tailWord_1762664, baseEnd_1762664] using wordTrace_append hprefix tailTrace_1762664
  have hstable : (prefixWord ++ tailWord_1762664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762664).length < 2 ^ (prefixWord ++ tailWord_1762664).sum := by decide
  have hdescent : baseEnd_1762664 < baseStart_1762664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762670 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_1762670 : Nat := 118140960795 + 1762670 * 2 ^ 59
def prefixEnd_1762670 : Nat := 4983230072969 + 3 ^ 40 * 1762670 * 2
def baseEnd_1762670 : Nat := 402265309004766124097171

theorem tailTrace_1762670 : CollatzResearch.WordTrace tailWord_1762670 prefixEnd_1762670 402265309004766124097171 := by
  unfold tailWord_1762670
  simp only [CollatzResearch.WordTrace]
  refine ⟨8036232065519388114260683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42859904349436736609390309 8036232065519388114260683)
  ·
    refine ⟨12054348098279082171391025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8036232065519388114260683 12054348098279082171391025)
    ·
      refine ⟨9040761073709311628543269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12054348098279082171391025 9040761073709311628543269)
      ·
        refine ⟨1695142701320495930351863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9040761073709311628543269 1695142701320495930351863)
        ·
          refine ⟨2542714051980743895527795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695142701320495930351863 2542714051980743895527795)
          ·
            refine ⟨3814071077971115843291693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542714051980743895527795 3814071077971115843291693)
            ·
              refine ⟨1430276654239168441234385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3814071077971115843291693 1430276654239168441234385)
              ·
                refine ⟨1072707490679376330925789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430276654239168441234385 1072707490679376330925789)
                ·
                  refine ⟨402265309004766124097171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072707490679376330925789 402265309004766124097171)
                  ·
                    rfl

theorem cell21_1762670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_1762670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762670 prefixEnd_1762670 := by exact prefixLift 1762670
  have htrace : WordTrace (prefixWord ++ tailWord_1762670) baseStart_1762670 baseEnd_1762670 := by
    simpa [prefixWord, tailWord_1762670, baseEnd_1762670] using wordTrace_append hprefix tailTrace_1762670
  have hstable : (prefixWord ++ tailWord_1762670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762670).length < 2 ^ (prefixWord ++ tailWord_1762670).sum := by decide
  have hdescent : baseEnd_1762670 < baseStart_1762670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762785 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_1762785 : Nat := 118140960795 + 1762785 * 2 ^ 59
def prefixEnd_1762785 : Nat := 4983230072969 + 3 ^ 40 * 1762785 * 2
def baseEnd_1762785 : Nat := 402291553571551479680269

theorem tailTrace_1762785 : CollatzResearch.WordTrace tailWord_1762785 prefixEnd_1762785 402291553571551479680269 := by
  unfold tailWord_1762785
  simp only [CollatzResearch.WordTrace]
  refine ⟨64294050918738479554521809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42862700612492319703014539 64294050918738479554521809)
  ·
    refine ⟨48220538189053859665891357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64294050918738479554521809 48220538189053859665891357)
    ·
      refine ⟨18082701820895197374709259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48220538189053859665891357 18082701820895197374709259)
      ·
        refine ⟨27124052731342796062063889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18082701820895197374709259 27124052731342796062063889)
        ·
          refine ⟨20343039548507097046547917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27124052731342796062063889 20343039548507097046547917)
          ·
            refine ⟨7628639830690161392455469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20343039548507097046547917 7628639830690161392455469)
            ·
              refine ⟨2860739936508810522170801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7628639830690161392455469 2860739936508810522170801)
              ·
                refine ⟨2145554952381607891628101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2860739936508810522170801 2145554952381607891628101)
                ·
                  refine ⟨402291553571551479680269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145554952381607891628101 402291553571551479680269)
                  ·
                    rfl

theorem cell21_1762785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_1762785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762785 prefixEnd_1762785 := by exact prefixLift 1762785
  have htrace : WordTrace (prefixWord ++ tailWord_1762785) baseStart_1762785 baseEnd_1762785 := by
    simpa [prefixWord, tailWord_1762785, baseEnd_1762785] using wordTrace_append hprefix tailTrace_1762785
  have hstable : (prefixWord ++ tailWord_1762785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762785).length < 2 ^ (prefixWord ++ tailWord_1762785).sum := by decide
  have hdescent : baseEnd_1762785 < baseStart_1762785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762844 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1762844 : Nat := 118140960795 + 1762844 * 2 ^ 59
def prefixEnd_1762844 : Nat := 4983230072969 + 3 ^ 40 * 1762844 * 2
def baseEnd_1762844 : Nat := 402305018175380488196815

theorem tailTrace_1762844 : CollatzResearch.WordTrace tailWord_1762844 prefixEnd_1762844 402305018175380488196815 := by
  unfold tailWord_1762844
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148101412762366315459793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42864135217016488420613057 32148101412762366315459793)
  ·
    refine ⟨24111076059571774736594845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32148101412762366315459793 24111076059571774736594845)
    ·
      refine ⟨9041653522339415526223067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24111076059571774736594845 9041653522339415526223067)
      ·
        refine ⟨13562480283509123289334601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041653522339415526223067 13562480283509123289334601)
        ·
          refine ⟨10171860212631842467000951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562480283509123289334601 10171860212631842467000951)
          ·
            refine ⟨15257790318947763700501427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10171860212631842467000951 15257790318947763700501427)
            ·
              refine ⟨22886685478421645550752141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15257790318947763700501427 22886685478421645550752141)
              ·
                refine ⟨8582507054408117081532053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22886685478421645550752141 8582507054408117081532053)
                ·
                  refine ⟨402305018175380488196815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8582507054408117081532053 402305018175380488196815)
                  ·
                    rfl

theorem cell21_1762844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1762844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762844 prefixEnd_1762844 := by exact prefixLift 1762844
  have htrace : WordTrace (prefixWord ++ tailWord_1762844) baseStart_1762844 baseEnd_1762844 := by
    simpa [prefixWord, tailWord_1762844, baseEnd_1762844] using wordTrace_append hprefix tailTrace_1762844
  have hstable : (prefixWord ++ tailWord_1762844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762844).length < 2 ^ (prefixWord ++ tailWord_1762844).sum := by decide
  have hdescent : baseEnd_1762844 < baseStart_1762844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762954 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_1762954 : Nat := 118140960795 + 1762954 * 2 ^ 59
def prefixEnd_1762954 : Nat := 4983230072969 + 3 ^ 40 * 1762954 * 2
def baseEnd_1762954 : Nat := 402330121674044741363257

theorem tailTrace_1762954 : CollatzResearch.WordTrace tailWord_1762954 prefixEnd_1762954 402330121674044741363257 := by
  unfold tailWord_1762954
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075053713781555354355979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42866809903417480944949277 16075053713781555354355979)
  ·
    refine ⟨24112580570672333031533969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16075053713781555354355979 24112580570672333031533969)
    ·
      refine ⟨18084435428004249773650477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24112580570672333031533969 18084435428004249773650477)
      ·
        refine ⟨6781663285501593665118929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18084435428004249773650477 6781663285501593665118929)
        ·
          refine ⟨5086247464126195248839197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6781663285501593665118929 5086247464126195248839197)
          ·
            refine ⟨1907342799047323218314699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5086247464126195248839197 1907342799047323218314699)
            ·
              refine ⟨2861014198570984827472049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907342799047323218314699 2861014198570984827472049)
              ·
                refine ⟨2145760648928238620604037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861014198570984827472049 2145760648928238620604037)
                ·
                  refine ⟨402330121674044741363257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145760648928238620604037 402330121674044741363257)
                  ·
                    rfl

theorem cell21_1762954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_1762954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762954 prefixEnd_1762954 := by exact prefixLift 1762954
  have htrace : WordTrace (prefixWord ++ tailWord_1762954) baseStart_1762954 baseEnd_1762954 := by
    simpa [prefixWord, tailWord_1762954, baseEnd_1762954] using wordTrace_append hprefix tailTrace_1762954
  have hstable : (prefixWord ++ tailWord_1762954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762954).length < 2 ^ (prefixWord ++ tailWord_1762954).sum := by decide
  have hdescent : baseEnd_1762954 < baseStart_1762954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1762999 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 3]
def baseStart_1762999 : Nat := 118140960795 + 1762999 * 2 ^ 59
def prefixEnd_1762999 : Nat := 4983230072969 + 3 ^ 40 * 1762999 * 2
def baseEnd_1762999 : Nat := 402340391287134663113165

theorem tailTrace_1762999 : CollatzResearch.WordTrace tailWord_1762999 prefixEnd_1762999 402340391287134663113165 := by
  unfold tailWord_1762999
  simp only [CollatzResearch.WordTrace]
  refine ⟨64301856139963194102812051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42867904093308796068541367 64301856139963194102812051)
  ·
    refine ⟨96452784209944791154218077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64301856139963194102812051 96452784209944791154218077)
    ·
      refine ⟨36169794078729296682831779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96452784209944791154218077 36169794078729296682831779)
      ·
        refine ⟨54254691118093945024247669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36169794078729296682831779 54254691118093945024247669)
        ·
          refine ⟨5086377292321307346023219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54254691118093945024247669 5086377292321307346023219)
          ·
            refine ⟨7629565938481961019034829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086377292321307346023219 7629565938481961019034829)
            ·
              refine ⟨2861087226930735382138061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7629565938481961019034829 2861087226930735382138061)
              ·
                refine ⟨1072907710099025768301773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2861087226930735382138061 1072907710099025768301773)
                ·
                  refine ⟨402340391287134663113165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072907710099025768301773 402340391287134663113165)
                  ·
                    rfl

theorem cell21_1762999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 3].length) (baseStart_1762999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1762999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1762999 prefixEnd_1762999 := by exact prefixLift 1762999
  have htrace : WordTrace (prefixWord ++ tailWord_1762999) baseStart_1762999 baseEnd_1762999 := by
    simpa [prefixWord, tailWord_1762999, baseEnd_1762999] using wordTrace_append hprefix tailTrace_1762999
  have hstable : (prefixWord ++ tailWord_1762999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1762999).length < 2 ^ (prefixWord ++ tailWord_1762999).sum := by decide
  have hdescent : baseEnd_1762999 < baseStart_1762999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1762999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763075 : List Nat := [1, 1, 1, 3, 2, 2, 6, 2, 3]
def baseStart_1763075 : Nat := 118140960795 + 1763075 * 2 ^ 59
def prefixEnd_1763075 : Nat := 4983230072969 + 3 ^ 40 * 1763075 * 2
def baseEnd_1763075 : Nat := 402357735522575419846343

theorem tailTrace_1763075 : CollatzResearch.WordTrace tailWord_1763075 prefixEnd_1763075 402357735522575419846343 := by
  unfold tailWord_1763075
  simp only [CollatzResearch.WordTrace]
  refine ⟨64304628087687859082578679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42869752058458572721719119 64304628087687859082578679)
  ·
    refine ⟨96456942131531788623868019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64304628087687859082578679 96456942131531788623868019)
    ·
      refine ⟨144685413197297682935802029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96456942131531788623868019 144685413197297682935802029)
      ·
        refine ⟨54257029948986631100925761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144685413197297682935802029 54257029948986631100925761)
        ·
          refine ⟨40692772461739973325694321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54257029948986631100925761 40692772461739973325694321)
          ·
            refine ⟨30519579346304979994270741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40692772461739973325694321 30519579346304979994270741)
            ·
              refine ⟨1430605281858045937231441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30519579346304979994270741 1430605281858045937231441)
              ·
                refine ⟨1072953961393534452923581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430605281858045937231441 1072953961393534452923581)
                ·
                  refine ⟨402357735522575419846343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072953961393534452923581 402357735522575419846343)
                  ·
                    rfl

theorem cell21_1763075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 3].length) (baseStart_1763075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763075 prefixEnd_1763075 := by exact prefixLift 1763075
  have htrace : WordTrace (prefixWord ++ tailWord_1763075) baseStart_1763075 baseEnd_1763075 := by
    simpa [prefixWord, tailWord_1763075, baseEnd_1763075] using wordTrace_append hprefix tailTrace_1763075
  have hstable : (prefixWord ++ tailWord_1763075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763075).length < 2 ^ (prefixWord ++ tailWord_1763075).sum := by decide
  have hdescent : baseEnd_1763075 < baseStart_1763075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763103 : List Nat := [1, 1, 2, 4, 2, 1, 5, 5]
def baseStart_1763103 : Nat := 118140960795 + 1763103 * 2 ^ 59
def prefixEnd_1763103 : Nat := 4983230072969 + 3 ^ 40 * 1763103 * 2
def baseEnd_1763103 : Nat := 134121375168017864459873

theorem tailTrace_1763103 : CollatzResearch.WordTrace tailWord_1763103 prefixEnd_1763103 134121375168017864459873 := by
  unfold tailWord_1763103
  simp only [CollatzResearch.WordTrace]
  refine ⟨64305649331586419864597963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42870432887724279909731975 64305649331586419864597963)
  ·
    refine ⟨96458473997379629796896945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64305649331586419864597963 96458473997379629796896945)
    ·
      refine ⟨72343855498034722347672709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96458473997379629796896945 72343855498034722347672709)
      ·
        refine ⟨13564472905881510440188633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72343855498034722347672709 13564472905881510440188633)
        ·
          refine ⟨10173354679411132830141475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13564472905881510440188633 10173354679411132830141475)
          ·
            refine ⟨15260032019116699245212213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10173354679411132830141475 15260032019116699245212213)
            ·
              refine ⟨1430628001792190554238645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15260032019116699245212213 1430628001792190554238645)
              ·
                refine ⟨134121375168017864459873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1430628001792190554238645 134121375168017864459873)
                ·
                  rfl

theorem cell21_1763103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 5].length) (baseStart_1763103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763103 prefixEnd_1763103 := by exact prefixLift 1763103
  have htrace : WordTrace (prefixWord ++ tailWord_1763103) baseStart_1763103 baseEnd_1763103 := by
    simpa [prefixWord, tailWord_1763103, baseEnd_1763103] using wordTrace_append hprefix tailTrace_1763103
  have hstable : (prefixWord ++ tailWord_1763103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763103).length < 2 ^ (prefixWord ++ tailWord_1763103).sum := by decide
  have hdescent : baseEnd_1763103 < baseStart_1763103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763134 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1763134 : Nat := 118140960795 + 1763134 * 2 ^ 59
def prefixEnd_1763134 : Nat := 4983230072969 + 3 ^ 40 * 1763134 * 2
def baseEnd_1763134 : Nat := 402371200126404428362889

theorem tailTrace_1763134 : CollatzResearch.WordTrace tailWord_1763134 prefixEnd_1763134 402371200126404428362889 := by
  unfold tailWord_1763134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038347499309264019872057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42871186662982741439317637 8038347499309264019872057)
  ·
    refine ⟨6028760624481948014904043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8038347499309264019872057 6028760624481948014904043)
    ·
      refine ⟨9043140936722922022356065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6028760624481948014904043 9043140936722922022356065)
      ·
        refine ⟨6782355702542191516767049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9043140936722922022356065 6782355702542191516767049)
        ·
          refine ⟨5086766776906643637575287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6782355702542191516767049 5086766776906643637575287)
          ·
            refine ⟨7630150165359965456362931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086766776906643637575287 7630150165359965456362931)
            ·
              refine ⟨11445225248039948184544397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7630150165359965456362931 11445225248039948184544397)
              ·
                refine ⟨4291959468014980569204149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11445225248039948184544397 4291959468014980569204149)
                ·
                  refine ⟨402371200126404428362889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291959468014980569204149 402371200126404428362889)
                  ·
                    rfl

theorem cell21_1763134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1763134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763134 prefixEnd_1763134 := by exact prefixLift 1763134
  have htrace : WordTrace (prefixWord ++ tailWord_1763134) baseStart_1763134 baseEnd_1763134 := by
    simpa [prefixWord, tailWord_1763134, baseEnd_1763134] using wordTrace_append hprefix tailTrace_1763134
  have hstable : (prefixWord ++ tailWord_1763134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763134).length < 2 ^ (prefixWord ++ tailWord_1763134).sum := by decide
  have hdescent : baseEnd_1763134 < baseStart_1763134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763162 : List Nat := [3, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1763162 : Nat := 118140960795 + 1763162 * 2 ^ 59
def prefixEnd_1763162 : Nat := 4983230072969 + 3 ^ 40 * 1763162 * 2
def baseEnd_1763162 : Nat := 134125863369294200632055

theorem tailTrace_1763162 : CollatzResearch.WordTrace tailWord_1763162 prefixEnd_1763162 134125863369294200632055 := by
  unfold tailWord_1763162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16076950309593168235248935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42871867492248448627330493 16076950309593168235248935)
  ·
    refine ⟨24115425464389752352873403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16076950309593168235248935 24115425464389752352873403)
    ·
      refine ⟨36173138196584628529310105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24115425464389752352873403 36173138196584628529310105)
      ·
        refine ⟨27129853647438471396982579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36173138196584628529310105 27129853647438471396982579)
        ·
          refine ⟨40694780471157707095473869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27129853647438471396982579 40694780471157707095473869)
          ·
            refine ⟨15260542676684140160802701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40694780471157707095473869 15260542676684140160802701)
            ·
              refine ⟨5722703503756552560301013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15260542676684140160802701 5722703503756552560301013)
              ·
                refine ⟨134125863369294200632055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5722703503756552560301013 134125863369294200632055)
                ·
                  rfl

theorem cell21_1763162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1763162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763162 prefixEnd_1763162 := by exact prefixLift 1763162
  have htrace : WordTrace (prefixWord ++ tailWord_1763162) baseStart_1763162 baseEnd_1763162 := by
    simpa [prefixWord, tailWord_1763162, baseEnd_1763162] using wordTrace_append hprefix tailTrace_1763162
  have hstable : (prefixWord ++ tailWord_1763162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763162).length < 2 ^ (prefixWord ++ tailWord_1763162).sum := by decide
  have hdescent : baseEnd_1763162 < baseStart_1763162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763292 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 4]
def baseStart_1763292 : Nat := 118140960795 + 1763292 * 2 ^ 59
def prefixEnd_1763292 : Nat := 4983230072969 + 3 ^ 40 * 1763292 * 2
def baseEnd_1763292 : Nat := 402407257879031264729233

theorem tailTrace_1763292 : CollatzResearch.WordTrace tailWord_1763292 prefixEnd_1763292 402407257879031264729233 := by
  unfold tailWord_1763292
  simp only [CollatzResearch.WordTrace]
  refine ⟨32156271363950852571614065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42875028485267803428818753 32156271363950852571614065)
  ·
    refine ⟨24117203522963139428710549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32156271363950852571614065 24117203522963139428710549)
    ·
      refine ⟨1130493915138897160720807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24117203522963139428710549 1130493915138897160720807)
      ·
        refine ⟨1695740872708345741081211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130493915138897160720807 1695740872708345741081211)
        ·
          refine ⟨2543611309062518611621817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695740872708345741081211 2543611309062518611621817)
          ·
            refine ⟨1907708481796888958716363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543611309062518611621817 1907708481796888958716363)
            ·
              refine ⟨2861562722695333438074545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907708481796888958716363 2861562722695333438074545)
              ·
                refine ⟨2146172042021500078555909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2861562722695333438074545 2146172042021500078555909)
                ·
                  refine ⟨402407257879031264729233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146172042021500078555909 402407257879031264729233)
                  ·
                    rfl

theorem cell21_1763292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_1763292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763292 prefixEnd_1763292 := by exact prefixLift 1763292
  have htrace : WordTrace (prefixWord ++ tailWord_1763292) baseStart_1763292 baseEnd_1763292 := by
    simpa [prefixWord, tailWord_1763292, baseEnd_1763292] using wordTrace_append hprefix tailTrace_1763292
  have hstable : (prefixWord ++ tailWord_1763292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763292).length < 2 ^ (prefixWord ++ tailWord_1763292).sum := by decide
  have hdescent : baseEnd_1763292 < baseStart_1763292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763328 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1763328 : Nat := 118140960795 + 1763328 * 2 ^ 59
def prefixEnd_1763328 : Nat := 4983230072969 + 3 ^ 40 * 1763328 * 2
def baseEnd_1763328 : Nat := 402415473569503202129159

theorem tailTrace_1763328 : CollatzResearch.WordTrace tailWord_1763328 prefixEnd_1763328 402415473569503202129159 := by
  unfold tailWord_1763328
  simp only [CollatzResearch.WordTrace]
  refine ⟨32156927877885641645769319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42875903837180855527692425 32156927877885641645769319)
  ·
    refine ⟨48235391816828462468653979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32156927877885641645769319 48235391816828462468653979)
    ·
      refine ⟨72353087725242693702980969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48235391816828462468653979 72353087725242693702980969)
      ·
        refine ⟨54264815793932020277235727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72353087725242693702980969 54264815793932020277235727)
        ·
          refine ⟨81397223690898030415853591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54264815793932020277235727 81397223690898030415853591)
          ·
            refine ⟨122095835536347045623780387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81397223690898030415853591 122095835536347045623780387)
            ·
              refine ⟨183143753304520568435670581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122095835536347045623780387 183143753304520568435670581)
              ·
                refine ⟨17169726872298803290844117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 183143753304520568435670581 17169726872298803290844117)
                ·
                  refine ⟨402415473569503202129159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17169726872298803290844117 402415473569503202129159)
                  ·
                    rfl

theorem cell21_1763328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1763328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763328 prefixEnd_1763328 := by exact prefixLift 1763328
  have htrace : WordTrace (prefixWord ++ tailWord_1763328) baseStart_1763328 baseEnd_1763328 := by
    simpa [prefixWord, tailWord_1763328, baseEnd_1763328] using wordTrace_append hprefix tailTrace_1763328
  have hstable : (prefixWord ++ tailWord_1763328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763328).length < 2 ^ (prefixWord ++ tailWord_1763328).sum := by decide
  have hdescent : baseEnd_1763328 < baseStart_1763328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763359 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 6]
def baseStart_1763359 : Nat := 118140960795 + 1763359 * 2 ^ 59
def prefixEnd_1763359 : Nat := 4983230072969 + 3 ^ 40 * 1763359 * 2
def baseEnd_1763359 : Nat := 402422548191854037112429

theorem tailTrace_1763359 : CollatzResearch.WordTrace tailWord_1763359 prefixEnd_1763359 402422548191854037112429 := by
  unfold tailWord_1763359
  simp only [CollatzResearch.WordTrace]
  refine ⟨64314986418658975585917131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42876657612439317057278087 64314986418658975585917131)
  ·
    refine ⟨96472479627988463378875697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64314986418658975585917131 96472479627988463378875697)
    ·
      refine ⟨72354359720991347534156773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96472479627988463378875697 72354359720991347534156773)
      ·
        refine ⟨13566442447685877662654395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72354359720991347534156773 13566442447685877662654395)
        ·
          refine ⟨20349663671528816493981593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13566442447685877662654395 20349663671528816493981593)
          ·
            refine ⟨15262247753646612370486195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20349663671528816493981593 15262247753646612370486195)
            ·
              refine ⟨22893371630469918555729293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15262247753646612370486195 22893371630469918555729293)
              ·
                refine ⟨8585014361426219458398485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22893371630469918555729293 8585014361426219458398485)
                ·
                  refine ⟨402422548191854037112429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8585014361426219458398485 402422548191854037112429)
                  ·
                    rfl

theorem cell21_1763359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_1763359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763359 prefixEnd_1763359 := by exact prefixLift 1763359
  have htrace : WordTrace (prefixWord ++ tailWord_1763359) baseStart_1763359 baseEnd_1763359 := by
    simpa [prefixWord, tailWord_1763359, baseEnd_1763359] using wordTrace_append hprefix tailTrace_1763359
  have hstable : (prefixWord ++ tailWord_1763359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763359).length < 2 ^ (prefixWord ++ tailWord_1763359).sum := by decide
  have hdescent : baseEnd_1763359 < baseStart_1763359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763368 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_1763368 : Nat := 118140960795 + 1763368 * 2 ^ 59
def prefixEnd_1763368 : Nat := 4983230072969 + 3 ^ 40 * 1763368 * 2
def baseEnd_1763368 : Nat := 402424602114472021462411

theorem tailTrace_1763368 : CollatzResearch.WordTrace tailWord_1763368 prefixEnd_1763368 402424602114472021462411 := by
  unfold tailWord_1763368
  simp only [CollatzResearch.WordTrace]
  refine ⟨32157657337813185061497379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42876876450417580081996505 32157657337813185061497379)
  ·
    refine ⟨48236486006719777592246069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32157657337813185061497379 48236486006719777592246069)
    ·
      refine ⟨4522170563129979149273069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48236486006719777592246069 4522170563129979149273069)
      ·
        refine ⟨1695813961173742180977401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4522170563129979149273069 1695813961173742180977401)
        ·
          refine ⟨1271860470880306635733051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1695813961173742180977401 1271860470880306635733051)
          ·
            refine ⟨1907790706320459953599577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271860470880306635733051 1907790706320459953599577)
            ·
              refine ⟨1430843029740344965199683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907790706320459953599577 1430843029740344965199683)
              ·
                refine ⟨2146264544610517447799525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430843029740344965199683 2146264544610517447799525)
                ·
                  refine ⟨402424602114472021462411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146264544610517447799525 402424602114472021462411)
                  ·
                    rfl

theorem cell21_1763368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_1763368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763368 prefixEnd_1763368 := by exact prefixLift 1763368
  have htrace : WordTrace (prefixWord ++ tailWord_1763368) baseStart_1763368 baseEnd_1763368 := by
    simpa [prefixWord, tailWord_1763368, baseEnd_1763368] using wordTrace_append hprefix tailTrace_1763368
  have hstable : (prefixWord ++ tailWord_1763368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763368).length < 2 ^ (prefixWord ++ tailWord_1763368).sum := by decide
  have hdescent : baseEnd_1763368 < baseStart_1763368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763376 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_1763376 : Nat := 118140960795 + 1763376 * 2 ^ 59
def prefixEnd_1763376 : Nat := 4983230072969 + 3 ^ 40 * 1763376 * 2
def baseEnd_1763376 : Nat := 402426427823465785329061

theorem tailTrace_1763376 : CollatzResearch.WordTrace tailWord_1763376 prefixEnd_1763376 402426427823465785329061 := by
  unfold tailWord_1763376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32157803229798693744642991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42877070973064924992857321 32157803229798693744642991)
  ·
    refine ⟨48236704844698040616964487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32157803229798693744642991 48236704844698040616964487)
    ·
      refine ⟨72355057267047060925446731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48236704844698040616964487 72355057267047060925446731)
      ·
        refine ⟨108532585900570591388170097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72355057267047060925446731 108532585900570591388170097)
        ·
          refine ⟨81399439425427943541127573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108532585900570591388170097 81399439425427943541127573)
          ·
            refine ⟨3815598723066934853490355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81399439425427943541127573 3815598723066934853490355)
            ·
              refine ⟨5723398084600402280235533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3815598723066934853490355 5723398084600402280235533)
              ·
                refine ⟨2146274281725150855088325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5723398084600402280235533 2146274281725150855088325)
                ·
                  refine ⟨402426427823465785329061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146274281725150855088325 402426427823465785329061)
                  ·
                    rfl

theorem cell21_1763376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_1763376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763376 prefixEnd_1763376 := by exact prefixLift 1763376
  have htrace : WordTrace (prefixWord ++ tailWord_1763376) baseStart_1763376 baseEnd_1763376 := by
    simpa [prefixWord, tailWord_1763376, baseEnd_1763376] using wordTrace_append hprefix tailTrace_1763376
  have hstable : (prefixWord ++ tailWord_1763376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763376).length < 2 ^ (prefixWord ++ tailWord_1763376).sum := by decide
  have hdescent : baseEnd_1763376 < baseStart_1763376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763466 : List Nat := [3, 1, 2, 3, 1, 3, 8]
def baseStart_1763466 : Nat := 118140960795 + 1763466 * 2 ^ 59
def prefixEnd_1763466 : Nat := 4983230072969 + 3 ^ 40 * 1763466 * 2
def baseEnd_1763466 : Nat := 44716329672182847647653

theorem tailTrace_1763466 : CollatzResearch.WordTrace tailWord_1763466 prefixEnd_1763466 44716329672182847647653 := by
  unfold tailWord_1763466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079722257317833215015563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42879259352847555240041501 16079722257317833215015563)
  ·
    refine ⟨24119583385976749822523345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079722257317833215015563 24119583385976749822523345)
    ·
      refine ⟨18089687539482562366892509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24119583385976749822523345 18089687539482562366892509)
      ·
        refine ⟨6783632827305960887584691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18089687539482562366892509 6783632827305960887584691)
        ·
          refine ⟨10175449240958941331377037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783632827305960887584691 10175449240958941331377037)
          ·
            refine ⟨3815793465359602999266389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10175449240958941331377037 3815793465359602999266389)
            ·
              refine ⟨44716329672182847647653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3815793465359602999266389 44716329672182847647653)
              ·
                rfl

theorem cell21_1763466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 8].length) (baseStart_1763466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763466 prefixEnd_1763466 := by exact prefixLift 1763466
  have htrace : WordTrace (prefixWord ++ tailWord_1763466) baseStart_1763466 baseEnd_1763466 := by
    simpa [prefixWord, tailWord_1763466, baseEnd_1763466] using wordTrace_append hprefix tailTrace_1763466
  have hstable : (prefixWord ++ tailWord_1763466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763466).length < 2 ^ (prefixWord ++ tailWord_1763466).sum := by decide
  have hdescent : baseEnd_1763466 < baseStart_1763466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763511 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_1763511 : Nat := 118140960795 + 1763511 * 2 ^ 59
def prefixEnd_1763511 : Nat := 4983230072969 + 3 ^ 40 * 1763511 * 2
def baseEnd_1763511 : Nat := 402457236662735550578785

theorem tailTrace_1763511 : CollatzResearch.WordTrace tailWord_1763511 prefixEnd_1763511 402457236662735550578785 := by
  unfold tailWord_1763511
  simp only [CollatzResearch.WordTrace]
  refine ⟨64320530314108305545450387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42880353542738870363633591 64320530314108305545450387)
  ·
    refine ⟨96480795471162458318175581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64320530314108305545450387 96480795471162458318175581)
    ·
      refine ⟨36180298301685921869315843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96480795471162458318175581 36180298301685921869315843)
      ·
        refine ⟨54270447452528882803973765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36180298301685921869315843 54270447452528882803973765)
        ·
          refine ⟨10175708897349165525745081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54270447452528882803973765 10175708897349165525745081)
          ·
            refine ⟨7631781673011874144308811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10175708897349165525745081 7631781673011874144308811)
            ·
              refine ⟨11447672509517811216463217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7631781673011874144308811 11447672509517811216463217)
              ·
                refine ⟨8585754382138358412347413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447672509517811216463217 8585754382138358412347413)
                ·
                  refine ⟨402457236662735550578785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8585754382138358412347413 402457236662735550578785)
                  ·
                    rfl

theorem cell21_1763511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_1763511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763511 prefixEnd_1763511 := by exact prefixLift 1763511
  have htrace : WordTrace (prefixWord ++ tailWord_1763511) baseStart_1763511 baseEnd_1763511 := by
    simpa [prefixWord, tailWord_1763511, baseEnd_1763511] using wordTrace_append hprefix tailTrace_1763511
  have hstable : (prefixWord ++ tailWord_1763511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763511).length < 2 ^ (prefixWord ++ tailWord_1763511).sum := by decide
  have hdescent : baseEnd_1763511 < baseStart_1763511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763514 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1763514 : Nat := 118140960795 + 1763514 * 2 ^ 59
def prefixEnd_1763514 : Nat := 4983230072969 + 3 ^ 40 * 1763514 * 2
def baseEnd_1763514 : Nat := 402457921303608212028779

theorem tailTrace_1763514 : CollatzResearch.WordTrace tailWord_1763514 prefixEnd_1763514 402457921303608212028779 := by
  unfold tailWord_1763514
  simp only [CollatzResearch.WordTrace]
  refine ⟨16080159933274359264452399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42880426488731624705206397 16080159933274359264452399)
  ·
    refine ⟨24120239899911538896678599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16080159933274359264452399 24120239899911538896678599)
    ·
      refine ⟨36180359849867308345017899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24120239899911538896678599 36180359849867308345017899)
      ·
        refine ⟨54270539774800962517526849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36180359849867308345017899 54270539774800962517526849)
        ·
          refine ⟨40702904831100721888145137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54270539774800962517526849 40702904831100721888145137)
          ·
            refine ⟨30527178623325541416108853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40702904831100721888145137 30527178623325541416108853)
            ·
              refine ⟨2861922995936769507760205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30527178623325541416108853 2861922995936769507760205)
              ·
                refine ⟨1073221123476288565410077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2861922995936769507760205 1073221123476288565410077)
                ·
                  refine ⟨402457921303608212028779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073221123476288565410077 402457921303608212028779)
                  ·
                    rfl

theorem cell21_1763514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1763514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763514 prefixEnd_1763514 := by exact prefixLift 1763514
  have htrace : WordTrace (prefixWord ++ tailWord_1763514) baseStart_1763514 baseEnd_1763514 := by
    simpa [prefixWord, tailWord_1763514, baseEnd_1763514] using wordTrace_append hprefix tailTrace_1763514
  have hstable : (prefixWord ++ tailWord_1763514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763514).length < 2 ^ (prefixWord ++ tailWord_1763514).sum := by decide
  have hdescent : baseEnd_1763514 < baseStart_1763514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763525 : List Nat := [1, 3, 1, 1, 1, 1, 13]
def baseStart_1763525 : Nat := 118140960795 + 1763525 * 2 ^ 59
def prefixEnd_1763525 : Nat := 4983230072969 + 3 ^ 40 * 1763525 * 2
def baseEnd_1763525 : Nat := 44717825739274959705047

theorem tailTrace_1763525 : CollatzResearch.WordTrace tailWord_1763525 prefixEnd_1763525 44717825739274959705047 := by
  unfold tailWord_1763525
  simp only [CollatzResearch.WordTrace]
  refine ⟨64321040936057585936460029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42880693957371723957640019 64321040936057585936460029)
  ·
    refine ⟨24120390351021594726172511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64321040936057585936460029 24120390351021594726172511)
    ·
      refine ⟨36180585526532392089258767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24120390351021594726172511 36180585526532392089258767)
      ·
        refine ⟨54270878289798588133888151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36180585526532392089258767 54270878289798588133888151)
        ·
          refine ⟨81406317434697882200832227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54270878289798588133888151 81406317434697882200832227)
          ·
            refine ⟨122109476152046823301248341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81406317434697882200832227 122109476152046823301248341)
            ·
              refine ⟨44717825739274959705047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 122109476152046823301248341 44717825739274959705047)
              ·
                rfl

theorem cell21_1763525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 13].length) (baseStart_1763525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763525 prefixEnd_1763525 := by exact prefixLift 1763525
  have htrace : WordTrace (prefixWord ++ tailWord_1763525) baseStart_1763525 baseEnd_1763525 := by
    simpa [prefixWord, tailWord_1763525, baseEnd_1763525] using wordTrace_append hprefix tailTrace_1763525
  have hstable : (prefixWord ++ tailWord_1763525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763525).length < 2 ^ (prefixWord ++ tailWord_1763525).sum := by decide
  have hdescent : baseEnd_1763525 < baseStart_1763525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763556 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1763556 : Nat := 118140960795 + 1763556 * 2 ^ 59
def prefixEnd_1763556 : Nat := 4983230072969 + 3 ^ 40 * 1763556 * 2
def baseEnd_1763556 : Nat := 402467506275825472328693

theorem tailTrace_1763556 : CollatzResearch.WordTrace tailWord_1763556 prefixEnd_1763556 402467506275825472328693 := by
  unfold tailWord_1763556
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161085799472639115419261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42881447732630185487225681 32161085799472639115419261)
  ·
    refine ⟨12060407174802239668282223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32161085799472639115419261 12060407174802239668282223)
    ·
      refine ⟨18090610762203359502423335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12060407174802239668282223 18090610762203359502423335)
      ·
        refine ⟨27135916143305039253635003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18090610762203359502423335 27135916143305039253635003)
        ·
          refine ⟨40703874214957558880452505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27135916143305039253635003 40703874214957558880452505)
          ·
            refine ⟨30527905661218169160339379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40703874214957558880452505 30527905661218169160339379)
            ·
              refine ⟨45791858491827253740509069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30527905661218169160339379 45791858491827253740509069)
              ·
                refine ⟨17171946934435220152690901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45791858491827253740509069 17171946934435220152690901)
                ·
                  refine ⟨402467506275825472328693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17171946934435220152690901 402467506275825472328693)
                  ·
                    rfl

theorem cell21_1763556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1763556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763556 prefixEnd_1763556 := by exact prefixLift 1763556
  have htrace : WordTrace (prefixWord ++ tailWord_1763556) baseStart_1763556 baseEnd_1763556 := by
    simpa [prefixWord, tailWord_1763556, baseEnd_1763556] using wordTrace_append hprefix tailTrace_1763556
  have hstable : (prefixWord ++ tailWord_1763556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763556).length < 2 ^ (prefixWord ++ tailWord_1763556).sum := by decide
  have hdescent : baseEnd_1763556 < baseStart_1763556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763708 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 5]
def baseStart_1763708 : Nat := 118140960795 + 1763708 * 2 ^ 59
def prefixEnd_1763708 : Nat := 4983230072969 + 3 ^ 40 * 1763708 * 2
def baseEnd_1763708 : Nat := 402502194746706985795049

theorem tailTrace_1763708 : CollatzResearch.WordTrace tailWord_1763708 prefixEnd_1763708 402502194746706985795049 := by
  unfold tailWord_1763708
  simp only [CollatzResearch.WordTrace]
  refine ⟨32163857747197304095185889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42885143662929738793581185 32163857747197304095185889)
  ·
    refine ⟨24122893310397978071389417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32163857747197304095185889 24122893310397978071389417)
    ·
      refine ⟨18092169982798483553542063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24122893310397978071389417 18092169982798483553542063)
      ·
        refine ⟨27138254974197725330313095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092169982798483553542063 27138254974197725330313095)
        ·
          refine ⟨40707382461296587995469643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27138254974197725330313095 40707382461296587995469643)
          ·
            refine ⟨61061073691944881993204465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40707382461296587995469643 61061073691944881993204465)
            ·
              refine ⟨45795805268958661494903349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61061073691944881993204465 45795805268958661494903349)
              ·
                refine ⟨4293356743964874515147189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45795805268958661494903349 4293356743964874515147189)
                ·
                  refine ⟨402502194746706985795049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4293356743964874515147189 402502194746706985795049)
                  ·
                    rfl

theorem cell21_1763708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_1763708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763708 prefixEnd_1763708 := by exact prefixLift 1763708
  have htrace : WordTrace (prefixWord ++ tailWord_1763708) baseStart_1763708 baseEnd_1763708 := by
    simpa [prefixWord, tailWord_1763708, baseEnd_1763708] using wordTrace_append hprefix tailTrace_1763708
  have hstable : (prefixWord ++ tailWord_1763708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763708).length < 2 ^ (prefixWord ++ tailWord_1763708).sum := by decide
  have hdescent : baseEnd_1763708 < baseStart_1763708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763714 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1763714 : Nat := 118140960795 + 1763714 * 2 ^ 59
def prefixEnd_1763714 : Nat := 4983230072969 + 3 ^ 40 * 1763714 * 2
def baseEnd_1763714 : Nat := 402503564028452308695037

theorem tailTrace_1763714 : CollatzResearch.WordTrace tailWord_1763714 prefixEnd_1763714 402503564028452308695037 := by
  unfold tailWord_1763714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16081983583093217803772549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42885289554915247476726797 16081983583093217803772549)
  ·
    refine ⟨3015371921829978338207353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16081983583093217803772549 3015371921829978338207353)
    ·
      refine ⟨2261528941372483753655515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3015371921829978338207353 2261528941372483753655515)
      ·
        refine ⟨3392293412058725630483273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261528941372483753655515 3392293412058725630483273)
        ·
          refine ⟨2544220059044044222862455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3392293412058725630483273 2544220059044044222862455)
          ·
            refine ⟨3816330088566066334293683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544220059044044222862455 3816330088566066334293683)
            ·
              refine ⟨5724495132849099501440525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816330088566066334293683 5724495132849099501440525)
              ·
                refine ⟨2146685674818412313040197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5724495132849099501440525 2146685674818412313040197)
                ·
                  refine ⟨402503564028452308695037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146685674818412313040197 402503564028452308695037)
                  ·
                    rfl

theorem cell21_1763714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1763714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763714 prefixEnd_1763714 := by exact prefixLift 1763714
  have htrace : WordTrace (prefixWord ++ tailWord_1763714) baseStart_1763714 baseEnd_1763714 := by
    simpa [prefixWord, tailWord_1763714, baseEnd_1763714] using wordTrace_append hprefix tailTrace_1763714
  have hstable : (prefixWord ++ tailWord_1763714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763714).length < 2 ^ (prefixWord ++ tailWord_1763714).sum := by decide
  have hdescent : baseEnd_1763714 < baseStart_1763714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763784 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_1763784 : Nat := 118140960795 + 1763784 * 2 ^ 59
def prefixEnd_1763784 : Nat := 4983230072969 + 3 ^ 40 * 1763784 * 2
def baseEnd_1763784 : Nat := 402519538982147742528227

theorem tailTrace_1763784 : CollatzResearch.WordTrace tailWord_1763784 prefixEnd_1763784 402519538982147742528227 := by
  unfold tailWord_1763784
  simp only [CollatzResearch.WordTrace]
  refine ⟨32165243721059636585069203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42886991628079515446758937 32165243721059636585069203)
  ·
    refine ⟨48247865581589454877603805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32165243721059636585069203 48247865581589454877603805)
    ·
      refine ⟨18092949593096045579101427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48247865581589454877603805 18092949593096045579101427)
      ·
        refine ⟨27139424389644068368652141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18092949593096045579101427 27139424389644068368652141)
        ·
          refine ⟨10177284146116525638244553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27139424389644068368652141 10177284146116525638244553)
          ·
            refine ⟨7632963109587394228683415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10177284146116525638244553 7632963109587394228683415)
            ·
              refine ⟨11449444664381091343025123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7632963109587394228683415 11449444664381091343025123)
              ·
                refine ⟨17174166996571637014537685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11449444664381091343025123 17174166996571637014537685)
                ·
                  refine ⟨402519538982147742528227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17174166996571637014537685 402519538982147742528227)
                  ·
                    rfl

theorem cell21_1763784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_1763784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763784 prefixEnd_1763784 := by exact prefixLift 1763784
  have htrace : WordTrace (prefixWord ++ tailWord_1763784) baseStart_1763784 baseEnd_1763784 := by
    simpa [prefixWord, tailWord_1763784, baseEnd_1763784] using wordTrace_append hprefix tailTrace_1763784
  have hstable : (prefixWord ++ tailWord_1763784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763784).length < 2 ^ (prefixWord ++ tailWord_1763784).sum := by decide
  have hdescent : baseEnd_1763784 < baseStart_1763784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763815 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 6]
def baseStart_1763815 : Nat := 118140960795 + 1763815 * 2 ^ 59
def prefixEnd_1763815 : Nat := 4983230072969 + 3 ^ 40 * 1763815 * 2
def baseEnd_1763815 : Nat := 402526613604498577511497

theorem tailTrace_1763815 : CollatzResearch.WordTrace tailWord_1763815 prefixEnd_1763815 402526613604498577511497 := by
  unfold tailWord_1763815
  simp only [CollatzResearch.WordTrace]
  refine ⟨64331618105006965464516899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42887745403337976976344599 64331618105006965464516899)
  ·
    refine ⟨96497427157510448196775349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64331618105006965464516899 96497427157510448196775349)
    ·
      refine ⟨9046633796016604518447689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96497427157510448196775349 9046633796016604518447689)
      ·
        refine ⟨6784975347012453388835767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9046633796016604518447689 6784975347012453388835767)
        ·
          refine ⟨10177463020518680083253651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784975347012453388835767 10177463020518680083253651)
          ·
            refine ⟨15266194530778020124880477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10177463020518680083253651 15266194530778020124880477)
            ·
              refine ⟨5724822949041757546830179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15266194530778020124880477 5724822949041757546830179)
              ·
                refine ⟨8587234423562636320245269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724822949041757546830179 8587234423562636320245269)
                ·
                  refine ⟨402526613604498577511497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8587234423562636320245269 402526613604498577511497)
                  ·
                    rfl

theorem cell21_1763815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_1763815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763815 prefixEnd_1763815 := by exact prefixLift 1763815
  have htrace : WordTrace (prefixWord ++ tailWord_1763815) baseStart_1763815 baseEnd_1763815 := by
    simpa [prefixWord, tailWord_1763815, baseEnd_1763815] using wordTrace_append hprefix tailTrace_1763815
  have hstable : (prefixWord ++ tailWord_1763815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763815).length < 2 ^ (prefixWord ++ tailWord_1763815).sum := by decide
  have hdescent : baseEnd_1763815 < baseStart_1763815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763818 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_1763818 : Nat := 118140960795 + 1763818 * 2 ^ 59
def prefixEnd_1763818 : Nat := 4983230072969 + 3 ^ 40 * 1763818 * 2
def baseEnd_1763818 : Nat := 402527298245371238961491

theorem tailTrace_1763818 : CollatzResearch.WordTrace tailWord_1763818 prefixEnd_1763818 402527298245371238961491 := by
  unfold tailWord_1763818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082931880999024244219027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42887818349330731317917405 16082931880999024244219027)
  ·
    refine ⟨24124397821498536366328541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16082931880999024244219027 24124397821498536366328541)
    ·
      refine ⟨9046649183061951137373203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24124397821498536366328541 9046649183061951137373203)
      ·
        refine ⟨13569973774592926706059805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9046649183061951137373203 13569973774592926706059805)
        ·
          refine ⟨5088740165472347514772427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13569973774592926706059805 5088740165472347514772427)
          ·
            refine ⟨7633110248208521272158641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5088740165472347514772427 7633110248208521272158641)
            ·
              refine ⟨5724832686156390954118981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7633110248208521272158641 5724832686156390954118981)
              ·
                refine ⟨1073406128654323303897309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5724832686156390954118981 1073406128654323303897309)
                ·
                  refine ⟨402527298245371238961491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073406128654323303897309 402527298245371238961491)
                  ·
                    rfl

theorem cell21_1763818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_1763818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763818 prefixEnd_1763818 := by exact prefixLift 1763818
  have htrace : WordTrace (prefixWord ++ tailWord_1763818) baseStart_1763818 baseEnd_1763818 := by
    simpa [prefixWord, tailWord_1763818, baseEnd_1763818] using wordTrace_append hprefix tailTrace_1763818
  have hstable : (prefixWord ++ tailWord_1763818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763818).length < 2 ^ (prefixWord ++ tailWord_1763818).sum := by decide
  have hdescent : baseEnd_1763818 < baseStart_1763818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763832 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_1763832 : Nat := 118140960795 + 1763832 * 2 ^ 59
def prefixEnd_1763832 : Nat := 4983230072969 + 3 ^ 40 * 1763832 * 2
def baseEnd_1763832 : Nat := 402530493236110325728129

theorem tailTrace_1763832 : CollatzResearch.WordTrace tailWord_1763832 prefixEnd_1763832 402530493236110325728129 := by
  unfold tailWord_1763832
  simp only [CollatzResearch.WordTrace]
  refine ⟨32166119072972688683942875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42888158763963584911923833 32166119072972688683942875)
  ·
    refine ⟨48249178609459033025914313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32166119072972688683942875 48249178609459033025914313)
    ·
      refine ⟨36186883957094274769435735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48249178609459033025914313 36186883957094274769435735)
      ·
        refine ⟨54280325935641412154153603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36186883957094274769435735 54280325935641412154153603)
        ·
          refine ⟨81420488903462118231230405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54280325935641412154153603 81420488903462118231230405)
          ·
            refine ⟨15266341669399147168355701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81420488903462118231230405 15266341669399147168355701)
            ·
              refine ⟨1431219531506170047033347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15266341669399147168355701 1431219531506170047033347)
              ·
                refine ⟨2146829297259255070550021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431219531506170047033347 2146829297259255070550021)
                ·
                  refine ⟨402530493236110325728129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146829297259255070550021 402530493236110325728129)
                  ·
                    rfl

theorem cell21_1763832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_1763832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763832 prefixEnd_1763832 := by exact prefixLift 1763832
  have htrace : WordTrace (prefixWord ++ tailWord_1763832) baseStart_1763832 baseEnd_1763832 := by
    simpa [prefixWord, tailWord_1763832, baseEnd_1763832] using wordTrace_append hprefix tailTrace_1763832
  have hstable : (prefixWord ++ tailWord_1763832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763832).length < 2 ^ (prefixWord ++ tailWord_1763832).sum := by decide
  have hdescent : baseEnd_1763832 < baseStart_1763832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763863 : List Nat := [1, 1, 3, 6, 1, 2, 7]
def baseStart_1763863 : Nat := 118140960795 + 1763863 * 2 ^ 59
def prefixEnd_1763863 : Nat := 4983230072969 + 3 ^ 40 * 1763863 * 2
def baseEnd_1763863 : Nat := 44726396428717906745711

theorem tailTrace_1763863 : CollatzResearch.WordTrace tailWord_1763863 prefixEnd_1763863 44726396428717906745711 := by
  unfold tailWord_1763863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64333368808833069662264243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42888912539222046441509495 64333368808833069662264243)
  ·
    refine ⟨96500053213249604493396365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64333368808833069662264243 96500053213249604493396365)
    ·
      refine ⟨36187519954968601685023637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96500053213249604493396365 36187519954968601685023637)
      ·
        refine ⟨1696289997889153203985483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36187519954968601685023637 1696289997889153203985483)
        ·
          refine ⟨2544434996833729805978225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696289997889153203985483 2544434996833729805978225)
          ·
            refine ⟨1908326247625297354483669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544434996833729805978225 1908326247625297354483669)
            ·
              refine ⟨44726396428717906745711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1908326247625297354483669 44726396428717906745711)
              ·
                rfl

theorem cell21_1763863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 7].length) (baseStart_1763863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763863 prefixEnd_1763863 := by exact prefixLift 1763863
  have htrace : WordTrace (prefixWord ++ tailWord_1763863) baseStart_1763863 baseEnd_1763863 := by
    simpa [prefixWord, tailWord_1763863, baseEnd_1763863] using wordTrace_append hprefix tailTrace_1763863
  have hstable : (prefixWord ++ tailWord_1763863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763863).length < 2 ^ (prefixWord ++ tailWord_1763863).sum := by decide
  have hdescent : baseEnd_1763863 < baseStart_1763863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763877 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 3]
def baseStart_1763877 : Nat := 118140960795 + 1763877 * 2 ^ 59
def prefixEnd_1763877 : Nat := 4983230072969 + 3 ^ 40 * 1763877 * 2
def baseEnd_1763877 : Nat := 402540762849200247478037

theorem tailTrace_1763877 : CollatzResearch.WordTrace tailWord_1763877 prefixEnd_1763877 402540762849200247478037 := by
  unfold tailWord_1763877
  simp only [CollatzResearch.WordTrace]
  refine ⟨64333879430782350053273885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42889252953854900035515923 64333879430782350053273885)
  ·
    refine ⟨24125204786543381269977707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64333879430782350053273885 24125204786543381269977707)
    ·
      refine ⟨36187807179815071904966561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24125204786543381269977707 36187807179815071904966561)
      ·
        refine ⟨27140855384861303928724921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36187807179815071904966561 27140855384861303928724921)
        ·
          refine ⟨20355641538645977946543691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27140855384861303928724921 20355641538645977946543691)
          ·
            refine ⟨30533462307968966919815537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20355641538645977946543691 30533462307968966919815537)
            ·
              refine ⟨22900096730976725189861653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30533462307968966919815537 22900096730976725189861653)
              ·
                refine ⟨1073442034264533993274765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22900096730976725189861653 1073442034264533993274765)
                ·
                  refine ⟨402540762849200247478037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073442034264533993274765 402540762849200247478037)
                  ·
                    rfl

theorem cell21_1763877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_1763877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763877 prefixEnd_1763877 := by exact prefixLift 1763877
  have htrace : WordTrace (prefixWord ++ tailWord_1763877) baseStart_1763877 baseEnd_1763877 := by
    simpa [prefixWord, tailWord_1763877, baseEnd_1763877] using wordTrace_append hprefix tailTrace_1763877
  have hstable : (prefixWord ++ tailWord_1763877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763877).length < 2 ^ (prefixWord ++ tailWord_1763877).sum := by decide
  have hdescent : baseEnd_1763877 < baseStart_1763877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763891 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_1763891 : Nat := 118140960795 + 1763891 * 2 ^ 59
def prefixEnd_1763891 : Nat := 4983230072969 + 3 ^ 40 * 1763891 * 2
def baseEnd_1763891 : Nat := 402543957839939334244675

theorem tailTrace_1763891 : CollatzResearch.WordTrace tailWord_1763891 prefixEnd_1763891 402543957839939334244675 := by
  unfold tailWord_1763891
  simp only [CollatzResearch.WordTrace]
  refine ⟨64334390052731630444283527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42889593368487753629522351 64334390052731630444283527)
  ·
    refine ⟨96501585079097445666425291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64334390052731630444283527 96501585079097445666425291)
    ·
      refine ⟨144752377618646168499637937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96501585079097445666425291 144752377618646168499637937)
      ·
        refine ⟨108564283213984626374728453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144752377618646168499637937 108564283213984626374728453)
        ·
          refine ⟨20355803102622117445261585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108564283213984626374728453 20355803102622117445261585)
          ·
            refine ⟨15266852326966588083946189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20355803102622117445261585 15266852326966588083946189)
            ·
              refine ⟨5725069622612470531479821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15266852326966588083946189 5725069622612470531479821)
              ·
                refine ⟨2146901108479676449304933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5725069622612470531479821 2146901108479676449304933)
                ·
                  refine ⟨402543957839939334244675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146901108479676449304933 402543957839939334244675)
                  ·
                    rfl

theorem cell21_1763891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_1763891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763891 prefixEnd_1763891 := by exact prefixLift 1763891
  have htrace : WordTrace (prefixWord ++ tailWord_1763891) baseStart_1763891 baseEnd_1763891 := by
    simpa [prefixWord, tailWord_1763891, baseEnd_1763891] using wordTrace_append hprefix tailTrace_1763891
  have hstable : (prefixWord ++ tailWord_1763891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763891).length < 2 ^ (prefixWord ++ tailWord_1763891).sum := by decide
  have hdescent : baseEnd_1763891 < baseStart_1763891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1763998 : List Nat := [4, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1763998 : Nat := 118140960795 + 1763998 * 2 ^ 59
def prefixEnd_1763998 : Nat := 4983230072969 + 3 ^ 40 * 1763998 * 2
def baseEnd_1763998 : Nat := 134189458899243641987041

theorem tailTrace_1763998 : CollatzResearch.WordTrace tailWord_1763998 prefixEnd_1763998 134189458899243641987041 := by
  unfold tailWord_1763998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042286582917998464803581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42892195108895991812285765 8042286582917998464803581)
  ·
    refine ⟨3015857468594249424301343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8042286582917998464803581 3015857468594249424301343)
    ·
      refine ⟨4523786202891374136452015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015857468594249424301343 4523786202891374136452015)
      ·
        refine ⟨6785679304337061204678023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523786202891374136452015 6785679304337061204678023)
        ·
          refine ⟨10178518956505591807017035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785679304337061204678023 10178518956505591807017035)
          ·
            refine ⟨15267778434758387710525553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10178518956505591807017035 15267778434758387710525553)
            ·
              refine ⟨11450833826068790782894165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15267778434758387710525553 11450833826068790782894165)
              ·
                refine ⟨134189458899243641987041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11450833826068790782894165 134189458899243641987041)
                ·
                  rfl

theorem cell21_1763998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1763998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1763998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1763998 prefixEnd_1763998 := by exact prefixLift 1763998
  have htrace : WordTrace (prefixWord ++ tailWord_1763998) baseStart_1763998 baseEnd_1763998 := by
    simpa [prefixWord, tailWord_1763998, baseEnd_1763998] using wordTrace_append hprefix tailTrace_1763998
  have hstable : (prefixWord ++ tailWord_1763998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1763998).length < 2 ^ (prefixWord ++ tailWord_1763998).sum := by decide
  have hdescent : baseEnd_1763998 < baseStart_1763998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1763998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764001 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 4]
def baseStart_1764001 : Nat := 118140960795 + 1764001 * 2 ^ 59
def prefixEnd_1764001 : Nat := 4983230072969 + 3 ^ 40 * 1764001 * 2
def baseEnd_1764001 : Nat := 402569061338603587411117

theorem tailTrace_1764001 : CollatzResearch.WordTrace tailWord_1764001 prefixEnd_1764001 402569061338603587411117 := by
  unfold tailWord_1764001
  simp only [CollatzResearch.WordTrace]
  refine ⟨64338402082333119230787857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42892268054888746153858571 64338402082333119230787857)
  ·
    refine ⟨48253801561749839423090893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64338402082333119230787857 48253801561749839423090893)
    ·
      refine ⟨18095175585656189783659085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48253801561749839423090893 18095175585656189783659085)
      ·
        refine ⟨6785690844621071168872157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18095175585656189783659085 6785690844621071168872157)
        ·
          refine ⟨2544634066732901688327059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6785690844621071168872157 2544634066732901688327059)
          ·
            refine ⟨3816951100099352532490589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544634066732901688327059 3816951100099352532490589)
            ·
              refine ⟨1431356662537257199683971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3816951100099352532490589 1431356662537257199683971)
              ·
                refine ⟨2147034993805885799525957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431356662537257199683971 2147034993805885799525957)
                ·
                  refine ⟨402569061338603587411117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147034993805885799525957 402569061338603587411117)
                  ·
                    rfl

theorem cell21_1764001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_1764001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764001 prefixEnd_1764001 := by exact prefixLift 1764001
  have htrace : WordTrace (prefixWord ++ tailWord_1764001) baseStart_1764001 baseEnd_1764001 := by
    simpa [prefixWord, tailWord_1764001, baseEnd_1764001] using wordTrace_append hprefix tailTrace_1764001
  have hstable : (prefixWord ++ tailWord_1764001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764001).length < 2 ^ (prefixWord ++ tailWord_1764001).sum := by decide
  have hdescent : baseEnd_1764001 < baseStart_1764001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764026 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_1764026 : Nat := 118140960795 + 1764026 * 2 ^ 59
def prefixEnd_1764026 : Nat := 4983230072969 + 3 ^ 40 * 1764026 * 2
def baseEnd_1764026 : Nat := 402574766679209099494399

theorem tailTrace_1764026 : CollatzResearch.WordTrace tailWord_1764026 prefixEnd_1764026 402574766679209099494399 := by
  unfold tailWord_1764026
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084828476810637125111983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42892875938161699000298621 16084828476810637125111983)
  ·
    refine ⟨24127242715215955687667975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16084828476810637125111983 24127242715215955687667975)
    ·
      refine ⟨36190864072823933531501963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24127242715215955687667975 36190864072823933531501963)
      ·
        refine ⟨54286296109235900297252945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36190864072823933531501963 54286296109235900297252945)
        ·
          refine ⟨40714722081926925222939709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54286296109235900297252945 40714722081926925222939709)
          ·
            refine ⟨15268020780722596958602391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40714722081926925222939709 15268020780722596958602391)
            ·
              refine ⟨22902031171083895437903587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15268020780722596958602391 22902031171083895437903587)
              ·
                refine ⟨34353046756625843156855381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22902031171083895437903587 34353046756625843156855381)
                ·
                  refine ⟨402574766679209099494399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34353046756625843156855381 402574766679209099494399)
                  ·
                    rfl

theorem cell21_1764026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_1764026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764026 prefixEnd_1764026 := by exact prefixLift 1764026
  have htrace : WordTrace (prefixWord ++ tailWord_1764026) baseStart_1764026 baseEnd_1764026 := by
    simpa [prefixWord, tailWord_1764026, baseEnd_1764026] using wordTrace_append hprefix tailTrace_1764026
  have hstable : (prefixWord ++ tailWord_1764026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764026).length < 2 ^ (prefixWord ++ tailWord_1764026).sum := by decide
  have hdescent : baseEnd_1764026 < baseStart_1764026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764057 : List Nat := [1, 2, 1, 2, 3, 2, 4, 6]
def baseStart_1764057 : Nat := 118140960795 + 1764057 * 2 ^ 59
def prefixEnd_1764057 : Nat := 4983230072969 + 3 ^ 40 * 1764057 * 2
def baseEnd_1764057 : Nat := 134193947100519978159223

theorem tailTrace_1764057 : CollatzResearch.WordTrace tailWord_1764057 prefixEnd_1764057 134193947100519978159223 := by
  unfold tailWord_1764057
  simp only [CollatzResearch.WordTrace]
  refine ⟨64340444570130240794826425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42893629713420160529884283 64340444570130240794826425)
  ·
    refine ⟨48255333427597680596119819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64340444570130240794826425 48255333427597680596119819)
    ·
      refine ⟨72383000141396520894179729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48255333427597680596119819 72383000141396520894179729)
      ·
        refine ⟨54287250106047390670634797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72383000141396520894179729 54287250106047390670634797)
        ·
          refine ⟨20357718789767771501488049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54287250106047390670634797 20357718789767771501488049)
          ·
            refine ⟨15268289092325828626116037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20357718789767771501488049 15268289092325828626116037)
            ·
              refine ⟨2862804204811092867396757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15268289092325828626116037 2862804204811092867396757)
              ·
                refine ⟨134193947100519978159223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2862804204811092867396757 134193947100519978159223)
                ·
                  rfl

theorem cell21_1764057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_1764057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764057 prefixEnd_1764057 := by exact prefixLift 1764057
  have htrace : WordTrace (prefixWord ++ tailWord_1764057) baseStart_1764057 baseEnd_1764057 := by
    simpa [prefixWord, tailWord_1764057, baseEnd_1764057] using wordTrace_append hprefix tailTrace_1764057
  have hstable : (prefixWord ++ tailWord_1764057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764057).length < 2 ^ (prefixWord ++ tailWord_1764057).sum := by decide
  have hdescent : baseEnd_1764057 < baseStart_1764057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764209 : List Nat := [1, 2, 2, 2, 1, 6, 7]
def baseStart_1764209 : Nat := 118140960795 + 1764209 * 2 ^ 59
def prefixEnd_1764209 : Nat := 4983230072969 + 3 ^ 40 * 1764209 * 2
def baseEnd_1764209 : Nat := 44735169974715716438225

theorem tailTrace_1764209 : CollatzResearch.WordTrace tailWord_1764209 prefixEnd_1764209 44735169974715716438225 := by
  unfold tailWord_1764209
  simp only [CollatzResearch.WordTrace]
  refine ⟨64345988465579570754359681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42897325643719713836239787 64345988465579570754359681)
  ·
    refine ⟨48259491349184678065769761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64345988465579570754359681 48259491349184678065769761)
    ·
      refine ⟨36194618511888508549327321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48259491349184678065769761 36194618511888508549327321)
      ·
        refine ⟨27145963883916381411995491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36194618511888508549327321 27145963883916381411995491)
        ·
          refine ⟨40718945825874572117993237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27145963883916381411995491 40718945825874572117993237)
          ·
            refine ⟨1908700585587870568030933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40718945825874572117993237 1908700585587870568030933)
            ·
              refine ⟨44735169974715716438225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1908700585587870568030933 44735169974715716438225)
              ·
                rfl

theorem cell21_1764209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 7].length) (baseStart_1764209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764209 prefixEnd_1764209 := by exact prefixLift 1764209
  have htrace : WordTrace (prefixWord ++ tailWord_1764209) baseStart_1764209 baseEnd_1764209 := by
    simpa [prefixWord, tailWord_1764209, baseEnd_1764209] using wordTrace_append hprefix tailTrace_1764209
  have hstable : (prefixWord ++ tailWord_1764209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764209).length < 2 ^ (prefixWord ++ tailWord_1764209).sum := by decide
  have hdescent : baseEnd_1764209 < baseStart_1764209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764294 : List Nat := [6, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1764294 : Nat := 118140960795 + 1764294 * 2 ^ 59
def prefixEnd_1764294 : Nat := 4983230072969 + 3 ^ 40 * 1764294 * 2
def baseEnd_1764294 : Nat := 134211975976833396342395

theorem tailTrace_1764294 : CollatzResearch.WordTrace tailWord_1764294 prefixEnd_1764294 134211975976833396342395 := by
  unfold tailWord_1764294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010909020945988445975123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42899392446847753514135957 2010909020945988445975123)
  ·
    refine ⟨3016363531418982668962685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2010909020945988445975123 3016363531418982668962685)
    ·
      refine ⟨1131136324282118500861007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3016363531418982668962685 1131136324282118500861007)
      ·
        refine ⟨1696704486423177751291511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131136324282118500861007 1696704486423177751291511)
        ·
          refine ⟨2545056729634766626937267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696704486423177751291511 2545056729634766626937267)
          ·
            refine ⟨3817585094452149940405901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545056729634766626937267 3817585094452149940405901)
            ·
              refine ⟨1431594410419556227652213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3817585094452149940405901 1431594410419556227652213)
              ·
                refine ⟨134211975976833396342395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431594410419556227652213 134211975976833396342395)
                ·
                  rfl

theorem cell21_1764294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1764294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764294 prefixEnd_1764294 := by exact prefixLift 1764294
  have htrace : WordTrace (prefixWord ++ tailWord_1764294) baseStart_1764294 baseEnd_1764294 := by
    simpa [prefixWord, tailWord_1764294, baseEnd_1764294] using wordTrace_append hprefix tailTrace_1764294
  have hstable : (prefixWord ++ tailWord_1764294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764294).length < 2 ^ (prefixWord ++ tailWord_1764294).sum := by decide
  have hdescent : baseEnd_1764294 < baseStart_1764294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764299 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_1764299 : Nat := 118140960795 + 1764299 * 2 ^ 59
def prefixEnd_1764299 : Nat := 4983230072969 + 3 ^ 40 * 1764299 * 2
def baseEnd_1764299 : Nat := 402637068998621291443841

theorem tailTrace_1764299 : CollatzResearch.WordTrace tailWord_1764299 prefixEnd_1764299 402637068998621291443841 := by
  unfold tailWord_1764299
  simp only [CollatzResearch.WordTrace]
  refine ⟨64349271035253516125135951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42899514023502344083423967 64349271035253516125135951)
  ·
    refine ⟨96523906552880274187703927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64349271035253516125135951 96523906552880274187703927)
    ·
      refine ⟨144785859829320411281555891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96523906552880274187703927 144785859829320411281555891)
      ·
        refine ⟨217178789743980616922333837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144785859829320411281555891 217178789743980616922333837)
        ·
          refine ⟨81442046153992731345875189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217178789743980616922333837 81442046153992731345875189)
          ·
            refine ⟨7635191826936818563675799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81442046153992731345875189 7635191826936818563675799)
            ·
              refine ⟨11452787740405227845513699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635191826936818563675799 11452787740405227845513699)
              ·
                refine ⟨17179181610607841768270549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11452787740405227845513699 17179181610607841768270549)
                ·
                  refine ⟨402637068998621291443841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17179181610607841768270549 402637068998621291443841)
                  ·
                    rfl

theorem cell21_1764299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_1764299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764299 prefixEnd_1764299 := by exact prefixLift 1764299
  have htrace : WordTrace (prefixWord ++ tailWord_1764299) baseStart_1764299 baseEnd_1764299 := by
    simpa [prefixWord, tailWord_1764299, baseEnd_1764299] using wordTrace_append hprefix tailTrace_1764299
  have hstable : (prefixWord ++ tailWord_1764299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764299).length < 2 ^ (prefixWord ++ tailWord_1764299).sum := by decide
  have hdescent : baseEnd_1764299 < baseStart_1764299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764302 : List Nat := [4, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1764302 : Nat := 118140960795 + 1764302 * 2 ^ 59
def prefixEnd_1764302 : Nat := 4983230072969 + 3 ^ 40 * 1764302 * 2
def baseEnd_1764302 : Nat := 134212584546497984297945

theorem tailTrace_1764302 : CollatzResearch.WordTrace tailWord_1764302 prefixEnd_1764302 134212584546497984297945 := by
  unfold tailWord_1764302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043672556780330954686895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42899586969495098424996773 8043672556780330954686895)
  ·
    refine ⟨12065508835170496432030343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8043672556780330954686895 12065508835170496432030343)
    ·
      refine ⟨18098263252755744648045515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12065508835170496432030343 18098263252755744648045515)
      ·
        refine ⟨27147394879133616972068273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18098263252755744648045515 27147394879133616972068273)
        ·
          refine ⟨20360546159350212729051205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27147394879133616972068273 20360546159350212729051205)
          ·
            refine ⟨3817602404878164886697101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20360546159350212729051205 3817602404878164886697101)
            ·
              refine ⟨1431600901829311832511413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3817602404878164886697101 1431600901829311832511413)
              ·
                refine ⟨134212584546497984297945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431600901829311832511413 134212584546497984297945)
                ·
                  rfl

theorem cell21_1764302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1764302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764302 prefixEnd_1764302 := by exact prefixLift 1764302
  have htrace : WordTrace (prefixWord ++ tailWord_1764302) baseStart_1764302 baseEnd_1764302 := by
    simpa [prefixWord, tailWord_1764302, baseEnd_1764302] using wordTrace_append hprefix tailTrace_1764302
  have hstable : (prefixWord ++ tailWord_1764302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764302).length < 2 ^ (prefixWord ++ tailWord_1764302).sum := by decide
  have hdescent : baseEnd_1764302 < baseStart_1764302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764344 : List Nat := [2, 1, 2, 1, 1, 3, 1, 10]
def baseStart_1764344 : Nat := 118140960795 + 1764344 * 2 ^ 59
def prefixEnd_1764344 : Nat := 4983230072969 + 3 ^ 40 * 1764344 * 2
def baseEnd_1764344 : Nat := 134215779537237071064583

theorem tailTrace_1764344 : CollatzResearch.WordTrace tailWord_1764344 prefixEnd_1764344 134215779537237071064583 := by
  unfold tailWord_1764344
  simp only [CollatzResearch.WordTrace]
  refine ⟨32175456160045244405262043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42900608213393659207016057 32175456160045244405262043)
  ·
    refine ⟨48263184240067866607893065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32175456160045244405262043 48263184240067866607893065)
    ·
      refine ⟨36197388180050899955919799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48263184240067866607893065 36197388180050899955919799)
      ·
        refine ⟨54296082270076349933879699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36197388180050899955919799 54296082270076349933879699)
        ·
          refine ⟨81444123405114524900819549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54296082270076349933879699 81444123405114524900819549)
          ·
            refine ⟨30541546276917946837807331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81444123405114524900819549 30541546276917946837807331)
            ·
              refine ⟨45812319415376920256710997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30541546276917946837807331 45812319415376920256710997)
              ·
                refine ⟨134215779537237071064583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45812319415376920256710997 134215779537237071064583)
                ·
                  rfl

theorem cell21_1764344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_1764344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764344 prefixEnd_1764344 := by exact prefixLift 1764344
  have htrace : WordTrace (prefixWord ++ tailWord_1764344) baseStart_1764344 baseEnd_1764344 := by
    simpa [prefixWord, tailWord_1764344, baseEnd_1764344] using wordTrace_append hprefix tailTrace_1764344
  have hstable : (prefixWord ++ tailWord_1764344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764344).length < 2 ^ (prefixWord ++ tailWord_1764344).sum := by decide
  have hdescent : baseEnd_1764344 < baseStart_1764344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764451 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 5]
def baseStart_1764451 : Nat := 118140960795 + 1764451 * 2 ^ 59
def prefixEnd_1764451 : Nat := 4983230072969 + 3 ^ 40 * 1764451 * 2
def baseEnd_1764451 : Nat := 402671757469502804910197

theorem tailTrace_1764451 : CollatzResearch.WordTrace tailWord_1764451 prefixEnd_1764451 402671757469502804910197 := by
  unfold tailWord_1764451
  simp only [CollatzResearch.WordTrace]
  refine ⟨64354814930702846084669207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42903209953801897389779471 64354814930702846084669207)
  ·
    refine ⟨96532222396054269127003811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64354814930702846084669207 96532222396054269127003811)
    ·
      refine ⟨144798333594081403690505717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96532222396054269127003811 144798333594081403690505717)
      ·
        refine ⟨13574843774445131595984911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144798333594081403690505717 13574843774445131595984911)
        ·
          refine ⟨20362265661667697393977367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13574843774445131595984911 20362265661667697393977367)
          ·
            refine ⟨30543398492501546090966051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20362265661667697393977367 30543398492501546090966051)
            ·
              refine ⟨45815097738752319136449077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30543398492501546090966051 45815097738752319136449077)
              ·
                refine ⟨4295165413008029919042101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45815097738752319136449077 4295165413008029919042101)
                ·
                  refine ⟨402671757469502804910197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295165413008029919042101 402671757469502804910197)
                  ·
                    rfl

theorem cell21_1764451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_1764451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764451 prefixEnd_1764451 := by exact prefixLift 1764451
  have htrace : WordTrace (prefixWord ++ tailWord_1764451) baseStart_1764451 baseEnd_1764451 := by
    simpa [prefixWord, tailWord_1764451, baseEnd_1764451] using wordTrace_append hprefix tailTrace_1764451
  have hstable : (prefixWord ++ tailWord_1764451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764451).length < 2 ^ (prefixWord ++ tailWord_1764451).sum := by decide
  have hdescent : baseEnd_1764451 < baseStart_1764451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764516 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1764516 : Nat := 118140960795 + 1764516 * 2 ^ 59
def prefixEnd_1764516 : Nat := 4983230072969 + 3 ^ 40 * 1764516 * 2
def baseEnd_1764516 : Nat := 402686591355077136326731

theorem tailTrace_1764516 : CollatzResearch.WordTrace tailWord_1764516 prefixEnd_1764516 402686591355077136326731 := by
  unfold tailWord_1764516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32178592837733681092892701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42904790450311574790523601 32178592837733681092892701)
  ·
    refine ⟨12066972314150130409834763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32178592837733681092892701 12066972314150130409834763)
    ·
      refine ⟨18100458471225195614752145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066972314150130409834763 18100458471225195614752145)
      ·
        refine ⟨13575343853418896711064109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18100458471225195614752145 13575343853418896711064109)
        ·
          refine ⟨5090753945032086266649041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13575343853418896711064109 5090753945032086266649041)
          ·
            refine ⟨3818065458774064699986781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5090753945032086266649041 3818065458774064699986781)
            ·
              refine ⟨1431774547040274262495043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3818065458774064699986781 1431774547040274262495043)
              ·
                refine ⟨2147661820560411393742565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431774547040274262495043 2147661820560411393742565)
                ·
                  refine ⟨402686591355077136326731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147661820560411393742565 402686591355077136326731)
                  ·
                    rfl

theorem cell21_1764516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1764516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764516 prefixEnd_1764516 := by exact prefixLift 1764516
  have htrace : WordTrace (prefixWord ++ tailWord_1764516) baseStart_1764516 baseEnd_1764516 := by
    simpa [prefixWord, tailWord_1764516, baseEnd_1764516] using wordTrace_append hprefix tailTrace_1764516
  have hstable : (prefixWord ++ tailWord_1764516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764516).length < 2 ^ (prefixWord ++ tailWord_1764516).sum := by decide
  have hdescent : baseEnd_1764516 < baseStart_1764516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764527 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 5]
def baseStart_1764527 : Nat := 118140960795 + 1764527 * 2 ^ 59
def prefixEnd_1764527 : Nat := 4983230072969 + 3 ^ 40 * 1764527 * 2
def baseEnd_1764527 : Nat := 402689101704943561643375

theorem tailTrace_1764527 : CollatzResearch.WordTrace tailWord_1764527 prefixEnd_1764527 402689101704943561643375 := by
  unfold tailWord_1764527
  simp only [CollatzResearch.WordTrace]
  refine ⟨64357586878427511064435835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42905057918951674042957223 64357586878427511064435835)
  ·
    refine ⟨96536380317641266596653753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64357586878427511064435835 96536380317641266596653753)
    ·
      refine ⟨72402285238230949947490315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96536380317641266596653753 72402285238230949947490315)
      ·
        refine ⟨108603427857346424921235473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72402285238230949947490315 108603427857346424921235473)
        ·
          refine ⟨81452570893009818690926605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108603427857346424921235473 81452570893009818690926605)
          ·
            refine ⟨30544714084878682009097477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81452570893009818690926605 30544714084878682009097477)
            ·
              refine ⟨5727133890914752876705777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30544714084878682009097477 5727133890914752876705777)
              ·
                refine ⟨4295350418186064657529333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5727133890914752876705777 4295350418186064657529333)
                ·
                  refine ⟨402689101704943561643375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295350418186064657529333 402689101704943561643375)
                  ·
                    rfl

theorem cell21_1764527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 5].length) (baseStart_1764527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764527 prefixEnd_1764527 := by exact prefixLift 1764527
  have htrace : WordTrace (prefixWord ++ tailWord_1764527) baseStart_1764527 baseEnd_1764527 := by
    simpa [prefixWord, tailWord_1764527, baseEnd_1764527] using wordTrace_append hprefix tailTrace_1764527
  have hstable : (prefixWord ++ tailWord_1764527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764527).length < 2 ^ (prefixWord ++ tailWord_1764527).sum := by decide
  have hdescent : baseEnd_1764527 < baseStart_1764527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764530 : List Nat := [3, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1764530 : Nat := 118140960795 + 1764530 * 2 ^ 59
def prefixEnd_1764530 : Nat := 4983230072969 + 3 ^ 40 * 1764530 * 2
def baseEnd_1764530 : Nat := 134229928781938741031123

theorem tailTrace_1764530 : CollatzResearch.WordTrace tailWord_1764530 prefixEnd_1764530 134229928781938741031123 := by
  unfold tailWord_1764530
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089424074354160644198761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42905130864944428384530029 16089424074354160644198761)
  ·
    refine ⟨12067068055765620483149071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16089424074354160644198761 12067068055765620483149071)
    ·
      refine ⟨18100602083648430724723607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12067068055765620483149071 18100602083648430724723607)
      ·
        refine ⟨27150903125472646087085411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18100602083648430724723607 27150903125472646087085411)
        ·
          refine ⟨40726354688208969130628117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27150903125472646087085411 40726354688208969130628117)
          ·
            refine ⟨1909047876009795427998193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40726354688208969130628117 1909047876009795427998193)
            ·
              refine ⟨1431785907007346570998645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909047876009795427998193 1431785907007346570998645)
              ·
                refine ⟨134229928781938741031123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431785907007346570998645 134229928781938741031123)
                ·
                  rfl

theorem cell21_1764530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1764530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764530 prefixEnd_1764530 := by exact prefixLift 1764530
  have htrace : WordTrace (prefixWord ++ tailWord_1764530) baseStart_1764530 baseEnd_1764530 := by
    simpa [prefixWord, tailWord_1764530, baseEnd_1764530] using wordTrace_append hprefix tailTrace_1764530
  have hstable : (prefixWord ++ tailWord_1764530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764530).length < 2 ^ (prefixWord ++ tailWord_1764530).sum := by decide
  have hdescent : baseEnd_1764530 < baseStart_1764530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764575 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 4]
def baseStart_1764575 : Nat := 118140960795 + 1764575 * 2 ^ 59
def prefixEnd_1764575 : Nat := 4983230072969 + 3 ^ 40 * 1764575 * 2
def baseEnd_1764575 : Nat := 402700055958906144843277

theorem tailTrace_1764575 : CollatzResearch.WordTrace tailWord_1764575 prefixEnd_1764575 402700055958906144843277 := by
  unfold tailWord_1764575
  simp only [CollatzResearch.WordTrace]
  refine ⟨64359337582253615262183179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42906225054835743508122119 64359337582253615262183179)
  ·
    refine ⟨96539006373380422893274769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64359337582253615262183179 96539006373380422893274769)
    ·
      refine ⟨72404254780035317169956077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96539006373380422893274769 72404254780035317169956077)
      ·
        refine ⟨27151595542513243938733529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72404254780035317169956077 27151595542513243938733529)
        ·
          refine ⟨20363696656884932954050147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27151595542513243938733529 20363696656884932954050147)
          ·
            refine ⟨30545544985327399431075221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20363696656884932954050147 30545544985327399431075221)
            ·
              refine ⟨1431822421187221848331651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30545544985327399431075221 1431822421187221848331651)
              ·
                refine ⟨2147733631780832772497477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431822421187221848331651 2147733631780832772497477)
                ·
                  refine ⟨402700055958906144843277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147733631780832772497477 402700055958906144843277)
                  ·
                    rfl

theorem cell21_1764575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_1764575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764575 prefixEnd_1764575 := by exact prefixLift 1764575
  have htrace : WordTrace (prefixWord ++ tailWord_1764575) baseStart_1764575 baseEnd_1764575 := by
    simpa [prefixWord, tailWord_1764575, baseEnd_1764575] using wordTrace_append hprefix tailTrace_1764575
  have hstable : (prefixWord ++ tailWord_1764575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764575).length < 2 ^ (prefixWord ++ tailWord_1764575).sum := by decide
  have hdescent : baseEnd_1764575 < baseStart_1764575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764589 : List Nat := [1, 5, 1, 2, 2, 1, 2, 7]
def baseStart_1764589 : Nat := 118140960795 + 1764589 * 2 ^ 59
def prefixEnd_1764589 : Nat := 4983230072969 + 3 ^ 40 * 1764589 * 2
def baseEnd_1764589 : Nat := 134234416983215077203305

theorem tailTrace_1764589 : CollatzResearch.WordTrace tailWord_1764589 prefixEnd_1764589 134234416983215077203305 := by
  unfold tailWord_1764589
  simp only [CollatzResearch.WordTrace]
  refine ⟨64359848204202895653192821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42906565469468597102128547 64359848204202895653192821)
  ·
    refine ⟨6033735769144021467486827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64359848204202895653192821 6033735769144021467486827)
    ·
      refine ⟨9050603653716032201230241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033735769144021467486827 9050603653716032201230241)
      ·
        refine ⟨6787952740287024150922681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9050603653716032201230241 6787952740287024150922681)
        ·
          refine ⟨5090964555215268113192011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6787952740287024150922681 5090964555215268113192011)
          ·
            refine ⟨7636446832822902169788017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5090964555215268113192011 7636446832822902169788017)
            ·
              refine ⟨5727335124617176627341013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7636446832822902169788017 5727335124617176627341013)
              ·
                refine ⟨134234416983215077203305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5727335124617176627341013 134234416983215077203305)
                ·
                  rfl

theorem cell21_1764589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 7].length) (baseStart_1764589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764589 prefixEnd_1764589 := by exact prefixLift 1764589
  have htrace : WordTrace (prefixWord ++ tailWord_1764589) baseStart_1764589 baseEnd_1764589 := by
    simpa [prefixWord, tailWord_1764589, baseEnd_1764589] using wordTrace_append hprefix tailTrace_1764589
  have hstable : (prefixWord ++ tailWord_1764589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764589).length < 2 ^ (prefixWord ++ tailWord_1764589).sum := by decide
  have hdescent : baseEnd_1764589 < baseStart_1764589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764665 : List Nat := [1, 2, 1, 6, 2, 1, 8]
def baseStart_1764665 : Nat := 118140960795 + 1764665 * 2 ^ 59
def prefixEnd_1764665 : Nat := 4983230072969 + 3 ^ 40 * 1764665 * 2
def baseEnd_1764665 : Nat := 44746732798342887593677

theorem tailTrace_1764665 : CollatzResearch.WordTrace tailWord_1764665 prefixEnd_1764665 44746732798342887593677 := by
  unfold tailWord_1764665
  simp only [CollatzResearch.WordTrace]
  refine ⟨64362620151927560632959449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42908413434618373755306299 64362620151927560632959449)
  ·
    refine ⟨48271965113945670474719587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64362620151927560632959449 48271965113945670474719587)
    ·
      refine ⟨72407947670918505712079381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48271965113945670474719587 72407947670918505712079381)
      ·
        refine ⟨3394122547074304955253721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 72407947670918505712079381 3394122547074304955253721)
        ·
          refine ⟨2545591910305728716440291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394122547074304955253721 2545591910305728716440291)
          ·
            refine ⟨3818387865458593074660437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545591910305728716440291 3818387865458593074660437)
            ·
              refine ⟨44746732798342887593677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3818387865458593074660437 44746732798342887593677)
              ·
                rfl

theorem cell21_1764665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 8].length) (baseStart_1764665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764665 prefixEnd_1764665 := by exact prefixLift 1764665
  have htrace : WordTrace (prefixWord ++ tailWord_1764665) baseStart_1764665 baseEnd_1764665 := by
    simpa [prefixWord, tailWord_1764665, baseEnd_1764665] using wordTrace_append hprefix tailTrace_1764665
  have hstable : (prefixWord ++ tailWord_1764665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764665).length < 2 ^ (prefixWord ++ tailWord_1764665).sum := by decide
  have hdescent : baseEnd_1764665 < baseStart_1764665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764679 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 5]
def baseStart_1764679 : Nat := 118140960795 + 1764679 * 2 ^ 59
def prefixEnd_1764679 : Nat := 4983230072969 + 3 ^ 40 * 1764679 * 2
def baseEnd_1764679 : Nat := 402723790175825075109731

theorem tailTrace_1764679 : CollatzResearch.WordTrace tailWord_1764679 prefixEnd_1764679 402723790175825075109731 := by
  unfold tailWord_1764679
  simp only [CollatzResearch.WordTrace]
  refine ⟨64363130773876841023969091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42908753849251227349312727 64363130773876841023969091)
  ·
    refine ⟨96544696160815261535953637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64363130773876841023969091 96544696160815261535953637)
    ·
      refine ⟨18102130530152861537991307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96544696160815261535953637 18102130530152861537991307)
      ·
        refine ⟨27153195795229292306986961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18102130530152861537991307 27153195795229292306986961)
        ·
          refine ⟨20364896846421969230240221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27153195795229292306986961 20364896846421969230240221)
          ·
            refine ⟨7636836317408238461340083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20364896846421969230240221 7636836317408238461340083)
            ·
              refine ⟨11455254476112357692010125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7636836317408238461340083 11455254476112357692010125)
              ·
                refine ⟨4295720428542134134503797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11455254476112357692010125 4295720428542134134503797)
                ·
                  refine ⟨402723790175825075109731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4295720428542134134503797 402723790175825075109731)
                  ·
                    rfl

theorem cell21_1764679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_1764679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764679 prefixEnd_1764679 := by exact prefixLift 1764679
  have htrace : WordTrace (prefixWord ++ tailWord_1764679) baseStart_1764679 baseEnd_1764679 := by
    simpa [prefixWord, tailWord_1764679, baseEnd_1764679] using wordTrace_append hprefix tailTrace_1764679
  have hstable : (prefixWord ++ tailWord_1764679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764679).length < 2 ^ (prefixWord ++ tailWord_1764679).sum := by decide
  have hdescent : baseEnd_1764679 < baseStart_1764679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764744 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_1764744 : Nat := 118140960795 + 1764744 * 2 ^ 59
def prefixEnd_1764744 : Nat := 4983230072969 + 3 ^ 40 * 1764744 * 2
def baseEnd_1764744 : Nat := 402738624061399406526265

theorem tailTrace_1764744 : CollatzResearch.WordTrace tailWord_1764744 prefixEnd_1764744 402738624061399406526265 := by
  unfold tailWord_1764744
  simp only [CollatzResearch.WordTrace]
  refine ⟨32182750759320678562542643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42910334345760904750056857 32182750759320678562542643)
  ·
    refine ⟨48274126138981017843813965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32182750759320678562542643 48274126138981017843813965)
    ·
      refine ⟨18102797302117881691430237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48274126138981017843813965 18102797302117881691430237)
      ·
        refine ⟨6788548988294205634286339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18102797302117881691430237 6788548988294205634286339)
        ·
          refine ⟨10182823482441308451429509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788548988294205634286339 10182823482441308451429509)
          ·
            refine ⟨1909279402957745334643033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10182823482441308451429509 1909279402957745334643033)
            ·
              refine ⟨1431959552218309000982275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909279402957745334643033 1431959552218309000982275)
              ·
                refine ⟨2147939328327463501473413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1431959552218309000982275 2147939328327463501473413)
                ·
                  refine ⟨402738624061399406526265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147939328327463501473413 402738624061399406526265)
                  ·
                    rfl

theorem cell21_1764744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_1764744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764744 prefixEnd_1764744 := by exact prefixLift 1764744
  have htrace : WordTrace (prefixWord ++ tailWord_1764744) baseStart_1764744 baseEnd_1764744 := by
    simpa [prefixWord, tailWord_1764744, baseEnd_1764744] using wordTrace_append hprefix tailTrace_1764744
  have hstable : (prefixWord ++ tailWord_1764744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764744).length < 2 ^ (prefixWord ++ tailWord_1764744).sum := by decide
  have hdescent : baseEnd_1764744 < baseStart_1764744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1764772 : Nat := 118140960795 + 1764772 * 2 ^ 59
def prefixEnd_1764772 : Nat := 4983230072969 + 3 ^ 40 * 1764772 * 2
def baseEnd_1764772 : Nat := 402745014042877580059541

theorem tailTrace_1764772 : CollatzResearch.WordTrace tailWord_1764772 prefixEnd_1764772 402745014042877580059541 := by
  unfold tailWord_1764772
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183261381269958953552285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42911015175026611938069713 32183261381269958953552285)
  ·
    refine ⟨12068723017976234607582107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32183261381269958953552285 12068723017976234607582107)
    ·
      refine ⟨18103084526964351911373161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068723017976234607582107 18103084526964351911373161)
      ·
        refine ⟨13577313395223263933529871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18103084526964351911373161 13577313395223263933529871)
        ·
          refine ⟨20365970092834895900294807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577313395223263933529871 20365970092834895900294807)
          ·
            refine ⟨30548955139252343850442211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20365970092834895900294807 30548955139252343850442211)
            ·
              refine ⟨45823432708878515775663317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30548955139252343850442211 45823432708878515775663317)
              ·
                refine ⟨1073986704114340213492109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 45823432708878515775663317 1073986704114340213492109)
                ·
                  refine ⟨402745014042877580059541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073986704114340213492109 402745014042877580059541)
                  ·
                    rfl

theorem cell21_1764772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1764772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764772 prefixEnd_1764772 := by exact prefixLift 1764772
  have htrace : WordTrace (prefixWord ++ tailWord_1764772) baseStart_1764772 baseEnd_1764772 := by
    simpa [prefixWord, tailWord_1764772, baseEnd_1764772] using wordTrace_append hprefix tailTrace_1764772
  have hstable : (prefixWord ++ tailWord_1764772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764772).length < 2 ^ (prefixWord ++ tailWord_1764772).sum := by decide
  have hdescent : baseEnd_1764772 < baseStart_1764772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764789 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 3]
def baseStart_1764789 : Nat := 118140960795 + 1764789 * 2 ^ 59
def prefixEnd_1764789 : Nat := 4983230072969 + 3 ^ 40 * 1764789 * 2
def baseEnd_1764789 : Nat := 402748893674489328276173

theorem tailTrace_1764789 : CollatzResearch.WordTrace tailWord_1764789 prefixEnd_1764789 402748893674489328276173 := by
  unfold tailWord_1764789
  simp only [CollatzResearch.WordTrace]
  refine ⟨64367142803478329810473421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42911428535652219873648947 64367142803478329810473421)
  ·
    refine ⟨24137678551304373678927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64367142803478329810473421 24137678551304373678927533)
    ·
      refine ⟨9051629456739140129597825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24137678551304373678927533 9051629456739140129597825)
      ·
        refine ⟨6788722092554355097198369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9051629456739140129597825 6788722092554355097198369)
        ·
          refine ⟨5091541569415766322898777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6788722092554355097198369 5091541569415766322898777)
          ·
            refine ⟨3818656177061824742174083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5091541569415766322898777 3818656177061824742174083)
            ·
              refine ⟨5727984265592737113261125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3818656177061824742174083 5727984265592737113261125)
              ·
                refine ⟨1073997049798638208736461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5727984265592737113261125 1073997049798638208736461)
                ·
                  refine ⟨402748893674489328276173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073997049798638208736461 402748893674489328276173)
                  ·
                    rfl

theorem cell21_1764789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_1764789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764789 prefixEnd_1764789 := by exact prefixLift 1764789
  have htrace : WordTrace (prefixWord ++ tailWord_1764789) baseStart_1764789 baseEnd_1764789 := by
    simpa [prefixWord, tailWord_1764789, baseEnd_1764789] using wordTrace_append hprefix tailTrace_1764789
  have hstable : (prefixWord ++ tailWord_1764789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764789).length < 2 ^ (prefixWord ++ tailWord_1764789).sum := by decide
  have hdescent : baseEnd_1764789 < baseStart_1764789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764800 : List Nat := [2, 1, 1, 2, 3, 1, 5, 6]
def baseStart_1764800 : Nat := 118140960795 + 1764800 * 2 ^ 59
def prefixEnd_1764800 : Nat := 4983230072969 + 3 ^ 40 * 1764800 * 2
def baseEnd_1764800 : Nat := 134250468008118584530939

theorem tailTrace_1764800 : CollatzResearch.WordTrace tailWord_1764800 prefixEnd_1764800 134250468008118584530939 := by
  unfold tailWord_1764800
  simp only [CollatzResearch.WordTrace]
  refine ⟨32183772003219239344561927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42911696004292319126082569 32183772003219239344561927)
  ·
    refine ⟨48275658004828859016842891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32183772003219239344561927 48275658004828859016842891)
    ·
      refine ⟨72413487007243288525264337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48275658004828859016842891 72413487007243288525264337)
      ·
        refine ⟨54310115255432466393948253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72413487007243288525264337 54310115255432466393948253)
        ·
          refine ⟨20366293220787174897730595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54310115255432466393948253 20366293220787174897730595)
          ·
            refine ⟨30549439831180762346595893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20366293220787174897730595 30549439831180762346595893)
            ·
              refine ⟨2864009984173196469993365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30549439831180762346595893 2864009984173196469993365)
              ·
                refine ⟨134250468008118584530939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2864009984173196469993365 134250468008118584530939)
                ·
                  rfl

theorem cell21_1764800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_1764800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764800 prefixEnd_1764800 := by exact prefixLift 1764800
  have htrace : WordTrace (prefixWord ++ tailWord_1764800) baseStart_1764800 baseEnd_1764800 := by
    simpa [prefixWord, tailWord_1764800, baseEnd_1764800] using wordTrace_append hprefix tailTrace_1764800
  have hstable : (prefixWord ++ tailWord_1764800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764800).length < 2 ^ (prefixWord ++ tailWord_1764800).sum := by decide
  have hdescent : baseEnd_1764800 < baseStart_1764800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764848 : List Nat := [2, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_1764848 : Nat := 118140960795 + 1764848 * 2 ^ 59
def prefixEnd_1764848 : Nat := 4983230072969 + 3 ^ 40 * 1764848 * 2
def baseEnd_1764848 : Nat := 402762358278318336792719

theorem tailTrace_1764848 : CollatzResearch.WordTrace tailWord_1764848 prefixEnd_1764848 402762358278318336792719 := by
  unfold tailWord_1764848
  simp only [CollatzResearch.WordTrace]
  refine ⟨32184647355132291443435599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42912863140176388591247465 32184647355132291443435599)
  ·
    refine ⟨48276971032698437165153399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32184647355132291443435599 48276971032698437165153399)
    ·
      refine ⟨72415456549047655747730099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48276971032698437165153399 72415456549047655747730099)
      ·
        refine ⟨108623184823571483621595149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72415456549047655747730099 108623184823571483621595149)
        ·
          refine ⟨40733694308839306358098181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108623184823571483621595149 40733694308839306358098181)
          ·
            refine ⟨7637567682907369942143409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40733694308839306358098181 7637567682907369942143409)
            ·
              refine ⟨5728175762180527456607557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637567682907369942143409 5728175762180527456607557)
              ·
                refine ⟨1074032955408848898113917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5728175762180527456607557 1074032955408848898113917)
                ·
                  refine ⟨402762358278318336792719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074032955408848898113917 402762358278318336792719)
                  ·
                    rfl

theorem cell21_1764848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_1764848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764848 prefixEnd_1764848 := by exact prefixLift 1764848
  have htrace : WordTrace (prefixWord ++ tailWord_1764848) baseStart_1764848 baseEnd_1764848 := by
    simpa [prefixWord, tailWord_1764848, baseEnd_1764848] using wordTrace_append hprefix tailTrace_1764848
  have hstable : (prefixWord ++ tailWord_1764848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764848).length < 2 ^ (prefixWord ++ tailWord_1764848).sum := by decide
  have hdescent : baseEnd_1764848 < baseStart_1764848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1764997 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_1764997 : Nat := 118140960795 + 1764997 * 2 ^ 59
def prefixEnd_1764997 : Nat := 4983230072969 + 3 ^ 40 * 1764997 * 2
def baseEnd_1764997 : Nat := 402796362108327188809081

theorem tailTrace_1764997 : CollatzResearch.WordTrace tailWord_1764997 prefixEnd_1764997 402796362108327188809081 := by
  unfold tailWord_1764997
  simp only [CollatzResearch.WordTrace]
  refine ⟨64374729186724781334045245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42916486124483187556030163 64374729186724781334045245)
  ·
    refine ⟨24140523445021793000266967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64374729186724781334045245 24140523445021793000266967)
    ·
      refine ⟨36210785167532689500400451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140523445021793000266967 36210785167532689500400451)
      ·
        refine ⟨54316177751299034250600677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36210785167532689500400451 54316177751299034250600677)
        ·
          refine ⟨10184283328368568921987627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54316177751299034250600677 10184283328368568921987627)
          ·
            refine ⟨15276424992552853382981441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184283328368568921987627 15276424992552853382981441)
            ·
              refine ⟨11457318744414640037236081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15276424992552853382981441 11457318744414640037236081)
              ·
                refine ⟨8592989058310980027927061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11457318744414640037236081 8592989058310980027927061)
                ·
                  refine ⟨402796362108327188809081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8592989058310980027927061 402796362108327188809081)
                  ·
                    rfl

theorem cell21_1764997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_1764997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1764997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1764997 prefixEnd_1764997 := by exact prefixLift 1764997
  have htrace : WordTrace (prefixWord ++ tailWord_1764997) baseStart_1764997 baseEnd_1764997 := by
    simpa [prefixWord, tailWord_1764997, baseEnd_1764997] using wordTrace_append hprefix tailTrace_1764997
  have hstable : (prefixWord ++ tailWord_1764997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1764997).length < 2 ^ (prefixWord ++ tailWord_1764997).sum := by decide
  have hdescent : baseEnd_1764997 < baseStart_1764997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1764997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765045 : List Nat := [1, 3, 3, 3, 2, 1, 1, 7]
def baseStart_1765045 : Nat := 118140960795 + 1765045 * 2 ^ 59
def prefixEnd_1765045 : Nat := 4983230072969 + 3 ^ 40 * 1765045 * 2
def baseEnd_1765045 : Nat := 134269105454096590669661

theorem tailTrace_1765045 : CollatzResearch.WordTrace tailWord_1765045 prefixEnd_1765045 134269105454096590669661 := by
  unfold tailWord_1765045
  simp only [CollatzResearch.WordTrace]
  refine ⟨64376479890550885531792589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42917653260367257021195059 64376479890550885531792589)
  ·
    refine ⟨24141179958956582074422221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64376479890550885531792589 24141179958956582074422221)
    ·
      refine ⟨9052942484608718277908333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24141179958956582074422221 9052942484608718277908333)
      ·
        refine ⟨3394853431728269354215625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9052942484608718277908333 3394853431728269354215625)
        ·
          refine ⟨2546140073796202015661719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3394853431728269354215625 2546140073796202015661719)
          ·
            refine ⟨3819210110694303023492579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546140073796202015661719 3819210110694303023492579)
            ·
              refine ⟨5728815166041454535238869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819210110694303023492579 5728815166041454535238869)
              ·
                refine ⟨134269105454096590669661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5728815166041454535238869 134269105454096590669661)
                ·
                  rfl

theorem cell21_1765045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 7].length) (baseStart_1765045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765045 prefixEnd_1765045 := by exact prefixLift 1765045
  have htrace : WordTrace (prefixWord ++ tailWord_1765045) baseStart_1765045 baseEnd_1765045 := by
    simpa [prefixWord, tailWord_1765045, baseEnd_1765045] using wordTrace_append hprefix tailTrace_1765045
  have hstable : (prefixWord ++ tailWord_1765045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765045).length < 2 ^ (prefixWord ++ tailWord_1765045).sum := by decide
  have hdescent : baseEnd_1765045 < baseStart_1765045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765062 : List Nat := [6, 1, 2, 1, 1, 1, 9]
def baseStart_1765062 : Nat := 118140960795 + 1765062 * 2 ^ 59
def prefixEnd_1765062 : Nat := 4983230072969 + 3 ^ 40 * 1765062 * 2
def baseEnd_1765062 : Nat := 44756799554877946691735

theorem tailTrace_1765062 : CollatzResearch.WordTrace tailWord_1765062 prefixEnd_1765062 44756799554877946691735 := by
  unfold tailWord_1765062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011784372859040544848795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 42918066620992864956774293 2011784372859040544848795)
  ·
    refine ⟨3017676559288560817273193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011784372859040544848795 3017676559288560817273193)
    ·
      refine ⟨2263257419466420612954895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3017676559288560817273193 2263257419466420612954895)
      ·
        refine ⟨3394886129199630919432343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263257419466420612954895 3394886129199630919432343)
        ·
          refine ⟨5092329193799446379148515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394886129199630919432343 5092329193799446379148515)
          ·
            refine ⟨7638493790699169568722773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092329193799446379148515 7638493790699169568722773)
            ·
              refine ⟨44756799554877946691735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7638493790699169568722773 44756799554877946691735)
              ·
                rfl

theorem cell21_1765062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 9].length) (baseStart_1765062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765062 prefixEnd_1765062 := by exact prefixLift 1765062
  have htrace : WordTrace (prefixWord ++ tailWord_1765062) baseStart_1765062 baseEnd_1765062 := by
    simpa [prefixWord, tailWord_1765062, baseEnd_1765062] using wordTrace_append hprefix tailTrace_1765062
  have hstable : (prefixWord ++ tailWord_1765062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765062).length < 2 ^ (prefixWord ++ tailWord_1765062).sum := by decide
  have hdescent : baseEnd_1765062 < baseStart_1765062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765073 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1765073 : Nat := 118140960795 + 1765073 * 2 ^ 59
def prefixEnd_1765073 : Nat := 4983230072969 + 3 ^ 40 * 1765073 * 2
def baseEnd_1765073 : Nat := 402813706343767945542259

theorem tailTrace_1765073 : CollatzResearch.WordTrace tailWord_1765073 prefixEnd_1765073 402813706343767945542259 := by
  unfold tailWord_1765073
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377501134449446313811873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42918334089632964209207915 64377501134449446313811873)
  ·
    refine ⟨48283125850837084735358905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64377501134449446313811873 48283125850837084735358905)
    ·
      refine ⟨36212344388127813551519179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48283125850837084735358905 36212344388127813551519179)
      ·
        refine ⟨54318516582191720327278769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36212344388127813551519179 54318516582191720327278769)
        ·
          refine ⟨40738887436643790245459077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54318516582191720327278769 40738887436643790245459077)
          ·
            refine ⟨7638541394370710671023577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40738887436643790245459077 7638541394370710671023577)
            ·
              refine ⟨5728906045778033003267683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638541394370710671023577 5728906045778033003267683)
              ·
                refine ⟨8593359068667049504901525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728906045778033003267683 8593359068667049504901525)
                ·
                  refine ⟨402813706343767945542259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8593359068667049504901525 402813706343767945542259)
                  ·
                    rfl

theorem cell21_1765073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1765073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765073 prefixEnd_1765073 := by exact prefixLift 1765073
  have htrace : WordTrace (prefixWord ++ tailWord_1765073) baseStart_1765073 baseEnd_1765073 := by
    simpa [prefixWord, tailWord_1765073, baseEnd_1765073] using wordTrace_append hprefix tailTrace_1765073
  have hstable : (prefixWord ++ tailWord_1765073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765073).length < 2 ^ (prefixWord ++ tailWord_1765073).sum := by decide
  have hdescent : baseEnd_1765073 < baseStart_1765073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765076 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 5]
def baseStart_1765076 : Nat := 118140960795 + 1765076 * 2 ^ 59
def prefixEnd_1765076 : Nat := 4983230072969 + 3 ^ 40 * 1765076 * 2
def baseEnd_1765076 : Nat := 402814390984640606992253

theorem tailTrace_1765076 : CollatzResearch.WordTrace tailWord_1765076 prefixEnd_1765076 402814390984640606992253 := by
  unfold tailWord_1765076
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188805276719288913085541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42918407035625718550780721 32188805276719288913085541)
  ·
    refine ⟨6035400989384866671203539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32188805276719288913085541 6035400989384866671203539)
    ·
      refine ⟨9053101484077300006805309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035400989384866671203539 9053101484077300006805309)
      ·
        refine ⟨3394913056528987502551991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9053101484077300006805309 3394913056528987502551991)
        ·
          refine ⟨5092369584793481253827987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394913056528987502551991 5092369584793481253827987)
          ·
            refine ⟨7638554377190221880741981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092369584793481253827987 7638554377190221880741981)
            ·
              refine ⟨2864457891446333205278243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7638554377190221880741981 2864457891446333205278243)
              ·
                refine ⟨4296686837169499807917365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864457891446333205278243 4296686837169499807917365)
                ·
                  refine ⟨402814390984640606992253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4296686837169499807917365 402814390984640606992253)
                  ·
                    rfl

theorem cell21_1765076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_1765076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765076 prefixEnd_1765076 := by exact prefixLift 1765076
  have htrace : WordTrace (prefixWord ++ tailWord_1765076) baseStart_1765076 baseEnd_1765076 := by
    simpa [prefixWord, tailWord_1765076, baseEnd_1765076] using wordTrace_append hprefix tailTrace_1765076
  have hstable : (prefixWord ++ tailWord_1765076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765076).length < 2 ^ (prefixWord ++ tailWord_1765076).sum := by decide
  have hdescent : baseEnd_1765076 < baseStart_1765076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765127 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 3]
def baseStart_1765127 : Nat := 118140960795 + 1765127 * 2 ^ 59
def prefixEnd_1765127 : Nat := 4983230072969 + 3 ^ 40 * 1765127 * 2
def baseEnd_1765127 : Nat := 402826029879475851642149

theorem tailTrace_1765127 : CollatzResearch.WordTrace tailWord_1765127 prefixEnd_1765127 402826029879475851642149 := by
  unfold tailWord_1765127
  simp only [CollatzResearch.WordTrace]
  refine ⟨64379470676253813536277635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42919647117502542357518423 64379470676253813536277635)
  ·
    refine ⟨96569206014380720304416453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64379470676253813536277635 96569206014380720304416453)
    ·
      refine ⟨18106726127696385057078085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96569206014380720304416453 18106726127696385057078085)
      ·
        refine ⟨3395011148943072198202141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18106726127696385057078085 3395011148943072198202141)
        ·
          refine ⟨1273129180853652074325803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3395011148943072198202141 1273129180853652074325803)
          ·
            refine ⟨1909693771280478111488705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273129180853652074325803 1909693771280478111488705)
            ·
              refine ⟨1432270328460358583616529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1909693771280478111488705 1432270328460358583616529)
              ·
                refine ⟨1074202746345268937712397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432270328460358583616529 1074202746345268937712397)
                ·
                  refine ⟨402826029879475851642149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074202746345268937712397 402826029879475851642149)
                  ·
                    rfl

theorem cell21_1765127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].length) (baseStart_1765127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765127 prefixEnd_1765127 := by exact prefixLift 1765127
  have htrace : WordTrace (prefixWord ++ tailWord_1765127) baseStart_1765127 baseEnd_1765127 := by
    simpa [prefixWord, tailWord_1765127, baseEnd_1765127] using wordTrace_append hprefix tailTrace_1765127
  have hstable : (prefixWord ++ tailWord_1765127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765127).length < 2 ^ (prefixWord ++ tailWord_1765127).sum := by decide
  have hdescent : baseEnd_1765127 < baseStart_1765127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765138 : List Nat := [3, 2, 4, 1, 1, 3, 1, 6]
def baseStart_1765138 : Nat := 118140960795 + 1765138 * 2 ^ 59
def prefixEnd_1765138 : Nat := 4983230072969 + 3 ^ 40 * 1765138 * 2
def baseEnd_1765138 : Nat := 134276180076447425652931

theorem tailTrace_1765138 : CollatzResearch.WordTrace tailWord_1765138 prefixEnd_1765138 134276180076447425652931 := by
  unfold tailWord_1765138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094967969803490603732017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42919914586142641609952045 16094967969803490603732017)
  ·
    refine ⟨12071225977352617952799013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16094967969803490603732017 12071225977352617952799013)
    ·
      refine ⟨2263354870753615866149815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12071225977352617952799013 2263354870753615866149815)
      ·
        refine ⟨3395032306130423799224723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263354870753615866149815 3395032306130423799224723)
        ·
          refine ⟨5092548459195635698837085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395032306130423799224723 5092548459195635698837085)
          ·
            refine ⟨1909705672198363387063907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5092548459195635698837085 1909705672198363387063907)
            ·
              refine ⟨2864558508297545080595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909705672198363387063907 2864558508297545080595861)
              ·
                refine ⟨134276180076447425652931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2864558508297545080595861 134276180076447425652931)
                ·
                  rfl

theorem cell21_1765138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_1765138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765138 prefixEnd_1765138 := by exact prefixLift 1765138
  have htrace : WordTrace (prefixWord ++ tailWord_1765138) baseStart_1765138 baseEnd_1765138 := by
    simpa [prefixWord, tailWord_1765138, baseEnd_1765138] using wordTrace_append hprefix tailTrace_1765138
  have hstable : (prefixWord ++ tailWord_1765138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765138).length < 2 ^ (prefixWord ++ tailWord_1765138).sum := by decide
  have hdescent : baseEnd_1765138 < baseStart_1765138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765183 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 4]
def baseStart_1765183 : Nat := 118140960795 + 1765183 * 2 ^ 59
def prefixEnd_1765183 : Nat := 4983230072969 + 3 ^ 40 * 1765183 * 2
def baseEnd_1765183 : Nat := 402838809842432198708701

theorem tailTrace_1765183 : CollatzResearch.WordTrace tailWord_1765183 prefixEnd_1765183 402838809842432198708701 := by
  unfold tailWord_1765183
  simp only [CollatzResearch.WordTrace]
  refine ⟨64381513164050935100316203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42921008776033956733544135 64381513164050935100316203)
  ·
    refine ⟨96572269746076402650474305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64381513164050935100316203 96572269746076402650474305)
    ·
      refine ⟨72429202309557301987855729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96572269746076402650474305 72429202309557301987855729)
      ·
        refine ⟨54321901732167976490891797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72429202309557301987855729 54321901732167976490891797)
        ·
          refine ⟨2546339143695373898010553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54321901732167976490891797 2546339143695373898010553)
          ·
            refine ⟨1909754357771530423507915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546339143695373898010553 1909754357771530423507915)
            ·
              refine ⟨2864631536657295635261873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909754357771530423507915 2864631536657295635261873)
              ·
                refine ⟨2148473652492971726446405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2864631536657295635261873 2148473652492971726446405)
                ·
                  refine ⟨402838809842432198708701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148473652492971726446405 402838809842432198708701)
                  ·
                    rfl

theorem cell21_1765183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_1765183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765183 prefixEnd_1765183 := by exact prefixLift 1765183
  have htrace : WordTrace (prefixWord ++ tailWord_1765183) baseStart_1765183 baseEnd_1765183 := by
    simpa [prefixWord, tailWord_1765183, baseEnd_1765183] using wordTrace_append hprefix tailTrace_1765183
  have hstable : (prefixWord ++ tailWord_1765183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765183).length < 2 ^ (prefixWord ++ tailWord_1765183).sum := by decide
  have hdescent : baseEnd_1765183 < baseStart_1765183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765228 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_1765228 : Nat := 118140960795 + 1765228 * 2 ^ 59
def prefixEnd_1765228 : Nat := 4983230072969 + 3 ^ 40 * 1765228 * 2
def baseEnd_1765228 : Nat := 402849079455522120458609

theorem tailTrace_1765228 : CollatzResearch.WordTrace tailWord_1765228 prefixEnd_1765228 402849079455522120458609 := by
  unfold tailWord_1765228
  simp only [CollatzResearch.WordTrace]
  refine ⟨32191577224443953892852169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42922102965925271857136225 32191577224443953892852169)
  ·
    refine ⟨24143682918332965419639127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32191577224443953892852169 24143682918332965419639127)
    ·
      refine ⟨36215524377499448129458691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24143682918332965419639127 36215524377499448129458691)
      ·
        refine ⟨54323286566249172194188037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36215524377499448129458691 54323286566249172194188037)
        ·
          refine ⟨10185616231171719786410257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54323286566249172194188037 10185616231171719786410257)
          ·
            refine ⟨7639212173378789839807693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185616231171719786410257 7639212173378789839807693)
            ·
              refine ⟨2864704565017046189927885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7639212173378789839807693 2864704565017046189927885)
              ·
                refine ⟨1074264211881392321222957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864704565017046189927885 1074264211881392321222957)
                ·
                  refine ⟨402849079455522120458609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074264211881392321222957 402849079455522120458609)
                  ·
                    rfl

theorem cell21_1765228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_1765228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765228 prefixEnd_1765228 := by exact prefixLift 1765228
  have htrace : WordTrace (prefixWord ++ tailWord_1765228) baseStart_1765228 baseEnd_1765228 := by
    simpa [prefixWord, tailWord_1765228, baseEnd_1765228] using wordTrace_append hprefix tailTrace_1765228
  have hstable : (prefixWord ++ tailWord_1765228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765228).length < 2 ^ (prefixWord ++ tailWord_1765228).sum := by decide
  have hdescent : baseEnd_1765228 < baseStart_1765228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765397 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 3]
def baseStart_1765397 : Nat := 118140960795 + 1765397 * 2 ^ 59
def prefixEnd_1765397 : Nat := 4983230072969 + 3 ^ 40 * 1765397 * 2
def baseEnd_1765397 : Nat := 402887647558015382141597

theorem tailTrace_1765397 : CollatzResearch.WordTrace tailWord_1765397 prefixEnd_1765397 402887647558015382141597 := by
  unfold tailWord_1765397
  simp only [CollatzResearch.WordTrace]
  refine ⟨64389318385275649648606445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42926212256850433099070963 64389318385275649648606445)
  ·
    refine ⟨24145994394478368618227417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64389318385275649648606445 24145994394478368618227417)
    ·
      refine ⟨18109495795858776463670563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24145994394478368618227417 18109495795858776463670563)
      ·
        refine ⟨27164243693788164695505845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18109495795858776463670563 27164243693788164695505845)
        ·
          refine ⟨2546647846292640440203673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27164243693788164695505845 2546647846292640440203673)
          ·
            refine ⟨1909985884719480330152755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2546647846292640440203673 1909985884719480330152755)
            ·
              refine ⟨2864978827079220495229133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909985884719480330152755 2864978827079220495229133)
              ·
                refine ⟨1074367060154707685710925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864978827079220495229133 1074367060154707685710925)
                ·
                  refine ⟨402887647558015382141597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074367060154707685710925 402887647558015382141597)
                  ·
                    rfl

theorem cell21_1765397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_1765397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765397 prefixEnd_1765397 := by exact prefixLift 1765397
  have htrace : WordTrace (prefixWord ++ tailWord_1765397) baseStart_1765397 baseEnd_1765397 := by
    simpa [prefixWord, tailWord_1765397, baseEnd_1765397] using wordTrace_append hprefix tailTrace_1765397
  have hstable : (prefixWord ++ tailWord_1765397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765397).length < 2 ^ (prefixWord ++ tailWord_1765397).sum := by decide
  have hdescent : baseEnd_1765397 < baseStart_1765397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765484 : List Nat := [2, 2, 1, 1, 3, 5, 1, 6]
def baseStart_1765484 : Nat := 118140960795 + 1765484 * 2 ^ 59
def prefixEnd_1765484 : Nat := 4983230072969 + 3 ^ 40 * 1765484 * 2
def baseEnd_1765484 : Nat := 134302500714440854730473

theorem tailTrace_1765484 : CollatzResearch.WordTrace tailWord_1765484 prefixEnd_1765484 134302500714440854730473 := by
  unfold tailWord_1765484
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196245767980231753511753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42928327690640309004682337 32196245767980231753511753)
  ·
    refine ⟨24147184325985173815133815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32196245767980231753511753 24147184325985173815133815)
    ·
      refine ⟨36220776488977760722700723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147184325985173815133815 36220776488977760722700723)
      ·
        refine ⟨54331164733466641084051085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36220776488977760722700723 54331164733466641084051085)
        ·
          refine ⟨20374186775049990406519157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54331164733466641084051085 20374186775049990406519157)
          ·
            refine ⟨1910080010160936600611171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20374186775049990406519157 1910080010160936600611171)
            ·
              refine ⟨2865120015241404900916757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910080010160936600611171 2865120015241404900916757)
              ·
                refine ⟨134302500714440854730473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2865120015241404900916757 134302500714440854730473)
                ·
                  rfl

theorem cell21_1765484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_1765484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765484 prefixEnd_1765484 := by exact prefixLift 1765484
  have htrace : WordTrace (prefixWord ++ tailWord_1765484) baseStart_1765484 baseEnd_1765484 := by
    simpa [prefixWord, tailWord_1765484, baseEnd_1765484] using wordTrace_append hprefix tailTrace_1765484
  have hstable : (prefixWord ++ tailWord_1765484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765484).length < 2 ^ (prefixWord ++ tailWord_1765484).sum := by decide
  have hdescent : baseEnd_1765484 < baseStart_1765484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765566 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1765566 : Nat := 118140960795 + 1765566 * 2 ^ 59
def prefixEnd_1765566 : Nat := 4983230072969 + 3 ^ 40 * 1765566 * 2
def baseEnd_1765566 : Nat := 402926215660508643824585

theorem tailTrace_1765566 : CollatzResearch.WordTrace tailWord_1765566 prefixEnd_1765566 402926215660508643824585 := by
  unfold tailWord_1765566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049435290207923938938569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42930321547775594341005701 8049435290207923938938569)
  ·
    refine ⟨6037076467655942954203927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8049435290207923938938569 6037076467655942954203927)
    ·
      refine ⟨9055614701483914431305891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037076467655942954203927 9055614701483914431305891)
      ·
        refine ⟨13583422052225871646958837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055614701483914431305891 13583422052225871646958837)
        ·
          refine ⟨1273445817396175466902391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13583422052225871646958837 1273445817396175466902391)
          ·
            refine ⟨1910168726094263200353587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273445817396175466902391 1910168726094263200353587)
            ·
              refine ⟨2865253089141394800530381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910168726094263200353587 2865253089141394800530381)
              ·
                refine ⟨1074469908428023050198893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865253089141394800530381 1074469908428023050198893)
                ·
                  refine ⟨402926215660508643824585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074469908428023050198893 402926215660508643824585)
                  ·
                    rfl

theorem cell21_1765566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1765566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765566 prefixEnd_1765566 := by exact prefixLift 1765566
  have htrace : WordTrace (prefixWord ++ tailWord_1765566) baseStart_1765566 baseEnd_1765566 := by
    simpa [prefixWord, tailWord_1765566, baseEnd_1765566] using wordTrace_append hprefix tailTrace_1765566
  have hstable : (prefixWord ++ tailWord_1765566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765566).length < 2 ^ (prefixWord ++ tailWord_1765566).sum := by decide
  have hdescent : baseEnd_1765566 < baseStart_1765566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765636 : List Nat := [2, 3, 2, 2, 4, 8]
def baseStart_1765636 : Nat := 118140960795 + 1765636 * 2 ^ 59
def prefixEnd_1765636 : Nat := 4983230072969 + 3 ^ 40 * 1765636 * 2
def baseEnd_1765636 : Nat := 14923784837563113987325

theorem tailTrace_1765636 : CollatzResearch.WordTrace tailWord_1765636 prefixEnd_1765636 14923784837563113987325 := by
  unfold tailWord_1765636
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199017715704896733278381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42932023620939862311037841 32199017715704896733278381)
  ·
    refine ⟨12074631643389336274979393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32199017715704896733278381 12074631643389336274979393)
    ·
      refine ⟨9055973732542002206234545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12074631643389336274979393 9055973732542002206234545)
      ·
        refine ⟨6791980299406501654675909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9055973732542002206234545 6791980299406501654675909)
        ·
          refine ⟨1273496306138719060251733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6791980299406501654675909 1273496306138719060251733)
          ·
            refine ⟨14923784837563113987325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1273496306138719060251733 14923784837563113987325)
            ·
              rfl

theorem cell21_1765636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 8].length) (baseStart_1765636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765636 prefixEnd_1765636 := by exact prefixLift 1765636
  have htrace : WordTrace (prefixWord ++ tailWord_1765636) baseStart_1765636 baseEnd_1765636 := by
    simpa [prefixWord, tailWord_1765636, baseEnd_1765636] using wordTrace_append hprefix tailTrace_1765636
  have hstable : (prefixWord ++ tailWord_1765636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765636).length < 2 ^ (prefixWord ++ tailWord_1765636).sum := by decide
  have hdescent : baseEnd_1765636 < baseStart_1765636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765639 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 4]
def baseStart_1765639 : Nat := 118140960795 + 1765639 * 2 ^ 59
def prefixEnd_1765639 : Nat := 4983230072969 + 3 ^ 40 * 1765639 * 2
def baseEnd_1765639 : Nat := 402942875255076739107769

theorem tailTrace_1765639 : CollatzResearch.WordTrace tailWord_1765639 prefixEnd_1765639 402942875255076739107769 := by
  unfold tailWord_1765639
  simp only [CollatzResearch.WordTrace]
  refine ⟨64398144850398924978915971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42932096566932616652610647 64398144850398924978915971)
  ·
    refine ⟨96597217275598387468373957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64398144850398924978915971 96597217275598387468373957)
    ·
      refine ⟨18111978239174697650320117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96597217275598387468373957 18111978239174697650320117)
      ·
        refine ⟨1697997959922627904717511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18111978239174697650320117 1697997959922627904717511)
        ·
          refine ⟨2546996939883941857076267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697997959922627904717511 2546996939883941857076267)
          ·
            refine ⟨3820495409825912785614401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546996939883941857076267 3820495409825912785614401)
            ·
              refine ⟨2865371557369434589210801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820495409825912785614401 2865371557369434589210801)
              ·
                refine ⟨2149028668027075941908101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865371557369434589210801 2149028668027075941908101)
                ·
                  refine ⟨402942875255076739107769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149028668027075941908101 402942875255076739107769)
                  ·
                    rfl

theorem cell21_1765639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_1765639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765639 prefixEnd_1765639 := by exact prefixLift 1765639
  have htrace : WordTrace (prefixWord ++ tailWord_1765639) baseStart_1765639 baseEnd_1765639 := by
    simpa [prefixWord, tailWord_1765639, baseEnd_1765639] using wordTrace_append hprefix tailTrace_1765639
  have hstable : (prefixWord ++ tailWord_1765639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765639).length < 2 ^ (prefixWord ++ tailWord_1765639).sum := by decide
  have hdescent : baseEnd_1765639 < baseStart_1765639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765684 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1765684 : Nat := 118140960795 + 1765684 * 2 ^ 59
def prefixEnd_1765684 : Nat := 4983230072969 + 3 ^ 40 * 1765684 * 2
def baseEnd_1765684 : Nat := 402953144868166660857677

theorem tailTrace_1765684 : CollatzResearch.WordTrace tailWord_1765684 prefixEnd_1765684 402953144868166660857677 := by
  unfold tailWord_1765684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199893067617948832152053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42933190756823931776202737 32199893067617948832152053)
  ·
    refine ⟨3018739975089182703014255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32199893067617948832152053 3018739975089182703014255)
    ·
      refine ⟨4528109962633774054521383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3018739975089182703014255 4528109962633774054521383)
      ·
        refine ⟨6792164943950661081782075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528109962633774054521383 6792164943950661081782075)
        ·
          refine ⟨10188247415925991622673113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792164943950661081782075 10188247415925991622673113)
          ·
            refine ⟨7641185561944493717004835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10188247415925991622673113 7641185561944493717004835)
            ·
              refine ⟨11461778342916740575507253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641185561944493717004835 11461778342916740575507253)
              ·
                refine ⟨1074541719648444428953805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11461778342916740575507253 1074541719648444428953805)
                ·
                  refine ⟨402953144868166660857677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074541719648444428953805 402953144868166660857677)
                  ·
                    rfl

theorem cell21_1765684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1765684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765684 prefixEnd_1765684 := by exact prefixLift 1765684
  have htrace : WordTrace (prefixWord ++ tailWord_1765684) baseStart_1765684 baseEnd_1765684 := by
    simpa [prefixWord, tailWord_1765684, baseEnd_1765684] using wordTrace_append hprefix tailTrace_1765684
  have hstable : (prefixWord ++ tailWord_1765684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765684).length < 2 ^ (prefixWord ++ tailWord_1765684).sum := by decide
  have hdescent : baseEnd_1765684 < baseStart_1765684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765771 : List Nat := [1, 1, 1, 1, 4, 5, 2, 6]
def baseStart_1765771 : Nat := 118140960795 + 1765771 * 2 ^ 59
def prefixEnd_1765771 : Nat := 4983230072969 + 3 ^ 40 * 1765771 * 2
def baseEnd_1765771 : Nat := 134324333151157947635833

theorem tailTrace_1765771 : CollatzResearch.WordTrace tailWord_1765771 prefixEnd_1765771 134324333151157947635833 := by
  unfold tailWord_1765771
  simp only [CollatzResearch.WordTrace]
  refine ⟨64402959285920711522721167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42935306190613807681814111 64402959285920711522721167)
  ·
    refine ⟨96604438928881067284081751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64402959285920711522721167 96604438928881067284081751)
    ·
      refine ⟨144906658393321600926122627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96604438928881067284081751 144906658393321600926122627)
      ·
        refine ⟨217359987589982401389183941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144906658393321600926122627 217359987589982401389183941)
        ·
          refine ⟨40754997673121700260471989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217359987589982401389183941 40754997673121700260471989)
          ·
            refine ⟨3820781031855159399419249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40754997673121700260471989 3820781031855159399419249)
            ·
              refine ⟨2865585773891369549564437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820781031855159399419249 2865585773891369549564437)
              ·
                refine ⟨134324333151157947635833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2865585773891369549564437 134324333151157947635833)
                ·
                  rfl

theorem cell21_1765771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 6].length) (baseStart_1765771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765771 prefixEnd_1765771 := by exact prefixLift 1765771
  have htrace : WordTrace (prefixWord ++ tailWord_1765771) baseStart_1765771 baseEnd_1765771 := by
    simpa [prefixWord, tailWord_1765771, baseEnd_1765771] using wordTrace_append hprefix tailTrace_1765771
  have hstable : (prefixWord ++ tailWord_1765771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765771).length < 2 ^ (prefixWord ++ tailWord_1765771).sum := by decide
  have hdescent : baseEnd_1765771 < baseStart_1765771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765774 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_1765774 : Nat := 118140960795 + 1765774 * 2 ^ 59
def prefixEnd_1765774 : Nat := 4983230072969 + 3 ^ 40 * 1765774 * 2
def baseEnd_1765774 : Nat := 402973684094346504357493

theorem tailTrace_1765774 : CollatzResearch.WordTrace tailWord_1765774 prefixEnd_1765774 402973684094346504357493 := by
  unfold tailWord_1765774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050383588113730379385047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42935379136606562023386917 8050383588113730379385047)
  ·
    refine ⟨12075575382170595569077571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8050383588113730379385047 12075575382170595569077571)
    ·
      refine ⟨18113363073255893353616357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12075575382170595569077571 18113363073255893353616357)
      ·
        refine ⟨3396255576235480003803067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18113363073255893353616357 3396255576235480003803067)
        ·
          refine ⟨5094383364353220005704601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396255576235480003803067 5094383364353220005704601)
          ·
            refine ⟨3820787523264915004278451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094383364353220005704601 3820787523264915004278451)
            ·
              refine ⟨5731181284897372506417677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820787523264915004278451 5731181284897372506417677)
              ·
                refine ⟨2149192981836514689906629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5731181284897372506417677 2149192981836514689906629)
                ·
                  refine ⟨402973684094346504357493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149192981836514689906629 402973684094346504357493)
                  ·
                    rfl

theorem cell21_1765774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_1765774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765774 prefixEnd_1765774 := by exact prefixLift 1765774
  have htrace : WordTrace (prefixWord ++ tailWord_1765774) baseStart_1765774 baseEnd_1765774 := by
    simpa [prefixWord, tailWord_1765774, baseEnd_1765774] using wordTrace_append hprefix tailTrace_1765774
  have hstable : (prefixWord ++ tailWord_1765774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765774).length < 2 ^ (prefixWord ++ tailWord_1765774).sum := by decide
  have hdescent : baseEnd_1765774 < baseStart_1765774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765785 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_1765785 : Nat := 118140960795 + 1765785 * 2 ^ 59
def prefixEnd_1765785 : Nat := 4983230072969 + 3 ^ 40 * 1765785 * 2
def baseEnd_1765785 : Nat := 402976194444212929674137

theorem tailTrace_1765785 : CollatzResearch.WordTrace tailWord_1765785 prefixEnd_1765785 402976194444212929674137 := by
  unfold tailWord_1765785
  simp only [CollatzResearch.WordTrace]
  refine ⟨64403469907869991913730809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42935646605246661275820539 64403469907869991913730809)
  ·
    refine ⟨48302602430902493935298107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64403469907869991913730809 48302602430902493935298107)
    ·
      refine ⟨72453903646353740902947161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48302602430902493935298107 72453903646353740902947161)
      ·
        refine ⟨54340427734765305677210371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72453903646353740902947161 54340427734765305677210371)
        ·
          refine ⟨81510641602147958515815557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54340427734765305677210371 81510641602147958515815557)
          ·
            refine ⟨15283245300402742221715417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81510641602147958515815557 15283245300402742221715417)
            ·
              refine ⟨11462433975302056666286563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15283245300402742221715417 11462433975302056666286563)
              ·
                refine ⟨17193650962953084999429845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462433975302056666286563 17193650962953084999429845)
                ·
                  refine ⟨402976194444212929674137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17193650962953084999429845 402976194444212929674137)
                  ·
                    rfl

theorem cell21_1765785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_1765785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765785 prefixEnd_1765785 := by exact prefixLift 1765785
  have htrace : WordTrace (prefixWord ++ tailWord_1765785) baseStart_1765785 baseEnd_1765785 := by
    simpa [prefixWord, tailWord_1765785, baseEnd_1765785] using wordTrace_append hprefix tailTrace_1765785
  have hstable : (prefixWord ++ tailWord_1765785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765785).length < 2 ^ (prefixWord ++ tailWord_1765785).sum := by decide
  have hdescent : baseEnd_1765785 < baseStart_1765785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765912 : List Nat := [2, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_1765912 : Nat := 118140960795 + 1765912 * 2 ^ 59
def prefixEnd_1765912 : Nat := 4983230072969 + 3 ^ 40 * 1765912 * 2
def baseEnd_1765912 : Nat := 403005177574488931057211

theorem tailTrace_1765912 : CollatzResearch.WordTrace tailWord_1765912 prefixEnd_1765912 403005177574488931057211 := by
  unfold tailWord_1765912
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204050989204946301801995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42938734652273261735735993 32204050989204946301801995)
  ·
    refine ⟨48306076483807419452702993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32204050989204946301801995 48306076483807419452702993)
    ·
      refine ⟨36229557362855564589527245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48306076483807419452702993 36229557362855564589527245)
      ·
        refine ⟨13586084011070836721072717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36229557362855564589527245 13586084011070836721072717)
        ·
          refine ⟨5094781504151563770402269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13586084011070836721072717 5094781504151563770402269)
          ·
            refine ⟨1910543064056836413900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5094781504151563770402269 1910543064056836413900851)
            ·
              refine ⟨2865814596085254620851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910543064056836413900851 2865814596085254620851277)
              ·
                refine ⟨1074680473531970482819229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2865814596085254620851277 1074680473531970482819229)
                ·
                  refine ⟨403005177574488931057211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074680473531970482819229 403005177574488931057211)
                  ·
                    rfl

theorem cell21_1765912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_1765912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765912 prefixEnd_1765912 := by exact prefixLift 1765912
  have htrace : WordTrace (prefixWord ++ tailWord_1765912) baseStart_1765912 baseEnd_1765912 := by
    simpa [prefixWord, tailWord_1765912, baseEnd_1765912] using wordTrace_append hprefix tailTrace_1765912
  have hstable : (prefixWord ++ tailWord_1765912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765912).length < 2 ^ (prefixWord ++ tailWord_1765912).sum := by decide
  have hdescent : baseEnd_1765912 < baseStart_1765912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765923 : List Nat := [1, 1, 1, 4, 4, 3, 7]
def baseStart_1765923 : Nat := 118140960795 + 1765923 * 2 ^ 59
def prefixEnd_1765923 : Nat := 4983230072969 + 3 ^ 40 * 1765923 * 2
def baseEnd_1765923 : Nat := 44778631991595039597095

theorem tailTrace_1765923 : CollatzResearch.WordTrace tailWord_1765923 prefixEnd_1765923 44778631991595039597095 := by
  unfold tailWord_1765923
  simp only [CollatzResearch.WordTrace]
  refine ⟨64408503181370041482254423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42939002120913360988169615 64408503181370041482254423)
  ·
    refine ⟨96612754772055062223381635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64408503181370041482254423 96612754772055062223381635)
    ·
      refine ⟨144919132158082593335072453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96612754772055062223381635 144919132158082593335072453)
      ·
        refine ⟨27172337279640486250326085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144919132158082593335072453 27172337279640486250326085)
        ·
          refine ⟨5094813239932591171936141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27172337279640486250326085 5094813239932591171936141)
          ·
            refine ⟨1910554964974721689476053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5094813239932591171936141 1910554964974721689476053)
            ·
              refine ⟨44778631991595039597095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1910554964974721689476053 44778631991595039597095)
              ·
                rfl

theorem cell21_1765923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 7].length) (baseStart_1765923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765923 prefixEnd_1765923 := by exact prefixLift 1765923
  have htrace : WordTrace (prefixWord ++ tailWord_1765923) baseStart_1765923 baseEnd_1765923 := by
    simpa [prefixWord, tailWord_1765923, baseEnd_1765923] using wordTrace_append hprefix tailTrace_1765923
  have hstable : (prefixWord ++ tailWord_1765923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765923).length < 2 ^ (prefixWord ++ tailWord_1765923).sum := by decide
  have hdescent : baseEnd_1765923 < baseStart_1765923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1765985 : List Nat := [1, 2, 3, 1, 1, 5, 2, 2, 4]
def baseStart_1765985 : Nat := 118140960795 + 1765985 * 2 ^ 59
def prefixEnd_1765985 : Nat := 4983230072969 + 3 ^ 40 * 1765985 * 2
def baseEnd_1765985 : Nat := 403021837169057026340395

theorem tailTrace_1765985 : CollatzResearch.WordTrace tailWord_1765985 prefixEnd_1765985 403021837169057026340395 := by
  unfold tailWord_1765985
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410764507145426071011409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42940509671430284047340939 64410764507145426071011409)
  ·
    refine ⟨48308073380359069553258557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64410764507145426071011409 48308073380359069553258557)
    ·
      refine ⟨18115527517634651082471959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48308073380359069553258557 18115527517634651082471959)
      ·
        refine ⟨27173291276451976623707939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18115527517634651082471959 27173291276451976623707939)
        ·
          refine ⟨40759936914677964935561909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27173291276451976623707939 40759936914677964935561909)
          ·
            refine ⟨3821244085751059212708929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40759936914677964935561909 3821244085751059212708929)
            ·
              refine ⟨2865933064313294409531697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3821244085751059212708929 2865933064313294409531697)
              ·
                refine ⟨2149449798234970807148773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865933064313294409531697 2149449798234970807148773)
                ·
                  refine ⟨403021837169057026340395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149449798234970807148773 403021837169057026340395)
                  ·
                    rfl

theorem cell21_1765985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 4].length) (baseStart_1765985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1765985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1765985 prefixEnd_1765985 := by exact prefixLift 1765985
  have htrace : WordTrace (prefixWord ++ tailWord_1765985) baseStart_1765985 baseEnd_1765985 := by
    simpa [prefixWord, tailWord_1765985, baseEnd_1765985] using wordTrace_append hprefix tailTrace_1765985
  have hstable : (prefixWord ++ tailWord_1765985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1765985).length < 2 ^ (prefixWord ++ tailWord_1765985).sum := by decide
  have hdescent : baseEnd_1765985 < baseStart_1765985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1765985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766165 : List Nat := [1, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_1766165 : Nat := 118140960795 + 1766165 * 2 ^ 59
def prefixEnd_1766165 : Nat := 4983230072969 + 3 ^ 40 * 1766165 * 2
def baseEnd_1766165 : Nat := 403062915621416713340027

theorem tailTrace_1766165 : CollatzResearch.WordTrace tailWord_1766165 prefixEnd_1766165 403062915621416713340027 := by
  unfold tailWord_1766165
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417329646493316812563949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42944886430995544541709299 64417329646493316812563949)
  ·
    refine ⟨24156498617434993804711481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64417329646493316812563949 24156498617434993804711481)
    ·
      refine ⟨18117373963076245353533611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24156498617434993804711481 18117373963076245353533611)
      ·
        refine ⟨27176060944614368030300417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18117373963076245353533611 27176060944614368030300417)
        ·
          refine ⟨20382045708460776022725313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27176060944614368030300417 20382045708460776022725313)
          ·
            refine ⟨15286534281345582017043985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20382045708460776022725313 15286534281345582017043985)
            ·
              refine ⟨11464900711009186512782989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15286534281345582017043985 11464900711009186512782989)
              ·
                refine ⟨4299337766628444942293621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11464900711009186512782989 4299337766628444942293621)
                ·
                  refine ⟨403062915621416713340027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4299337766628444942293621 403062915621416713340027)
                  ·
                    rfl

theorem cell21_1766165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_1766165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766165 prefixEnd_1766165 := by exact prefixLift 1766165
  have htrace : WordTrace (prefixWord ++ tailWord_1766165) baseStart_1766165 baseEnd_1766165 := by
    simpa [prefixWord, tailWord_1766165, baseEnd_1766165] using wordTrace_append hprefix tailTrace_1766165
  have hstable : (prefixWord ++ tailWord_1766165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766165).length < 2 ^ (prefixWord ++ tailWord_1766165).sum := by decide
  have hdescent : baseEnd_1766165 < baseStart_1766165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766179 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_1766179 : Nat := 118140960795 + 1766179 * 2 ^ 59
def prefixEnd_1766179 : Nat := 4983230072969 + 3 ^ 40 * 1766179 * 2
def baseEnd_1766179 : Nat := 403066110612155800106665

theorem tailTrace_1766179 : CollatzResearch.WordTrace tailWord_1766179 prefixEnd_1766179 403066110612155800106665 := by
  unfold tailWord_1766179
  simp only [CollatzResearch.WordTrace]
  refine ⟨64417840268442597203573591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42945226845628398135715727 64417840268442597203573591)
  ·
    refine ⟨96626760402663895805360387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64417840268442597203573591 96626760402663895805360387)
    ·
      refine ⟨144940140603995843708040581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96626760402663895805360387 144940140603995843708040581)
      ·
        refine ⟨27176276363249220695257609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144940140603995843708040581 27176276363249220695257609)
        ·
          refine ⟨20382207272436915521443207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27176276363249220695257609 20382207272436915521443207)
          ·
            refine ⟨30573310908655373282164811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20382207272436915521443207 30573310908655373282164811)
            ·
              refine ⟨45859966362983059923247217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30573310908655373282164811 45859966362983059923247217)
              ·
                refine ⟨34394974772237294942435413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45859966362983059923247217 34394974772237294942435413)
                ·
                  refine ⟨403066110612155800106665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34394974772237294942435413 403066110612155800106665)
                  ·
                    rfl

theorem cell21_1766179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_1766179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766179 prefixEnd_1766179 := by exact prefixLift 1766179
  have htrace : WordTrace (prefixWord ++ tailWord_1766179) baseStart_1766179 baseEnd_1766179 := by
    simpa [prefixWord, tailWord_1766179, baseEnd_1766179] using wordTrace_append hprefix tailTrace_1766179
  have hstable : (prefixWord ++ tailWord_1766179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766179).length < 2 ^ (prefixWord ++ tailWord_1766179).sum := by decide
  have hdescent : baseEnd_1766179 < baseStart_1766179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766244 : List Nat := [2, 3, 1, 1, 4, 3, 2, 5]
def baseStart_1766244 : Nat := 118140960795 + 1766244 * 2 ^ 59
def prefixEnd_1766244 : Nat := 4983230072969 + 3 ^ 40 * 1766244 * 2
def baseEnd_1766244 : Nat := 134360314832576710507733

theorem tailTrace_1766244 : CollatzResearch.WordTrace tailWord_1766244 prefixEnd_1766244 134360314832576710507733 := by
  unfold tailWord_1766244
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210105506603556652344893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42946807342138075536459857 32210105506603556652344893)
  ·
    refine ⟨12078789564976333744629335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32210105506603556652344893 12078789564976333744629335)
    ·
      refine ⟨18118184347464500616944003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12078789564976333744629335 18118184347464500616944003)
      ·
        refine ⟨27177276521196750925416005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18118184347464500616944003 27177276521196750925416005)
        ·
          refine ⟨5095739347724390798515501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27177276521196750925416005 5095739347724390798515501)
          ·
            refine ⟨1910902255396646549443313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5095739347724390798515501 1910902255396646549443313)
            ·
              refine ⟨1433176691547484912082485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1910902255396646549443313 1433176691547484912082485)
              ·
                refine ⟨134360314832576710507733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1433176691547484912082485 134360314832576710507733)
                ·
                  rfl

theorem cell21_1766244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_1766244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766244 prefixEnd_1766244 := by exact prefixLift 1766244
  have htrace : WordTrace (prefixWord ++ tailWord_1766244) baseStart_1766244 baseEnd_1766244 := by
    simpa [prefixWord, tailWord_1766244, baseEnd_1766244] using wordTrace_append hprefix tailTrace_1766244
  have hstable : (prefixWord ++ tailWord_1766244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766244).length < 2 ^ (prefixWord ++ tailWord_1766244).sum := by decide
  have hdescent : baseEnd_1766244 < baseStart_1766244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766275 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 3]
def baseStart_1766275 : Nat := 118140960795 + 1766275 * 2 ^ 59
def prefixEnd_1766275 : Nat := 4983230072969 + 3 ^ 40 * 1766275 * 2
def baseEnd_1766275 : Nat := 403088019120080966506469

theorem tailTrace_1766275 : CollatzResearch.WordTrace tailWord_1766275 prefixEnd_1766275 403088019120080966506469 := by
  unfold tailWord_1766275
  simp only [CollatzResearch.WordTrace]
  refine ⟨64421341676094805599068279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42947561117396537066045519 64421341676094805599068279)
  ·
    refine ⟨96632012514142208398602419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64421341676094805599068279 96632012514142208398602419)
    ·
      refine ⟨144948018771213312597903629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96632012514142208398602419 144948018771213312597903629)
      ·
        refine ⟨54355507039204992224213861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144948018771213312597903629 54355507039204992224213861)
        ·
          refine ⟨10191657569850936042040099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54355507039204992224213861 10191657569850936042040099)
          ·
            refine ⟨15287486354776404063060149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191657569850936042040099 15287486354776404063060149)
            ·
              refine ⟨1433201845760287880911889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15287486354776404063060149 1433201845760287880911889)
              ·
                refine ⟨1074901384320215910683917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433201845760287880911889 1074901384320215910683917)
                ·
                  refine ⟨403088019120080966506469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074901384320215910683917 403088019120080966506469)
                  ·
                    rfl

theorem cell21_1766275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 3].length) (baseStart_1766275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766275 prefixEnd_1766275 := by exact prefixLift 1766275
  have htrace : WordTrace (prefixWord ++ tailWord_1766275) baseStart_1766275 baseEnd_1766275 := by
    simpa [prefixWord, tailWord_1766275, baseEnd_1766275] using wordTrace_append hprefix tailTrace_1766275
  have hstable : (prefixWord ++ tailWord_1766275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766275).length < 2 ^ (prefixWord ++ tailWord_1766275).sum := by decide
  have hdescent : baseEnd_1766275 < baseStart_1766275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766326 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1766326 : Nat := 118140960795 + 1766326 * 2 ^ 59
def prefixEnd_1766326 : Nat := 4983230072969 + 3 ^ 40 * 1766326 * 2
def baseEnd_1766326 : Nat := 403099658014916211156365

theorem tailTrace_1766326 : CollatzResearch.WordTrace tailWord_1766326 prefixEnd_1766326 403099658014916211156365 := by
  unfold tailWord_1766326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026450112431877581823427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42948801199273360872783221 4026450112431877581823427)
  ·
    refine ⟨6039675168647816372735141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026450112431877581823427 6039675168647816372735141)
    ·
      refine ⟨1132439094121465569887839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6039675168647816372735141 1132439094121465569887839)
      ·
        refine ⟨1698658641182198354831759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132439094121465569887839 1698658641182198354831759)
        ·
          refine ⟨2547987961773297532247639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698658641182198354831759 2547987961773297532247639)
          ·
            refine ⟨3821981942659946298371459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547987961773297532247639 3821981942659946298371459)
            ·
              refine ⟨5732972913989919447557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821981942659946298371459 5732972913989919447557189)
              ·
                refine ⟨1074932421373109896416973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5732972913989919447557189 1074932421373109896416973)
                ·
                  refine ⟨403099658014916211156365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074932421373109896416973 403099658014916211156365)
                  ·
                    rfl

theorem cell21_1766326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1766326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766326 prefixEnd_1766326 := by exact prefixLift 1766326
  have htrace : WordTrace (prefixWord ++ tailWord_1766326) baseStart_1766326 baseEnd_1766326 := by
    simpa [prefixWord, tailWord_1766326, baseEnd_1766326] using wordTrace_append hprefix tailTrace_1766326
  have hstable : (prefixWord ++ tailWord_1766326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766326).length < 2 ^ (prefixWord ++ tailWord_1766326).sum := by decide
  have hdescent : baseEnd_1766326 < baseStart_1766326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766348 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_1766348 : Nat := 118140960795 + 1766348 * 2 ^ 59
def prefixEnd_1766348 : Nat := 4983230072969 + 3 ^ 40 * 1766348 * 2
def baseEnd_1766348 : Nat := 403104678714649061789653

theorem tailTrace_1766348 : CollatzResearch.WordTrace tailWord_1766348 prefixEnd_1766348 403104678714649061789653 := by
  unfold tailWord_1766348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32212002102415169533237849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42949336136553559377650465 32212002102415169533237849)
  ·
    refine ⟨24159001576811377149928387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32212002102415169533237849 24159001576811377149928387)
    ·
      refine ⟨36238502365217065724892581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24159001576811377149928387 36238502365217065724892581)
      ·
        refine ⟨6794719193478199823417359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36238502365217065724892581 6794719193478199823417359)
        ·
          refine ⟨10192078790217299735126039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794719193478199823417359 10192078790217299735126039)
          ·
            refine ⟨15288118185325949602689059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192078790217299735126039 15288118185325949602689059)
            ·
              refine ⟨22932177277988924404033589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15288118185325949602689059 22932177277988924404033589)
              ·
                refine ⟨2149891619811461662878149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22932177277988924404033589 2149891619811461662878149)
                ·
                  refine ⟨403104678714649061789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149891619811461662878149 403104678714649061789653)
                  ·
                    rfl

theorem cell21_1766348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_1766348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766348 prefixEnd_1766348 := by exact prefixLift 1766348
  have htrace : WordTrace (prefixWord ++ tailWord_1766348) baseStart_1766348 baseEnd_1766348 := by
    simpa [prefixWord, tailWord_1766348, baseEnd_1766348] using wordTrace_append hprefix tailTrace_1766348
  have hstable : (prefixWord ++ tailWord_1766348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766348).length < 2 ^ (prefixWord ++ tailWord_1766348).sum := by decide
  have hdescent : baseEnd_1766348 < baseStart_1766348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766382 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1766382 : Nat := 118140960795 + 1766382 * 2 ^ 59
def prefixEnd_1766382 : Nat := 4983230072969 + 3 ^ 40 * 1766382 * 2
def baseEnd_1766382 : Nat := 403112437977872558222917

theorem tailTrace_1766382 : CollatzResearch.WordTrace tailWord_1766382 prefixEnd_1766382 403112437977872558222917 := by
  unfold tailWord_1766382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053155535838395359151675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42950162857804775248808933 8053155535838395359151675)
  ·
    refine ⟨12079733303757593038727513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8053155535838395359151675 12079733303757593038727513)
    ·
      refine ⟨9059799977818194779045635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12079733303757593038727513 9059799977818194779045635)
      ·
        refine ⟨13589699966727292168568453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059799977818194779045635 13589699966727292168568453)
        ·
          refine ⟨2548068743761367281606585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13589699966727292168568453 2548068743761367281606585)
          ·
            refine ⟨1911051557821025461204939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548068743761367281606585 1911051557821025461204939)
            ·
              refine ⟨2866577336731538191807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911051557821025461204939 2866577336731538191807409)
              ·
                refine ⟨2149933002548653643855557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866577336731538191807409 2149933002548653643855557)
                ·
                  refine ⟨403112437977872558222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2149933002548653643855557 403112437977872558222917)
                  ·
                    rfl

theorem cell21_1766382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1766382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766382 prefixEnd_1766382 := by exact prefixLift 1766382
  have htrace : WordTrace (prefixWord ++ tailWord_1766382) baseStart_1766382 baseEnd_1766382 := by
    simpa [prefixWord, tailWord_1766382, baseEnd_1766382] using wordTrace_append hprefix tailTrace_1766382
  have hstable : (prefixWord ++ tailWord_1766382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766382).length < 2 ^ (prefixWord ++ tailWord_1766382).sum := by decide
  have hdescent : baseEnd_1766382 < baseStart_1766382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766393 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_1766393 : Nat := 118140960795 + 1766393 * 2 ^ 59
def prefixEnd_1766393 : Nat := 4983230072969 + 3 ^ 40 * 1766393 * 2
def baseEnd_1766393 : Nat := 403114948327738983539561

theorem tailTrace_1766393 : CollatzResearch.WordTrace tailWord_1766393 prefixEnd_1766393 403114948327738983539561 := by
  unfold tailWord_1766393
  simp only [CollatzResearch.WordTrace]
  refine ⟨64425645489667311751863833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42950430326444874501242555 64425645489667311751863833)
  ·
    refine ⟨48319234117250483813897875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64425645489667311751863833 48319234117250483813897875)
    ·
      refine ⟨72478851175875725720846813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48319234117250483813897875 72478851175875725720846813)
      ·
        refine ⟨27179569190953397145317555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72478851175875725720846813 27179569190953397145317555)
        ·
          refine ⟨40769353786430095717976333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27179569190953397145317555 40769353786430095717976333)
          ·
            refine ⟨15288507669911285894241125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40769353786430095717976333 15288507669911285894241125)
            ·
              refine ⟨2866595188108366105170211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15288507669911285894241125 2866595188108366105170211)
              ·
                refine ⟨4299892782162549157755317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866595188108366105170211 4299892782162549157755317)
                ·
                  refine ⟨403114948327738983539561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4299892782162549157755317 403114948327738983539561)
                  ·
                    rfl

theorem cell21_1766393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_1766393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766393 prefixEnd_1766393 := by exact prefixLift 1766393
  have htrace : WordTrace (prefixWord ++ tailWord_1766393) baseStart_1766393 baseEnd_1766393 := by
    simpa [prefixWord, tailWord_1766393, baseEnd_1766393] using wordTrace_append hprefix tailTrace_1766393
  have hstable : (prefixWord ++ tailWord_1766393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766393).length < 2 ^ (prefixWord ++ tailWord_1766393).sum := by decide
  have hdescent : baseEnd_1766393 < baseStart_1766393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766503 : List Nat := [1, 1, 5, 1, 1, 3, 4, 2, 3]
def baseStart_1766503 : Nat := 118140960795 + 1766503 * 2 ^ 59
def prefixEnd_1766503 : Nat := 4983230072969 + 3 ^ 40 * 1766503 * 2
def baseEnd_1766503 : Nat := 403140051826403236706003

theorem tailTrace_1766503 : CollatzResearch.WordTrace tailWord_1766503 prefixEnd_1766503 403140051826403236706003 := by
  unfold tailWord_1766503
  simp only [CollatzResearch.WordTrace]
  refine ⟨64429657519268800538368163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42953105012845867025578775 64429657519268800538368163)
  ·
    refine ⟨96644486278903200807552245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64429657519268800538368163 96644486278903200807552245)
    ·
      refine ⟨9060420588647175075708023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96644486278903200807552245 9060420588647175075708023)
      ·
        refine ⟨13590630882970762613562035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060420588647175075708023 13590630882970762613562035)
        ·
          refine ⟨20385946324456143920343053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13590630882970762613562035 20385946324456143920343053)
          ·
            refine ⟨7644729871671053970128645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20385946324456143920343053 7644729871671053970128645)
            ·
              refine ⟨1433386850938322619399121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7644729871671053970128645 1433386850938322619399121)
              ·
                refine ⟨1075040138203741964549341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1433386850938322619399121 1075040138203741964549341)
                ·
                  refine ⟨403140051826403236706003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075040138203741964549341 403140051826403236706003)
                  ·
                    rfl

theorem cell21_1766503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 2, 3].length) (baseStart_1766503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766503 prefixEnd_1766503 := by exact prefixLift 1766503
  have htrace : WordTrace (prefixWord ++ tailWord_1766503) baseStart_1766503 baseEnd_1766503 := by
    simpa [prefixWord, tailWord_1766503, baseEnd_1766503] using wordTrace_append hprefix tailTrace_1766503
  have hstable : (prefixWord ++ tailWord_1766503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766503).length < 2 ^ (prefixWord ++ tailWord_1766503).sum := by decide
  have hdescent : baseEnd_1766503 < baseStart_1766503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766528 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_1766528 : Nat := 118140960795 + 1766528 * 2 ^ 59
def prefixEnd_1766528 : Nat := 4983230072969 + 3 ^ 40 * 1766528 * 2
def baseEnd_1766528 : Nat := 403145757167008748789285

theorem tailTrace_1766528 : CollatzResearch.WordTrace tailWord_1766528 prefixEnd_1766528 403145757167008748789285 := by
  unfold tailWord_1766528
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215284672089114904014119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42953712896118819872018825 32215284672089114904014119)
  ·
    refine ⟨48322927008133672356021179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215284672089114904014119 48322927008133672356021179)
    ·
      refine ⟨72484390512200508534031769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48322927008133672356021179 72484390512200508534031769)
      ·
        refine ⟨54363292884150381400523827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72484390512200508534031769 54363292884150381400523827)
        ·
          refine ⟨81544939326225572100785741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54363292884150381400523827 81544939326225572100785741)
          ·
            refine ⟨30579352247334589537794653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81544939326225572100785741 30579352247334589537794653)
            ·
              refine ⟨11467257092750471076672995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30579352247334589537794653 11467257092750471076672995)
              ·
                refine ⟨17200885639125706615009493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467257092750471076672995 17200885639125706615009493)
                ·
                  refine ⟨403145757167008748789285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17200885639125706615009493 403145757167008748789285)
                  ·
                    rfl

theorem cell21_1766528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_1766528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766528 prefixEnd_1766528 := by exact prefixLift 1766528
  have htrace : WordTrace (prefixWord ++ tailWord_1766528) baseStart_1766528 baseEnd_1766528 := by
    simpa [prefixWord, tailWord_1766528, baseEnd_1766528] using wordTrace_append hprefix tailTrace_1766528
  have hstable : (prefixWord ++ tailWord_1766528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766528).length < 2 ^ (prefixWord ++ tailWord_1766528).sum := by decide
  have hdescent : baseEnd_1766528 < baseStart_1766528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766582 : List Nat := [5, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1766582 : Nat := 118140960795 + 1766582 * 2 ^ 59
def prefixEnd_1766582 : Nat := 4983230072969 + 3 ^ 40 * 1766582 * 2
def baseEnd_1766582 : Nat := 134386026900905551629725

theorem tailTrace_1766582 : CollatzResearch.WordTrace tailWord_1766582 prefixEnd_1766582 134386026900905551629725 := by
  unfold tailWord_1766582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027033680373912314405875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42955025923988398020329333 4027033680373912314405875)
  ·
    refine ⟨6040550520560868471608813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4027033680373912314405875 6040550520560868471608813)
    ·
      refine ⟨2265206445210325676853305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6040550520560868471608813 2265206445210325676853305)
      ·
        refine ⟨1698904833907744257639979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2265206445210325676853305 1698904833907744257639979)
        ·
          refine ⟨2548357250861616386459969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698904833907744257639979 2548357250861616386459969)
          ·
            refine ⟨1911267938146212289844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548357250861616386459969 1911267938146212289844977)
            ·
              refine ⟨1433450953609659217383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1911267938146212289844977 1433450953609659217383733)
              ·
                refine ⟨134386026900905551629725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1433450953609659217383733 134386026900905551629725)
                ·
                  rfl

theorem cell21_1766582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1766582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766582 prefixEnd_1766582 := by exact prefixLift 1766582
  have htrace : WordTrace (prefixWord ++ tailWord_1766582) baseStart_1766582 baseEnd_1766582 := by
    simpa [prefixWord, tailWord_1766582, baseEnd_1766582] using wordTrace_append hprefix tailTrace_1766582
  have hstable : (prefixWord ++ tailWord_1766582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766582).length < 2 ^ (prefixWord ++ tailWord_1766582).sum := by decide
  have hdescent : baseEnd_1766582 < baseStart_1766582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766596 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_1766596 : Nat := 118140960795 + 1766596 * 2 ^ 59
def prefixEnd_1766596 : Nat := 4983230072969 + 3 ^ 40 * 1766596 * 2
def baseEnd_1766596 : Nat := 403161275693455741655813

theorem tailTrace_1766596 : CollatzResearch.WordTrace tailWord_1766596 prefixEnd_1766596 403161275693455741655813 := by
  unfold tailWord_1766596
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216524753965938710751821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42955366338621251614335761 32216524753965938710751821)
  ·
    refine ⟨12081196782737227016531933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32216524753965938710751821 12081196782737227016531933)
    ·
      refine ⟨4530448793526460131199475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12081196782737227016531933 4530448793526460131199475)
      ·
        refine ⟨6795673190289690196799213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530448793526460131199475 6795673190289690196799213)
        ·
          refine ⟨2548377446358633823799705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6795673190289690196799213 2548377446358633823799705)
          ·
            refine ⟨1911283084768975367849779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2548377446358633823799705 1911283084768975367849779)
            ·
              refine ⟨2866924627153463051774669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1911283084768975367849779 2866924627153463051774669)
              ·
                refine ⟨1075096735182548644415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2866924627153463051774669 1075096735182548644415501)
                ·
                  refine ⟨403161275693455741655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075096735182548644415501 403161275693455741655813)
                  ·
                    rfl

theorem cell21_1766596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_1766596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766596 prefixEnd_1766596 := by exact prefixLift 1766596
  have htrace : WordTrace (prefixWord ++ tailWord_1766596) baseStart_1766596 baseEnd_1766596 := by
    simpa [prefixWord, tailWord_1766596, baseEnd_1766596] using wordTrace_append hprefix tailTrace_1766596
  have hstable : (prefixWord ++ tailWord_1766596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766596).length < 2 ^ (prefixWord ++ tailWord_1766596).sum := by decide
  have hdescent : baseEnd_1766596 < baseStart_1766596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766649 : List Nat := [1, 2, 1, 3, 1, 1, 3, 9]
def baseStart_1766649 : Nat := 118140960795 + 1766649 * 2 ^ 59
def prefixEnd_1766649 : Nat := 4983230072969 + 3 ^ 40 * 1766649 * 2
def baseEnd_1766649 : Nat := 134391123671846475757457

theorem tailTrace_1766649 : CollatzResearch.WordTrace tailWord_1766649 prefixEnd_1766649 134391123671846475757457 := by
  unfold tailWord_1766649
  simp only [CollatzResearch.WordTrace]
  refine ⟨64434982576739867473183001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42956655051159911648788667 64434982576739867473183001)
  ·
    refine ⟨48326236932554900604887251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64434982576739867473183001 48326236932554900604887251)
    ·
      refine ⟨72489355398832350907330877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48326236932554900604887251 72489355398832350907330877)
      ·
        refine ⟨27183508274562131590249079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72489355398832350907330877 27183508274562131590249079)
        ·
          refine ⟨40775262411843197385373619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27183508274562131590249079 40775262411843197385373619)
          ·
            refine ⟨61162893617764796078060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40775262411843197385373619 61162893617764796078060429)
            ·
              refine ⟨22936085106661798529272661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61162893617764796078060429 22936085106661798529272661)
              ·
                refine ⟨134391123671846475757457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22936085106661798529272661 134391123671846475757457)
                ·
                  rfl

theorem cell21_1766649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 9].length) (baseStart_1766649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766649 prefixEnd_1766649 := by exact prefixLift 1766649
  have htrace : WordTrace (prefixWord ++ tailWord_1766649) baseStart_1766649 baseEnd_1766649 := by
    simpa [prefixWord, tailWord_1766649, baseEnd_1766649] using wordTrace_append hprefix tailTrace_1766649
  have hstable : (prefixWord ++ tailWord_1766649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766649).length < 2 ^ (prefixWord ++ tailWord_1766649).sum := by decide
  have hdescent : baseEnd_1766649 < baseStart_1766649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766714 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_1766714 : Nat := 118140960795 + 1766714 * 2 ^ 59
def prefixEnd_1766714 : Nat := 4983230072969 + 3 ^ 40 * 1766714 * 2
def baseEnd_1766714 : Nat := 403188204901113758688905

theorem tailTrace_1766714 : CollatzResearch.WordTrace tailWord_1766714 prefixEnd_1766714 403188204901113758688905 := by
  unfold tailWord_1766714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16109338330376095893574799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42958235547669589049532797 16109338330376095893574799)
  ·
    refine ⟨24164007495564143840362199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16109338330376095893574799 24164007495564143840362199)
    ·
      refine ⟨36246011243346215760543299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24164007495564143840362199 36246011243346215760543299)
      ·
        refine ⟨54369016865019323640814949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36246011243346215760543299 54369016865019323640814949)
        ·
          refine ⟨10194190662191123182652803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54369016865019323640814949 10194190662191123182652803)
          ·
            refine ⟨15291285993286684773979205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194190662191123182652803 15291285993286684773979205)
            ·
              refine ⟨2867116123741253395121101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15291285993286684773979205 2867116123741253395121101)
              ·
                refine ⟨1075168546402970023170413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2867116123741253395121101 1075168546402970023170413)
                ·
                  refine ⟨403188204901113758688905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075168546402970023170413 403188204901113758688905)
                  ·
                    rfl

theorem cell21_1766714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_1766714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766714 prefixEnd_1766714 := by exact prefixLift 1766714
  have htrace : WordTrace (prefixWord ++ tailWord_1766714) baseStart_1766714 baseEnd_1766714 := by
    simpa [prefixWord, tailWord_1766714, baseEnd_1766714] using wordTrace_append hprefix tailTrace_1766714
  have hstable : (prefixWord ++ tailWord_1766714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766714).length < 2 ^ (prefixWord ++ tailWord_1766714).sum := by decide
  have hdescent : baseEnd_1766714 < baseStart_1766714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766787 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 6]
def baseStart_1766787 : Nat := 118140960795 + 1766787 * 2 ^ 59
def prefixEnd_1766787 : Nat := 4983230072969 + 3 ^ 40 * 1766787 * 2
def baseEnd_1766787 : Nat := 403204864495681853972089

theorem tailTrace_1766787 : CollatzResearch.WordTrace tailWord_1766787 prefixEnd_1766787 403204864495681853972089 := by
  unfold tailWord_1766787
  simp only [CollatzResearch.WordTrace]
  refine ⟨64440015850239917041706615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42960010566826611361137743 64440015850239917041706615)
  ·
    refine ⟨96660023775359875562559923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64440015850239917041706615 96660023775359875562559923)
    ·
      refine ⟨144990035663039813343839885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96660023775359875562559923 144990035663039813343839885)
      ·
        refine ⟨54371263373639930003939957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144990035663039813343839885 54371263373639930003939957)
        ·
          refine ⟨5097305941278743437869371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54371263373639930003939957 5097305941278743437869371)
          ·
            refine ⟨7645958911918115156804057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097305941278743437869371 7645958911918115156804057)
            ·
              refine ⟨5734469183938586367603043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645958911918115156804057 5734469183938586367603043)
              ·
                refine ⟨8601703775907879551404565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734469183938586367603043 8601703775907879551404565)
                ·
                  refine ⟨403204864495681853972089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8601703775907879551404565 403204864495681853972089)
                  ·
                    rfl

theorem cell21_1766787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_1766787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766787 prefixEnd_1766787 := by exact prefixLift 1766787
  have htrace : WordTrace (prefixWord ++ tailWord_1766787) baseStart_1766787 baseEnd_1766787 := by
    simpa [prefixWord, tailWord_1766787, baseEnd_1766787] using wordTrace_append hprefix tailTrace_1766787
  have hstable : (prefixWord ++ tailWord_1766787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766787).length < 2 ^ (prefixWord ++ tailWord_1766787).sum := by decide
  have hdescent : baseEnd_1766787 < baseStart_1766787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766818 : List Nat := [3, 3, 1, 2, 1, 2, 2, 7]
def baseStart_1766818 : Nat := 118140960795 + 1766818 * 2 ^ 59
def prefixEnd_1766818 : Nat := 4983230072969 + 3 ^ 40 * 1766818 * 2
def baseEnd_1766818 : Nat := 134403979706010896318453

theorem tailTrace_1766818 : CollatzResearch.WordTrace tailWord_1766818 prefixEnd_1766818 134403979706010896318453 := by
  unfold tailWord_1766818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16110286628281902334021277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42960764342085072890723405 16110286628281902334021277)
  ·
    refine ⟨6041357485605713375257979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16110286628281902334021277 6041357485605713375257979)
    ·
      refine ⟨9062036228408570062886969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041357485605713375257979 9062036228408570062886969)
      ·
        refine ⟨6796527171306427547165227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9062036228408570062886969 6796527171306427547165227)
        ·
          refine ⟨10194790756959641320747841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796527171306427547165227 10194790756959641320747841)
          ·
            refine ⟨7646093067719730990560881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10194790756959641320747841 7646093067719730990560881)
            ·
              refine ⟨5734569800789798242920661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646093067719730990560881 5734569800789798242920661)
              ·
                refine ⟨134403979706010896318453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5734569800789798242920661 134403979706010896318453)
                ·
                  rfl

theorem cell21_1766818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_1766818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766818 prefixEnd_1766818 := by exact prefixLift 1766818
  have htrace : WordTrace (prefixWord ++ tailWord_1766818) baseStart_1766818 baseEnd_1766818 := by
    simpa [prefixWord, tailWord_1766818, baseEnd_1766818] using wordTrace_append hprefix tailTrace_1766818
  have hstable : (prefixWord ++ tailWord_1766818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766818).length < 2 ^ (prefixWord ++ tailWord_1766818).sum := by decide
  have hdescent : baseEnd_1766818 < baseStart_1766818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766863 : List Nat := [1, 1, 2, 1, 1, 4, 4, 3, 4]
def baseStart_1766863 : Nat := 118140960795 + 1766863 * 2 ^ 59
def prefixEnd_1766863 : Nat := 4983230072969 + 3 ^ 40 * 1766863 * 2
def baseEnd_1766863 : Nat := 403222208731122610705267

theorem tailTrace_1766863 : CollatzResearch.WordTrace tailWord_1766863 prefixEnd_1766863 403222208731122610705267 := by
  unfold tailWord_1766863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64442787797964582021473243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42961858531976388014315495 64442787797964582021473243)
  ·
    refine ⟨96664181696946873032209865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64442787797964582021473243 96664181696946873032209865)
    ·
      refine ⟨72498136272710154774157399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96664181696946873032209865 72498136272710154774157399)
      ·
        refine ⟨108747204409065232161236099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72498136272710154774157399 108747204409065232161236099)
        ·
          refine ⟨163120806613597848241854149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108747204409065232161236099 163120806613597848241854149)
          ·
            refine ⟨30585151240049596545347653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163120806613597848241854149 30585151240049596545347653)
            ·
              refine ⟨5734715857509299352252685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30585151240049596545347653 5734715857509299352252685)
              ·
                refine ⟨2150518446565987257094757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734715857509299352252685 2150518446565987257094757)
                ·
                  refine ⟨403222208731122610705267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150518446565987257094757 403222208731122610705267)
                  ·
                    rfl

theorem cell21_1766863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_1766863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766863 prefixEnd_1766863 := by exact prefixLift 1766863
  have htrace : WordTrace (prefixWord ++ tailWord_1766863) baseStart_1766863 baseEnd_1766863 := by
    simpa [prefixWord, tailWord_1766863, baseEnd_1766863] using wordTrace_append hprefix tailTrace_1766863
  have hstable : (prefixWord ++ tailWord_1766863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766863).length < 2 ^ (prefixWord ++ tailWord_1766863).sum := by decide
  have hdescent : baseEnd_1766863 < baseStart_1766863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766908 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_1766908 : Nat := 118140960795 + 1766908 * 2 ^ 59
def prefixEnd_1766908 : Nat := 4983230072969 + 3 ^ 40 * 1766908 * 2
def baseEnd_1766908 : Nat := 403232478344212532455175

theorem tailTrace_1766908 : CollatzResearch.WordTrace tailWord_1766908 prefixEnd_1766908 403232478344212532455175 := by
  unfold tailWord_1766908
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222214541400777353430689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42962952721867703137907585 32222214541400777353430689)
  ·
    refine ⟨24166660906050583015073017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32222214541400777353430689 24166660906050583015073017)
    ·
      refine ⟨18124995679537937261304763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24166660906050583015073017 18124995679537937261304763)
      ·
        refine ⟨27187493519306905891957145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18124995679537937261304763 27187493519306905891957145)
        ·
          refine ⟨20390620139480179418967859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27187493519306905891957145 20390620139480179418967859)
          ·
            refine ⟨30585930209220269128451789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20390620139480179418967859 30585930209220269128451789)
            ·
              refine ⟨11469723828457600923169421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30585930209220269128451789 11469723828457600923169421)
              ·
                refine ⟨4301146435671600346188533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11469723828457600923169421 4301146435671600346188533)
                ·
                  refine ⟨403232478344212532455175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301146435671600346188533 403232478344212532455175)
                  ·
                    rfl

theorem cell21_1766908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_1766908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766908 prefixEnd_1766908 := by exact prefixLift 1766908
  have htrace : WordTrace (prefixWord ++ tailWord_1766908) baseStart_1766908 baseEnd_1766908 := by
    simpa [prefixWord, tailWord_1766908, baseEnd_1766908] using wordTrace_append hprefix tailTrace_1766908
  have hstable : (prefixWord ++ tailWord_1766908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766908).length < 2 ^ (prefixWord ++ tailWord_1766908).sum := by decide
  have hdescent : baseEnd_1766908 < baseStart_1766908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1766914 : List Nat := [3, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1766914 : Nat := 118140960795 + 1766914 * 2 ^ 59
def prefixEnd_1766914 : Nat := 4983230072969 + 3 ^ 40 * 1766914 * 2
def baseEnd_1766914 : Nat := 403233847625957855355163

theorem tailTrace_1766914 : CollatzResearch.WordTrace tailWord_1766914 prefixEnd_1766914 403233847625957855355163 := by
  unfold tailWord_1766914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111161980194954432894949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42963098613853211821053197 16111161980194954432894949)
  ·
    refine ⟨3020842871286553956167803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16111161980194954432894949 3020842871286553956167803)
    ·
      refine ⟨4531264306929830934251705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020842871286553956167803 4531264306929830934251705)
      ·
        refine ⟨3398448230197373200688779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4531264306929830934251705 3398448230197373200688779)
        ·
          refine ⟨5097672345296059801033169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398448230197373200688779 5097672345296059801033169)
          ·
            refine ⟨3823254258972044850774877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5097672345296059801033169 3823254258972044850774877)
            ·
              refine ⟨1433720347114516819040579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3823254258972044850774877 1433720347114516819040579)
              ·
                refine ⟨2150580520671775228560869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1433720347114516819040579 2150580520671775228560869)
                ·
                  refine ⟨403233847625957855355163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150580520671775228560869 403233847625957855355163)
                  ·
                    rfl

theorem cell21_1766914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1766914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1766914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1766914 prefixEnd_1766914 := by exact prefixLift 1766914
  have htrace : WordTrace (prefixWord ++ tailWord_1766914) baseStart_1766914 baseEnd_1766914 := by
    simpa [prefixWord, tailWord_1766914, baseEnd_1766914] using wordTrace_append hprefix tailTrace_1766914
  have hstable : (prefixWord ++ tailWord_1766914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1766914).length < 2 ^ (prefixWord ++ tailWord_1766914).sum := by decide
  have hdescent : baseEnd_1766914 < baseStart_1766914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1766914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767015 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 4]
def baseStart_1767015 : Nat := 118140960795 + 1767015 * 2 ^ 59
def prefixEnd_1767015 : Nat := 4983230072969 + 3 ^ 40 * 1767015 * 2
def baseEnd_1767015 : Nat := 403256897202004124171623

theorem tailTrace_1767015 : CollatzResearch.WordTrace tailWord_1767015 prefixEnd_1767015 403256897202004124171623 := by
  unfold tailWord_1767015
  simp only [CollatzResearch.WordTrace]
  refine ⟨64448331693413911981006499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42965554462275941320670999 64448331693413911981006499)
  ·
    refine ⟨96672497540120867971509749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64448331693413911981006499 96672497540120867971509749)
    ·
      refine ⟨9063046644386331372329039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96672497540120867971509749 9063046644386331372329039)
      ·
        refine ⟨13594569966579497058493559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063046644386331372329039 13594569966579497058493559)
        ·
          refine ⟨20391854949869245587740339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594569966579497058493559 20391854949869245587740339)
          ·
            refine ⟨30587782424803868381610509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391854949869245587740339 30587782424803868381610509)
            ·
              refine ⟨11470418409301450643103941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30587782424803868381610509 11470418409301450643103941)
              ·
                refine ⟨2150703451744021995581989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11470418409301450643103941 2150703451744021995581989)
                ·
                  refine ⟨403256897202004124171623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2150703451744021995581989 403256897202004124171623)
                  ·
                    rfl

theorem cell21_1767015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_1767015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767015 prefixEnd_1767015 := by exact prefixLift 1767015
  have htrace : WordTrace (prefixWord ++ tailWord_1767015) baseStart_1767015 baseEnd_1767015 := by
    simpa [prefixWord, tailWord_1767015, baseEnd_1767015] using wordTrace_append hprefix tailTrace_1767015
  have hstable : (prefixWord ++ tailWord_1767015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767015).length < 2 ^ (prefixWord ++ tailWord_1767015).sum := by decide
  have hdescent : baseEnd_1767015 < baseStart_1767015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767018 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_1767018 : Nat := 118140960795 + 1767018 * 2 ^ 59
def prefixEnd_1767018 : Nat := 4983230072969 + 3 ^ 40 * 1767018 * 2
def baseEnd_1767018 : Nat := 403257581842876785621617

theorem tailTrace_1767018 : CollatzResearch.WordTrace tailWord_1767018 prefixEnd_1767018 403257581842876785621617 := by
  unfold tailWord_1767018
  simp only [CollatzResearch.WordTrace]
  refine ⟨16112110278100760873341427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42965627408268695662243805 16112110278100760873341427)
  ·
    refine ⟨24168165417151141310012141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16112110278100760873341427 24168165417151141310012141)
    ·
      refine ⟨9063062031431677991254553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24168165417151141310012141 9063062031431677991254553)
      ·
        refine ⟨6797296523573758493440915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063062031431677991254553 6797296523573758493440915)
        ·
          refine ⟨10195944785360637740161373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797296523573758493440915 10195944785360637740161373)
          ·
            refine ⟨3823479294510239152560515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10195944785360637740161373 3823479294510239152560515)
            ·
              refine ⟨5735218941765358728840773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823479294510239152560515 5735218941765358728840773)
              ·
                refine ⟨1075353551581004761657645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5735218941765358728840773 1075353551581004761657645)
                ·
                  refine ⟨403257581842876785621617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075353551581004761657645 403257581842876785621617)
                  ·
                    rfl

theorem cell21_1767018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_1767018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767018 prefixEnd_1767018 := by exact prefixLift 1767018
  have htrace : WordTrace (prefixWord ++ tailWord_1767018) baseStart_1767018 baseEnd_1767018 := by
    simpa [prefixWord, tailWord_1767018, baseEnd_1767018] using wordTrace_append hprefix tailTrace_1767018
  have hstable : (prefixWord ++ tailWord_1767018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767018).length < 2 ^ (prefixWord ++ tailWord_1767018).sum := by decide
  have hdescent : baseEnd_1767018 < baseStart_1767018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767077 : List Nat := [1, 3, 1, 2, 1, 2, 4, 4, 3]
def baseStart_1767077 : Nat := 118140960795 + 1767077 * 2 ^ 59
def prefixEnd_1767077 : Nat := 4983230072969 + 3 ^ 40 * 1767077 * 2
def baseEnd_1767077 : Nat := 403271046446705794138163

theorem tailTrace_1767077 : CollatzResearch.WordTrace tailWord_1767077 prefixEnd_1767077 403271046446705794138163 := by
  unfold tailWord_1767077
  simp only [CollatzResearch.WordTrace]
  refine ⟨64450593019189296569763485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42967062012792864379842323 64450593019189296569763485)
  ·
    refine ⟨24168972382195986213661307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64450593019189296569763485 24168972382195986213661307)
    ·
      refine ⟨36253458573293979320491961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24168972382195986213661307 36253458573293979320491961)
      ·
        refine ⟨27190093929970484490368971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36253458573293979320491961 27190093929970484490368971)
        ·
          refine ⟨40785140894955726735553457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190093929970484490368971 40785140894955726735553457)
          ·
            refine ⟨30588855671216795051665093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40785140894955726735553457 30588855671216795051665093)
            ·
              refine ⟨5735410438353149072187205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30588855671216795051665093 5735410438353149072187205)
              ·
                refine ⟨1075389457191215451035101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5735410438353149072187205 1075389457191215451035101)
                ·
                  refine ⟨403271046446705794138163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075389457191215451035101 403271046446705794138163)
                  ·
                    rfl

theorem cell21_1767077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_1767077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767077 prefixEnd_1767077 := by exact prefixLift 1767077
  have htrace : WordTrace (prefixWord ++ tailWord_1767077) baseStart_1767077 baseEnd_1767077 := by
    simpa [prefixWord, tailWord_1767077, baseEnd_1767077] using wordTrace_append hprefix tailTrace_1767077
  have hstable : (prefixWord ++ tailWord_1767077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767077).length < 2 ^ (prefixWord ++ tailWord_1767077).sum := by decide
  have hdescent : baseEnd_1767077 < baseStart_1767077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767094 : List Nat := [5, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1767094 : Nat := 118140960795 + 1767094 * 2 ^ 59
def prefixEnd_1767094 : Nat := 4983230072969 + 3 ^ 40 * 1767094 * 2
def baseEnd_1767094 : Nat := 403274926078317542354795

theorem tailTrace_1767094 : CollatzResearch.WordTrace tailWord_1767094 prefixEnd_1767094 403274926078317542354795 := by
  unfold tailWord_1767094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028200816257981779570771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42967475373418472315421557 4028200816257981779570771)
  ·
    refine ⟨6042301224386972669356157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028200816257981779570771 6042301224386972669356157)
    ·
      refine ⟨2265862959145114751008559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6042301224386972669356157 2265862959145114751008559)
      ·
        refine ⟨3398794438717672126512839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265862959145114751008559 3398794438717672126512839)
        ·
          refine ⟨5098191658076508189769259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398794438717672126512839 5098191658076508189769259)
          ·
            refine ⟨7647287487114762284653889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098191658076508189769259 7647287487114762284653889)
            ·
              refine ⟨5735465615336071713490417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647287487114762284653889 5735465615336071713490417)
              ·
                refine ⟨4301599211502053785117813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735465615336071713490417 4301599211502053785117813)
                ·
                  refine ⟨403274926078317542354795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301599211502053785117813 403274926078317542354795)
                  ·
                    rfl

theorem cell21_1767094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1767094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767094 prefixEnd_1767094 := by exact prefixLift 1767094
  have htrace : WordTrace (prefixWord ++ tailWord_1767094) baseStart_1767094 baseEnd_1767094 := by
    simpa [prefixWord, tailWord_1767094, baseEnd_1767094] using wordTrace_append hprefix tailTrace_1767094
  have hstable : (prefixWord ++ tailWord_1767094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767094).length < 2 ^ (prefixWord ++ tailWord_1767094).sum := by decide
  have hdescent : baseEnd_1767094 < baseStart_1767094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767119 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 7]
def baseStart_1767119 : Nat := 118140960795 + 1767119 * 2 ^ 59
def prefixEnd_1767119 : Nat := 4983230072969 + 3 ^ 40 * 1767119 * 2
def baseEnd_1767119 : Nat := 403280631418923054438077

theorem tailTrace_1767119 : CollatzResearch.WordTrace tailWord_1767119 prefixEnd_1767119 403280631418923054438077 := by
  unfold tailWord_1767119
  simp only [CollatzResearch.WordTrace]
  refine ⟨64452124885037137742792411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42968083256691425161861607 64452124885037137742792411)
  ·
    refine ⟨96678187327555706614188617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64452124885037137742792411 96678187327555706614188617)
    ·
      refine ⟨72508640495666779960641463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96678187327555706614188617 72508640495666779960641463)
      ·
        refine ⟨108762960743500169940962195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72508640495666779960641463 108762960743500169940962195)
        ·
          refine ⟨163144441115250254911443293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108762960743500169940962195 163144441115250254911443293)
          ·
            refine ⟨61179165418218845591791235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163144441115250254911443293 61179165418218845591791235)
            ·
              refine ⟨91768748127328268387686853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61179165418218845591791235 91768748127328268387686853)
              ·
                refine ⟨17206640273874050322691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91768748127328268387686853 17206640273874050322691285)
                ·
                  refine ⟨403280631418923054438077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17206640273874050322691285 403280631418923054438077)
                  ·
                    rfl

theorem cell21_1767119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_1767119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767119 prefixEnd_1767119 := by exact prefixLift 1767119
  have htrace : WordTrace (prefixWord ++ tailWord_1767119) baseStart_1767119 baseEnd_1767119 := by
    simpa [prefixWord, tailWord_1767119, baseEnd_1767119] using wordTrace_append hprefix tailTrace_1767119
  have hstable : (prefixWord ++ tailWord_1767119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767119).length < 2 ^ (prefixWord ++ tailWord_1767119).sum := by decide
  have hdescent : baseEnd_1767119 < baseStart_1767119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767122 : List Nat := [3, 2, 2, 2, 2, 3, 7]
def baseStart_1767122 : Nat := 118140960795 + 1767122 * 2 ^ 59
def prefixEnd_1767122 : Nat := 4983230072969 + 3 ^ 40 * 1767122 * 2
def baseEnd_1767122 : Nat := 44809035117755079543119

theorem tailTrace_1767122 : CollatzResearch.WordTrace tailWord_1767122 prefixEnd_1767122 44809035117755079543119 := by
  unfold tailWord_1767122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113058576006567313787905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42968156202684179503434413 16113058576006567313787905)
  ·
    refine ⟨12084793932004925485340929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16113058576006567313787905 12084793932004925485340929)
    ·
      refine ⟨9063595449003694114005697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12084793932004925485340929 9063595449003694114005697)
      ·
        refine ⟨6797696586752770585504273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9063595449003694114005697 6797696586752770585504273)
        ·
          refine ⟨5098272440064577939128205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6797696586752770585504273 5098272440064577939128205)
          ·
            refine ⟨1911852165024216727173077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5098272440064577939128205 1911852165024216727173077)
            ·
              refine ⟨44809035117755079543119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1911852165024216727173077 44809035117755079543119)
              ·
                rfl

theorem cell21_1767122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 7].length) (baseStart_1767122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767122 prefixEnd_1767122 := by exact prefixLift 1767122
  have htrace : WordTrace (prefixWord ++ tailWord_1767122) baseStart_1767122 baseEnd_1767122 := by
    simpa [prefixWord, tailWord_1767122, baseEnd_1767122] using wordTrace_append hprefix tailTrace_1767122
  have hstable : (prefixWord ++ tailWord_1767122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767122).length < 2 ^ (prefixWord ++ tailWord_1767122).sum := by decide
  have hdescent : baseEnd_1767122 < baseStart_1767122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767136 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_1767136 : Nat := 118140960795 + 1767136 * 2 ^ 59
def prefixEnd_1767136 : Nat := 4983230072969 + 3 ^ 40 * 1767136 * 2
def baseEnd_1767136 : Nat := 403284511050534802654709

theorem tailTrace_1767136 : CollatzResearch.WordTrace tailWord_1767136 prefixEnd_1767136 403284511050534802654709 := by
  unfold tailWord_1767136
  simp only [CollatzResearch.WordTrace]
  refine ⟨32226372462987774823080631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42968496617317033097440841 32226372462987774823080631)
  ·
    refine ⟨48339558694481662234620947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32226372462987774823080631 48339558694481662234620947)
    ·
      refine ⟨72509338041722493351931421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48339558694481662234620947 72509338041722493351931421)
      ·
        refine ⟨27191001765645935006974283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72509338041722493351931421 27191001765645935006974283)
        ·
          refine ⟨40786502648468902510461425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27191001765645935006974283 40786502648468902510461425)
          ·
            refine ⟨30589876986351676882846069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40786502648468902510461425 30589876986351676882846069)
            ·
              refine ⟨2867800967470469707766819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30589876986351676882846069 2867800967470469707766819)
              ·
                refine ⟨4301701451205704561650229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867800967470469707766819 4301701451205704561650229)
                ·
                  refine ⟨403284511050534802654709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301701451205704561650229 403284511050534802654709)
                  ·
                    rfl

theorem cell21_1767136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_1767136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767136 prefixEnd_1767136 := by exact prefixLift 1767136
  have htrace : WordTrace (prefixWord ++ tailWord_1767136) baseStart_1767136 baseEnd_1767136 := by
    simpa [prefixWord, tailWord_1767136, baseEnd_1767136] using wordTrace_append hprefix tailTrace_1767136
  have hstable : (prefixWord ++ tailWord_1767136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767136).length < 2 ^ (prefixWord ++ tailWord_1767136).sum := by decide
  have hdescent : baseEnd_1767136 < baseStart_1767136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767170 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1767170 : Nat := 118140960795 + 1767170 * 2 ^ 59
def prefixEnd_1767170 : Nat := 4983230072969 + 3 ^ 40 * 1767170 * 2
def baseEnd_1767170 : Nat := 403292270313758299087973

theorem tailTrace_1767170 : CollatzResearch.WordTrace tailWord_1767170 prefixEnd_1767170 403292270313758299087973 := by
  unfold tailWord_1767170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113496251963093363224741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42969323338568248968599309 16113496251963093363224741)
  ·
    refine ⟨3021280547243080005604639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16113496251963093363224741 3021280547243080005604639)
    ·
      refine ⟨4531920820864620008406959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021280547243080005604639 4531920820864620008406959)
      ·
        refine ⟨6797881231296930012610439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531920820864620008406959 6797881231296930012610439)
        ·
          refine ⟨10196821846945395018915659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797881231296930012610439 10196821846945395018915659)
          ·
            refine ⟨15295232770418092528373489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196821846945395018915659 15295232770418092528373489)
            ·
              refine ⟨11471424577813569396280117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15295232770418092528373489 11471424577813569396280117)
              ·
                refine ⟨1075446054170022130901261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11471424577813569396280117 1075446054170022130901261)
                ·
                  refine ⟨403292270313758299087973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075446054170022130901261 403292270313758299087973)
                  ·
                    rfl

theorem cell21_1767170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1767170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767170 prefixEnd_1767170 := by exact prefixLift 1767170
  have htrace : WordTrace (prefixWord ++ tailWord_1767170) baseStart_1767170 baseEnd_1767170 := by
    simpa [prefixWord, tailWord_1767170, baseEnd_1767170] using wordTrace_append hprefix tailTrace_1767170
  have hstable : (prefixWord ++ tailWord_1767170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767170).length < 2 ^ (prefixWord ++ tailWord_1767170).sum := by decide
  have hdescent : baseEnd_1767170 < baseStart_1767170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767212 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_1767212 : Nat := 118140960795 + 1767212 * 2 ^ 59
def prefixEnd_1767212 : Nat := 4983230072969 + 3 ^ 40 * 1767212 * 2
def baseEnd_1767212 : Nat := 403301855285975559387887

theorem tailTrace_1767212 : CollatzResearch.WordTrace tailWord_1767212 prefixEnd_1767212 403301855285975559387887 := by
  unfold tailWord_1767212
  simp only [CollatzResearch.WordTrace]
  refine ⟨32227758436850107312963945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42970344582466809750618593 32227758436850107312963945)
  ·
    refine ⟨24170818827637580484722959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32227758436850107312963945 24170818827637580484722959)
    ·
      refine ⟨36256228241456370727084439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24170818827637580484722959 36256228241456370727084439)
      ·
        refine ⟨54384342362184556090626659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36256228241456370727084439 54384342362184556090626659)
        ·
          refine ⟨81576513543276834135939989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54384342362184556090626659 81576513543276834135939989)
          ·
            refine ⟨3823899072341101600122187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81576513543276834135939989 3823899072341101600122187)
            ·
              refine ⟨5735848608511652400183281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823899072341101600122187 5735848608511652400183281)
              ·
                refine ⟨4301886456383739300137461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735848608511652400183281 4301886456383739300137461)
                ·
                  refine ⟨403301855285975559387887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4301886456383739300137461 403301855285975559387887)
                  ·
                    rfl

theorem cell21_1767212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_1767212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767212 prefixEnd_1767212 := by exact prefixLift 1767212
  have htrace : WordTrace (prefixWord ++ tailWord_1767212) baseStart_1767212 baseEnd_1767212 := by
    simpa [prefixWord, tailWord_1767212, baseEnd_1767212] using wordTrace_append hprefix tailTrace_1767212
  have hstable : (prefixWord ++ tailWord_1767212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767212).length < 2 ^ (prefixWord ++ tailWord_1767212).sum := by decide
  have hdescent : baseEnd_1767212 < baseStart_1767212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767319 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 4]
def baseStart_1767319 : Nat := 118140960795 + 1767319 * 2 ^ 59
def prefixEnd_1767319 : Nat := 4983230072969 + 3 ^ 40 * 1767319 * 2
def baseEnd_1767319 : Nat := 403326274143767151104335

theorem tailTrace_1767319 : CollatzResearch.WordTrace tailWord_1767319 prefixEnd_1767319 403326274143767151104335 := by
  unfold tailWord_1767319
  simp only [CollatzResearch.WordTrace]
  refine ⟨64459419484312571900073011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42972946322875047933382007 64459419484312571900073011)
  ·
    refine ⟨96689129226468857850109517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64459419484312571900073011 96689129226468857850109517)
    ·
      refine ⟨36258423459925821693791069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96689129226468857850109517 36258423459925821693791069)
      ·
        refine ⟨13596908797472183135171651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36258423459925821693791069 13596908797472183135171651)
        ·
          refine ⟨20395363196208274702757477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13596908797472183135171651 20395363196208274702757477)
          ·
            refine ⟨3824130599289051506767027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20395363196208274702757477 3824130599289051506767027)
            ·
              refine ⟨5736195898933577260150541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824130599289051506767027 5736195898933577260150541)
              ·
                refine ⟨2151073462100091472556453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5736195898933577260150541 2151073462100091472556453)
                ·
                  refine ⟨403326274143767151104335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151073462100091472556453 403326274143767151104335)
                  ·
                    rfl

theorem cell21_1767319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_1767319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767319 prefixEnd_1767319 := by exact prefixLift 1767319
  have htrace : WordTrace (prefixWord ++ tailWord_1767319) baseStart_1767319 baseEnd_1767319 := by
    simpa [prefixWord, tailWord_1767319, baseEnd_1767319] using wordTrace_append hprefix tailTrace_1767319
  have hstable : (prefixWord ++ tailWord_1767319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767319).length < 2 ^ (prefixWord ++ tailWord_1767319).sum := by decide
  have hdescent : baseEnd_1767319 < baseStart_1767319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767350 : List Nat := [5, 1, 4, 11]
def baseStart_1767350 : Nat := 118140960795 + 1767350 * 2 ^ 59
def prefixEnd_1767350 : Nat := 4983230072969 + 3 ^ 40 * 1767350 * 2
def baseEnd_1767350 : Nat := 1659808019613654263735

theorem tailTrace_1767350 : CollatzResearch.WordTrace tailWord_1767350 prefixEnd_1767350 1659808019613654263735 := by
  unfold tailWord_1767350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028784384200016512153219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 42973700098133509462967669 4028784384200016512153219)
  ·
    refine ⟨6043176576300024768229829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028784384200016512153219 6043176576300024768229829)
    ·
      refine ⟨1133095608056254644043093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6043176576300024768229829 1133095608056254644043093)
      ·
        refine ⟨1659808019613654263735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1133095608056254644043093 1659808019613654263735)
        ·
          rfl

theorem cell21_1767350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 11].length) (baseStart_1767350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767350 prefixEnd_1767350 := by exact prefixLift 1767350
  have htrace : WordTrace (prefixWord ++ tailWord_1767350) baseStart_1767350 baseEnd_1767350 := by
    simpa [prefixWord, tailWord_1767350, baseEnd_1767350] using wordTrace_append hprefix tailTrace_1767350
  have hstable : (prefixWord ++ tailWord_1767350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767350).length < 2 ^ (prefixWord ++ tailWord_1767350).sum := by decide
  have hdescent : baseEnd_1767350 < baseStart_1767350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767356 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_1767356 : Nat := 118140960795 + 1767356 * 2 ^ 59
def prefixEnd_1767356 : Nat := 4983230072969 + 3 ^ 40 * 1767356 * 2
def baseEnd_1767356 : Nat := 403334718047863308987593

theorem tailTrace_1767356 : CollatzResearch.WordTrace tailWord_1767356 prefixEnd_1767356 403334718047863308987593 := by
  unfold tailWord_1767356
  simp only [CollatzResearch.WordTrace]
  refine ⟨32230384492589263609584961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42973845990119018146113281 32230384492589263609584961)
  ·
    refine ⟨24172788369441947707188721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32230384492589263609584961 24172788369441947707188721)
    ·
      refine ⟨18129591277081460780391541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24172788369441947707188721 18129591277081460780391541)
      ·
        refine ⟨1699649182226386948161707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18129591277081460780391541 1699649182226386948161707)
        ·
          refine ⟨2549473773339580422242561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699649182226386948161707 2549473773339580422242561)
          ·
            refine ⟨1912105330004685316681921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2549473773339580422242561 1912105330004685316681921)
            ·
              refine ⟨1434078997503513987511441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912105330004685316681921 1434078997503513987511441)
              ·
                refine ⟨1075559248127635490633581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434078997503513987511441 1075559248127635490633581)
                ·
                  refine ⟨403334718047863308987593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075559248127635490633581 403334718047863308987593)
                  ·
                    rfl

theorem cell21_1767356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_1767356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767356 prefixEnd_1767356 := by exact prefixLift 1767356
  have htrace : WordTrace (prefixWord ++ tailWord_1767356) baseStart_1767356 baseEnd_1767356 := by
    simpa [prefixWord, tailWord_1767356, baseEnd_1767356] using wordTrace_append hprefix tailTrace_1767356
  have hstable : (prefixWord ++ tailWord_1767356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767356).length < 2 ^ (prefixWord ++ tailWord_1767356).sum := by decide
  have hdescent : baseEnd_1767356 < baseStart_1767356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767392 : List Nat := [2, 1, 1, 3, 1, 1, 1, 11]
def baseStart_1767392 : Nat := 118140960795 + 1767392 * 2 ^ 59
def prefixEnd_1767392 : Nat := 4983230072969 + 3 ^ 40 * 1767392 * 2
def baseEnd_1767392 : Nat := 134447644579445082129173

theorem tailTrace_1767392 : CollatzResearch.WordTrace tailWord_1767392 prefixEnd_1767392 134447644579445082129173 := by
  unfold tailWord_1767392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231041006524052683740215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42974721342032070244986953 32231041006524052683740215)
  ·
    refine ⟨48346561509786079025610323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32231041006524052683740215 48346561509786079025610323)
    ·
      refine ⟨72519842264679118538415485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48346561509786079025610323 72519842264679118538415485)
      ·
        refine ⟨27194940849254669451905807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72519842264679118538415485 27194940849254669451905807)
        ·
          refine ⟨40792411273882004177858711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27194940849254669451905807 40792411273882004177858711)
          ·
            refine ⟨61188616910823006266788067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40792411273882004177858711 61188616910823006266788067)
            ·
              refine ⟨91782925366234509400182101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61188616910823006266788067 91782925366234509400182101)
              ·
                refine ⟨134447644579445082129173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91782925366234509400182101 134447644579445082129173)
                ·
                  rfl

theorem cell21_1767392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_1767392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767392 prefixEnd_1767392 := by exact prefixLift 1767392
  have htrace : WordTrace (prefixWord ++ tailWord_1767392) baseStart_1767392 baseEnd_1767392 := by
    simpa [prefixWord, tailWord_1767392, baseEnd_1767392] using wordTrace_append hprefix tailTrace_1767392
  have hstable : (prefixWord ++ tailWord_1767392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767392).length < 2 ^ (prefixWord ++ tailWord_1767392).sum := by decide
  have hdescent : baseEnd_1767392 < baseStart_1767392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767409 : List Nat := [1, 2, 2, 2, 5, 1, 8]
def baseStart_1767409 : Nat := 118140960795 + 1767409 * 2 ^ 59
def prefixEnd_1767409 : Nat := 4983230072969 + 3 ^ 40 * 1767409 * 2
def baseEnd_1767409 : Nat := 44816312596660777178239

theorem tailTrace_1767409 : CollatzResearch.WordTrace tailWord_1767409 prefixEnd_1767409 44816312596660777178239 := by
  unfold tailWord_1767409
  simp only [CollatzResearch.WordTrace]
  refine ⟨64462702053986517270849281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42975134702657678180566187 64462702053986517270849281)
  ·
    refine ⟨48347026540489887953136961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64462702053986517270849281 48347026540489887953136961)
    ·
      refine ⟨36260269905367415964852721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48347026540489887953136961 36260269905367415964852721)
      ·
        refine ⟨27195202429025561973639541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36260269905367415964852721 27195202429025561973639541)
        ·
          refine ⟨2549550227721146435028707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27195202429025561973639541 2549550227721146435028707)
          ·
            refine ⟨3824325341581719652543061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549550227721146435028707 3824325341581719652543061)
            ·
              refine ⟨44816312596660777178239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3824325341581719652543061 44816312596660777178239)
              ·
                rfl

theorem cell21_1767409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 8].length) (baseStart_1767409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767409 prefixEnd_1767409 := by exact prefixLift 1767409
  have htrace : WordTrace (prefixWord ++ tailWord_1767409) baseStart_1767409 baseEnd_1767409 := by
    simpa [prefixWord, tailWord_1767409, baseEnd_1767409] using wordTrace_append hprefix tailTrace_1767409
  have hstable : (prefixWord ++ tailWord_1767409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767409).length < 2 ^ (prefixWord ++ tailWord_1767409).sum := by decide
  have hdescent : baseEnd_1767409 < baseStart_1767409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767474 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_1767474 : Nat := 118140960795 + 1767474 * 2 ^ 59
def prefixEnd_1767474 : Nat := 4983230072969 + 3 ^ 40 * 1767474 * 2
def baseEnd_1767474 : Nat := 403361647255521326020685

theorem tailTrace_1767474 : CollatzResearch.WordTrace tailWord_1767474 prefixEnd_1767474 403361647255521326020685 := by
  unfold tailWord_1767474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16116268199687758342991369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42976715199167355581310317 16116268199687758342991369)
  ·
    refine ⟨12087201149765818757243527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16116268199687758342991369 12087201149765818757243527)
    ·
      refine ⟨18130801724648728135865291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087201149765818757243527 18130801724648728135865291)
      ·
        refine ⟨27196202586973092203797937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18130801724648728135865291 27196202586973092203797937)
        ·
          refine ⟨20397151940229819152848453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27196202586973092203797937 20397151940229819152848453)
          ·
            refine ⟨3824465988793091091159085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20397151940229819152848453 3824465988793091091159085)
            ·
              refine ⟨1434174745797409159184657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824465988793091091159085 1434174745797409159184657)
              ·
                refine ⟨1075631059348056869388493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1434174745797409159184657 1075631059348056869388493)
                ·
                  refine ⟨403361647255521326020685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075631059348056869388493 403361647255521326020685)
                  ·
                    rfl

theorem cell21_1767474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_1767474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767474 prefixEnd_1767474 := by exact prefixLift 1767474
  have htrace : WordTrace (prefixWord ++ tailWord_1767474) baseStart_1767474 baseEnd_1767474 := by
    simpa [prefixWord, tailWord_1767474, baseEnd_1767474] using wordTrace_append hprefix tailTrace_1767474
  have hstable : (prefixWord ++ tailWord_1767474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767474).length < 2 ^ (prefixWord ++ tailWord_1767474).sum := by decide
  have hdescent : baseEnd_1767474 < baseStart_1767474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767485 : List Nat := [1, 4, 1, 3, 1, 1, 4, 6]
def baseStart_1767485 : Nat := 118140960795 + 1767485 * 2 ^ 59
def prefixEnd_1767485 : Nat := 4983230072969 + 3 ^ 40 * 1767485 * 2
def baseEnd_1767485 : Nat := 134454719201795917112443

theorem tailTrace_1767485 : CollatzResearch.WordTrace tailWord_1767485 prefixEnd_1767485 134454719201795917112443 := by
  unfold tailWord_1767485
  simp only [CollatzResearch.WordTrace]
  refine ⟨64465474001711182250615909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42976982667807454833743939 64465474001711182250615909)
  ·
    refine ⟨12087276375320846671990483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64465474001711182250615909 12087276375320846671990483)
    ·
      refine ⟨18130914562981270007985725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087276375320846671990483 18130914562981270007985725)
      ·
        refine ⟨6799092961117976252994647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18130914562981270007985725 6799092961117976252994647)
        ·
          refine ⟨10198639441676964379491971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799092961117976252994647 10198639441676964379491971)
          ·
            refine ⟨15297959162515446569237957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198639441676964379491971 15297959162515446569237957)
            ·
              refine ⟨2868367342971646231732117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15297959162515446569237957 2868367342971646231732117)
              ·
                refine ⟨134454719201795917112443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2868367342971646231732117 134454719201795917112443)
                ·
                  rfl

theorem cell21_1767485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_1767485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767485 prefixEnd_1767485 := by exact prefixLift 1767485
  have htrace : WordTrace (prefixWord ++ tailWord_1767485) baseStart_1767485 baseEnd_1767485 := by
    simpa [prefixWord, tailWord_1767485, baseEnd_1767485] using wordTrace_append hprefix tailTrace_1767485
  have hstable : (prefixWord ++ tailWord_1767485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767485).length < 2 ^ (prefixWord ++ tailWord_1767485).sum := by decide
  have hdescent : baseEnd_1767485 < baseStart_1767485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767488 : List Nat := [2, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_1767488 : Nat := 118140960795 + 1767488 * 2 ^ 59
def prefixEnd_1767488 : Nat := 4983230072969 + 3 ^ 40 * 1767488 * 2
def baseEnd_1767488 : Nat := 403364842246260412787323

theorem tailTrace_1767488 : CollatzResearch.WordTrace tailWord_1767488 prefixEnd_1767488 403364842246260412787323 := by
  unfold tailWord_1767488
  simp only [CollatzResearch.WordTrace]
  refine ⟨32232791710350156881487559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 42977055613800209175316745 32232791710350156881487559)
  ·
    refine ⟨48349187565525235322231339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32232791710350156881487559 48349187565525235322231339)
    ·
      refine ⟨72523781348287852983347009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48349187565525235322231339 72523781348287852983347009)
      ·
        refine ⟨54392836011215889737510257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72523781348287852983347009 54392836011215889737510257)
        ·
          refine ⟨40794627008411917303132693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54392836011215889737510257 40794627008411917303132693)
          ·
            refine ⟨1912248141019308623584345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40794627008411917303132693 1912248141019308623584345)
            ·
              refine ⟨1434186105764481467688259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1912248141019308623584345 1434186105764481467688259)
              ·
                refine ⟨2151279158646722201532389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434186105764481467688259 2151279158646722201532389)
                ·
                  refine ⟨403364842246260412787323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151279158646722201532389 403364842246260412787323)
                  ·
                    rfl

theorem cell21_1767488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_1767488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767488 prefixEnd_1767488 := by exact prefixLift 1767488
  have htrace : WordTrace (prefixWord ++ tailWord_1767488) baseStart_1767488 baseEnd_1767488 := by
    simpa [prefixWord, tailWord_1767488, baseEnd_1767488] using wordTrace_append hprefix tailTrace_1767488
  have hstable : (prefixWord ++ tailWord_1767488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767488).length < 2 ^ (prefixWord ++ tailWord_1767488).sum := by decide
  have hdescent : baseEnd_1767488 < baseStart_1767488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767533 : List Nat := [1, 5, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1767533 : Nat := 118140960795 + 1767533 * 2 ^ 59
def prefixEnd_1767533 : Nat := 4983230072969 + 3 ^ 40 * 1767533 * 2
def baseEnd_1767533 : Nat := 403375111859350334537231

theorem tailTrace_1767533 : CollatzResearch.WordTrace tailWord_1767533 prefixEnd_1767533 403375111859350334537231 := by
  unfold tailWord_1767533
  simp only [CollatzResearch.WordTrace]
  refine ⟨64467224705537286448363253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42978149803691524298908835 64467224705537286448363253)
  ·
    refine ⟨6043802316144120604534055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64467224705537286448363253 6043802316144120604534055)
    ·
      refine ⟨9065703474216180906801083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043802316144120604534055 9065703474216180906801083)
      ·
        refine ⟨13598555211324271360201625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065703474216180906801083 13598555211324271360201625)
        ·
          refine ⟨10198916408493203520151219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13598555211324271360201625 10198916408493203520151219)
          ·
            refine ⟨15298374612739805280226829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198916408493203520151219 15298374612739805280226829)
            ·
              refine ⟨5736890479777426980085061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15298374612739805280226829 5736890479777426980085061)
              ·
                refine ⟨1075666964958267558765949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5736890479777426980085061 1075666964958267558765949)
                ·
                  refine ⟨403375111859350334537231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1075666964958267558765949 403375111859350334537231)
                  ·
                    rfl

theorem cell21_1767533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1767533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767533 prefixEnd_1767533 := by exact prefixLift 1767533
  have htrace : WordTrace (prefixWord ++ tailWord_1767533) baseStart_1767533 baseEnd_1767533 := by
    simpa [prefixWord, tailWord_1767533, baseEnd_1767533] using wordTrace_append hprefix tailTrace_1767533
  have hstable : (prefixWord ++ tailWord_1767533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767533).length < 2 ^ (prefixWord ++ tailWord_1767533).sum := by decide
  have hdescent : baseEnd_1767533 < baseStart_1767533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767561 : List Nat := [1, 2, 1, 1, 4, 2, 5, 5]
def baseStart_1767561 : Nat := 118140960795 + 1767561 * 2 ^ 59
def prefixEnd_1767561 : Nat := 4983230072969 + 3 ^ 40 * 1767561 * 2
def baseEnd_1767561 : Nat := 134460500613609502690169

theorem tailTrace_1767561 : CollatzResearch.WordTrace tailWord_1767561 prefixEnd_1767561 134460500613609502690169 := by
  unfold tailWord_1767561
  simp only [CollatzResearch.WordTrace]
  refine ⟨64468245949435847230382537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 42978830632957231486921691 64468245949435847230382537)
  ·
    refine ⟨48351184462076885422786903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64468245949435847230382537 48351184462076885422786903)
    ·
      refine ⟨72526776693115328134180355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48351184462076885422786903 72526776693115328134180355)
      ·
        refine ⟨108790165039672992201270533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72526776693115328134180355 108790165039672992201270533)
        ·
          refine ⟨20398155944938686037738225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108790165039672992201270533 20398155944938686037738225)
          ·
            refine ⟨15298616958704014528303669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20398155944938686037738225 15298616958704014528303669)
            ·
              refine ⟨1434245339878501362028469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15298616958704014528303669 1434245339878501362028469)
              ·
                refine ⟨134460500613609502690169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434245339878501362028469 134460500613609502690169)
                ·
                  rfl

theorem cell21_1767561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 5].length) (baseStart_1767561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767561 prefixEnd_1767561 := by exact prefixLift 1767561
  have htrace : WordTrace (prefixWord ++ tailWord_1767561) baseStart_1767561 baseEnd_1767561 := by
    simpa [prefixWord, tailWord_1767561, baseEnd_1767561] using wordTrace_append hprefix tailTrace_1767561
  have hstable : (prefixWord ++ tailWord_1767561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767561).length < 2 ^ (prefixWord ++ tailWord_1767561).sum := by decide
  have hdescent : baseEnd_1767561 < baseStart_1767561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767598 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1767598 : Nat := 118140960795 + 1767598 * 2 ^ 59
def prefixEnd_1767598 : Nat := 4983230072969 + 3 ^ 40 * 1767598 * 2
def baseEnd_1767598 : Nat := 403389945744924665953765

theorem tailTrace_1767598 : CollatzResearch.WordTrace tailWord_1767598 prefixEnd_1767598 403389945744924665953765 := by
  unfold tailWord_1767598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058699431287725318684931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42979730300201201699652965 8058699431287725318684931)
  ·
    refine ⟨12088049146931587978027397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058699431287725318684931 12088049146931587978027397)
    ·
      refine ⟨2266509215049672745880137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12088049146931587978027397 2266509215049672745880137)
      ·
        refine ⟨1699881911287254559410103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266509215049672745880137 1699881911287254559410103)
        ·
          refine ⟨2549822866930881839115155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699881911287254559410103 2549822866930881839115155)
          ·
            refine ⟨3824734300396322758672733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549822866930881839115155 3824734300396322758672733)
            ·
              refine ⟨1434275362648621034502275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824734300396322758672733 1434275362648621034502275)
              ·
                refine ⟨2151413043972931551753413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1434275362648621034502275 2151413043972931551753413)
                ·
                  refine ⟨403389945744924665953765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151413043972931551753413 403389945744924665953765)
                  ·
                    rfl

theorem cell21_1767598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1767598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767598 prefixEnd_1767598 := by exact prefixLift 1767598
  have htrace : WordTrace (prefixWord ++ tailWord_1767598) baseStart_1767598 baseEnd_1767598 := by
    simpa [prefixWord, tailWord_1767598, baseEnd_1767598] using wordTrace_append hprefix tailTrace_1767598
  have hstable : (prefixWord ++ tailWord_1767598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767598).length < 2 ^ (prefixWord ++ tailWord_1767598).sum := by decide
  have hdescent : baseEnd_1767598 < baseStart_1767598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767730 : List Nat := [3, 2, 1, 1, 5, 1, 3, 5]
def baseStart_1767730 : Nat := 118140960795 + 1767730 * 2 ^ 59
def prefixEnd_1767730 : Nat := 4983230072969 + 3 ^ 40 * 1767730 * 2
def baseEnd_1767730 : Nat := 134473356647773923251165

theorem tailTrace_1767730 : CollatzResearch.WordTrace tailWord_1767730 prefixEnd_1767730 134473356647773923251165 := by
  unfold tailWord_1767730
  simp only [CollatzResearch.WordTrace]
  refine ⟨16118602471455897273321161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 42982939923882392728856429 16118602471455897273321161)
  ·
    refine ⟨12088951853591922954990871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16118602471455897273321161 12088951853591922954990871)
    ·
      refine ⟨18133427780387884432486307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12088951853591922954990871 18133427780387884432486307)
      ·
        refine ⟨27200141670581826648729461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133427780387884432486307 27200141670581826648729461)
        ·
          refine ⟨2550013281617046248318387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27200141670581826648729461 2550013281617046248318387)
          ·
            refine ⟨3825019922425569372477581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550013281617046248318387 3825019922425569372477581)
            ·
              refine ⟨1434382470909588514679093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3825019922425569372477581 1434382470909588514679093)
              ·
                refine ⟨134473356647773923251165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434382470909588514679093 134473356647773923251165)
                ·
                  rfl

theorem cell21_1767730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_1767730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767730 prefixEnd_1767730 := by exact prefixLift 1767730
  have htrace : WordTrace (prefixWord ++ tailWord_1767730) baseStart_1767730 baseEnd_1767730 := by
    simpa [prefixWord, tailWord_1767730, baseEnd_1767730] using wordTrace_append hprefix tailTrace_1767730
  have hstable : (prefixWord ++ tailWord_1767730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767730).length < 2 ^ (prefixWord ++ tailWord_1767730).sum := by decide
  have hdescent : baseEnd_1767730 < baseStart_1767730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1767758 : List Nat := [4, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_1767758 : Nat := 118140960795 + 1767758 * 2 ^ 59
def prefixEnd_1767758 : Nat := 4983230072969 + 3 ^ 40 * 1767758 * 2
def baseEnd_1767758 : Nat := 403426459924799943286771

theorem tailTrace_1767758 : CollatzResearch.WordTrace tailWord_1767758 prefixEnd_1767758 403426459924799943286771 := by
  unfold tailWord_1767758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059428891215268734412991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 42983620753148099916869285 8059428891215268734412991)
  ·
    refine ⟨12089143336822903101619487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8059428891215268734412991 12089143336822903101619487)
    ·
      refine ⟨18133715005234354652429231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12089143336822903101619487 18133715005234354652429231)
      ·
        refine ⟨27200572507851531978643847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18133715005234354652429231 27200572507851531978643847)
        ·
          refine ⟨40800858761777297967965771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27200572507851531978643847 40800858761777297967965771)
          ·
            refine ⟨61201288142665946951948657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40800858761777297967965771 61201288142665946951948657)
            ·
              refine ⟨45900966106999460213961493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61201288142665946951948657 45900966106999460213961493)
              ·
                refine ⟨2151607786265599697529445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45900966106999460213961493 2151607786265599697529445)
                ·
                  refine ⟨403426459924799943286771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2151607786265599697529445 403426459924799943286771)
                  ·
                    rfl

theorem cell21_1767758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_1767758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1767758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1767758 prefixEnd_1767758 := by exact prefixLift 1767758
  have htrace : WordTrace (prefixWord ++ tailWord_1767758) baseStart_1767758 baseEnd_1767758 := by
    simpa [prefixWord, tailWord_1767758, baseEnd_1767758] using wordTrace_append hprefix tailTrace_1767758
  have hstable : (prefixWord ++ tailWord_1767758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1767758).length < 2 ^ (prefixWord ++ tailWord_1767758).sum := by decide
  have hdescent : baseEnd_1767758 < baseStart_1767758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1767758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
