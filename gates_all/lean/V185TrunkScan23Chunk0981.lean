import V185TrunkScan23Chunk0980

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5806884 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_5806884 : Nat := 118140960795 + 5806884 * 2 ^ 59
def prefixEnd_5806884 : Nat := 4983230072969 + 3 ^ 40 * 5806884 * 2
def baseEnd_5806884 : Nat := 993907532300987924448211

theorem tailTrace_5806884 : CollatzResearch.WordTrace tailWord_5806884 prefixEnd_5806884 993907532300987924448211 := by
  unfold tailWord_5806884
  simp only [CollatzResearch.WordTrace]
  refine ⟨105897229547329239838053853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141196306063105653117405137 105897229547329239838053853)
  ·
    refine ⟨39711461080248464939270195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105897229547329239838053853 39711461080248464939270195)
    ·
      refine ⟨59567191620372697408905293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39711461080248464939270195 59567191620372697408905293)
      ·
        refine ⟨22337696857639761528339485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59567191620372697408905293 22337696857639761528339485)
        ·
          refine ⟨8376636321614910573127307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22337696857639761528339485 8376636321614910573127307)
          ·
            refine ⟨12564954482422365859690961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376636321614910573127307 12564954482422365859690961)
            ·
              refine ⟨9423715861816774394768221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12564954482422365859690961 9423715861816774394768221)
              ·
                refine ⟨3533893448181290398038083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9423715861816774394768221 3533893448181290398038083)
                ·
                  refine ⟨5300840172271935597057125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533893448181290398038083 5300840172271935597057125)
                  ·
                    refine ⟨993907532300987924448211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5300840172271935597057125 993907532300987924448211)
                    ·
                      rfl

theorem cell23_5806884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_5806884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806884 prefixEnd_5806884 := by exact prefixLift 5806884
  have htrace : WordTrace (prefixWord ++ tailWord_5806884) baseStart_5806884 baseEnd_5806884 := by
    simpa [prefixWord, tailWord_5806884, baseEnd_5806884] using wordTrace_append hprefix tailTrace_5806884
  have hstable : (prefixWord ++ tailWord_5806884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806884).length < 2 ^ (prefixWord ++ tailWord_5806884).sum := by decide
  have hdescent : baseEnd_5806884 < baseStart_5806884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806930 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_5806930 : Nat := 118140960795 + 5806930 * 2 ^ 59
def prefixEnd_5806930 : Nat := 4983230072969 + 3 ^ 40 * 5806930 * 2
def baseEnd_5806930 : Nat := 2981746217013070593369421

theorem tailTrace_5806930 : CollatzResearch.WordTrace tailWord_5806930 prefixEnd_5806930 2981746217013070593369421 := by
  unfold tailWord_5806930
  simp only [CollatzResearch.WordTrace]
  refine ⟨52949034213122957383070561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141197424568327886354854829 52949034213122957383070561)
  ·
    refine ⟨39711775659842218037302921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52949034213122957383070561 39711775659842218037302921)
    ·
      refine ⟨29783831744881663527977191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39711775659842218037302921 29783831744881663527977191)
      ·
        refine ⟨44675747617322495291965787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29783831744881663527977191 44675747617322495291965787)
        ·
          refine ⟨67013621425983742937948681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44675747617322495291965787 67013621425983742937948681)
          ·
            refine ⟨50260216069487807203461511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67013621425983742937948681 50260216069487807203461511)
            ·
              refine ⟨75390324104231710805192267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50260216069487807203461511 75390324104231710805192267)
              ·
                refine ⟨113085486156347566207788401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75390324104231710805192267 113085486156347566207788401)
                ·
                  refine ⟨84814114617260674655841301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113085486156347566207788401 84814114617260674655841301)
                  ·
                    refine ⟨3975661622684094124492561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84814114617260674655841301 3975661622684094124492561)
                    ·
                      refine ⟨2981746217013070593369421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975661622684094124492561 2981746217013070593369421)
                      ·
                        rfl

theorem cell23_5806930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_5806930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806930 prefixEnd_5806930 := by exact prefixLift 5806930
  have htrace : WordTrace (prefixWord ++ tailWord_5806930) baseStart_5806930 baseEnd_5806930 := by
    simpa [prefixWord, tailWord_5806930, baseEnd_5806930] using wordTrace_append hprefix tailTrace_5806930
  have hstable : (prefixWord ++ tailWord_5806930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806930).length < 2 ^ (prefixWord ++ tailWord_5806930).sum := by decide
  have hdescent : baseEnd_5806930 < baseStart_5806930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806933 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_5806933 : Nat := 118140960795 + 5806933 * 2 ^ 59
def prefixEnd_5806933 : Nat := 4983230072969 + 3 ^ 40 * 5806933 * 2
def baseEnd_5806933 : Nat := 2981747757455034081631907

theorem tailTrace_5806933 : CollatzResearch.WordTrace tailWord_5806933 prefixEnd_5806933 2981747757455034081631907 := by
  unfold tailWord_5806933
  simp only [CollatzResearch.WordTrace]
  refine ⟨211796246271480961044641453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141197497514320640696427635 211796246271480961044641453)
  ·
    refine ⟨79423592351805360391740545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211796246271480961044641453 79423592351805360391740545)
    ·
      refine ⟨59567694263854020293805409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79423592351805360391740545 59567694263854020293805409)
      ·
        refine ⟨44675770697890515220354057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59567694263854020293805409 44675770697890515220354057)
        ·
          refine ⟨33506828023417886415265543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44675770697890515220354057 33506828023417886415265543)
          ·
            refine ⟨50260242035126829622898315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33506828023417886415265543 50260242035126829622898315)
            ·
              refine ⟨75390363052690244434347473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50260242035126829622898315 75390363052690244434347473)
              ·
                refine ⟨56542772289517683325760605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75390363052690244434347473 56542772289517683325760605)
                ·
                  refine ⟨21203539608569131247160227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56542772289517683325760605 21203539608569131247160227)
                  ·
                    refine ⟨31805309412853696870740341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21203539608569131247160227 31805309412853696870740341)
                    ·
                      refine ⟨2981747757455034081631907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31805309412853696870740341 2981747757455034081631907)
                      ·
                        rfl

theorem cell23_5806933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_5806933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806933 prefixEnd_5806933 := by exact prefixLift 5806933
  have htrace : WordTrace (prefixWord ++ tailWord_5806933) baseStart_5806933 baseEnd_5806933 := by
    simpa [prefixWord, tailWord_5806933, baseEnd_5806933] using wordTrace_append hprefix tailTrace_5806933
  have hstable : (prefixWord ++ tailWord_5806933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806933).length < 2 ^ (prefixWord ++ tailWord_5806933).sum := by decide
  have hdescent : baseEnd_5806933 < baseStart_5806933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806943 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_5806943 : Nat := 118140960795 + 5806943 * 2 ^ 59
def prefixEnd_5806943 : Nat := 4983230072969 + 3 ^ 40 * 5806943 * 2
def baseEnd_5806943 : Nat := 2981752892261579042506861

theorem tailTrace_5806943 : CollatzResearch.WordTrace tailWord_5806943 prefixEnd_5806943 2981752892261579042506861 := by
  unfold tailWord_5806943
  simp only [CollatzResearch.WordTrace]
  refine ⟨211796611001444732752505483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141197740667629821835003655 211796611001444732752505483)
  ·
    refine ⟨317694916502167099128758225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211796611001444732752505483 317694916502167099128758225)
    ·
      refine ⟨238271187376625324346568669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317694916502167099128758225 238271187376625324346568669)
      ·
        refine ⟨89351695266234496629963251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238271187376625324346568669 89351695266234496629963251)
        ·
          refine ⟨134027542899351744944944877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89351695266234496629963251 134027542899351744944944877)
          ·
            refine ⟨50260328587256904354354329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134027542899351744944944877 50260328587256904354354329)
            ·
              refine ⟨37695246440442678265765747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50260328587256904354354329 37695246440442678265765747)
              ·
                refine ⟨56542869660664017398648621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37695246440442678265765747 56542869660664017398648621)
                ·
                  refine ⟨21203576122749006524493233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56542869660664017398648621 21203576122749006524493233)
                  ·
                    refine ⟨15902682092061754893369925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21203576122749006524493233 15902682092061754893369925)
                    ·
                      refine ⟨2981752892261579042506861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15902682092061754893369925 2981752892261579042506861)
                      ·
                        rfl

theorem cell23_5806943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_5806943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806943 prefixEnd_5806943 := by exact prefixLift 5806943
  have htrace : WordTrace (prefixWord ++ tailWord_5806943) baseStart_5806943 baseEnd_5806943 := by
    simpa [prefixWord, tailWord_5806943, baseEnd_5806943] using wordTrace_append hprefix tailTrace_5806943
  have hstable : (prefixWord ++ tailWord_5806943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806943).length < 2 ^ (prefixWord ++ tailWord_5806943).sum := by decide
  have hdescent : baseEnd_5806943 < baseStart_5806943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806958 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5806958 : Nat := 118140960795 + 5806958 * 2 ^ 59
def prefixEnd_5806958 : Nat := 4983230072969 + 3 ^ 40 * 5806958 * 2
def baseEnd_5806958 : Nat := 2981760594471396483819293

theorem tailTrace_5806958 : CollatzResearch.WordTrace tailWord_5806958 prefixEnd_5806958 2981760594471396483819293 := by
  unfold tailWord_5806958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26474644762048798789287691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141198105397593593542867685 26474644762048798789287691)
  ·
    refine ⟨39711967143073198183931537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26474644762048798789287691 39711967143073198183931537)
    ·
      refine ⟨29783975357304898637948653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39711967143073198183931537 29783975357304898637948653)
      ·
        refine ⟨11168990758989336989230745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29783975357304898637948653 11168990758989336989230745)
        ·
          refine ⟨8376743069242002741923059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11168990758989336989230745 8376743069242002741923059)
          ·
            refine ⟨12565114603863004112884589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376743069242002741923059 12565114603863004112884589)
            ·
              refine ⟨4711917976448626542331721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12565114603863004112884589 4711917976448626542331721)
              ·
                refine ⟨3533938482336469906748791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711917976448626542331721 3533938482336469906748791)
                ·
                  refine ⟨5300907723504704860123187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533938482336469906748791 5300907723504704860123187)
                  ·
                    refine ⟨7951361585257057290184781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5300907723504704860123187 7951361585257057290184781)
                    ·
                      refine ⟨2981760594471396483819293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951361585257057290184781 2981760594471396483819293)
                      ·
                        rfl

theorem cell23_5806958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5806958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806958 prefixEnd_5806958 := by exact prefixLift 5806958
  have htrace : WordTrace (prefixWord ++ tailWord_5806958) baseStart_5806958 baseEnd_5806958 := by
    simpa [prefixWord, tailWord_5806958, baseEnd_5806958] using wordTrace_append hprefix tailTrace_5806958
  have hstable : (prefixWord ++ tailWord_5806958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806958).length < 2 ^ (prefixWord ++ tailWord_5806958).sum := by decide
  have hdescent : baseEnd_5806958 < baseStart_5806958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806978 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5806978 : Nat := 118140960795 + 5806978 * 2 ^ 59
def prefixEnd_5806978 : Nat := 4983230072969 + 3 ^ 40 * 5806978 * 2
def baseEnd_5806978 : Nat := 993923621361495468523067

theorem tailTrace_5806978 : CollatzResearch.WordTrace tailWord_5806978 prefixEnd_5806978 993923621361495468523067 := by
  unfold tailWord_5806978
  simp only [CollatzResearch.WordTrace]
  refine ⟨52949471889079483432507397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141198591704211955820019725 52949471889079483432507397)
  ·
    refine ⟨9928025979202403143595137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52949471889079483432507397 9928025979202403143595137)
    ·
      refine ⟨7446019484401802357696353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9928025979202403143595137 7446019484401802357696353)
      ·
        refine ⟨5584514613301351768272265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7446019484401802357696353 5584514613301351768272265)
        ·
          refine ⟨4188385959976013826204199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5584514613301351768272265 4188385959976013826204199)
          ·
            refine ⟨6282578939964020739306299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188385959976013826204199 6282578939964020739306299)
            ·
              refine ⟨9423868409946031108959449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282578939964020739306299 9423868409946031108959449)
              ·
                refine ⟨7067901307459523331719587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9423868409946031108959449 7067901307459523331719587)
                ·
                  refine ⟨10601851961189284997579381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067901307459523331719587 10601851961189284997579381)
                  ·
                    refine ⟨993923621361495468523067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10601851961189284997579381 993923621361495468523067)
                    ·
                      rfl

theorem cell23_5806978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5806978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806978 prefixEnd_5806978 := by exact prefixLift 5806978
  have htrace : WordTrace (prefixWord ++ tailWord_5806978) baseStart_5806978 baseEnd_5806978 := by
    simpa [prefixWord, tailWord_5806978, baseEnd_5806978] using wordTrace_append hprefix tailTrace_5806978
  have hstable : (prefixWord ++ tailWord_5806978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806978).length < 2 ^ (prefixWord ++ tailWord_5806978).sum := by decide
  have hdescent : baseEnd_5806978 < baseStart_5806978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806980 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_5806980 : Nat := 118140960795 + 5806980 * 2 ^ 59
def prefixEnd_5806980 : Nat := 4983230072969 + 3 ^ 40 * 5806980 * 2
def baseEnd_5806980 : Nat := 2981771891045795397744191

theorem tailTrace_5806980 : CollatzResearch.WordTrace tailWord_5806980 prefixEnd_5806980 2981771891045795397744191 := by
  unfold tailWord_5806980
  simp only [CollatzResearch.WordTrace]
  refine ⟨105898980251155344035801197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141198640334873792047734929 105898980251155344035801197)
  ·
    refine ⟨39712117594183254013425449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105898980251155344035801197 39712117594183254013425449)
    ·
      refine ⟨29784088195637440510069087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39712117594183254013425449 29784088195637440510069087)
      ·
        refine ⟨44676132293456160765103631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29784088195637440510069087 44676132293456160765103631)
        ·
          refine ⟨67014198440184241147655447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44676132293456160765103631 67014198440184241147655447)
          ·
            refine ⟨100521297660276361721483171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67014198440184241147655447 100521297660276361721483171)
            ·
              refine ⟨150781946490414542582224757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100521297660276361721483171 150781946490414542582224757)
              ·
                refine ⟨14135807483476363367083571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150781946490414542582224757 14135807483476363367083571)
                ·
                  refine ⟨21203711225214545050625357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14135807483476363367083571 21203711225214545050625357)
                  ·
                    refine ⟨7951391709455454393984509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21203711225214545050625357 7951391709455454393984509)
                    ·
                      refine ⟨2981771891045795397744191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951391709455454393984509 2981771891045795397744191)
                      ·
                        rfl

theorem cell23_5806980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_5806980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806980 prefixEnd_5806980 := by exact prefixLift 5806980
  have htrace : WordTrace (prefixWord ++ tailWord_5806980) baseStart_5806980 baseEnd_5806980 := by
    simpa [prefixWord, tailWord_5806980, baseEnd_5806980] using wordTrace_append hprefix tailTrace_5806980
  have hstable : (prefixWord ++ tailWord_5806980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806980).length < 2 ^ (prefixWord ++ tailWord_5806980).sum := by decide
  have hdescent : baseEnd_5806980 < baseStart_5806980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806984 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_5806984 : Nat := 118140960795 + 5806984 * 2 ^ 59
def prefixEnd_5806984 : Nat := 4983230072969 + 3 ^ 40 * 5806984 * 2
def baseEnd_5806984 : Nat := 2981773944968413382094173

theorem tailTrace_5806984 : CollatzResearch.WordTrace tailWord_5806984 prefixEnd_5806984 2981773944968413382094173 := by
  unfold tailWord_5806984
  simp only [CollatzResearch.WordTrace]
  refine ⟨105899053197148098377374003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141198737596197464503165337 105899053197148098377374003)
  ·
    refine ⟨158848579795722147566061005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105899053197148098377374003 158848579795722147566061005)
    ·
      refine ⟨59568217423395805337272877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158848579795722147566061005 59568217423395805337272877)
      ·
        refine ⟨22338081533773427001477329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59568217423395805337272877 22338081533773427001477329)
        ·
          refine ⟨16753561150330070251107997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22338081533773427001477329 16753561150330070251107997)
          ·
            refine ⟨6282585431373776344165499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16753561150330070251107997 6282585431373776344165499)
            ·
              refine ⟨9423878147060664516248249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282585431373776344165499 9423878147060664516248249)
              ·
                refine ⟨7067908610295498387186187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9423878147060664516248249 7067908610295498387186187)
                ·
                  refine ⟨10601862915443247580779281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067908610295498387186187 10601862915443247580779281)
                  ·
                    refine ⟨7951397186582435685584461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10601862915443247580779281 7951397186582435685584461)
                    ·
                      refine ⟨2981773944968413382094173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951397186582435685584461 2981773944968413382094173)
                      ·
                        rfl

theorem cell23_5806984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_5806984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806984 prefixEnd_5806984 := by exact prefixLift 5806984
  have htrace : WordTrace (prefixWord ++ tailWord_5806984) baseStart_5806984 baseEnd_5806984 := by
    simpa [prefixWord, tailWord_5806984, baseEnd_5806984] using wordTrace_append hprefix tailTrace_5806984
  have hstable : (prefixWord ++ tailWord_5806984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806984).length < 2 ^ (prefixWord ++ tailWord_5806984).sum := by decide
  have hdescent : baseEnd_5806984 < baseStart_5806984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5806998 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5806998 : Nat := 118140960795 + 5806998 * 2 ^ 59
def prefixEnd_5806998 : Nat := 4983230072969 + 3 ^ 40 * 5806998 * 2
def baseEnd_5806998 : Nat := 2981781133697576327319109

theorem tailTrace_5806998 : CollatzResearch.WordTrace tailWord_5806998 prefixEnd_5806998 2981781133697576327319109 := by
  unfold tailWord_5806998
  simp only [CollatzResearch.WordTrace]
  refine ⟨13237413563515342321609853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141199078010830318097171765 13237413563515342321609853)
  ·
    refine ⟨4964030086318253370603695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13237413563515342321609853 4964030086318253370603695)
    ·
      refine ⟨7446045129477380055905543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4964030086318253370603695 7446045129477380055905543)
      ·
        refine ⟨11169067694216070083858315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446045129477380055905543 11169067694216070083858315)
        ·
          refine ⟨16753601541324105125787473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169067694216070083858315 16753601541324105125787473)
          ·
            refine ⟨12565201155993078844340605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16753601541324105125787473 12565201155993078844340605)
            ·
              refine ⟨4711950433497404566627727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12565201155993078844340605 4711950433497404566627727)
              ·
                refine ⟨7067925650246106849941591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711950433497404566627727 7067925650246106849941591)
                ·
                  refine ⟨10601888475369160274912387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067925650246106849941591 10601888475369160274912387)
                  ·
                    refine ⟨15902832713053740412368581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10601888475369160274912387 15902832713053740412368581)
                    ·
                      refine ⟨2981781133697576327319109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15902832713053740412368581 2981781133697576327319109)
                      ·
                        rfl

theorem cell23_5806998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5806998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5806998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5806998 prefixEnd_5806998 := by exact prefixLift 5806998
  have htrace : WordTrace (prefixWord ++ tailWord_5806998) baseStart_5806998 baseEnd_5806998 := by
    simpa [prefixWord, tailWord_5806998, baseEnd_5806998] using wordTrace_append hprefix tailTrace_5806998
  have hstable : (prefixWord ++ tailWord_5806998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5806998).length < 2 ^ (prefixWord ++ tailWord_5806998).sum := by decide
  have hdescent : baseEnd_5806998 < baseStart_5806998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5806998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807015 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_5807015 : Nat := 118140960795 + 5807015 * 2 ^ 59
def prefixEnd_5807015 : Nat := 4983230072969 + 3 ^ 40 * 5807015 * 2
def baseEnd_5807015 : Nat := 2981789862868702760806531

theorem tailTrace_5807015 : CollatzResearch.WordTrace tailWord_5807015 prefixEnd_5807015 2981789862868702760806531 := by
  unfold tailWord_5807015
  simp only [CollatzResearch.WordTrace]
  refine ⟨211799237057183889049126499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141199491371455926032750999 211799237057183889049126499)
  ·
    refine ⟨317698855585775833573689749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211799237057183889049126499 317698855585775833573689749)
    ·
      refine ⟨14892133855583242198766707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317698855585775833573689749 14892133855583242198766707)
      ·
        refine ⟨22338200783374863298150061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892133855583242198766707 22338200783374863298150061)
        ·
          refine ⟨8376825293765573736806273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22338200783374863298150061 8376825293765573736806273)
          ·
            refine ⟨6282618970324180302604705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8376825293765573736806273 6282618970324180302604705)
            ·
              refine ⟨4711964227743135226953529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6282618970324180302604705 4711964227743135226953529)
              ·
                refine ⟨3533973170807351420215147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711964227743135226953529 3533973170807351420215147)
                ·
                  refine ⟨5300959756211027130322721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3533973170807351420215147 5300959756211027130322721)
                  ·
                    refine ⟨3975719817158270347742041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5300959756211027130322721 3975719817158270347742041)
                    ·
                      refine ⟨2981789862868702760806531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975719817158270347742041 2981789862868702760806531)
                      ·
                        rfl

theorem cell23_5807015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_5807015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807015 prefixEnd_5807015 := by exact prefixLift 5807015
  have htrace : WordTrace (prefixWord ++ tailWord_5807015) baseStart_5807015 baseEnd_5807015 := by
    simpa [prefixWord, tailWord_5807015, baseEnd_5807015] using wordTrace_append hprefix tailTrace_5807015
  have hstable : (prefixWord ++ tailWord_5807015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807015).length < 2 ^ (prefixWord ++ tailWord_5807015).sum := by decide
  have hdescent : baseEnd_5807015 < baseStart_5807015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_5807023 : Nat := 118140960795 + 5807023 * 2 ^ 59
def prefixEnd_5807023 : Nat := 4983230072969 + 3 ^ 40 * 5807023 * 2
def baseEnd_5807023 : Nat := 2981793970713938729506493

theorem tailTrace_5807023 : CollatzResearch.WordTrace tailWord_5807023 prefixEnd_5807023 2981793970713938729506493 := by
  unfold tailWord_5807023
  simp only [CollatzResearch.WordTrace]
  refine ⟨211799528841154906415417723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141199685894103270943611815 211799528841154906415417723)
  ·
    refine ⟨317699293261732359623126585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211799528841154906415417723 317699293261732359623126585)
    ·
      refine ⟨238274469946299269717344939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317699293261732359623126585 238274469946299269717344939)
      ·
        refine ⟨357411704919448904576017409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238274469946299269717344939 357411704919448904576017409)
        ·
          refine ⟨268058778689586678432013057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357411704919448904576017409 268058778689586678432013057)
          ·
            refine ⟨201044084017190008824009793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268058778689586678432013057 201044084017190008824009793)
            ·
              refine ⟨150783063012892506618007345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201044084017190008824009793 150783063012892506618007345)
              ·
                refine ⟨113087297259669379963505509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150783063012892506618007345 113087297259669379963505509)
                ·
                  refine ⟨21203868236188008743157283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113087297259669379963505509 21203868236188008743157283)
                  ·
                    refine ⟨31805802354282013114735925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21203868236188008743157283 31805802354282013114735925)
                    ·
                      refine ⟨2981793970713938729506493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31805802354282013114735925 2981793970713938729506493)
                      ·
                        rfl

theorem cell23_5807023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_5807023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807023 prefixEnd_5807023 := by exact prefixLift 5807023
  have htrace : WordTrace (prefixWord ++ tailWord_5807023) baseStart_5807023 baseEnd_5807023 := by
    simpa [prefixWord, tailWord_5807023, baseEnd_5807023] using wordTrace_append hprefix tailTrace_5807023
  have hstable : (prefixWord ++ tailWord_5807023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807023).length < 2 ^ (prefixWord ++ tailWord_5807023).sum := by decide
  have hdescent : baseEnd_5807023 < baseStart_5807023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807043 : List Nat := [1, 1, 1, 3, 1, 1, 2, 6, 7]
def baseStart_5807043 : Nat := 118140960795 + 5807043 * 2 ^ 59
def prefixEnd_5807043 : Nat := 4983230072969 + 3 ^ 40 * 5807043 * 2
def baseEnd_5807043 : Nat := 331311582258558739028489

theorem tailTrace_5807043 : CollatzResearch.WordTrace tailWord_5807043 prefixEnd_5807043 331311582258558739028489 := by
  unfold tailWord_5807043
  simp only [CollatzResearch.WordTrace]
  refine ⟨211800258301082449831145783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141200172200721633220763855 211800258301082449831145783)
  ·
    refine ⟨317700387451623674746718675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211800258301082449831145783 317700387451623674746718675)
    ·
      refine ⟨476550581177435512120078013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317700387451623674746718675 476550581177435512120078013)
      ·
        refine ⟨178706467941538317045029255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476550581177435512120078013 178706467941538317045029255)
        ·
          refine ⟨268059701912307475567543883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178706467941538317045029255 268059701912307475567543883)
          ·
            refine ⟨402089552868461213351315825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268059701912307475567543883 402089552868461213351315825)
            ·
              refine ⟨301567164651345910013486869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402089552868461213351315825 301567164651345910013486869)
              ·
                refine ⟨14135960843031839531882197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 301567164651345910013486869 14135960843031839531882197)
                ·
                  refine ⟨331311582258558739028489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14135960843031839531882197 331311582258558739028489)
                  ·
                    rfl

theorem cell23_5807043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 7].length) (baseStart_5807043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807043 prefixEnd_5807043 := by exact prefixLift 5807043
  have htrace : WordTrace (prefixWord ++ tailWord_5807043) baseStart_5807043 baseEnd_5807043 := by
    simpa [prefixWord, tailWord_5807043, baseEnd_5807043] using wordTrace_append hprefix tailTrace_5807043
  have hstable : (prefixWord ++ tailWord_5807043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807043).length < 2 ^ (prefixWord ++ tailWord_5807043).sum := by decide
  have hdescent : baseEnd_5807043 < baseStart_5807043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807058 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5807058 : Nat := 118140960795 + 5807058 * 2 ^ 59
def prefixEnd_5807058 : Nat := 4983230072969 + 3 ^ 40 * 5807058 * 2
def baseEnd_5807058 : Nat := 2981811942536846092568833

theorem tailTrace_5807058 : CollatzResearch.WordTrace tailWord_5807058 prefixEnd_5807058 2981811942536846092568833 := by
  unfold tailWord_5807058
  simp only [CollatzResearch.WordTrace]
  refine ⟨52950201349007026848235457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141200536930685404928627885 52950201349007026848235457)
  ·
    refine ⟨39712651011755270136176593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52950201349007026848235457 39712651011755270136176593)
    ·
      refine ⟨29784488258816452602132445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39712651011755270136176593 29784488258816452602132445)
      ·
        refine ⟨11169183097056169725799667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29784488258816452602132445 11169183097056169725799667)
        ·
          refine ⟨16753774645584254588699501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169183097056169725799667 16753774645584254588699501)
          ·
            refine ⟨6282665492094095470762313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16753774645584254588699501 6282665492094095470762313)
            ·
              refine ⟨4711999119070571603071735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6282665492094095470762313 4711999119070571603071735)
              ·
                refine ⟨7067998678605857404607603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4711999119070571603071735 7067998678605857404607603)
                ·
                  refine ⟨10601998017908786106911405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7067998678605857404607603 10601998017908786106911405)
                  ·
                    refine ⟨3975749256715794790091777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10601998017908786106911405 3975749256715794790091777)
                    ·
                      refine ⟨2981811942536846092568833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975749256715794790091777 2981811942536846092568833)
                      ·
                        rfl

theorem cell23_5807058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5807058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807058 prefixEnd_5807058 := by exact prefixLift 5807058
  have htrace : WordTrace (prefixWord ++ tailWord_5807058) baseStart_5807058 baseEnd_5807058 := by
    simpa [prefixWord, tailWord_5807058, baseEnd_5807058] using wordTrace_append hprefix tailTrace_5807058
  have hstable : (prefixWord ++ tailWord_5807058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807058).length < 2 ^ (prefixWord ++ tailWord_5807058).sum := by decide
  have hdescent : baseEnd_5807058 < baseStart_5807058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807092 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5807092 : Nat := 118140960795 + 5807092 * 2 ^ 59
def prefixEnd_5807092 : Nat := 4983230072969 + 3 ^ 40 * 5807092 * 2
def baseEnd_5807092 : Nat := 2981829400879098959543677

theorem tailTrace_5807092 : CollatzResearch.WordTrace tailWord_5807092 prefixEnd_5807092 2981829400879098959543677 := by
  unfold tailWord_5807092
  simp only [CollatzResearch.WordTrace]
  refine ⟨105901022738952465599839765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141201363651936620799786353 105901022738952465599839765)
  ·
    refine ⟨4964110440888396824992489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105901022738952465599839765 4964110440888396824992489)
    ·
      refine ⟨3723082830666297618744367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4964110440888396824992489 3723082830666297618744367)
      ·
        refine ⟨5584624245999446428116551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3723082830666297618744367 5584624245999446428116551)
        ·
          refine ⟨8376936368999169642174827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584624245999446428116551 8376936368999169642174827)
          ·
            refine ⟨12565404553498754463262241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376936368999169642174827 12565404553498754463262241)
            ·
              refine ⟨9424053415124065847446681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12565404553498754463262241 9424053415124065847446681)
              ·
                refine ⟨7068040061343049385585011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424053415124065847446681 7068040061343049385585011)
                ·
                  refine ⟨10602060092014574078377517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068040061343049385585011 10602060092014574078377517)
                  ·
                    refine ⟨3975772534505465279391569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10602060092014574078377517 3975772534505465279391569)
                    ·
                      refine ⟨2981829400879098959543677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975772534505465279391569 2981829400879098959543677)
                      ·
                        rfl

theorem cell23_5807092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5807092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807092 prefixEnd_5807092 := by exact prefixLift 5807092
  have htrace : WordTrace (prefixWord ++ tailWord_5807092) baseStart_5807092 baseEnd_5807092 := by
    simpa [prefixWord, tailWord_5807092, baseEnd_5807092] using wordTrace_append hprefix tailTrace_5807092
  have hstable : (prefixWord ++ tailWord_5807092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807092).length < 2 ^ (prefixWord ++ tailWord_5807092).sum := by decide
  have hdescent : baseEnd_5807092 < baseStart_5807092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807127 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5807127 : Nat := 118140960795 + 5807127 * 2 ^ 59
def prefixEnd_5807127 : Nat := 4983230072969 + 3 ^ 40 * 5807127 * 2
def baseEnd_5807127 : Nat := 2981847372702006322606015

theorem tailTrace_5807127 : CollatzResearch.WordTrace tailWord_5807127 prefixEnd_5807127 2981847372702006322606015 := by
  unfold tailWord_5807127
  simp only [CollatzResearch.WordTrace]
  refine ⟨211803322032778132177203635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141202214688518754784802423 211803322032778132177203635)
  ·
    refine ⟨317704983049167198265805453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211803322032778132177203635 317704983049167198265805453)
    ·
      refine ⟨119139368643437699349677045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317704983049167198265805453 119139368643437699349677045)
      ·
        refine ⟨11169315810322284314032223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119139368643437699349677045 11169315810322284314032223)
        ·
          refine ⟨16753973715483426471048335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169315810322284314032223 16753973715483426471048335)
          ·
            refine ⟨25130960573225139706572503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16753973715483426471048335 25130960573225139706572503)
            ·
              refine ⟨37696440859837709559858755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25130960573225139706572503 37696440859837709559858755)
              ·
                refine ⟨56544661289756564339788133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37696440859837709559858755 56544661289756564339788133)
                ·
                  refine ⟨10602123991829355813710275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56544661289756564339788133 10602123991829355813710275)
                  ·
                    refine ⟨15903185987744033720565413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10602123991829355813710275 15903185987744033720565413)
                    ·
                      refine ⟨2981847372702006322606015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15903185987744033720565413 2981847372702006322606015)
                      ·
                        rfl

theorem cell23_5807127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5807127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807127 prefixEnd_5807127 := by exact prefixLift 5807127
  have htrace : WordTrace (prefixWord ++ tailWord_5807127) baseStart_5807127 baseEnd_5807127 := by
    simpa [prefixWord, tailWord_5807127, baseEnd_5807127] using wordTrace_append hprefix tailTrace_5807127
  have hstable : (prefixWord ++ tailWord_5807127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807127).length < 2 ^ (prefixWord ++ tailWord_5807127).sum := by decide
  have hdescent : baseEnd_5807127 < baseStart_5807127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807164 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_5807164 : Nat := 118140960795 + 5807164 * 2 ^ 59
def prefixEnd_5807164 : Nat := 4983230072969 + 3 ^ 40 * 5807164 * 2
def baseEnd_5807164 : Nat := 2981866371486222677843345

theorem tailTrace_5807164 : CollatzResearch.WordTrace tailWord_5807164 prefixEnd_5807164 2981866371486222677843345 := by
  unfold tailWord_5807164
  simp only [CollatzResearch.WordTrace]
  refine ⟨105902335766822043748150273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141203114355762724997533697 105902335766822043748150273)
  ·
    refine ⟨79426751825116532811112705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105902335766822043748150273 79426751825116532811112705)
    ·
      refine ⟨59570063868837399608334529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79426751825116532811112705 59570063868837399608334529)
      ·
        refine ⟨44677547901628049706250897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59570063868837399608334529 44677547901628049706250897)
        ·
          refine ⟨33508160926221037279688173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44677547901628049706250897 33508160926221037279688173)
          ·
            refine ⟨12565560347332888979883065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33508160926221037279688173 12565560347332888979883065)
            ·
              refine ⟨9424170260499666734912299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12565560347332888979883065 9424170260499666734912299)
              ·
                refine ⟨14136255390749500102368449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9424170260499666734912299 14136255390749500102368449)
                ·
                  refine ⟨10602191543062125076776337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14136255390749500102368449 10602191543062125076776337)
                  ·
                    refine ⟨7951643657296593807582253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10602191543062125076776337 7951643657296593807582253)
                    ·
                      refine ⟨2981866371486222677843345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951643657296593807582253 2981866371486222677843345)
                      ·
                        rfl

theorem cell23_5807164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_5807164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807164 prefixEnd_5807164 := by exact prefixLift 5807164
  have htrace : WordTrace (prefixWord ++ tailWord_5807164) baseStart_5807164 baseEnd_5807164 := by
    simpa [prefixWord, tailWord_5807164, baseEnd_5807164] using wordTrace_append hprefix tailTrace_5807164
  have hstable : (prefixWord ++ tailWord_5807164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807164).length < 2 ^ (prefixWord ++ tailWord_5807164).sum := by decide
  have hdescent : baseEnd_5807164 < baseStart_5807164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807177 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 3]
def baseStart_5807177 : Nat := 118140960795 + 5807177 * 2 ^ 59
def prefixEnd_5807177 : Nat := 4983230072969 + 3 ^ 40 * 5807177 * 2
def baseEnd_5807177 : Nat := 2981873046734731126980785

theorem tailTrace_5807177 : CollatzResearch.WordTrace tailWord_5807177 prefixEnd_5807177 2981873046734731126980785 := by
  unfold tailWord_5807177
  simp only [CollatzResearch.WordTrace]
  refine ⟨211805145682596990716523785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141203430455064660477682523 211805145682596990716523785)
  ·
    refine ⟨158853859261947743037392839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211805145682596990716523785 158853859261947743037392839)
    ·
      refine ⟨238280788892921614556089259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158853859261947743037392839 238280788892921614556089259)
      ·
        refine ⟨357421183339382421834133889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238280788892921614556089259 357421183339382421834133889)
        ·
          refine ⟨268065887504536816375600417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357421183339382421834133889 268065887504536816375600417)
          ·
            refine ⟨201049415628402612281700313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268065887504536816375600417 201049415628402612281700313)
            ·
              refine ⟨150787061721301959211275235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201049415628402612281700313 150787061721301959211275235)
              ·
                refine ⟨226180592581952938816912853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150787061721301959211275235 226180592581952938816912853)
                ·
                  refine ⟨5301107638639522003521395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226180592581952938816912853 5301107638639522003521395)
                  ·
                    refine ⟨7951661457959283005282093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301107638639522003521395 7951661457959283005282093)
                    ·
                      refine ⟨2981873046734731126980785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951661457959283005282093 2981873046734731126980785)
                      ·
                        rfl

theorem cell23_5807177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 3].length) (baseStart_5807177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807177 prefixEnd_5807177 := by exact prefixLift 5807177
  have htrace : WordTrace (prefixWord ++ tailWord_5807177) baseStart_5807177 baseEnd_5807177 := by
    simpa [prefixWord, tailWord_5807177, baseEnd_5807177] using wordTrace_append hprefix tailTrace_5807177
  have hstable : (prefixWord ++ tailWord_5807177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807177).length < 2 ^ (prefixWord ++ tailWord_5807177).sum := by decide
  have hdescent : baseEnd_5807177 < baseStart_5807177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807217 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_5807217 : Nat := 118140960795 + 5807217 * 2 ^ 59
def prefixEnd_5807217 : Nat := 4983230072969 + 3 ^ 40 * 5807217 * 2
def baseEnd_5807217 : Nat := 2981893585960910970480601

theorem tailTrace_5807217 : CollatzResearch.WordTrace tailWord_5807217 prefixEnd_5807217 2981893585960910970480601 := by
  unfold tailWord_5807217
  simp only [CollatzResearch.WordTrace]
  refine ⟨211806604602452077547979905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141204403068301385031986603 211806604602452077547979905)
  ·
    refine ⟨158854953451839058160984929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211806604602452077547979905 158854953451839058160984929)
    ·
      refine ⟨119141215088879293620738697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158854953451839058160984929 119141215088879293620738697)
      ·
        refine ⟨89355911316659470215554023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119141215088879293620738697 89355911316659470215554023)
        ·
          refine ⟨134033866974989205323331035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89355911316659470215554023 134033866974989205323331035)
          ·
            refine ⟨201050800462483807984996553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134033866974989205323331035 201050800462483807984996553)
            ·
              refine ⟨150788100346862855988747415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201050800462483807984996553 150788100346862855988747415)
              ·
                refine ⟨226182150520294283983121123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150788100346862855988747415 226182150520294283983121123)
                ·
                  refine ⟨339273225780441425974681685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226182150520294283983121123 339273225780441425974681685)
                  ·
                    refine ⟨3975858114614547960640801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 339273225780441425974681685 3975858114614547960640801)
                    ·
                      refine ⟨2981893585960910970480601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975858114614547960640801 2981893585960910970480601)
                      ·
                        rfl

theorem cell23_5807217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_5807217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807217 prefixEnd_5807217 := by exact prefixLift 5807217
  have htrace : WordTrace (prefixWord ++ tailWord_5807217) baseStart_5807217 baseEnd_5807217 := by
    simpa [prefixWord, tailWord_5807217, baseEnd_5807217] using wordTrace_append hprefix tailTrace_5807217
  have hstable : (prefixWord ++ tailWord_5807217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807217).length < 2 ^ (prefixWord ++ tailWord_5807217).sum := by decide
  have hdescent : baseEnd_5807217 < baseStart_5807217 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807261 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_5807261 : Nat := 118140960795 + 5807261 * 2 ^ 59
def prefixEnd_5807261 : Nat := 4983230072969 + 3 ^ 40 * 5807261 * 2
def baseEnd_5807261 : Nat := 993972059703236266110133

theorem tailTrace_5807261 : CollatzResearch.WordTrace tailWord_5807261 prefixEnd_5807261 993972059703236266110133 := by
  unfold tailWord_5807261
  simp only [CollatzResearch.WordTrace]
  refine ⟨211808209414292673062581637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141205472942861782041721091 211808209414292673062581637)
  ·
    refine ⟨39714039265179876199234057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211808209414292673062581637 39714039265179876199234057)
    ·
      refine ⟨29785529448884907149425543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39714039265179876199234057 29785529448884907149425543)
      ·
        refine ⟨44678294173327360724138315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29785529448884907149425543 44678294173327360724138315)
        ·
          refine ⟨67017441259991041086207473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44678294173327360724138315 67017441259991041086207473)
          ·
            refine ⟨50263080944993280814655605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67017441259991041086207473 50263080944993280814655605)
            ·
              refine ⟨4712163838593120076373963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50263080944993280814655605 4712163838593120076373963)
              ·
                refine ⟨7068245757889680114560945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712163838593120076373963 7068245757889680114560945)
                ·
                  refine ⟨5301184318417260085920709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068245757889680114560945 5301184318417260085920709)
                  ·
                    refine ⟨993972059703236266110133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301184318417260085920709 993972059703236266110133)
                    ·
                      rfl

theorem cell23_5807261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_5807261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807261 prefixEnd_5807261 := by exact prefixLift 5807261
  have htrace : WordTrace (prefixWord ++ tailWord_5807261) baseStart_5807261 baseEnd_5807261 := by
    simpa [prefixWord, tailWord_5807261, baseEnd_5807261] using wordTrace_append hprefix tailTrace_5807261
  have hstable : (prefixWord ++ tailWord_5807261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807261).length < 2 ^ (prefixWord ++ tailWord_5807261).sum := by decide
  have hdescent : baseEnd_5807261 < baseStart_5807261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807271 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_5807271 : Nat := 118140960795 + 5807271 * 2 ^ 59
def prefixEnd_5807271 : Nat := 4983230072969 + 3 ^ 40 * 5807271 * 2
def baseEnd_5807271 : Nat := 2981921313916253759205353

theorem tailTrace_5807271 : CollatzResearch.WordTrace tailWord_5807271 prefixEnd_5807271 2981921313916253759205353 := by
  unfold tailWord_5807271
  simp only [CollatzResearch.WordTrace]
  refine ⟨211808574144256444770445667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141205716096170963180297111 211808574144256444770445667)
  ·
    refine ⟨317712861216384667155668501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211808574144256444770445667 317712861216384667155668501)
    ·
      refine ⟨14892790369518031272921961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317712861216384667155668501 14892790369518031272921961)
      ·
        refine ⟨11169592777138523454691471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14892790369518031272921961 11169592777138523454691471)
        ·
          refine ⟨16754389165707785182037207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169592777138523454691471 16754389165707785182037207)
          ·
            refine ⟨25131583748561677773055811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16754389165707785182037207 25131583748561677773055811)
            ·
              refine ⟨37697375622842516659583717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25131583748561677773055811 37697375622842516659583717)
              ·
                refine ⟨7068257929282971873671947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37697375622842516659583717 7068257929282971873671947)
                ·
                  refine ⟨10602386893924457810507921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068257929282971873671947 10602386893924457810507921)
                  ·
                    refine ⟨7951790170443343357880941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10602386893924457810507921 7951790170443343357880941)
                    ·
                      refine ⟨2981921313916253759205353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951790170443343357880941 2981921313916253759205353)
                      ·
                        rfl

theorem cell23_5807271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_5807271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807271 prefixEnd_5807271 := by exact prefixLift 5807271
  have htrace : WordTrace (prefixWord ++ tailWord_5807271) baseStart_5807271 baseEnd_5807271 := by
    simpa [prefixWord, tailWord_5807271, baseEnd_5807271] using wordTrace_append hprefix tailTrace_5807271
  have hstable : (prefixWord ++ tailWord_5807271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807271).length < 2 ^ (prefixWord ++ tailWord_5807271).sum := by decide
  have hdescent : baseEnd_5807271 < baseStart_5807271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807274 : List Nat := [3, 1, 5, 1, 1, 2, 1, 9]
def baseStart_5807274 : Nat := 118140960795 + 5807274 * 2 ^ 59
def prefixEnd_5807274 : Nat := 4983230072969 + 3 ^ 40 * 5807274 * 2
def baseEnd_5807274 : Nat := 110441587198452490646957

theorem tailTrace_5807274 : CollatzResearch.WordTrace tailWord_5807274 prefixEnd_5807274 110441587198452490646957 := by
  unfold tailWord_5807274
  simp only [CollatzResearch.WordTrace]
  refine ⟨52952170890811394070701219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141205789042163717521869917 52952170890811394070701219)
  ·
    refine ⟨79428256336217091106051829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52952170890811394070701219 79428256336217091106051829)
    ·
      refine ⟨7446399031520352291192359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79428256336217091106051829 7446399031520352291192359)
      ·
        refine ⟨11169598547280528436788539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446399031520352291192359 11169598547280528436788539)
        ·
          refine ⟨16754397820920792655182809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11169598547280528436788539 16754397820920792655182809)
          ·
            refine ⟨12565798365690594491387107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16754397820920792655182809 12565798365690594491387107)
            ·
              refine ⟨18848697548535891737080661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12565798365690594491387107 18848697548535891737080661)
              ·
                refine ⟨110441587198452490646957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18848697548535891737080661 110441587198452490646957)
                ·
                  rfl

theorem cell23_5807274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_5807274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807274 prefixEnd_5807274 := by exact prefixLift 5807274
  have htrace : WordTrace (prefixWord ++ tailWord_5807274) baseStart_5807274 baseEnd_5807274 := by
    simpa [prefixWord, tailWord_5807274, baseEnd_5807274] using wordTrace_append hprefix tailTrace_5807274
  have hstable : (prefixWord ++ tailWord_5807274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807274).length < 2 ^ (prefixWord ++ tailWord_5807274).sum := by decide
  have hdescent : baseEnd_5807274 < baseStart_5807274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807327 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_5807327 : Nat := 118140960795 + 5807327 * 2 ^ 59
def prefixEnd_5807327 : Nat := 4983230072969 + 3 ^ 40 * 5807327 * 2
def baseEnd_5807327 : Nat := 2981950068832905540105095

theorem tailTrace_5807327 : CollatzResearch.WordTrace tailWord_5807327 prefixEnd_5807327 2981950068832905540105095 := by
  unfold tailWord_5807327
  simp only [CollatzResearch.WordTrace]
  refine ⟨211810616632053566334484235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141207077754702377556322823 211810616632053566334484235)
  ·
    refine ⟨317715924948080349501726353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211810616632053566334484235 317715924948080349501726353)
    ·
      refine ⟨238286943711060262126294765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317715924948080349501726353 238286943711060262126294765)
      ·
        refine ⟨89357603891647598297360537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238286943711060262126294765 89357603891647598297360537)
        ·
          refine ⟨67018202918735698723020403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89357603891647598297360537 67018202918735698723020403)
          ·
            refine ⟨100527304378103548084530605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67018202918735698723020403 100527304378103548084530605)
            ·
              refine ⟨37697739141788830531698977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100527304378103548084530605 37697739141788830531698977)
              ·
                refine ⟨28273304356341622898774233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37697739141788830531698977 28273304356341622898774233)
                ·
                  refine ⟨21204978267256217174080675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28273304356341622898774233 21204978267256217174080675)
                  ·
                    refine ⟨31807467400884325761121013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21204978267256217174080675 31807467400884325761121013)
                    ·
                      refine ⟨2981950068832905540105095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31807467400884325761121013 2981950068832905540105095)
                      ·
                        rfl

theorem cell23_5807327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_5807327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807327 prefixEnd_5807327 := by exact prefixLift 5807327
  have htrace : WordTrace (prefixWord ++ tailWord_5807327) baseStart_5807327 baseEnd_5807327 := by
    simpa [prefixWord, tailWord_5807327, baseEnd_5807327] using wordTrace_append hprefix tailTrace_5807327
  have hstable : (prefixWord ++ tailWord_5807327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807327).length < 2 ^ (prefixWord ++ tailWord_5807327).sum := by decide
  have hdescent : baseEnd_5807327 < baseStart_5807327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807328 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2]
def baseStart_5807328 : Nat := 118140960795 + 5807328 * 2 ^ 59
def prefixEnd_5807328 : Nat := 4983230072969 + 3 ^ 40 * 5807328 * 2
def baseEnd_5807328 : Nat := 2981950582313560036192591

theorem tailTrace_5807328 : CollatzResearch.WordTrace tailWord_5807328 prefixEnd_5807328 2981950582313560036192591 := by
  unfold tailWord_5807328
  simp only [CollatzResearch.WordTrace]
  refine ⟨105905326552524971752635319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141207102070033295670180425 105905326552524971752635319)
  ·
    refine ⟨158857989828787457628952979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105905326552524971752635319 158857989828787457628952979)
    ·
      refine ⟨238286984743181186443429469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158857989828787457628952979 238286984743181186443429469)
      ·
        refine ⟨89357619278692944916286051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238286984743181186443429469 89357619278692944916286051)
        ·
          refine ⟨134036428918039417374429077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89357619278692944916286051 134036428918039417374429077)
          ·
            refine ⟨6282957605533097689426363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134036428918039417374429077 6282957605533097689426363)
            ·
              refine ⟨9424436408299646534139545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6282957605533097689426363 9424436408299646534139545)
              ·
                refine ⟨7068327306224734900604659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9424436408299646534139545 7068327306224734900604659)
                ·
                  refine ⟨10602490959337102350906989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068327306224734900604659 10602490959337102350906989)
                  ·
                    refine ⟨3975934109751413381590121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10602490959337102350906989 3975934109751413381590121)
                    ·
                      refine ⟨2981950582313560036192591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975934109751413381590121 2981950582313560036192591)
                      ·
                        rfl

theorem cell23_5807328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_5807328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807328 prefixEnd_5807328 := by exact prefixLift 5807328
  have htrace : WordTrace (prefixWord ++ tailWord_5807328) baseStart_5807328 baseEnd_5807328 := by
    simpa [prefixWord, tailWord_5807328, baseEnd_5807328] using wordTrace_append hprefix tailTrace_5807328
  have hstable : (prefixWord ++ tailWord_5807328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807328).length < 2 ^ (prefixWord ++ tailWord_5807328).sum := by decide
  have hdescent : baseEnd_5807328 < baseStart_5807328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807341 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_5807341 : Nat := 118140960795 + 5807341 * 2 ^ 59
def prefixEnd_5807341 : Nat := 4983230072969 + 3 ^ 40 * 5807341 * 2
def baseEnd_5807341 : Nat := 2981957257562068485330031

theorem tailTrace_5807341 : CollatzResearch.WordTrace tailWord_5807341 prefixEnd_5807341 2981957257562068485330031 := by
  unfold tailWord_5807341
  simp only [CollatzResearch.WordTrace]
  refine ⟨211811127254002846725493877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141207418169335231150329251 211811127254002846725493877)
  ·
    refine ⟨19857293180062766880515051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211811127254002846725493877 19857293180062766880515051)
    ·
      refine ⟨29785939770094150320772577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857293180062766880515051 29785939770094150320772577)
      ·
        refine ⟨22339454827570612740579433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29785939770094150320772577 22339454827570612740579433)
        ·
          refine ⟨16754591120677959555434575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22339454827570612740579433 16754591120677959555434575)
          ·
            refine ⟨25131886681016939333151863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16754591120677959555434575 25131886681016939333151863)
            ·
              refine ⟨37697830021525408999727795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25131886681016939333151863 37697830021525408999727795)
              ·
                refine ⟨56546745032288113499591693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37697830021525408999727795 56546745032288113499591693)
                ·
                  refine ⟨21205029387108042562346885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56546745032288113499591693 21205029387108042562346885)
                  ·
                    refine ⟨3975943010082757980440041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21205029387108042562346885 3975943010082757980440041)
                    ·
                      refine ⟨2981957257562068485330031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3975943010082757980440041 2981957257562068485330031)
                      ·
                        rfl

theorem cell23_5807341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_5807341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807341 prefixEnd_5807341 := by exact prefixLift 5807341
  have htrace : WordTrace (prefixWord ++ tailWord_5807341) baseStart_5807341 baseEnd_5807341 := by
    simpa [prefixWord, tailWord_5807341, baseEnd_5807341] using wordTrace_append hprefix tailTrace_5807341
  have hstable : (prefixWord ++ tailWord_5807341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807341).length < 2 ^ (prefixWord ++ tailWord_5807341).sum := by decide
  have hdescent : baseEnd_5807341 < baseStart_5807341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807374 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_5807374 : Nat := 118140960795 + 5807374 * 2 ^ 59
def prefixEnd_5807374 : Nat := 4983230072969 + 3 ^ 40 * 5807374 * 2
def baseEnd_5807374 : Nat := 2981974202423666856217379

theorem tailTrace_5807374 : CollatzResearch.WordTrace tailWord_5807374 prefixEnd_5807374 2981974202423666856217379 := by
  unfold tailWord_5807374
  simp only [CollatzResearch.WordTrace]
  refine ⟨26476541357860411670180647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141208220575255528907630117 26476541357860411670180647)
  ·
    refine ⟨39714812036790617505270971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26476541357860411670180647 39714812036790617505270971)
    ·
      refine ⟨59572218055185926257906457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39714812036790617505270971 59572218055185926257906457)
      ·
        refine ⟨44679163541389444693429843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59572218055185926257906457 44679163541389444693429843)
        ·
          refine ⟨67018745312084167040144765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44679163541389444693429843 67018745312084167040144765)
          ·
            refine ⟨25132029492031562640054287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67018745312084167040144765 25132029492031562640054287)
            ·
              refine ⟨37698044238047343960081431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25132029492031562640054287 37698044238047343960081431)
              ·
                refine ⟨56547066357071015940122147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37698044238047343960081431 56547066357071015940122147)
                ·
                  refine ⟨84820599535606523910183221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56547066357071015940122147 84820599535606523910183221)
                  ·
                    refine ⟨7951931206463111616579677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84820599535606523910183221 7951931206463111616579677)
                    ·
                      refine ⟨2981974202423666856217379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7951931206463111616579677 2981974202423666856217379)
                      ·
                        rfl

theorem cell23_5807374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_5807374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807374 prefixEnd_5807374 := by exact prefixLift 5807374
  have htrace : WordTrace (prefixWord ++ tailWord_5807374) baseStart_5807374 baseEnd_5807374 := by
    simpa [prefixWord, tailWord_5807374, baseEnd_5807374] using wordTrace_append hprefix tailTrace_5807374
  have hstable : (prefixWord ++ tailWord_5807374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807374).length < 2 ^ (prefixWord ++ tailWord_5807374).sum := by decide
  have hdescent : baseEnd_5807374 < baseStart_5807374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807377 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 7]
def baseStart_5807377 : Nat := 118140960795 + 5807377 * 2 ^ 59
def prefixEnd_5807377 : Nat := 4983230072969 + 3 ^ 40 * 5807377 * 2
def baseEnd_5807377 : Nat := 993991914288543448159955

theorem tailTrace_5807377 : CollatzResearch.WordTrace tailWord_5807377 prefixEnd_5807377 993991914288543448159955 := by
  unfold tailWord_5807377
  simp only [CollatzResearch.WordTrace]
  refine ⟨211812440281872424873804385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141208293521248283249202923 211812440281872424873804385)
  ·
    refine ⟨158859330211404318655353289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211812440281872424873804385 158859330211404318655353289)
    ·
      refine ⟨119144497658553238991514967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158859330211404318655353289 119144497658553238991514967)
      ·
        refine ⟨178716746487829858487272451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119144497658553238991514967 178716746487829858487272451)
        ·
          refine ⟨268075119731744787730908677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178716746487829858487272451 268075119731744787730908677)
          ·
            refine ⟨50264084949702147699545377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268075119731744787730908677 50264084949702147699545377)
            ·
              refine ⟨37698063712276610774659033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50264084949702147699545377 37698063712276610774659033)
              ·
                refine ⟨28273547784207458080994275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37698063712276610774659033 28273547784207458080994275)
                ·
                  refine ⟨42410321676311187121491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28273547784207458080994275 42410321676311187121491413)
                  ·
                    refine ⟨993991914288543448159955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42410321676311187121491413 993991914288543448159955)
                    ·
                      rfl

theorem cell23_5807377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_5807377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807377 prefixEnd_5807377 := by exact prefixLift 5807377
  have htrace : WordTrace (prefixWord ++ tailWord_5807377) baseStart_5807377 baseEnd_5807377 := by
    simpa [prefixWord, tailWord_5807377, baseEnd_5807377] using wordTrace_append hprefix tailTrace_5807377
  have hstable : (prefixWord ++ tailWord_5807377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807377).length < 2 ^ (prefixWord ++ tailWord_5807377).sum := by decide
  have hdescent : baseEnd_5807377 < baseStart_5807377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807427 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6]
def baseStart_5807427 : Nat := 118140960795 + 5807427 * 2 ^ 59
def prefixEnd_5807427 : Nat := 4983230072969 + 3 ^ 40 * 5807427 * 2
def baseEnd_5807427 : Nat := 2982001416898355148854635

theorem tailTrace_5807427 : CollatzResearch.WordTrace tailWord_5807427 prefixEnd_5807427 2982001416898355148854635 := by
  unfold tailWord_5807427
  simp only [CollatzResearch.WordTrace]
  refine ⟨211814263931691283413124535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141209509287794188942083023 211814263931691283413124535)
  ·
    refine ⟨317721395897536925119686803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211814263931691283413124535 317721395897536925119686803)
    ·
      refine ⟨476582093846305387679530205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317721395897536925119686803 476582093846305387679530205)
      ·
        refine ⟨178718285192364520379823827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476582093846305387679530205 178718285192364520379823827)
        ·
          refine ⟨268077427788546780569735741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178718285192364520379823827 268077427788546780569735741)
          ·
            refine ⟨100529035420705042713650903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268077427788546780569735741 100529035420705042713650903)
            ·
              refine ⟨150793553131057564070476355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100529035420705042713650903 150793553131057564070476355)
              ·
                refine ⟨226190329696586346105714533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150793553131057564070476355 226190329696586346105714533)
                ·
                  refine ⟨42410686818109939894821475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226190329696586346105714533 42410686818109939894821475)
                  ·
                    refine ⟨63616030227164909842232213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42410686818109939894821475 63616030227164909842232213)
                    ·
                      refine ⟨2982001416898355148854635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63616030227164909842232213 2982001416898355148854635)
                      ·
                        rfl

theorem cell23_5807427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_5807427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807427 prefixEnd_5807427 := by exact prefixLift 5807427
  have htrace : WordTrace (prefixWord ++ tailWord_5807427) baseStart_5807427 baseEnd_5807427 := by
    simpa [prefixWord, tailWord_5807427, baseEnd_5807427] using wordTrace_append hprefix tailTrace_5807427
  have hstable : (prefixWord ++ tailWord_5807427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807427).length < 2 ^ (prefixWord ++ tailWord_5807427).sum := by decide
  have hdescent : baseEnd_5807427 < baseStart_5807427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807431 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_5807431 : Nat := 118140960795 + 5807431 * 2 ^ 59
def prefixEnd_5807431 : Nat := 4983230072969 + 3 ^ 40 * 5807431 * 2
def baseEnd_5807431 : Nat := 2982003470820973133204617

theorem tailTrace_5807431 : CollatzResearch.WordTrace tailWord_5807431 prefixEnd_5807431 2982003470820973133204617 := by
  unfold tailWord_5807431
  simp only [CollatzResearch.WordTrace]
  refine ⟨211814409823676792096270147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141209606549117861397513431 211814409823676792096270147)
  ·
    refine ⟨317721614735515188144405221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211814409823676792096270147 317721614735515188144405221)
    ·
      refine ⟨59572802762909097777075979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317721614735515188144405221 59572802762909097777075979)
      ·
        refine ⟨89359204144363646665613969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59572802762909097777075979 89359204144363646665613969)
        ·
          refine ⟨67019403108272734999210477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89359204144363646665613969 67019403108272734999210477)
          ·
            refine ⟨25132276165602275624703929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67019403108272734999210477 25132276165602275624703929)
            ·
              refine ⟨18849207124201706718527947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25132276165602275624703929 18849207124201706718527947)
              ·
                refine ⟨28273810686302560077791921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18849207124201706718527947 28273810686302560077791921)
                ·
                  refine ⟨21205358014726920058343941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28273810686302560077791921 21205358014726920058343941)
                  ·
                    refine ⟨3976004627761297510939489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21205358014726920058343941 3976004627761297510939489)
                    ·
                      refine ⟨2982003470820973133204617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976004627761297510939489 2982003470820973133204617)
                      ·
                        rfl

theorem cell23_5807431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_5807431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807431 prefixEnd_5807431 := by exact prefixLift 5807431
  have htrace : WordTrace (prefixWord ++ tailWord_5807431) baseStart_5807431 baseEnd_5807431 := by
    simpa [prefixWord, tailWord_5807431, baseEnd_5807431] using wordTrace_append hprefix tailTrace_5807431
  have hstable : (prefixWord ++ tailWord_5807431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807431).length < 2 ^ (prefixWord ++ tailWord_5807431).sum := by decide
  have hdescent : baseEnd_5807431 < baseStart_5807431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807444 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5807444 : Nat := 118140960795 + 5807444 * 2 ^ 59
def prefixEnd_5807444 : Nat := 4983230072969 + 3 ^ 40 * 5807444 * 2
def baseEnd_5807444 : Nat := 2982010146069481582342057

theorem tailTrace_5807444 : CollatzResearch.WordTrace tailWord_5807444 prefixEnd_5807444 2982010146069481582342057 := by
  unfold tailWord_5807444
  simp only [CollatzResearch.WordTrace]
  refine ⟨105907441986314847658246693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141209922648419796877662257 105907441986314847658246693)
  ·
    refine ⟨19857645372434033935921255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105907441986314847658246693 19857645372434033935921255)
    ·
      refine ⟨29786468058651050903881883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19857645372434033935921255 29786468058651050903881883)
      ·
        refine ⟨44679702087976576355822825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29786468058651050903881883 44679702087976576355822825)
        ·
          refine ⟨33509776565982432266867119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44679702087976576355822825 33509776565982432266867119)
          ·
            refine ⟨50264664848973648400300679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33509776565982432266867119 50264664848973648400300679)
            ·
              refine ⟨75396997273460472600451019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50264664848973648400300679 75396997273460472600451019)
              ·
                refine ⟨113095495910190708900676529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75396997273460472600451019 113095495910190708900676529)
                ·
                  refine ⟨84821621932643031675507397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113095495910190708900676529 84821621932643031675507397)
                  ·
                    refine ⟨15904054112370568439157637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84821621932643031675507397 15904054112370568439157637)
                    ·
                      refine ⟨2982010146069481582342057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15904054112370568439157637 2982010146069481582342057)
                      ·
                        rfl

theorem cell23_5807444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5807444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807444 prefixEnd_5807444 := by exact prefixLift 5807444
  have htrace : WordTrace (prefixWord ++ tailWord_5807444) baseStart_5807444 baseEnd_5807444 := by
    simpa [prefixWord, tailWord_5807444, baseEnd_5807444] using wordTrace_append hprefix tailTrace_5807444
  have hstable : (prefixWord ++ tailWord_5807444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807444).length < 2 ^ (prefixWord ++ tailWord_5807444).sum := by decide
  have hdescent : baseEnd_5807444 < baseStart_5807444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807484 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_5807484 : Nat := 118140960795 + 5807484 * 2 ^ 59
def prefixEnd_5807484 : Nat := 4983230072969 + 3 ^ 40 * 5807484 * 2
def baseEnd_5807484 : Nat := 994010228431887141947291

theorem tailTrace_5807484 : CollatzResearch.WordTrace tailWord_5807484 prefixEnd_5807484 994010228431887141947291 := by
  unfold tailWord_5807484
  simp only [CollatzResearch.WordTrace]
  refine ⟨105908171446242391073974753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141210895261656521431966337 105908171446242391073974753)
  ·
    refine ⟨79431128584681793305481065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105908171446242391073974753 79431128584681793305481065)
    ·
      refine ⟨59573346438511344979110799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79431128584681793305481065 59573346438511344979110799)
      ·
        refine ⟨89360019657767017468666199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59573346438511344979110799 89360019657767017468666199)
        ·
          refine ⟨134040029486650526202999299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89360019657767017468666199 134040029486650526202999299)
          ·
            refine ⟨201060044229975789304498949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134040029486650526202999299 201060044229975789304498949)
            ·
              refine ⟨37698758293120460494593553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201060044229975789304498949 37698758293120460494593553)
              ·
                refine ⟨28274068719840345370945165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37698758293120460494593553 28274068719840345370945165)
                ·
                  refine ⟨10602775769940129514104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28274068719840345370945165 10602775769940129514104437)
                  ·
                    refine ⟨994010228431887141947291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10602775769940129514104437 994010228431887141947291)
                    ·
                      rfl

theorem cell23_5807484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_5807484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807484 prefixEnd_5807484 := by exact prefixLift 5807484
  have htrace : WordTrace (prefixWord ++ tailWord_5807484) baseStart_5807484 baseEnd_5807484 := by
    simpa [prefixWord, tailWord_5807484, baseEnd_5807484] using wordTrace_append hprefix tailTrace_5807484
  have hstable : (prefixWord ++ tailWord_5807484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807484).length < 2 ^ (prefixWord ++ tailWord_5807484).sum := by decide
  have hdescent : baseEnd_5807484 < baseStart_5807484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807544 : List Nat := [2, 1, 2, 1, 2, 2, 5, 8]
def baseStart_5807544 : Nat := 118140960795 + 5807544 * 2 ^ 59
def prefixEnd_5807544 : Nat := 4983230072969 + 3 ^ 40 * 5807544 * 2
def baseEnd_5807544 : Nat := 110446722004997451521911

theorem tailTrace_5807544 : CollatzResearch.WordTrace tailWord_5807544 prefixEnd_5807544 110446722004997451521911 := by
  unfold tailWord_5807544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105909265636133706197566843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141212354181511608263422457 105909265636133706197566843)
  ·
    refine ⟨158863898454200559296350265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105909265636133706197566843 158863898454200559296350265)
    ·
      refine ⟨119147923840650419472262699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158863898454200559296350265 119147923840650419472262699)
      ·
        refine ⟨178721885760975629208394049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119147923840650419472262699 178721885760975629208394049)
        ·
          refine ⟨134041414320731721906295537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178721885760975629208394049 134041414320731721906295537)
          ·
            refine ⟨100531060740548791429721653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134041414320731721906295537 100531060740548791429721653)
            ·
              refine ⟨9424786944426449196536405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100531060740548791429721653 9424786944426449196536405)
              ·
                refine ⟨110446722004997451521911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9424786944426449196536405 110446722004997451521911)
                ·
                  rfl

theorem cell23_5807544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 8].length) (baseStart_5807544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807544 prefixEnd_5807544 := by exact prefixLift 5807544
  have htrace : WordTrace (prefixWord ++ tailWord_5807544) baseStart_5807544 baseEnd_5807544 := by
    simpa [prefixWord, tailWord_5807544, baseEnd_5807544] using wordTrace_append hprefix tailTrace_5807544
  have hstable : (prefixWord ++ tailWord_5807544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807544).length < 2 ^ (prefixWord ++ tailWord_5807544).sum := by decide
  have hdescent : baseEnd_5807544 < baseStart_5807544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807548 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_5807548 : Nat := 118140960795 + 5807548 * 2 ^ 59
def prefixEnd_5807548 : Nat := 4983230072969 + 3 ^ 40 * 5807548 * 2
def baseEnd_5807548 : Nat := 994021182685849725147193

theorem tailTrace_5807548 : CollatzResearch.WordTrace tailWord_5807548 prefixEnd_5807548 994021182685849725147193 := by
  unfold tailWord_5807548
  simp only [CollatzResearch.WordTrace]
  refine ⟨105909338582126460539139649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141212451442835280718852865 105909338582126460539139649)
  ·
    refine ⟨79432003936594845404354737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105909338582126460539139649 79432003936594845404354737)
    ·
      refine ⟨59574002952446134053266053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79432003936594845404354737 59574002952446134053266053)
      ·
        refine ⟨11170125553583650134987385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59574002952446134053266053 11170125553583650134987385)
        ·
          refine ⟨8377594165187737601240539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11170125553583650134987385 8377594165187737601240539)
          ·
            refine ⟨12566391247781606401860809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8377594165187737601240539 12566391247781606401860809)
            ·
              refine ⟨9424793435836204801395607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12566391247781606401860809 9424793435836204801395607)
              ·
                refine ⟨14137190153754307202093411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9424793435836204801395607 14137190153754307202093411)
                ·
                  refine ⟨21205785230631460803140117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14137190153754307202093411 21205785230631460803140117)
                  ·
                    refine ⟨994021182685849725147193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21205785230631460803140117 994021182685849725147193)
                    ·
                      rfl

theorem cell23_5807548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_5807548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807548 prefixEnd_5807548 := by exact prefixLift 5807548
  have htrace : WordTrace (prefixWord ++ tailWord_5807548) baseStart_5807548 baseEnd_5807548 := by
    simpa [prefixWord, tailWord_5807548, baseEnd_5807548] using wordTrace_append hprefix tailTrace_5807548
  have hstable : (prefixWord ++ tailWord_5807548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807548).length < 2 ^ (prefixWord ++ tailWord_5807548).sum := by decide
  have hdescent : baseEnd_5807548 < baseStart_5807548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807572 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5807572 : Nat := 118140960795 + 5807572 * 2 ^ 59
def prefixEnd_5807572 : Nat := 4983230072969 + 3 ^ 40 * 5807572 * 2
def baseEnd_5807572 : Nat := 2982075871593257081541469

theorem tailTrace_5807572 : CollatzResearch.WordTrace tailWord_5807572 prefixEnd_5807572 2982075871593257081541469 := by
  unfold tailWord_5807572
  simp only [CollatzResearch.WordTrace]
  refine ⟨105909776258082986588576485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141213035010777315451435313 105909776258082986588576485)
  ·
    refine ⟨19858083048390559985358091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105909776258082986588576485 19858083048390559985358091)
    ·
      refine ⟨29787124572585839978037137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19858083048390559985358091 29787124572585839978037137)
      ·
        refine ⟨22340343429439379983527853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29787124572585839978037137 22340343429439379983527853)
        ·
          refine ⟨8377628786039767493822945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22340343429439379983527853 8377628786039767493822945)
          ·
            refine ⟨6283221589529825620367209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8377628786039767493822945 6283221589529825620367209)
            ·
              refine ⟨4712416192147369215275407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283221589529825620367209 4712416192147369215275407)
              ·
                refine ⟨7068624288221053822913111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712416192147369215275407 7068624288221053822913111)
                ·
                  refine ⟨10602936432331580734369667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7068624288221053822913111 10602936432331580734369667)
                  ·
                    refine ⟨15904404648497371101554501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10602936432331580734369667 15904404648497371101554501)
                    ·
                      refine ⟨2982075871593257081541469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15904404648497371101554501 2982075871593257081541469)
                      ·
                        rfl

theorem cell23_5807572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5807572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807572 prefixEnd_5807572 := by exact prefixLift 5807572
  have htrace : WordTrace (prefixWord ++ tailWord_5807572) baseStart_5807572 baseEnd_5807572 := by
    simpa [prefixWord, tailWord_5807572, baseEnd_5807572] using wordTrace_append hprefix tailTrace_5807572
  have hstable : (prefixWord ++ tailWord_5807572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807572).length < 2 ^ (prefixWord ++ tailWord_5807572).sum := by decide
  have hdescent : baseEnd_5807572 < baseStart_5807572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807584 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_5807584 : Nat := 118140960795 + 5807584 * 2 ^ 59
def prefixEnd_5807584 : Nat := 4983230072969 + 3 ^ 40 * 5807584 * 2
def baseEnd_5807584 : Nat := 2982082033361111034591413

theorem tailTrace_5807584 : CollatzResearch.WordTrace tailWord_5807584 prefixEnd_5807584 2982082033361111034591413 := by
  unfold tailWord_5807584
  simp only [CollatzResearch.WordTrace]
  refine ⟨105909995096061249613294903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141213326794748332817726537 105909995096061249613294903)
  ·
    refine ⟨158864992644091874419942355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105909995096061249613294903 158864992644091874419942355)
    ·
      refine ⟨238297488966137811629913533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158864992644091874419942355 238297488966137811629913533)
      ·
        refine ⟨89361558362301679361217575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238297488966137811629913533 89361558362301679361217575)
        ·
          refine ⟨134042337543452519041826363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89361558362301679361217575 134042337543452519041826363)
          ·
            refine ⟨201063506315178778562739545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134042337543452519041826363 201063506315178778562739545)
            ·
              refine ⟨150797629736384083922054659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201063506315178778562739545 150797629736384083922054659)
              ·
                refine ⟨226196444604576125883081989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150797629736384083922054659 226196444604576125883081989)
                ·
                  refine ⟨42411833363358023603077873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226196444604576125883081989 42411833363358023603077873)
                  ·
                    refine ⟨31808875022518517702308405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42411833363358023603077873 31808875022518517702308405)
                    ·
                      refine ⟨2982082033361111034591413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31808875022518517702308405 2982082033361111034591413)
                      ·
                        rfl

theorem cell23_5807584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_5807584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807584 prefixEnd_5807584 := by exact prefixLift 5807584
  have htrace : WordTrace (prefixWord ++ tailWord_5807584) baseStart_5807584 baseEnd_5807584 := by
    simpa [prefixWord, tailWord_5807584, baseEnd_5807584] using wordTrace_append hprefix tailTrace_5807584
  have hstable : (prefixWord ++ tailWord_5807584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807584).length < 2 ^ (prefixWord ++ tailWord_5807584).sum := by decide
  have hdescent : baseEnd_5807584 < baseStart_5807584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807605 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5807605 : Nat := 118140960795 + 5807605 * 2 ^ 59
def prefixEnd_5807605 : Nat := 4983230072969 + 3 ^ 40 * 5807605 * 2
def baseEnd_5807605 : Nat := 2982092816454855452428817

theorem tailTrace_5807605 : CollatzResearch.WordTrace tailWord_5807605 prefixEnd_5807605 2982092816454855452428817 := by
  unfold tailWord_5807605
  simp only [CollatzResearch.WordTrace]
  refine ⟨211820756125046419813104269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141213837416697613208736179 211820756125046419813104269)
  ·
    refine ⟨79432783546892407429914101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211820756125046419813104269 79432783546892407429914101)
    ·
      refine ⟨7446823457521163196554447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79432783546892407429914101 7446823457521163196554447)
      ·
        refine ⟨11170235186281744794831671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7446823457521163196554447 11170235186281744794831671)
        ·
          refine ⟨16755352779422617192247507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170235186281744794831671 16755352779422617192247507)
          ·
            refine ⟨25133029169133925788371261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755352779422617192247507 25133029169133925788371261)
            ·
              refine ⟨9424885938425222170639223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25133029169133925788371261 9424885938425222170639223)
              ·
                refine ⟨14137328907637833255958835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9424885938425222170639223 14137328907637833255958835)
                ·
                  refine ⟨21205993361456749883938253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14137328907637833255958835 21205993361456749883938253)
                  ·
                    refine ⟨7952247510546281206476845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21205993361456749883938253 7952247510546281206476845)
                    ·
                      refine ⟨2982092816454855452428817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952247510546281206476845 2982092816454855452428817)
                      ·
                        rfl

theorem cell23_5807605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5807605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807605 prefixEnd_5807605 := by exact prefixLift 5807605
  have htrace : WordTrace (prefixWord ++ tailWord_5807605) baseStart_5807605 baseEnd_5807605 := by
    simpa [prefixWord, tailWord_5807605, baseEnd_5807605] using wordTrace_append hprefix tailTrace_5807605
  have hstable : (prefixWord ++ tailWord_5807605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807605).length < 2 ^ (prefixWord ++ tailWord_5807605).sum := by decide
  have hdescent : baseEnd_5807605 < baseStart_5807605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807618 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_5807618 : Nat := 118140960795 + 5807618 * 2 ^ 59
def prefixEnd_5807618 : Nat := 4983230072969 + 3 ^ 40 * 5807618 * 2
def baseEnd_5807618 : Nat := 2982099491703363901566257

theorem tailTrace_5807618 : CollatzResearch.WordTrace tailWord_5807618 prefixEnd_5807618 2982099491703363901566257 := by
  unfold tailWord_5807618
  simp only [CollatzResearch.WordTrace]
  refine ⟨52955307568499830758331877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141214153515999548688885005 52955307568499830758331877)
  ·
    refine ⟨9929120169093718267187227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52955307568499830758331877 9929120169093718267187227)
    ·
      refine ⟨14893680253640577400780841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9929120169093718267187227 14893680253640577400780841)
      ·
        refine ⟨11170260190230433050585631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14893680253640577400780841 11170260190230433050585631)
        ·
          refine ⟨16755390285345649575878447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170260190230433050585631 16755390285345649575878447)
          ·
            refine ⟨25133085428018474363817671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755390285345649575878447 25133085428018474363817671)
            ·
              refine ⟨37699628142027711545726507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25133085428018474363817671 37699628142027711545726507)
              ·
                refine ⟨56549442213041567318589761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37699628142027711545726507 56549442213041567318589761)
                ·
                  refine ⟨42412081659781175488942321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56549442213041567318589761 42412081659781175488942321)
                  ·
                    refine ⟨31809061244835881616706741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42412081659781175488942321 31809061244835881616706741)
                    ·
                      refine ⟨2982099491703363901566257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31809061244835881616706741 2982099491703363901566257)
                      ·
                        rfl

theorem cell23_5807618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_5807618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807618 prefixEnd_5807618 := by exact prefixLift 5807618
  have htrace : WordTrace (prefixWord ++ tailWord_5807618) baseStart_5807618 baseEnd_5807618 := by
    simpa [prefixWord, tailWord_5807618, baseEnd_5807618] using wordTrace_append hprefix tailTrace_5807618
  have hstable : (prefixWord ++ tailWord_5807618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807618).length < 2 ^ (prefixWord ++ tailWord_5807618).sum := by decide
  have hdescent : baseEnd_5807618 < baseStart_5807618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807645 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_5807645 : Nat := 118140960795 + 5807645 * 2 ^ 59
def prefixEnd_5807645 : Nat := 4983230072969 + 3 ^ 40 * 5807645 * 2
def baseEnd_5807645 : Nat := 2982113355681035295928633

theorem tailTrace_5807645 : CollatzResearch.WordTrace tailWord_5807645 prefixEnd_5807645 2982113355681035295928633 := by
  unfold tailWord_5807645
  simp only [CollatzResearch.WordTrace]
  refine ⟨211822215044901506644560389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141214810029934337763040259 211822215044901506644560389)
  ·
    refine ⟨39716665320919032495855073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211822215044901506644560389 39716665320919032495855073)
    ·
      refine ⟨29787498990689274371891305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39716665320919032495855073 29787498990689274371891305)
      ·
        refine ⟨22340624243016955778918479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29787498990689274371891305 22340624243016955778918479)
        ·
          refine ⟨33510936364525433668377719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22340624243016955778918479 33510936364525433668377719)
          ·
            refine ⟨50266404546788150502566579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33510936364525433668377719 50266404546788150502566579)
            ·
              refine ⟨75399606820182225753849869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50266404546788150502566579 75399606820182225753849869)
              ·
                refine ⟨28274852557568334657693701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75399606820182225753849869 28274852557568334657693701)
                ·
                  refine ⟨5301534854544062748317569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28274852557568334657693701 5301534854544062748317569)
                  ·
                    refine ⟨3976151140908047061238177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301534854544062748317569 3976151140908047061238177)
                    ·
                      refine ⟨2982113355681035295928633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976151140908047061238177 2982113355681035295928633)
                      ·
                        rfl

theorem cell23_5807645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_5807645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807645 prefixEnd_5807645 := by exact prefixLift 5807645
  have htrace : WordTrace (prefixWord ++ tailWord_5807645) baseStart_5807645 baseEnd_5807645 := by
    simpa [prefixWord, tailWord_5807645, baseEnd_5807645] using wordTrace_append hprefix tailTrace_5807645
  have hstable : (prefixWord ++ tailWord_5807645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807645).length < 2 ^ (prefixWord ++ tailWord_5807645).sum := by decide
  have hdescent : baseEnd_5807645 < baseStart_5807645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807656 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5807656 : Nat := 118140960795 + 5807656 * 2 ^ 59
def prefixEnd_5807656 : Nat := 4983230072969 + 3 ^ 40 * 5807656 * 2
def baseEnd_5807656 : Nat := 2982119003968234752891083

theorem tailTrace_5807656 : CollatzResearch.WordTrace tailWord_5807656 prefixEnd_5807656 2982119003968234752891083 := by
  unfold tailWord_5807656
  simp only [CollatzResearch.WordTrace]
  refine ⟨105911308123930827761605411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141215077498574437015473881 105911308123930827761605411)
  ·
    refine ⟨158866962185896241642408117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105911308123930827761605411 158866962185896241642408117)
    ·
      refine ⟨14893777704927772653975761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158866962185896241642408117 14893777704927772653975761)
      ·
        refine ⟨11170333278695829490481821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14893777704927772653975761 11170333278695829490481821)
        ·
          refine ⟨4188874979510936058930683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11170333278695829490481821 4188874979510936058930683)
          ·
            refine ⟨6283312469266404088396025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4188874979510936058930683 6283312469266404088396025)
            ·
              refine ⟨4712484351949803066297019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283312469266404088396025 4712484351949803066297019)
              ·
                refine ⟨7068726527924704599445529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712484351949803066297019 7068726527924704599445529)
                ·
                  refine ⟨5301544895943528449584147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7068726527924704599445529 5301544895943528449584147)
                  ·
                    refine ⟨7952317343915292674376221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301544895943528449584147 7952317343915292674376221)
                    ·
                      refine ⟨2982119003968234752891083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952317343915292674376221 2982119003968234752891083)
                      ·
                        rfl

theorem cell23_5807656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5807656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807656 prefixEnd_5807656 := by exact prefixLift 5807656
  have htrace : WordTrace (prefixWord ++ tailWord_5807656) baseStart_5807656 baseEnd_5807656 := by
    simpa [prefixWord, tailWord_5807656, baseEnd_5807656] using wordTrace_append hprefix tailTrace_5807656
  have hstable : (prefixWord ++ tailWord_5807656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807656).length < 2 ^ (prefixWord ++ tailWord_5807656).sum := by decide
  have hdescent : baseEnd_5807656 < baseStart_5807656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807698 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_5807698 : Nat := 118140960795 + 5807698 * 2 ^ 59
def prefixEnd_5807698 : Nat := 4983230072969 + 3 ^ 40 * 5807698 * 2
def baseEnd_5807698 : Nat := 994046856718574529521963

theorem tailTrace_5807698 : CollatzResearch.WordTrace tailWord_5807698 prefixEnd_5807698 994046856718574529521963 := by
  unfold tailWord_5807698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956037028427374174059937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141216098742472997797493165 52956037028427374174059937)
  ·
    refine ⟨39717027771320530630544953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52956037028427374174059937 39717027771320530630544953)
    ·
      refine ⟨29787770828490397972908715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39717027771320530630544953 29787770828490397972908715)
      ·
        refine ⟨44681656242735596959363073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29787770828490397972908715 44681656242735596959363073)
        ·
          refine ⟨33511242182051697719522305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44681656242735596959363073 33511242182051697719522305)
          ·
            refine ⟨25133431636538773289641729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33511242182051697719522305 25133431636538773289641729)
            ·
              refine ⟨18850073727404079967231297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25133431636538773289641729 18850073727404079967231297)
              ·
                refine ⟨14137555295553059975423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18850073727404079967231297 14137555295553059975423473)
                ·
                  refine ⟨10603166471664794981567605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14137555295553059975423473 10603166471664794981567605)
                  ·
                    refine ⟨994046856718574529521963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10603166471664794981567605 994046856718574529521963)
                    ·
                      rfl

theorem cell23_5807698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_5807698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807698 prefixEnd_5807698 := by exact prefixLift 5807698
  have htrace : WordTrace (prefixWord ++ tailWord_5807698) baseStart_5807698 baseEnd_5807698 := by
    simpa [prefixWord, tailWord_5807698, baseEnd_5807698] using wordTrace_append hprefix tailTrace_5807698
  have hstable : (prefixWord ++ tailWord_5807698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807698).length < 2 ^ (prefixWord ++ tailWord_5807698).sum := by decide
  have hdescent : baseEnd_5807698 < baseStart_5807698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807701 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5807701 : Nat := 118140960795 + 5807701 * 2 ^ 59
def prefixEnd_5807701 : Nat := 4983230072969 + 3 ^ 40 * 5807701 * 2
def baseEnd_5807701 : Nat := 2982142110597687076828375

theorem tailTrace_5807701 : CollatzResearch.WordTrace tailWord_5807701 prefixEnd_5807701 2982142110597687076828375 := by
  unfold tailWord_5807701
  simp only [CollatzResearch.WordTrace]
  refine ⟨211824257532698628208598957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141216171688465752139065971 211824257532698628208598957)
  ·
    refine ⟨79434096574761985578224609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211824257532698628208598957 79434096574761985578224609)
    ·
      refine ⟨59575572431071489183668457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79434096574761985578224609 59575572431071489183668457)
      ·
        refine ⟨44681679323303616887751343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59575572431071489183668457 44681679323303616887751343)
        ·
          refine ⟨67022518984955425331627015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44681679323303616887751343 67022518984955425331627015)
          ·
            refine ⟨100533778477433137997440523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67022518984955425331627015 100533778477433137997440523)
            ·
              refine ⟨150800667716149706996160785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100533778477433137997440523 150800667716149706996160785)
              ·
                refine ⟨113100500787112280247120589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150800667716149706996160785 113100500787112280247120589)
                ·
                  refine ⟨42412687795167105092670221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113100500787112280247120589 42412687795167105092670221)
                  ·
                    refine ⟨15904757923187664409751333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42412687795167105092670221 15904757923187664409751333)
                    ·
                      refine ⟨2982142110597687076828375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15904757923187664409751333 2982142110597687076828375)
                      ·
                        rfl

theorem cell23_5807701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5807701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807701 prefixEnd_5807701 := by exact prefixLift 5807701
  have htrace : WordTrace (prefixWord ++ tailWord_5807701) baseStart_5807701 baseEnd_5807701 := by
    simpa [prefixWord, tailWord_5807701, baseEnd_5807701] using wordTrace_append hprefix tailTrace_5807701
  have hstable : (prefixWord ++ tailWord_5807701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807701).length < 2 ^ (prefixWord ++ tailWord_5807701).sum := by decide
  have hdescent : baseEnd_5807701 < baseStart_5807701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807708 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5807708 : Nat := 118140960795 + 5807708 * 2 ^ 59
def prefixEnd_5807708 : Nat := 4983230072969 + 3 ^ 40 * 5807708 * 2
def baseEnd_5807708 : Nat := 2982145704962268549440843

theorem tailTrace_5807708 : CollatzResearch.WordTrace tailWord_5807708 prefixEnd_5807708 2982145704962268549440843 := by
  unfold tailWord_5807708
  simp only [CollatzResearch.WordTrace]
  refine ⟨105912256421836634202051889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141216341895782178936069185 105912256421836634202051889)
  ·
    refine ⟨79434192316377475651538917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105912256421836634202051889 79434192316377475651538917)
    ·
      refine ⟨14893911059320776684663547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79434192316377475651538917 14893911059320776684663547)
      ·
        refine ⟨22340866588981165026995321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14893911059320776684663547 22340866588981165026995321)
        ·
          refine ⟨16755649941735873770246491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22340866588981165026995321 16755649941735873770246491)
          ·
            refine ⟨25133474912603810655369737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755649941735873770246491 25133474912603810655369737)
            ·
              refine ⟨18850106184452857991527303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25133474912603810655369737 18850106184452857991527303)
              ·
                refine ⟨28275159276679286987290955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18850106184452857991527303 28275159276679286987290955)
                ·
                  refine ⟨42412738915018930480936433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28275159276679286987290955 42412738915018930480936433)
                  ·
                    refine ⟨31809554186264197860702325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42412738915018930480936433 31809554186264197860702325)
                    ·
                      refine ⟨2982145704962268549440843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31809554186264197860702325 2982145704962268549440843)
                      ·
                        rfl

theorem cell23_5807708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5807708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807708 prefixEnd_5807708 := by exact prefixLift 5807708
  have htrace : WordTrace (prefixWord ++ tailWord_5807708) baseStart_5807708 baseEnd_5807708 := by
    simpa [prefixWord, tailWord_5807708, baseEnd_5807708] using wordTrace_append hprefix tailTrace_5807708
  have hstable : (prefixWord ++ tailWord_5807708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807708).length < 2 ^ (prefixWord ++ tailWord_5807708).sum := by decide
  have hdescent : baseEnd_5807708 < baseStart_5807708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807728 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_5807728 : Nat := 118140960795 + 5807728 * 2 ^ 59
def prefixEnd_5807728 : Nat := 4983230072969 + 3 ^ 40 * 5807728 * 2
def baseEnd_5807728 : Nat := 994051991525119490396917

theorem tailTrace_5807728 : CollatzResearch.WordTrace tailWord_5807728 prefixEnd_5807728 994051991525119490396917 := by
  unfold tailWord_5807728
  simp only [CollatzResearch.WordTrace]
  refine ⟨105912621151800405909915919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141216828202400541213221225 105912621151800405909915919)
  ·
    refine ⟨158868931727700608864873879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105912621151800405909915919 158868931727700608864873879)
    ·
      refine ⟨238303397591550913297310819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158868931727700608864873879 238303397591550913297310819)
      ·
        refine ⟨357455096387326369945966229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238303397591550913297310819 357455096387326369945966229)
        ·
          refine ⟨16755707643155923591217167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 357455096387326369945966229 16755707643155923591217167)
          ·
            refine ⟨25133561464733885386825751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16755707643155923591217167 25133561464733885386825751)
            ·
              refine ⟨37700342197100828080238627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25133561464733885386825751 37700342197100828080238627)
              ·
                refine ⟨56550513295651242120357941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37700342197100828080238627 56550513295651242120357941)
                ·
                  refine ⟨5301610621467303948783557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56550513295651242120357941 5301610621467303948783557)
                  ·
                    refine ⟨994051991525119490396917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301610621467303948783557 994051991525119490396917)
                    ·
                      rfl

theorem cell23_5807728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_5807728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807728 prefixEnd_5807728 := by exact prefixLift 5807728
  have htrace : WordTrace (prefixWord ++ tailWord_5807728) baseStart_5807728 baseEnd_5807728 := by
    simpa [prefixWord, tailWord_5807728, baseEnd_5807728] using wordTrace_append hprefix tailTrace_5807728
  have hstable : (prefixWord ++ tailWord_5807728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807728).length < 2 ^ (prefixWord ++ tailWord_5807728).sum := by decide
  have hdescent : baseEnd_5807728 < baseStart_5807728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807738 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3]
def baseStart_5807738 : Nat := 118140960795 + 5807738 * 2 ^ 59
def prefixEnd_5807738 : Nat := 4983230072969 + 3 ^ 40 * 5807738 * 2
def baseEnd_5807738 : Nat := 2982161109381903432065705

theorem tailTrace_5807738 : CollatzResearch.WordTrace tailWord_5807738 prefixEnd_5807738 2982161109381903432065705 := by
  unfold tailWord_5807738
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956401758391145881923967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141217071355709722351797245 52956401758391145881923967)
  ·
    refine ⟨79434602637586718822885951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52956401758391145881923967 79434602637586718822885951)
    ·
      refine ⟨119151903956380078234328927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79434602637586718822885951 119151903956380078234328927)
      ·
        refine ⟨178727855934570117351493391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119151903956380078234328927 178727855934570117351493391)
        ·
          refine ⟨268091783901855176027240087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178727855934570117351493391 268091783901855176027240087)
          ·
            refine ⟨402137675852782764040860131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268091783901855176027240087 402137675852782764040860131)
            ·
              refine ⟨603206513779174146061290197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402137675852782764040860131 603206513779174146061290197)
              ·
                refine ⟨14137652666699394048311489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 603206513779174146061290197 14137652666699394048311489)
                ·
                  refine ⟨10603239500024545536233617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14137652666699394048311489 10603239500024545536233617)
                  ·
                    refine ⟨7952429625018409152175213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10603239500024545536233617 7952429625018409152175213)
                    ·
                      refine ⟨2982161109381903432065705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952429625018409152175213 2982161109381903432065705)
                      ·
                        rfl

theorem cell23_5807738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_5807738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807738 prefixEnd_5807738 := by exact prefixLift 5807738
  have htrace : WordTrace (prefixWord ++ tailWord_5807738) baseStart_5807738 baseEnd_5807738 := by
    simpa [prefixWord, tailWord_5807738, baseEnd_5807738] using wordTrace_append hprefix tailTrace_5807738
  have hstable : (prefixWord ++ tailWord_5807738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807738).length < 2 ^ (prefixWord ++ tailWord_5807738).sum := by decide
  have hdescent : baseEnd_5807738 < baseStart_5807738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807758 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_5807758 : Nat := 118140960795 + 5807758 * 2 ^ 59
def prefixEnd_5807758 : Nat := 4983230072969 + 3 ^ 40 * 5807758 * 2
def baseEnd_5807758 : Nat := 331352375443888150423957

theorem tailTrace_5807758 : CollatzResearch.WordTrace tailWord_5807758 prefixEnd_5807758 331352375443888150423957 := by
  unfold tailWord_5807758
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478292061686515867927991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141217557662328084628949285 26478292061686515867927991)
  ·
    refine ⟨39717438092529773801891987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478292061686515867927991 39717438092529773801891987)
    ·
      refine ⟨59576157138794660702837981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39717438092529773801891987 59576157138794660702837981)
      ·
        refine ⟨22341058927047997763564243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59576157138794660702837981 22341058927047997763564243)
        ·
          refine ⟨33511588390571996645346365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341058927047997763564243 33511588390571996645346365)
          ·
            refine ⟨12566845646464498742004887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33511588390571996645346365 12566845646464498742004887)
            ·
              refine ⟨18850268469696748113007331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12566845646464498742004887 18850268469696748113007331)
              ·
                refine ⟨28275402704545122169510997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18850268469696748113007331 28275402704545122169510997)
                ·
                  refine ⟨331352375443888150423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28275402704545122169510997 331352375443888150423957)
                  ·
                    rfl

theorem cell23_5807758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_5807758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807758 prefixEnd_5807758 := by exact prefixLift 5807758
  have htrace : WordTrace (prefixWord ++ tailWord_5807758) baseStart_5807758 baseEnd_5807758 := by
    simpa [prefixWord, tailWord_5807758, baseEnd_5807758] using wordTrace_append hprefix tailTrace_5807758
  have hstable : (prefixWord ++ tailWord_5807758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807758).length < 2 ^ (prefixWord ++ tailWord_5807758).sum := by decide
  have hdescent : baseEnd_5807758 < baseStart_5807758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807762 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_5807762 : Nat := 118140960795 + 5807762 * 2 ^ 59
def prefixEnd_5807762 : Nat := 4983230072969 + 3 ^ 40 * 5807762 * 2
def baseEnd_5807762 : Nat := 994057810972537112721865

theorem tailTrace_5807762 : CollatzResearch.WordTrace tailWord_5807762 prefixEnd_5807762 994057810972537112721865 := by
  unfold tailWord_5807762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52956620596369408906642385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141217654923651757084379693 52956620596369408906642385)
  ·
    refine ⟨39717465447277056679981789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52956620596369408906642385 39717465447277056679981789)
    ·
      refine ⟨14894049542728896254993171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39717465447277056679981789 14894049542728896254993171)
      ·
        refine ⟨22341074314093344382489757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894049542728896254993171 22341074314093344382489757)
        ·
          refine ⟨8377902867785004143433659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22341074314093344382489757 8377902867785004143433659)
          ·
            refine ⟨12566854301677506215150489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8377902867785004143433659 12566854301677506215150489)
            ·
              refine ⟨9425140726258129661362867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12566854301677506215150489 9425140726258129661362867)
              ·
                refine ⟨14137711089387194492044301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425140726258129661362867 14137711089387194492044301)
                ·
                  refine ⟨5301641658520197934516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14137711089387194492044301 5301641658520197934516613)
                  ·
                    refine ⟨994057810972537112721865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301641658520197934516613 994057810972537112721865)
                    ·
                      rfl

theorem cell23_5807762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_5807762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807762 prefixEnd_5807762 := by exact prefixLift 5807762
  have htrace : WordTrace (prefixWord ++ tailWord_5807762) baseStart_5807762 baseEnd_5807762 := by
    simpa [prefixWord, tailWord_5807762, baseEnd_5807762] using wordTrace_append hprefix tailTrace_5807762
  have hstable : (prefixWord ++ tailWord_5807762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807762).length < 2 ^ (prefixWord ++ tailWord_5807762).sum := by decide
  have hdescent : baseEnd_5807762 < baseStart_5807762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807781 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_5807781 : Nat := 118140960795 + 5807781 * 2 ^ 59
def prefixEnd_5807781 : Nat := 4983230072969 + 3 ^ 40 * 5807781 * 2
def baseEnd_5807781 : Nat := 2982183189050046763828007

theorem tailTrace_5807781 : CollatzResearch.WordTrace tailWord_5807781 prefixEnd_5807781 2982183189050046763828007 := by
  unfold tailWord_5807781
  simp only [CollatzResearch.WordTrace]
  refine ⟨211827175372408801871511197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141218116914939201247674131 211827175372408801871511197)
  ·
    refine ⟨79435190764653300701816699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211827175372408801871511197 79435190764653300701816699)
    ·
      refine ⟨119152786146979951052725049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79435190764653300701816699 119152786146979951052725049)
      ·
        refine ⟨89364589610234963289543787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119152786146979951052725049 89364589610234963289543787)
        ·
          refine ⟨134046884415352444934315681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89364589610234963289543787 134046884415352444934315681)
          ·
            refine ⟨100535163311514333700736761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134046884415352444934315681 100535163311514333700736761)
            ·
              refine ⟨75401372483635750275552571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100535163311514333700736761 75401372483635750275552571)
              ·
                refine ⟨113102058725453625413328857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75401372483635750275552571 113102058725453625413328857)
                ·
                  refine ⟨84826544044090219059996643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113102058725453625413328857 84826544044090219059996643)
                  ·
                    refine ⟨127239816066135328589994965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84826544044090219059996643 127239816066135328589994965)
                    ·
                      refine ⟨2982183189050046763828007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127239816066135328589994965 2982183189050046763828007)
                      ·
                        rfl

theorem cell23_5807781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_5807781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807781 prefixEnd_5807781 := by exact prefixLift 5807781
  have htrace : WordTrace (prefixWord ++ tailWord_5807781) baseStart_5807781 baseEnd_5807781 := by
    simpa [prefixWord, tailWord_5807781, baseEnd_5807781] using wordTrace_append hprefix tailTrace_5807781
  have hstable : (prefixWord ++ tailWord_5807781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807781).length < 2 ^ (prefixWord ++ tailWord_5807781).sum := by decide
  have hdescent : baseEnd_5807781 < baseStart_5807781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807795 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 2, 3, 2]
def baseStart_5807795 : Nat := 118140960795 + 5807795 * 2 ^ 59
def prefixEnd_5807795 : Nat := 4983230072969 + 3 ^ 40 * 5807795 * 2
def baseEnd_5807795 : Nat := 2982190377779209709052943

theorem tailTrace_5807795 : CollatzResearch.WordTrace tailWord_5807795 prefixEnd_5807795 2982190377779209709052943 := by
  unfold tailWord_5807795
  simp only [CollatzResearch.WordTrace]
  refine ⟨211827685994358082262520839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141218457329572054841680559 211827685994358082262520839)
  ·
    refine ⟨317741528991537123393781259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211827685994358082262520839 317741528991537123393781259)
    ·
      refine ⟨476612293487305685090671889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317741528991537123393781259 476612293487305685090671889)
      ·
        refine ⟨357459220115479263818003917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476612293487305685090671889 357459220115479263818003917)
        ·
          refine ⟨134047207543304723931751469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357459220115479263818003917 134047207543304723931751469)
          ·
            refine ⟨50267702828739271474406801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134047207543304723931751469 50267702828739271474406801)
            ·
              refine ⟨37700777121554453605805101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50267702828739271474406801 37700777121554453605805101)
              ·
                refine ⟨14137791420582920102176913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37700777121554453605805101 14137791420582920102176913)
                ·
                  refine ⟨10603343565437190076632685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14137791420582920102176913 10603343565437190076632685)
                  ·
                    refine ⟨3976253837038946278737257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10603343565437190076632685 3976253837038946278737257)
                    ·
                      refine ⟨2982190377779209709052943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976253837038946278737257 2982190377779209709052943)
                      ·
                        rfl

theorem cell23_5807795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3, 2].length) (baseStart_5807795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807795 prefixEnd_5807795 := by exact prefixLift 5807795
  have htrace : WordTrace (prefixWord ++ tailWord_5807795) baseStart_5807795 baseEnd_5807795 := by
    simpa [prefixWord, tailWord_5807795, baseEnd_5807795] using wordTrace_append hprefix tailTrace_5807795
  have hstable : (prefixWord ++ tailWord_5807795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807795).length < 2 ^ (prefixWord ++ tailWord_5807795).sum := by decide
  have hdescent : baseEnd_5807795 < baseStart_5807795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807812 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_5807812 : Nat := 118140960795 + 5807812 * 2 ^ 59
def prefixEnd_5807812 : Nat := 4983230072969 + 3 ^ 40 * 5807812 * 2
def baseEnd_5807812 : Nat := 2982199106950336142540365

theorem tailTrace_5807812 : CollatzResearch.WordTrace tailWord_5807812 prefixEnd_5807812 2982199106950336142540365 := by
  unfold tailWord_5807812
  simp only [CollatzResearch.WordTrace]
  refine ⟨105914153017648247082944845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141218870690197662777259793 105914153017648247082944845)
  ·
    refine ⟨39717807381618092656104317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105914153017648247082944845 39717807381618092656104317)
    ·
      refine ⟨14894177768106784746039119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39717807381618092656104317 14894177768106784746039119)
      ·
        refine ⟨22341266652160177119058679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894177768106784746039119 22341266652160177119058679)
        ·
          refine ⟨33511899978240265678588019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341266652160177119058679 33511899978240265678588019)
          ·
            refine ⟨50267849967360398517882029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33511899978240265678588019 50267849967360398517882029)
            ·
              refine ⟨18850443737760149444205761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50267849967360398517882029 18850443737760149444205761)
              ·
                refine ⟨14137832803320112083154321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18850443737760149444205761 14137832803320112083154321)
                ·
                  refine ⟨10603374602490084062365741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14137832803320112083154321 10603374602490084062365741)
                  ·
                    refine ⟨3976265475933781523387153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10603374602490084062365741 3976265475933781523387153)
                    ·
                      refine ⟨2982199106950336142540365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976265475933781523387153 2982199106950336142540365)
                      ·
                        rfl

theorem cell23_5807812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_5807812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807812 prefixEnd_5807812 := by exact prefixLift 5807812
  have htrace : WordTrace (prefixWord ++ tailWord_5807812) baseStart_5807812 baseEnd_5807812 := by
    simpa [prefixWord, tailWord_5807812, baseEnd_5807812] using wordTrace_append hprefix tailTrace_5807812
  have hstable : (prefixWord ++ tailWord_5807812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807812).length < 2 ^ (prefixWord ++ tailWord_5807812).sum := by decide
  have hdescent : baseEnd_5807812 < baseStart_5807812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807845 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5807845 : Nat := 118140960795 + 5807845 * 2 ^ 59
def prefixEnd_5807845 : Nat := 4983230072969 + 3 ^ 40 * 5807845 * 2
def baseEnd_5807845 : Nat := 2982216051811934513427713

theorem tailTrace_5807845 : CollatzResearch.WordTrace tailWord_5807845 prefixEnd_5807845 2982216051811934513427713 := by
  unfold tailWord_5807845
  simp only [CollatzResearch.WordTrace]
  refine ⟨211829509644176940801840989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141219673096117960534560659 211829509644176940801840989)
  ·
    refine ⟨79436066116566352800690371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211829509644176940801840989 79436066116566352800690371)
    ·
      refine ⟨119154099174849529201035557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79436066116566352800690371 119154099174849529201035557)
      ·
        refine ⟨22341393595284286725194167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119154099174849529201035557 22341393595284286725194167)
        ·
          refine ⟨33512090392926430087791251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341393595284286725194167 33512090392926430087791251)
          ·
            refine ⟨50268135589389645131686877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33512090392926430087791251 50268135589389645131686877)
            ·
              refine ⟨18850550846021116924382579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50268135589389645131686877 18850550846021116924382579)
              ·
                refine ⟨28275826269031675386573869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18850550846021116924382579 28275826269031675386573869)
                ·
                  refine ⟨10603434850886878269965201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28275826269031675386573869 10603434850886878269965201)
                  ·
                    refine ⟨7952576138165158702473901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10603434850886878269965201 7952576138165158702473901)
                    ·
                      refine ⟨2982216051811934513427713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952576138165158702473901 2982216051811934513427713)
                      ·
                        rfl

theorem cell23_5807845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5807845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807845 prefixEnd_5807845 := by exact prefixLift 5807845
  have htrace : WordTrace (prefixWord ++ tailWord_5807845) baseStart_5807845 baseEnd_5807845 := by
    simpa [prefixWord, tailWord_5807845, baseEnd_5807845] using wordTrace_append hprefix tailTrace_5807845
  have hstable : (prefixWord ++ tailWord_5807845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807845).length < 2 ^ (prefixWord ++ tailWord_5807845).sum := by decide
  have hdescent : baseEnd_5807845 < baseStart_5807845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807848 : List Nat := [2, 1, 4, 1, 3, 1, 2, 9]
def baseStart_5807848 : Nat := 118140960795 + 5807848 * 2 ^ 59
def prefixEnd_5807848 : Nat := 4983230072969 + 3 ^ 40 * 5807848 * 2
def baseEnd_5807848 : Nat := 110452503416811037099637

theorem tailTrace_5807848 : CollatzResearch.WordTrace tailWord_5807848 prefixEnd_5807848 110452503416811037099637 := by
  unfold tailWord_5807848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105914809531583036157100099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141219746042110714876133465 105914809531583036157100099)
  ·
    refine ⟨158872214297374554235650149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105914809531583036157100099 158872214297374554235650149)
    ·
      refine ⟨29788540180757728919184403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158872214297374554235650149 29788540180757728919184403)
      ·
        refine ⟨44682810271136593378776605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29788540180757728919184403 44682810271136593378776605)
        ·
          refine ⟨16756053851676222517041227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44682810271136593378776605 16756053851676222517041227)
          ·
            refine ⟨25134080777514333775561841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16756053851676222517041227 25134080777514333775561841)
            ·
              refine ⟨18850560583135750331671381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25134080777514333775561841 18850560583135750331671381)
              ·
                refine ⟨110452503416811037099637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18850560583135750331671381 110452503416811037099637)
                ·
                  rfl

theorem cell23_5807848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 9].length) (baseStart_5807848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807848 prefixEnd_5807848 := by exact prefixLift 5807848
  have htrace : WordTrace (prefixWord ++ tailWord_5807848) baseStart_5807848 baseEnd_5807848 := by
    simpa [prefixWord, tailWord_5807848, baseEnd_5807848] using wordTrace_append hprefix tailTrace_5807848
  have hstable : (prefixWord ++ tailWord_5807848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807848).length < 2 ^ (prefixWord ++ tailWord_5807848).sum := by decide
  have hdescent : baseEnd_5807848 < baseStart_5807848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807862 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5807862 : Nat := 118140960795 + 5807862 * 2 ^ 59
def prefixEnd_5807862 : Nat := 4983230072969 + 3 ^ 40 * 5807862 * 2
def baseEnd_5807862 : Nat := 2982224780983060946915135

theorem tailTrace_5807862 : CollatzResearch.WordTrace tailWord_5807862 prefixEnd_5807862 2982224780983060946915135 := by
  unfold tailWord_5807862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239383105319709544075615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141220086456743568470139893 13239383105319709544075615)
  ·
    refine ⟨19859074657979564316113423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13239383105319709544075615 19859074657979564316113423)
    ·
      refine ⟨29788611986969346474170135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859074657979564316113423 29788611986969346474170135)
      ·
        refine ⟨44682917980454019711255203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29788611986969346474170135 44682917980454019711255203)
        ·
          refine ⟨67024376970681029566882805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44682917980454019711255203 67024376970681029566882805)
          ·
            refine ⟨6283535341001346521895263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67024376970681029566882805 6283535341001346521895263)
            ·
              refine ⟨9425303011502019782842895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283535341001346521895263 9425303011502019782842895)
              ·
                refine ⟨14137954517253029674264343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425303011502019782842895 14137954517253029674264343)
                ·
                  refine ⟨21206931775879544511396515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14137954517253029674264343 21206931775879544511396515)
                  ·
                    refine ⟨31810397663819316767094773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21206931775879544511396515 31810397663819316767094773)
                    ·
                      refine ⟨2982224780983060946915135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31810397663819316767094773 2982224780983060946915135)
                      ·
                        rfl

theorem cell23_5807862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5807862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807862 prefixEnd_5807862 := by exact prefixLift 5807862
  have htrace : WordTrace (prefixWord ++ tailWord_5807862) baseStart_5807862 baseEnd_5807862 := by
    simpa [prefixWord, tailWord_5807862, baseEnd_5807862] using wordTrace_append hprefix tailTrace_5807862
  have hstable : (prefixWord ++ tailWord_5807862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807862).length < 2 ^ (prefixWord ++ tailWord_5807862).sum := by decide
  have hdescent : baseEnd_5807862 < baseStart_5807862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807870 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5807870 : Nat := 118140960795 + 5807870 * 2 ^ 59
def prefixEnd_5807870 : Nat := 4983230072969 + 3 ^ 40 * 5807870 * 2
def baseEnd_5807870 : Nat := 2982228888828296915615099

theorem tailTrace_5807870 : CollatzResearch.WordTrace tailWord_5807870 prefixEnd_5807870 2982228888828296915615099 := by
  unfold tailWord_5807870
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478802683635796258937633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141220280979390913381000709 26478802683635796258937633)
  ·
    refine ⟨19859102012726847194203225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26478802683635796258937633 19859102012726847194203225)
    ·
      refine ⟨14894326509545135395652419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19859102012726847194203225 14894326509545135395652419)
      ·
        refine ⟨22341489764317703093478629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894326509545135395652419 22341489764317703093478629)
        ·
          refine ⟨4189029330809569330027243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22341489764317703093478629 4189029330809569330027243)
          ·
            refine ⟨6283543996214353995040865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189029330809569330027243 6283543996214353995040865)
            ·
              refine ⟨4712657997160765496280649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283543996214353995040865 4712657997160765496280649)
              ·
                refine ⟨3534493497870574122210487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712657997160765496280649 3534493497870574122210487)
                ·
                  refine ⟨5301740246805861183315731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534493497870574122210487 5301740246805861183315731)
                  ·
                    refine ⟨7952610370208791774973597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301740246805861183315731 7952610370208791774973597)
                    ·
                      refine ⟨2982228888828296915615099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952610370208791774973597 2982228888828296915615099)
                      ·
                        rfl

theorem cell23_5807870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5807870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807870 prefixEnd_5807870 := by exact prefixLift 5807870
  have htrace : WordTrace (prefixWord ++ tailWord_5807870) baseStart_5807870 baseEnd_5807870 := by
    simpa [prefixWord, tailWord_5807870, baseEnd_5807870] using wordTrace_append hprefix tailTrace_5807870
  have hstable : (prefixWord ++ tailWord_5807870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807870).length < 2 ^ (prefixWord ++ tailWord_5807870).sum := by decide
  have hdescent : baseEnd_5807870 < baseStart_5807870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807875 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 3]
def baseStart_5807875 : Nat := 118140960795 + 5807875 * 2 ^ 59
def prefixEnd_5807875 : Nat := 4983230072969 + 3 ^ 40 * 5807875 * 2
def baseEnd_5807875 : Nat := 2982231456231569396052575

theorem tailTrace_5807875 : CollatzResearch.WordTrace tailWord_5807875 prefixEnd_5807875 2982231456231569396052575 := by
  unfold tailWord_5807875
  simp only [CollatzResearch.WordTrace]
  refine ⟨211830603834068255925433079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141220402556045503950288719 211830603834068255925433079)
  ·
    refine ⟨317745905751102383888149619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211830603834068255925433079 317745905751102383888149619)
    ·
      refine ⟨476618858626653575832224429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317745905751102383888149619 476618858626653575832224429)
      ·
        refine ⟨178732071984995090937084161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476618858626653575832224429 178732071984995090937084161)
        ·
          refine ⟨134049053988746318202813121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178732071984995090937084161 134049053988746318202813121)
          ·
            refine ⟨100536790491559738652109841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134049053988746318202813121 100536790491559738652109841)
            ·
              refine ⟨75402592868669803989082381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100536790491559738652109841 75402592868669803989082381)
              ·
                refine ⟨28275972325751176495905893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75402592868669803989082381 28275972325751176495905893)
                ·
                  refine ⟨5301744811078345592982355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28275972325751176495905893 5301744811078345592982355)
                  ·
                    refine ⟨7952617216617518389473533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301744811078345592982355 7952617216617518389473533)
                    ·
                      refine ⟨2982231456231569396052575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952617216617518389473533 2982231456231569396052575)
                      ·
                        rfl

theorem cell23_5807875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_5807875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807875 prefixEnd_5807875 := by exact prefixLift 5807875
  have htrace : WordTrace (prefixWord ++ tailWord_5807875) baseStart_5807875 baseEnd_5807875 := by
    simpa [prefixWord, tailWord_5807875, baseEnd_5807875] using wordTrace_append hprefix tailTrace_5807875
  have hstable : (prefixWord ++ tailWord_5807875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807875).length < 2 ^ (prefixWord ++ tailWord_5807875).sum := by decide
  have hdescent : baseEnd_5807875 < baseStart_5807875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807876 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5807876 : Nat := 118140960795 + 5807876 * 2 ^ 59
def prefixEnd_5807876 : Nat := 4983230072969 + 3 ^ 40 * 5807876 * 2
def baseEnd_5807876 : Nat := 2982231969712223892140071

theorem tailTrace_5807876 : CollatzResearch.WordTrace tailWord_5807876 prefixEnd_5807876 2982231969712223892140071 := by
  unfold tailWord_5807876
  simp only [CollatzResearch.WordTrace]
  refine ⟨105915320153532316548109741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141220426871376422064146321 105915320153532316548109741)
  ·
    refine ⟨39718245057574618705541153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105915320153532316548109741 39718245057574618705541153)
    ·
      refine ⟨29788683793180964029155865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39718245057574618705541153 29788683793180964029155865)
      ·
        refine ⟨22341512844885723021866899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29788683793180964029155865 22341512844885723021866899)
        ·
          refine ⟨33512269267328584532800349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341512844885723021866899 33512269267328584532800349)
          ·
            refine ⟨12567100975248219199800131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33512269267328584532800349 12567100975248219199800131)
            ·
              refine ⟨18850651462872328799700197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12567100975248219199800131 18850651462872328799700197)
              ·
                refine ⟨3534497149288561649943787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18850651462872328799700197 3534497149288561649943787)
                ·
                  refine ⟨5301745723932842474915681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534497149288561649943787 5301745723932842474915681)
                  ·
                    refine ⟨3976309292949631856186761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5301745723932842474915681 3976309292949631856186761)
                    ·
                      refine ⟨2982231969712223892140071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976309292949631856186761 2982231969712223892140071)
                      ·
                        rfl

theorem cell23_5807876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5807876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807876 prefixEnd_5807876 := by exact prefixLift 5807876
  have htrace : WordTrace (prefixWord ++ tailWord_5807876) baseStart_5807876 baseEnd_5807876 := by
    simpa [prefixWord, tailWord_5807876, baseEnd_5807876] using wordTrace_append hprefix tailTrace_5807876
  have hstable : (prefixWord ++ tailWord_5807876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807876).length < 2 ^ (prefixWord ++ tailWord_5807876).sum := by decide
  have hdescent : baseEnd_5807876 < baseStart_5807876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807926 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5807926 : Nat := 118140960795 + 5807926 * 2 ^ 59
def prefixEnd_5807926 : Nat := 4983230072969 + 3 ^ 40 * 5807926 * 2
def baseEnd_5807926 : Nat := 2982257643744948696514841

theorem tailTrace_5807926 : CollatzResearch.WordTrace tailWord_5807926 prefixEnd_5807926 2982257643744948696514841 := by
  unfold tailWord_5807926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239528997305218227221227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141221642637922327757026421 13239528997305218227221227)
  ·
    refine ⟨19859293495957827340831841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13239528997305218227221227 19859293495957827340831841)
    ·
      refine ⟨14894470121968370505623881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19859293495957827340831841 14894470121968370505623881)
      ·
        refine ⟨11170852591476277879217911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14894470121968370505623881 11170852591476277879217911)
        ·
          refine ⟨16756278887214416818826867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11170852591476277879217911 16756278887214416818826867)
          ·
            refine ⟨25134418330821625228240301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16756278887214416818826867 25134418330821625228240301)
            ·
              refine ⟨9425406874058109460590113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25134418330821625228240301 9425406874058109460590113)
              ·
                refine ⟨7069055155543582095442585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425406874058109460590113 7069055155543582095442585)
                ·
                  refine ⟨5301791366657686571581939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7069055155543582095442585 5301791366657686571581939)
                  ·
                    refine ⟨7952687049986529857372909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301791366657686571581939 7952687049986529857372909)
                    ·
                      refine ⟨2982257643744948696514841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952687049986529857372909 2982257643744948696514841)
                      ·
                        rfl

theorem cell23_5807926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5807926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807926 prefixEnd_5807926 := by exact prefixLift 5807926
  have htrace : WordTrace (prefixWord ++ tailWord_5807926) baseStart_5807926 baseEnd_5807926 := by
    simpa [prefixWord, tailWord_5807926, baseEnd_5807926] using wordTrace_append hprefix tailTrace_5807926
  have hstable : (prefixWord ++ tailWord_5807926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807926).length < 2 ^ (prefixWord ++ tailWord_5807926).sum := by decide
  have hdescent : baseEnd_5807926 < baseStart_5807926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807985 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 2, 5]
def baseStart_5807985 : Nat := 118140960795 + 5807985 * 2 ^ 59
def prefixEnd_5807985 : Nat := 4983230072969 + 3 ^ 40 * 5807985 * 2
def baseEnd_5807985 : Nat := 994095979701187988559023

theorem tailTrace_5807985 : CollatzResearch.WordTrace tailWord_5807985 prefixEnd_5807985 994095979701187988559023 := by
  unfold tailWord_5807985
  simp only [CollatzResearch.WordTrace]
  refine ⟨211834615863669744711937409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141223077242446496474624939 211834615863669744711937409)
  ·
    refine ⟨158875961897752308533953057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211834615863669744711937409 158875961897752308533953057)
    ·
      refine ⟨119156971423314231400464793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158875961897752308533953057 119156971423314231400464793)
      ·
        refine ⟨89367728567485673550348595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119156971423314231400464793 89367728567485673550348595)
        ·
          refine ⟨134051592851228510325522893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89367728567485673550348595 134051592851228510325522893)
          ·
            refine ⟨50269347319210691372071085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134051592851228510325522893 50269347319210691372071085)
            ·
              refine ⟨18851005244704009264526657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50269347319210691372071085 18851005244704009264526657)
              ·
                refine ⟨14138253933528006948394993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18851005244704009264526657 14138253933528006948394993)
                ·
                  refine ⟨10603690450146005211296245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14138253933528006948394993 10603690450146005211296245)
                  ·
                    refine ⟨994095979701187988559023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10603690450146005211296245 994095979701187988559023)
                    ·
                      rfl

theorem cell23_5807985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 5].length) (baseStart_5807985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807985 prefixEnd_5807985 := by exact prefixLift 5807985
  have htrace : WordTrace (prefixWord ++ tailWord_5807985) baseStart_5807985 baseEnd_5807985 := by
    simpa [prefixWord, tailWord_5807985, baseEnd_5807985] using wordTrace_append hprefix tailTrace_5807985
  have hstable : (prefixWord ++ tailWord_5807985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807985).length < 2 ^ (prefixWord ++ tailWord_5807985).sum := by decide
  have hdescent : baseEnd_5807985 < baseStart_5807985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5807989 : List Nat := [1, 3, 4, 1, 1, 1, 5, 2, 5]
def baseStart_5807989 : Nat := 118140960795 + 5807989 * 2 ^ 59
def prefixEnd_5807989 : Nat := 4983230072969 + 3 ^ 40 * 5807989 * 2
def baseEnd_5807989 : Nat := 331365554780686883336339

theorem tailTrace_5807989 : CollatzResearch.WordTrace tailWord_5807989 prefixEnd_5807989 331365554780686883336339 := by
  unfold tailWord_5807989
  simp only [CollatzResearch.WordTrace]
  refine ⟨211834761755655253395083021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141223174503770168930055347 211834761755655253395083021)
  ·
    refine ⟨79438035658370720023156133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211834761755655253395083021 79438035658370720023156133)
    ·
      refine ⟨14894631685944510004341775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79438035658370720023156133 14894631685944510004341775)
      ·
        refine ⟨22341947528916765006512663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894631685944510004341775 22341947528916765006512663)
        ·
          refine ⟨33512921293375147509768995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22341947528916765006512663 33512921293375147509768995)
          ·
            refine ⟨50269381940062721264653493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33512921293375147509768995 50269381940062721264653493)
            ·
              refine ⟨4712754556880880118561265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50269381940062721264653493 4712754556880880118561265)
              ·
                refine ⟨3534565917660660088920949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712754556880880118561265 3534565917660660088920949)
                ·
                  refine ⟨331365554780686883336339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534565917660660088920949 331365554780686883336339)
                  ·
                    rfl

theorem cell23_5807989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_5807989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5807989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5807989 prefixEnd_5807989 := by exact prefixLift 5807989
  have htrace : WordTrace (prefixWord ++ tailWord_5807989) baseStart_5807989 baseEnd_5807989 := by
    simpa [prefixWord, tailWord_5807989, baseEnd_5807989] using wordTrace_append hprefix tailTrace_5807989
  have hstable : (prefixWord ++ tailWord_5807989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5807989).length < 2 ^ (prefixWord ++ tailWord_5807989).sum := by decide
  have hdescent : baseEnd_5807989 < baseStart_5807989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5807989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808005 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_5808005 : Nat := 118140960795 + 5808005 * 2 ^ 59
def prefixEnd_5808005 : Nat := 4983230072969 + 3 ^ 40 * 5808005 * 2
def baseEnd_5808005 : Nat := 2982298208716653887426977

theorem tailTrace_5808005 : CollatzResearch.WordTrace tailWord_5808005 prefixEnd_5808005 2982298208716653887426977 := by
  unfold tailWord_5808005
  simp only [CollatzResearch.WordTrace]
  refine ⟨211835345323597288127665469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141223563549064858751776979 211835345323597288127665469)
  ·
    refine ⟨79438254496348983047874551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211835345323597288127665469 79438254496348983047874551)
    ·
      refine ⟨119157381744523474571811827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79438254496348983047874551 119157381744523474571811827)
      ·
        refine ⟨178736072616785211857717741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119157381744523474571811827 178736072616785211857717741)
        ·
          refine ⟨67026027231294454446644153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178736072616785211857717741 67026027231294454446644153)
          ·
            refine ⟨50269520423470840834983115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67026027231294454446644153 50269520423470840834983115)
            ·
              refine ⟨75404280635206261252474673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50269520423470840834983115 75404280635206261252474673)
              ·
                refine ⟨56553210476404695939356005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75404280635206261252474673 56553210476404695939356005)
                ·
                  refine ⟨10603726964325880488629251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56553210476404695939356005 10603726964325880488629251)
                  ·
                    refine ⟨15905590446488820732943877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10603726964325880488629251 15905590446488820732943877)
                    ·
                      refine ⟨2982298208716653887426977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15905590446488820732943877 2982298208716653887426977)
                      ·
                        rfl

theorem cell23_5808005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_5808005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808005 prefixEnd_5808005 := by exact prefixLift 5808005
  have htrace : WordTrace (prefixWord ++ tailWord_5808005) baseStart_5808005 baseEnd_5808005 := by
    simpa [prefixWord, tailWord_5808005, baseEnd_5808005] using wordTrace_append hprefix tailTrace_5808005
  have hstable : (prefixWord ++ tailWord_5808005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808005).length < 2 ^ (prefixWord ++ tailWord_5808005).sum := by decide
  have hdescent : baseEnd_5808005 < baseStart_5808005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808025 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 3]
def baseStart_5808025 : Nat := 118140960795 + 5808025 * 2 ^ 59
def prefixEnd_5808025 : Nat := 4983230072969 + 3 ^ 40 * 5808025 * 2
def baseEnd_5808025 : Nat := 2982308478329743809176885

theorem tailTrace_5808025 : CollatzResearch.WordTrace tailWord_5808025 prefixEnd_5808025 2982308478329743809176885 := by
  unfold tailWord_5808025
  simp only [CollatzResearch.WordTrace]
  refine ⟨211836074783524831543393529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141224049855683221028929019 211836074783524831543393529)
  ·
    refine ⟨158877056087643623657545147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211836074783524831543393529 158877056087643623657545147)
    ·
      refine ⟨238315584131465435486317721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158877056087643623657545147 238315584131465435486317721)
      ·
        refine ⟨178736688098599076614738291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238315584131465435486317721 178736688098599076614738291)
        ·
          refine ⟨268105032147898614922107437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178736688098599076614738291 268105032147898614922107437)
          ·
            refine ⟨100539387055461980595790289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268105032147898614922107437 100539387055461980595790289)
            ·
              refine ⟨75404540291596485446842717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100539387055461980595790289 75404540291596485446842717)
              ·
                refine ⟨28276702609348682042566019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75404540291596485446842717 28276702609348682042566019)
                ·
                  refine ⟨42415053914023023063849029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28276702609348682042566019 42415053914023023063849029)
                  ·
                    refine ⟨7952822608879316824471693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42415053914023023063849029 7952822608879316824471693)
                    ·
                      refine ⟨2982308478329743809176885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952822608879316824471693 2982308478329743809176885)
                      ·
                        rfl

theorem cell23_5808025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_5808025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808025 prefixEnd_5808025 := by exact prefixLift 5808025
  have htrace : WordTrace (prefixWord ++ tailWord_5808025) baseStart_5808025 baseEnd_5808025 := by
    simpa [prefixWord, tailWord_5808025, baseEnd_5808025] using wordTrace_append hprefix tailTrace_5808025
  have hstable : (prefixWord ++ tailWord_5808025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808025).length < 2 ^ (prefixWord ++ tailWord_5808025).sum := by decide
  have hdescent : baseEnd_5808025 < baseStart_5808025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808040 : List Nat := [2, 1, 6, 2, 2, 1, 2, 2, 5]
def baseStart_5808040 : Nat := 118140960795 + 5808040 * 2 ^ 59
def prefixEnd_5808040 : Nat := 4983230072969 + 3 ^ 40 * 5808040 * 2
def baseEnd_5808040 : Nat := 331368464504395694498813

theorem tailTrace_5808040 : CollatzResearch.WordTrace tailWord_5808040 prefixEnd_5808040 331368464504395694498813 := by
  unfold tailWord_5808040
  simp only [CollatzResearch.WordTrace]
  refine ⟨105918310939235244552594787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141224414585646992736793049 105918310939235244552594787)
  ·
    refine ⟨158877466408852866828892181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105918310939235244552594787 158877466408852866828892181)
    ·
      refine ⟨7447381237914978132604321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158877466408852866828892181 7447381237914978132604321)
      ·
        refine ⟨5585535928436233599453241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447381237914978132604321 5585535928436233599453241)
        ·
          refine ⟨4189151946327175199589931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5585535928436233599453241 4189151946327175199589931)
          ·
            refine ⟨6283727919490762799384897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189151946327175199589931 6283727919490762799384897)
            ·
              refine ⟨4712795939618072099538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283727919490762799384897 4712795939618072099538673)
              ·
                refine ⟨3534596954713554074654005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712795939618072099538673 3534596954713554074654005)
                ·
                  refine ⟨331368464504395694498813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534596954713554074654005 331368464504395694498813)
                  ·
                    rfl

theorem cell23_5808040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 5].length) (baseStart_5808040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808040 prefixEnd_5808040 := by exact prefixLift 5808040
  have htrace : WordTrace (prefixWord ++ tailWord_5808040) baseStart_5808040 baseEnd_5808040 := by
    simpa [prefixWord, tailWord_5808040, baseEnd_5808040] using wordTrace_append hprefix tailTrace_5808040
  have hstable : (prefixWord ++ tailWord_5808040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808040).length < 2 ^ (prefixWord ++ tailWord_5808040).sum := by decide
  have hdescent : baseEnd_5808040 < baseStart_5808040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808055 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3]
def baseStart_5808055 : Nat := 118140960795 + 5808055 * 2 ^ 59
def prefixEnd_5808055 : Nat := 4983230072969 + 3 ^ 40 * 5808055 * 2
def baseEnd_5808055 : Nat := 2982323882749378691801747

theorem tailTrace_5808055 : CollatzResearch.WordTrace tailWord_5808055 prefixEnd_5808055 2982323882749378691801747 := by
  unfold tailWord_5808055
  simp only [CollatzResearch.WordTrace]
  refine ⟨211837168973416146666985619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141224779315610764444657079 211837168973416146666985619)
  ·
    refine ⟨317755753460124220000478429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211837168973416146666985619 317755753460124220000478429)
    ·
      refine ⟨119158407547546582500179411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317755753460124220000478429 119158407547546582500179411)
      ·
        refine ⟨178737611321319873750269117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119158407547546582500179411 178737611321319873750269117)
        ·
          refine ⟨67026604245494952656350919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178737611321319873750269117 67026604245494952656350919)
          ·
            refine ⟨100539906368242428984526379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67026604245494952656350919 100539906368242428984526379)
            ·
              refine ⟨150809859552363643476789569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100539906368242428984526379 150809859552363643476789569)
              ·
                refine ⟨113107394664272732607592177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150809859552363643476789569 113107394664272732607592177)
                ·
                  refine ⟨84830545998204549455694133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113107394664272732607592177 84830545998204549455694133)
                  ·
                    refine ⟨7952863687331676511471325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84830545998204549455694133 7952863687331676511471325)
                    ·
                      refine ⟨2982323882749378691801747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952863687331676511471325 2982323882749378691801747)
                      ·
                        rfl

theorem cell23_5808055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 3].length) (baseStart_5808055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808055 prefixEnd_5808055 := by exact prefixLift 5808055
  have htrace : WordTrace (prefixWord ++ tailWord_5808055) baseStart_5808055 baseEnd_5808055 := by
    simpa [prefixWord, tailWord_5808055, baseEnd_5808055] using wordTrace_append hprefix tailTrace_5808055
  have hstable : (prefixWord ++ tailWord_5808055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808055).length < 2 ^ (prefixWord ++ tailWord_5808055).sum := by decide
  have hdescent : baseEnd_5808055 < baseStart_5808055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808062 : List Nat := [4, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_5808062 : Nat := 118140960795 + 5808062 * 2 ^ 59
def prefixEnd_5808062 : Nat := 4983230072969 + 3 ^ 40 * 5808062 * 2
def baseEnd_5808062 : Nat := 331369719679328907157135

theorem tailTrace_5808062 : CollatzResearch.WordTrace tailWord_5808062 prefixEnd_5808062 331369719679328907157135 := by
  unfold tailWord_5808062
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479678035548848357811305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141224949522927191241660293 26479678035548848357811305)
  ·
    refine ⟨19859758526661636268358479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26479678035548848357811305 19859758526661636268358479)
    ·
      refine ⟨29789637789992454402537719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19859758526661636268358479 29789637789992454402537719)
      ·
        refine ⟨44684456684988681603806579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789637789992454402537719 44684456684988681603806579)
        ·
          refine ⟨67026685027483022405709869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44684456684988681603806579 67026685027483022405709869)
          ·
            refine ⟨25135006885306133402141201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67026685027483022405709869 25135006885306133402141201)
            ·
              refine ⟨18851255163979600051605901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25135006885306133402141201 18851255163979600051605901)
              ·
                refine ⟨7069220686492350019352213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18851255163979600051605901 7069220686492350019352213)
                ·
                  refine ⟨331369719679328907157135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7069220686492350019352213 331369719679328907157135)
                  ·
                    rfl

theorem cell23_5808062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_5808062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808062 prefixEnd_5808062 := by exact prefixLift 5808062
  have htrace : WordTrace (prefixWord ++ tailWord_5808062) baseStart_5808062 baseEnd_5808062 := by
    simpa [prefixWord, tailWord_5808062, baseEnd_5808062] using wordTrace_append hprefix tailTrace_5808062
  have hstable : (prefixWord ++ tailWord_5808062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808062).length < 2 ^ (prefixWord ++ tailWord_5808062).sum := by decide
  have hdescent : baseEnd_5808062 < baseStart_5808062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808075 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 3, 5]
def baseStart_5808075 : Nat := 118140960795 + 5808075 * 2 ^ 59
def prefixEnd_5808075 : Nat := 4983230072969 + 3 ^ 40 * 5808075 * 2
def baseEnd_5808075 : Nat := 994111384120822871183885

theorem tailTrace_5808075 : CollatzResearch.WordTrace tailWord_5808075 prefixEnd_5808075 994111384120822871183885 := by
  unfold tailWord_5808075
  simp only [CollatzResearch.WordTrace]
  refine ⟨211837898433343690082713679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141225265622229126721809119 211837898433343690082713679)
  ·
    refine ⟨317756847650015535124070519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211837898433343690082713679 317756847650015535124070519)
    ·
      refine ⟨476635271475023302686105779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317756847650015535124070519 476635271475023302686105779)
      ·
        refine ⟨714952907212534954029158669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476635271475023302686105779 714952907212534954029158669)
        ·
          refine ⟨268107340204700607760934501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 714952907212534954029158669 268107340204700607760934501)
          ·
            refine ⟨50270126288381363955175219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268107340204700607760934501 50270126288381363955175219)
            ·
              refine ⟨75405189432572045932762829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50270126288381363955175219 75405189432572045932762829)
              ·
                refine ⟨28276946037214517224786061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75405189432572045932762829 28276946037214517224786061)
                ·
                  refine ⟨10603854763955443959294773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28276946037214517224786061 10603854763955443959294773)
                  ·
                    refine ⟨994111384120822871183885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10603854763955443959294773 994111384120822871183885)
                    ·
                      rfl

theorem cell23_5808075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 5].length) (baseStart_5808075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808075 prefixEnd_5808075 := by exact prefixLift 5808075
  have htrace : WordTrace (prefixWord ++ tailWord_5808075) baseStart_5808075 baseEnd_5808075 := by
    simpa [prefixWord, tailWord_5808075, baseEnd_5808075] using wordTrace_append hprefix tailTrace_5808075
  have hstable : (prefixWord ++ tailWord_5808075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808075).length < 2 ^ (prefixWord ++ tailWord_5808075).sum := by decide
  have hdescent : baseEnd_5808075 < baseStart_5808075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808106 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3]
def baseStart_5808106 : Nat := 118140960795 + 5808106 * 2 ^ 59
def prefixEnd_5808106 : Nat := 4983230072969 + 3 ^ 40 * 5808106 * 2
def baseEnd_5808106 : Nat := 2982350070262757992264013

theorem tailTrace_5808106 : CollatzResearch.WordTrace tailWord_5808106 prefixEnd_5808106 2982350070262757992264013 := by
  unfold tailWord_5808106
  simp only [CollatzResearch.WordTrace]
  refine ⟨52959757274057845594273043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141226019397487588251394781 52959757274057845594273043)
  ·
    refine ⟨79439635911086768391409565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52959757274057845594273043 79439635911086768391409565)
    ·
      refine ⟨29789863466657538146778587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79439635911086768391409565 29789863466657538146778587)
      ·
        refine ⟨44684795199986307220167881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789863466657538146778587 44684795199986307220167881)
        ·
          refine ⟨33513596399989730415125911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44684795199986307220167881 33513596399989730415125911)
          ·
            refine ⟨50270394599984595622688867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33513596399989730415125911 50270394599984595622688867)
            ·
              refine ⟨75405591899976893434033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50270394599984595622688867 75405591899976893434033301)
              ·
                refine ⟨3534637120311416879720311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75405591899976893434033301 3534637120311416879720311)
                ·
                  refine ⟨5301955680467125319580467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534637120311416879720311 5301955680467125319580467)
                  ·
                    refine ⟨7952933520700687979370701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5301955680467125319580467 7952933520700687979370701)
                    ·
                      refine ⟨2982350070262757992264013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7952933520700687979370701 2982350070262757992264013)
                      ·
                        rfl

theorem cell23_5808106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_5808106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808106 prefixEnd_5808106 := by exact prefixLift 5808106
  have htrace : WordTrace (prefixWord ++ tailWord_5808106) baseStart_5808106 baseEnd_5808106 := by
    simpa [prefixWord, tailWord_5808106, baseEnd_5808106] using wordTrace_append hprefix tailTrace_5808106
  have hstable : (prefixWord ++ tailWord_5808106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808106).length < 2 ^ (prefixWord ++ tailWord_5808106).sum := by decide
  have hdescent : baseEnd_5808106 < baseStart_5808106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808126 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5808126 : Nat := 118140960795 + 5808126 * 2 ^ 59
def prefixEnd_5808126 : Nat := 4983230072969 + 3 ^ 40 * 5808126 * 2
def baseEnd_5808126 : Nat := 994120113291949304671307

theorem tailTrace_5808126 : CollatzResearch.WordTrace tailWord_5808126 prefixEnd_5808126 994120113291949304671307 := by
  unfold tailWord_5808126
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479969819519865724102529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141226505704105950528546821 26479969819519865724102529)
  ·
    refine ⟨19859977364639899293076897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26479969819519865724102529 19859977364639899293076897)
    ·
      refine ⟨14894983023479924469807673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19859977364639899293076897 14894983023479924469807673)
      ·
        refine ⟨11171237267609943352355755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14894983023479924469807673 11171237267609943352355755)
        ·
          refine ⟨16756855901414915028533633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171237267609943352355755 16756855901414915028533633)
          ·
            refine ⟨12567641926061186271400225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16756855901414915028533633 12567641926061186271400225)
            ·
              refine ⟨9425731444545889703550169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12567641926061186271400225 9425731444545889703550169)
              ·
                refine ⟨7069298583409417277662627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425731444545889703550169 7069298583409417277662627)
                ·
                  refine ⟨10603947875114125916493941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069298583409417277662627 10603947875114125916493941)
                  ·
                    refine ⟨994120113291949304671307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10603947875114125916493941 994120113291949304671307)
                    ·
                      rfl

theorem cell23_5808126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5808126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808126 prefixEnd_5808126 := by exact prefixLift 5808126
  have htrace : WordTrace (prefixWord ++ tailWord_5808126) baseStart_5808126 baseEnd_5808126 := by
    simpa [prefixWord, tailWord_5808126, baseEnd_5808126] using wordTrace_append hprefix tailTrace_5808126
  have hstable : (prefixWord ++ tailWord_5808126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808126).length < 2 ^ (prefixWord ++ tailWord_5808126).sum := by decide
  have hdescent : baseEnd_5808126 < baseStart_5808126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808129 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_5808129 : Nat := 118140960795 + 5808129 * 2 ^ 59
def prefixEnd_5808129 : Nat := 4983230072969 + 3 ^ 40 * 5808129 * 2
def baseEnd_5808129 : Nat := 2982361880317811402276407

theorem tailTrace_5808129 : CollatzResearch.WordTrace tailWord_5808129 prefixEnd_5808129 2982361880317811402276407 := by
  unfold tailWord_5808129
  simp only [CollatzResearch.WordTrace]
  refine ⟨211839867975148057305179441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141226578650098704870119627 211839867975148057305179441)
  ·
    refine ⟨158879900981361042978884581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211839867975148057305179441 158879900981361042978884581)
    ·
      refine ⟨29789981434005195558540859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158879900981361042978884581 29789981434005195558540859)
      ·
        refine ⟨44684972151007793337811289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29789981434005195558540859 44684972151007793337811289)
        ·
          refine ⟨33513729113255845003358467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44684972151007793337811289 33513729113255845003358467)
          ·
            refine ⟨50270593669883767505037701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33513729113255845003358467 50270593669883767505037701)
            ·
              refine ⟨9425736313103206407194569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50270593669883767505037701 9425736313103206407194569)
              ·
                refine ⟨7069302234827404805395927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425736313103206407194569 7069302234827404805395927)
                ·
                  refine ⟨10603953352241107208093891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069302234827404805395927 10603953352241107208093891)
                  ·
                    refine ⟨15905930028361660812140837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10603953352241107208093891 15905930028361660812140837)
                    ·
                      refine ⟨2982361880317811402276407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15905930028361660812140837 2982361880317811402276407)
                      ·
                        rfl

theorem cell23_5808129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_5808129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808129 prefixEnd_5808129 := by exact prefixLift 5808129
  have htrace : WordTrace (prefixWord ++ tailWord_5808129) baseStart_5808129 baseEnd_5808129 := by
    simpa [prefixWord, tailWord_5808129, baseEnd_5808129] using wordTrace_append hprefix tailTrace_5808129
  have hstable : (prefixWord ++ tailWord_5808129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808129).length < 2 ^ (prefixWord ++ tailWord_5808129).sum := by decide
  have hdescent : baseEnd_5808129 < baseStart_5808129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808134 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5808134 : Nat := 118140960795 + 5808134 * 2 ^ 59
def prefixEnd_5808134 : Nat := 4983230072969 + 3 ^ 40 * 5808134 * 2
def baseEnd_5808134 : Nat := 994121482573694627571295

theorem tailTrace_5808134 : CollatzResearch.WordTrace tailWord_5808134 prefixEnd_5808134 994121482573694627571295 := by
  unfold tailWord_5808134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620001573129060723722233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141226700226753295439407637 6620001573129060723722233)
  ·
    refine ⟨4965001179846795542791675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6620001573129060723722233 4965001179846795542791675)
    ·
      refine ⟨7447501769770193314187513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965001179846795542791675 7447501769770193314187513)
      ·
        refine ⟨5585626327327644985640635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7447501769770193314187513 5585626327327644985640635)
        ·
          refine ⟨8378439490991467478460953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5585626327327644985640635 8378439490991467478460953)
          ·
            refine ⟨6283829618243600608845715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8378439490991467478460953 6283829618243600608845715)
            ·
              refine ⟨9425744427365400913268573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283829618243600608845715 9425744427365400913268573)
              ·
                refine ⟨3534654160262025342475715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9425744427365400913268573 3534654160262025342475715)
                ·
                  refine ⟨5301981240393038013713573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534654160262025342475715 5301981240393038013713573)
                  ·
                    refine ⟨994121482573694627571295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5301981240393038013713573 994121482573694627571295)
                    ·
                      rfl

theorem cell23_5808134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5808134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808134 prefixEnd_5808134 := by exact prefixLift 5808134
  have htrace : WordTrace (prefixWord ++ tailWord_5808134) baseStart_5808134 baseEnd_5808134 := by
    simpa [prefixWord, tailWord_5808134, baseEnd_5808134] using wordTrace_append hprefix tailTrace_5808134
  have hstable : (prefixWord ++ tailWord_5808134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808134).length < 2 ^ (prefixWord ++ tailWord_5808134).sum := by decide
  have hdescent : baseEnd_5808134 < baseStart_5808134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808142 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4]
def baseStart_5808142 : Nat := 118140960795 + 5808142 * 2 ^ 59
def prefixEnd_5808142 : Nat := 4983230072969 + 3 ^ 40 * 5808142 * 2
def baseEnd_5808142 : Nat := 2982368555566319851413847

theorem tailTrace_5808142 : CollatzResearch.WordTrace tailWord_5808142 prefixEnd_5808142 2982368555566319851413847 := by
  unfold tailWord_5808142
  simp only [CollatzResearch.WordTrace]
  refine ⟨26480042765512620065675335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141226894749400640350268453 26480042765512620065675335)
  ·
    refine ⟨39720064148268930098513003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26480042765512620065675335 39720064148268930098513003)
    ·
      refine ⟨59580096222403395147769505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39720064148268930098513003 59580096222403395147769505)
      ·
        refine ⟨44685072166802546360827129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59580096222403395147769505 44685072166802546360827129)
        ·
          refine ⟨33513804125101909770620347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44685072166802546360827129 33513804125101909770620347)
          ·
            refine ⟨50270706187652864655930521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33513804125101909770620347 50270706187652864655930521)
            ·
              refine ⟨37703029640739648491947891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50270706187652864655930521 37703029640739648491947891)
              ·
                refine ⟨56554544461109472737921837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37703029640739648491947891 56554544461109472737921837)
                ·
                  refine ⟨21207954172916052276720689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56554544461109472737921837 21207954172916052276720689)
                  ·
                    refine ⟨15905965629687039207540517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21207954172916052276720689 15905965629687039207540517)
                    ·
                      refine ⟨2982368555566319851413847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15905965629687039207540517 2982368555566319851413847)
                      ·
                        rfl

theorem cell23_5808142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_5808142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808142 prefixEnd_5808142 := by exact prefixLift 5808142
  have htrace : WordTrace (prefixWord ++ tailWord_5808142) baseStart_5808142 baseEnd_5808142 := by
    simpa [prefixWord, tailWord_5808142, baseEnd_5808142] using wordTrace_append hprefix tailTrace_5808142
  have hstable : (prefixWord ++ tailWord_5808142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808142).length < 2 ^ (prefixWord ++ tailWord_5808142).sum := by decide
  have hdescent : baseEnd_5808142 < baseStart_5808142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808149 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_5808149 : Nat := 118140960795 + 5808149 * 2 ^ 59
def prefixEnd_5808149 : Nat := 4983230072969 + 3 ^ 40 * 5808149 * 2
def baseEnd_5808149 : Nat := 2982372149930901324026315

theorem tailTrace_5808149 : CollatzResearch.WordTrace tailWord_5808149 prefixEnd_5808149 2982372149930901324026315 := by
  unfold tailWord_5808149
  simp only [CollatzResearch.WordTrace]
  refine ⟨211840597435075600720907501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141227064956717067147271667 211840597435075600720907501)
  ·
    refine ⟨79440224038153350270340313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211840597435075600720907501 79440224038153350270340313)
    ·
      refine ⟨59580168028615012702755235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79440224038153350270340313 59580168028615012702755235)
      ·
        refine ⟨89370252042922519054132853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59580168028615012702755235 89370252042922519054132853)
        ·
          refine ⟨8378461129023986161324955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89370252042922519054132853 8378461129023986161324955)
          ·
            refine ⟨12567691693535979241987433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378461129023986161324955 12567691693535979241987433)
            ·
              refine ⟨9425768770151984431490575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12567691693535979241987433 9425768770151984431490575)
              ·
                refine ⟨14138653155227976647235863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425768770151984431490575 14138653155227976647235863)
                ·
                  refine ⟨21207979732841964970853795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14138653155227976647235863 21207979732841964970853795)
                  ·
                    refine ⟨31811969599262947456280693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21207979732841964970853795 31811969599262947456280693)
                    ·
                      refine ⟨2982372149930901324026315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31811969599262947456280693 2982372149930901324026315)
                      ·
                        rfl

theorem cell23_5808149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_5808149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808149 prefixEnd_5808149 := by exact prefixLift 5808149
  have htrace : WordTrace (prefixWord ++ tailWord_5808149) baseStart_5808149 baseEnd_5808149 := by
    simpa [prefixWord, tailWord_5808149, baseEnd_5808149] using wordTrace_append hprefix tailTrace_5808149
  have hstable : (prefixWord ++ tailWord_5808149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808149).length < 2 ^ (prefixWord ++ tailWord_5808149).sum := by decide
  have hdescent : baseEnd_5808149 < baseStart_5808149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808175 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_5808175 : Nat := 118140960795 + 5808175 * 2 ^ 59
def prefixEnd_5808175 : Nat := 4983230072969 + 3 ^ 40 * 5808175 * 2
def baseEnd_5808175 : Nat := 2982385500427918222301195

theorem tailTrace_5808175 : CollatzResearch.WordTrace tailWord_5808175 prefixEnd_5808175 2982385500427918222301195 := by
  unfold tailWord_5808175
  simp only [CollatzResearch.WordTrace]
  refine ⟨211841545732981407161353979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141227697155320938107569319 211841545732981407161353979)
  ·
    refine ⟨317762318599472110742030969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211841545732981407161353979 317762318599472110742030969)
    ·
      refine ⟨238321738949604083056523227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317762318599472110742030969 238321738949604083056523227)
      ·
        refine ⟨357482608424406124584784841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238321738949604083056523227 357482608424406124584784841)
        ·
          refine ⟨268111956318304593438588631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357482608424406124584784841 268111956318304593438588631)
          ·
            refine ⟨402167934477456890157882947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268111956318304593438588631 402167934477456890157882947)
            ·
              refine ⟨603251901716185335236824421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402167934477456890157882947 603251901716185335236824421)
              ·
                refine ⟨113109731571784750356904579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 603251901716185335236824421 113109731571784750356904579)
                ·
                  refine ⟨169664597357677125535356869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113109731571784750356904579 169664597357677125535356869)
                  ·
                    refine ⟨31812112004564461037879413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169664597357677125535356869 31812112004564461037879413)
                    ·
                      refine ⟨2982385500427918222301195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31812112004564461037879413 2982385500427918222301195)
                      ·
                        rfl

theorem cell23_5808175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_5808175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808175 prefixEnd_5808175 := by exact prefixLift 5808175
  have htrace : WordTrace (prefixWord ++ tailWord_5808175) baseStart_5808175 baseEnd_5808175 := by
    simpa [prefixWord, tailWord_5808175, baseEnd_5808175] using wordTrace_append hprefix tailTrace_5808175
  have hstable : (prefixWord ++ tailWord_5808175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808175).length < 2 ^ (prefixWord ++ tailWord_5808175).sum := by decide
  have hdescent : baseEnd_5808175 < baseStart_5808175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808180 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_5808180 : Nat := 118140960795 + 5808180 * 2 ^ 59
def prefixEnd_5808180 : Nat := 4983230072969 + 3 ^ 40 * 5808180 * 2
def baseEnd_5808180 : Nat := 2982388067831190702738673

theorem tailTrace_5808180 : CollatzResearch.WordTrace tailWord_5808180 prefixEnd_5808180 2982388067831190702738673 := by
  unfold tailWord_5808180
  simp only [CollatzResearch.WordTrace]
  refine ⟨105920864048981646507642997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141227818731975528676857329 105920864048981646507642997)
  ·
    refine ⟨9930081004592029360091531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105920864048981646507642997 9930081004592029360091531)
    ·
      refine ⟨14895121506888044040137297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9930081004592029360091531 14895121506888044040137297)
      ·
        refine ⟨11171341130166033030102973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14895121506888044040137297 11171341130166033030102973)
        ·
          refine ⟨4189252923812262386288615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11171341130166033030102973 4189252923812262386288615)
          ·
            refine ⟨6283879385718393579432923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189252923812262386288615 6283879385718393579432923)
            ·
              refine ⟨9425819078577590369149385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6283879385718393579432923 9425819078577590369149385)
              ·
                refine ⟨7069364308933192776862039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9425819078577590369149385 7069364308933192776862039)
                ·
                  refine ⟨10604046463399789165293059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069364308933192776862039 10604046463399789165293059)
                  ·
                    refine ⟨15906069695099683747939589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10604046463399789165293059 15906069695099683747939589)
                    ·
                      refine ⟨2982388067831190702738673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15906069695099683747939589 2982388067831190702738673)
                      ·
                        rfl

theorem cell23_5808180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_5808180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808180 prefixEnd_5808180 := by exact prefixLift 5808180
  have htrace : WordTrace (prefixWord ++ tailWord_5808180) baseStart_5808180 baseEnd_5808180 := by
    simpa [prefixWord, tailWord_5808180, baseEnd_5808180] using wordTrace_append hprefix tailTrace_5808180
  have hstable : (prefixWord ++ tailWord_5808180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808180).length < 2 ^ (prefixWord ++ tailWord_5808180).sum := by decide
  have hdescent : baseEnd_5808180 < baseStart_5808180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808195 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 8]
def baseStart_5808195 : Nat := 118140960795 + 5808195 * 2 ^ 59
def prefixEnd_5808195 : Nat := 4983230072969 + 3 ^ 40 * 5808195 * 2
def baseEnd_5808195 : Nat := 994131923347002714683701

theorem tailTrace_5808195 : CollatzResearch.WordTrace tailWord_5808195 prefixEnd_5808195 994131923347002714683701 := by
  unfold tailWord_5808195
  simp only [CollatzResearch.WordTrace]
  refine ⟨211842275192908950577082039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141228183461939300384721359 211842275192908950577082039)
  ·
    refine ⟨317763412789363425865623059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211842275192908950577082039 317763412789363425865623059)
    ·
      refine ⟨476645119184045138798434589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317763412789363425865623059 476645119184045138798434589)
      ·
        refine ⟨178741919694016927049412971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476645119184045138798434589 178741919694016927049412971)
        ·
          refine ⟨268112879541025390574119457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178741919694016927049412971 268112879541025390574119457)
          ·
            refine ⟨201084659655769042930589593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268112879541025390574119457 201084659655769042930589593)
            ·
              refine ⟨150813494741826782197942195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201084659655769042930589593 150813494741826782197942195)
              ·
                refine ⟨226220242112740173296913293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150813494741826782197942195 226220242112740173296913293)
                ·
                  refine ⟨84832590792277564986342485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226220242112740173296913293 84832590792277564986342485)
                  ·
                    refine ⟨994131923347002714683701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84832590792277564986342485 994131923347002714683701)
                    ·
                      rfl

theorem cell23_5808195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_5808195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808195 prefixEnd_5808195 := by exact prefixLift 5808195
  have htrace : WordTrace (prefixWord ++ tailWord_5808195) baseStart_5808195 baseEnd_5808195 := by
    simpa [prefixWord, tailWord_5808195, baseEnd_5808195] using wordTrace_append hprefix tailTrace_5808195
  have hstable : (prefixWord ++ tailWord_5808195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808195).length < 2 ^ (prefixWord ++ tailWord_5808195).sum := by decide
  have hdescent : baseEnd_5808195 < baseStart_5808195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808212 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_5808212 : Nat := 118140960795 + 5808212 * 2 ^ 59
def prefixEnd_5808212 : Nat := 4983230072969 + 3 ^ 40 * 5808212 * 2
def baseEnd_5808212 : Nat := 994134833070711525846175

theorem tailTrace_5808212 : CollatzResearch.WordTrace tailWord_5808212 prefixEnd_5808212 994134833070711525846175 := by
  unfold tailWord_5808212
  simp only [CollatzResearch.WordTrace]
  refine ⟨105921447616923681240225445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141228596822564908320300593 105921447616923681240225445)
  ·
    refine ⟨19860271428173190232542271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105921447616923681240225445 19860271428173190232542271)
    ·
      refine ⟨29790407142259785348813407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19860271428173190232542271 29790407142259785348813407)
      ·
        refine ⟨44685610713389678023220111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29790407142259785348813407 44685610713389678023220111)
        ·
          refine ⟨67028416070084517034830167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44685610713389678023220111 67028416070084517034830167)
          ·
            refine ⟨100542624105126775552245251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67028416070084517034830167 100542624105126775552245251)
            ·
              refine ⟨150813936157690163328367877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100542624105126775552245251 150813936157690163328367877)
              ·
                refine ⟨28277613029566905624068977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150813936157690163328367877 28277613029566905624068977)
                ·
                  refine ⟨21208209772175179218051733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28277613029566905624068977 21208209772175179218051733)
                  ·
                    refine ⟨994134833070711525846175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21208209772175179218051733 994134833070711525846175)
                    ·
                      rfl

theorem cell23_5808212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_5808212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808212 prefixEnd_5808212 := by exact prefixLift 5808212
  have htrace : WordTrace (prefixWord ++ tailWord_5808212) baseStart_5808212 baseEnd_5808212 := by
    simpa [prefixWord, tailWord_5808212, baseEnd_5808212] using wordTrace_append hprefix tailTrace_5808212
  have hstable : (prefixWord ++ tailWord_5808212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808212).length < 2 ^ (prefixWord ++ tailWord_5808212).sum := by decide
  have hdescent : baseEnd_5808212 < baseStart_5808212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808214 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5808214 : Nat := 118140960795 + 5808214 * 2 ^ 59
def prefixEnd_5808214 : Nat := 4983230072969 + 3 ^ 40 * 5808214 * 2
def baseEnd_5808214 : Nat := 2982405526173443569713517

theorem tailTrace_5808214 : CollatzResearch.WordTrace tailWord_5808214 prefixEnd_5808214 2982405526173443569713517 := by
  unfold tailWord_5808214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240185511240007301376481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141228645453226744548015797 13240185511240007301376481)
  ·
    refine ⟨9930139133430005476032361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13240185511240007301376481 9930139133430005476032361)
    ·
      refine ⟨7447604350072504107024271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9930139133430005476032361 7447604350072504107024271)
      ·
        refine ⟨11171406525108756160536407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447604350072504107024271 11171406525108756160536407)
        ·
          refine ⟨16757109787663134240804611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11171406525108756160536407 16757109787663134240804611)
          ·
            refine ⟨25135664681494701361206917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16757109787663134240804611 25135664681494701361206917)
            ·
              refine ⟨4712937127780256505226297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25135664681494701361206917 4712937127780256505226297)
              ·
                refine ⟨3534702845835192378919723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712937127780256505226297 3534702845835192378919723)
                ·
                  refine ⟨5302054268752788568379585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3534702845835192378919723 5302054268752788568379585)
                  ·
                    refine ⟨3976540701564591426284689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302054268752788568379585 3976540701564591426284689)
                    ·
                      refine ⟨2982405526173443569713517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976540701564591426284689 2982405526173443569713517)
                      ·
                        rfl

theorem cell23_5808214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5808214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808214 prefixEnd_5808214 := by exact prefixLift 5808214
  have htrace : WordTrace (prefixWord ++ tailWord_5808214) baseStart_5808214 baseEnd_5808214 := by
    simpa [prefixWord, tailWord_5808214, baseEnd_5808214] using wordTrace_append hprefix tailTrace_5808214
  have hstable : (prefixWord ++ tailWord_5808214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808214).length < 2 ^ (prefixWord ++ tailWord_5808214).sum := by decide
  have hdescent : baseEnd_5808214 < baseStart_5808214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808236 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 1, 4, 2]
def baseStart_5808236 : Nat := 118140960795 + 5808236 * 2 ^ 59
def prefixEnd_5808236 : Nat := 4983230072969 + 3 ^ 40 * 5808236 * 2
def baseEnd_5808236 : Nat := 2982416822747842483638415

theorem tailTrace_5808236 : CollatzResearch.WordTrace tailWord_5808236 prefixEnd_5808236 2982416822747842483638415 := by
  unfold tailWord_5808236
  simp only [CollatzResearch.WordTrace]
  refine ⟨105921885292880207289662281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141229180390506943052883041 105921885292880207289662281)
  ·
    refine ⟨79441413969660155467246711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105921885292880207289662281 79441413969660155467246711)
    ·
      refine ⟨119162120954490233200870067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79441413969660155467246711 119162120954490233200870067)
      ·
        refine ⟨178743181431735349801305101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119162120954490233200870067 178743181431735349801305101)
        ·
          refine ⟨67028693036900756175489413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178743181431735349801305101 67028693036900756175489413)
          ·
            refine ⟨12567879944418891782904265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67028693036900756175489413 12567879944418891782904265)
            ·
              refine ⟨9425909958314168837178199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12567879944418891782904265 9425909958314168837178199)
              ·
                refine ⟨14138864937471253255767299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9425909958314168837178199 14138864937471253255767299)
                ·
                  refine ⟨21208297406206879883650949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14138864937471253255767299 21208297406206879883650949)
                  ·
                    refine ⟨3976555763663789978184553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21208297406206879883650949 3976555763663789978184553)
                    ·
                      refine ⟨2982416822747842483638415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976555763663789978184553 2982416822747842483638415)
                      ·
                        rfl

theorem cell23_5808236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 4, 2].length) (baseStart_5808236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808236 prefixEnd_5808236 := by exact prefixLift 5808236
  have htrace : WordTrace (prefixWord ++ tailWord_5808236) baseStart_5808236 baseEnd_5808236 := by
    simpa [prefixWord, tailWord_5808236, baseEnd_5808236] using wordTrace_append hprefix tailTrace_5808236
  have hstable : (prefixWord ++ tailWord_5808236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808236).length < 2 ^ (prefixWord ++ tailWord_5808236).sum := by decide
  have hdescent : baseEnd_5808236 < baseStart_5808236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808242 : List Nat := [3, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_5808242 : Nat := 118140960795 + 5808242 * 2 ^ 59
def prefixEnd_5808242 : Nat := 4983230072969 + 3 ^ 40 * 5808242 * 2
def baseEnd_5808242 : Nat := 331379989292418828907043

theorem tailTrace_5808242 : CollatzResearch.WordTrace tailWord_5808242 prefixEnd_5808242 331379989292418828907043 := by
  unfold tailWord_5808242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52960997355934669401010745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141229326282492451736028653 52960997355934669401010745)
  ·
    refine ⟨39720748016951002050758059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52960997355934669401010745 39720748016951002050758059)
    ·
      refine ⟨59581122025426503076137089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39720748016951002050758059 59581122025426503076137089)
      ·
        refine ⟨44685841519069877307102817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59581122025426503076137089 44685841519069877307102817)
        ·
          refine ⟨33514381139302407980327113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44685841519069877307102817 33514381139302407980327113)
          ·
            refine ⟨25135785854476805985245335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33514381139302407980327113 25135785854476805985245335)
            ·
              refine ⟨37703678781715208977868003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25135785854476805985245335 37703678781715208977868003)
              ·
                refine ⟨56555518172572813466802005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37703678781715208977868003 56555518172572813466802005)
                ·
                  refine ⟨331379989292418828907043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56555518172572813466802005 331379989292418828907043)
                  ·
                    rfl

theorem cell23_5808242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_5808242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808242 prefixEnd_5808242 := by exact prefixLift 5808242
  have htrace : WordTrace (prefixWord ++ tailWord_5808242) baseStart_5808242 baseEnd_5808242 := by
    simpa [prefixWord, tailWord_5808242, baseEnd_5808242] using wordTrace_append hprefix tailTrace_5808242
  have hstable : (prefixWord ++ tailWord_5808242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808242).length < 2 ^ (prefixWord ++ tailWord_5808242).sum := by decide
  have hdescent : baseEnd_5808242 < baseStart_5808242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808257 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5808257 : Nat := 118140960795 + 5808257 * 2 ^ 59
def prefixEnd_5808257 : Nat := 4983230072969 + 3 ^ 40 * 5808257 * 2
def baseEnd_5808257 : Nat := 2982427605841586901475819

theorem tailTrace_5808257 : CollatzResearch.WordTrace tailWord_5808257 prefixEnd_5808257 2982427605841586901475819 := by
  unfold tailWord_5808257
  simp only [CollatzResearch.WordTrace]
  refine ⟨211844536518684335165839025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141229691012456223443892683 211844536518684335165839025)
  ·
    refine ⟨158883402389013251374379269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211844536518684335165839025 158883402389013251374379269)
    ·
      refine ⟨29790637947939984632696113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158883402389013251374379269 29790637947939984632696113)
      ·
        refine ⟨22342978460954988474522085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29790637947939984632696113 22342978460954988474522085)
        ·
          refine ⟨4189308461429060338972891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22342978460954988474522085 4189308461429060338972891)
          ·
            refine ⟨6283962692143590508459337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189308461429060338972891 6283962692143590508459337)
            ·
              refine ⟨4712972019107692881344503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283962692143590508459337 4712972019107692881344503)
              ·
                refine ⟨7069458028661539322016755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712972019107692881344503 7069458028661539322016755)
                ·
                  refine ⟨10604187042992308983025133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069458028661539322016755 10604187042992308983025133)
                  ·
                    refine ⟨3976570141122115868634425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10604187042992308983025133 3976570141122115868634425)
                    ·
                      refine ⟨2982427605841586901475819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976570141122115868634425 2982427605841586901475819)
                      ·
                        rfl

theorem cell23_5808257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5808257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808257 prefixEnd_5808257 := by exact prefixLift 5808257
  have htrace : WordTrace (prefixWord ++ tailWord_5808257) baseStart_5808257 baseEnd_5808257 := by
    simpa [prefixWord, tailWord_5808257, baseEnd_5808257] using wordTrace_append hprefix tailTrace_5808257
  have hstable : (prefixWord ++ tailWord_5808257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808257).length < 2 ^ (prefixWord ++ tailWord_5808257).sum := by decide
  have hdescent : baseEnd_5808257 < baseStart_5808257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808259 : List Nat := [1, 1, 1, 3, 3, 3, 1, 5, 5]
def baseStart_5808259 : Nat := 118140960795 + 5808259 * 2 ^ 59
def prefixEnd_5808259 : Nat := 4983230072969 + 3 ^ 40 * 5808259 * 2
def baseEnd_5808259 : Nat := 331380959200321765961201

theorem tailTrace_5808259 : CollatzResearch.WordTrace tailWord_5808259 prefixEnd_5808259 331380959200321765961201 := by
  unfold tailWord_5808259
  simp only [CollatzResearch.WordTrace]
  refine ⟨211844609464677089507411831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141229739643118059671607887 211844609464677089507411831)
  ·
    refine ⟨317766914197015634261117747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211844609464677089507411831 317766914197015634261117747)
    ·
      refine ⟨476650371295523451391676621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317766914197015634261117747 476650371295523451391676621)
      ·
        refine ⟨178743889235821294271878733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476650371295523451391676621 178743889235821294271878733)
        ·
          refine ⟨67028958463432985351954525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178743889235821294271878733 67028958463432985351954525)
          ·
            refine ⟨25135859423787369506982947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67028958463432985351954525 25135859423787369506982947)
            ·
              refine ⟨37703789135681054260474421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25135859423787369506982947 37703789135681054260474421)
              ·
                refine ⟨3534730231470098836919477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37703789135681054260474421 3534730231470098836919477)
                ·
                  refine ⟨331380959200321765961201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534730231470098836919477 331380959200321765961201)
                  ·
                    rfl

theorem cell23_5808259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 5, 5].length) (baseStart_5808259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808259 prefixEnd_5808259 := by exact prefixLift 5808259
  have htrace : WordTrace (prefixWord ++ tailWord_5808259) baseStart_5808259 baseEnd_5808259 := by
    simpa [prefixWord, tailWord_5808259, baseEnd_5808259] using wordTrace_append hprefix tailTrace_5808259
  have hstable : (prefixWord ++ tailWord_5808259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808259).length < 2 ^ (prefixWord ++ tailWord_5808259).sum := by decide
  have hdescent : baseEnd_5808259 < baseStart_5808259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808272 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_5808272 : Nat := 118140960795 + 5808272 * 2 ^ 59
def prefixEnd_5808272 : Nat := 4983230072969 + 3 ^ 40 * 5808272 * 2
def baseEnd_5808272 : Nat := 994145102683801447596083

theorem tailTrace_5808272 : CollatzResearch.WordTrace tailWord_5808272 prefixEnd_5808272 994145102683801447596083 := by
  unfold tailWord_5808272
  simp only [CollatzResearch.WordTrace]
  refine ⟨105922541806814996363817535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141230055742419995151756713 105922541806814996363817535)
  ·
    refine ⟨158883812710222494545726303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105922541806814996363817535 158883812710222494545726303)
    ·
      refine ⟨238325719065333741818589455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158883812710222494545726303 238325719065333741818589455)
      ·
        refine ⟨357488578598000612727884183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238325719065333741818589455 357488578598000612727884183)
        ·
          refine ⟨536232867897000919091826275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357488578598000612727884183 536232867897000919091826275)
          ·
            refine ⟨804349301845501378637739413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536232867897000919091826275 804349301845501378637739413)
            ·
              refine ⟨37703873524007877123644035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 804349301845501378637739413 37703873524007877123644035)
              ·
                refine ⟨56555810286011815685466053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37703873524007877123644035 56555810286011815685466053)
                ·
                  refine ⟨10604214428627215441024885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56555810286011815685466053 10604214428627215441024885)
                  ·
                    refine ⟨994145102683801447596083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10604214428627215441024885 994145102683801447596083)
                    ·
                      rfl

theorem cell23_5808272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_5808272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808272 prefixEnd_5808272 := by exact prefixLift 5808272
  have htrace : WordTrace (prefixWord ++ tailWord_5808272) baseStart_5808272 baseEnd_5808272 := by
    simpa [prefixWord, tailWord_5808272, baseEnd_5808272] using wordTrace_append hprefix tailTrace_5808272
  have hstable : (prefixWord ++ tailWord_5808272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808272).length < 2 ^ (prefixWord ++ tailWord_5808272).sum := by decide
  have hdescent : baseEnd_5808272 < baseStart_5808272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808416 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4]
def baseStart_5808416 : Nat := 118140960795 + 5808416 * 2 ^ 59
def prefixEnd_5808416 : Nat := 4983230072969 + 3 ^ 40 * 5808416 * 2
def baseEnd_5808416 : Nat := 2982509249265651779387587

theorem tailTrace_5808416 : CollatzResearch.WordTrace tailWord_5808416 prefixEnd_5808416 2982509249265651779387587 := by
  unfold tailWord_5808416
  simp only [CollatzResearch.WordTrace]
  refine ⟨105925167862554152660438551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141233557150072203547251401 105925167862554152660438551)
  ·
    refine ⟨158887751793831228990657827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105925167862554152660438551 158887751793831228990657827)
    ·
      refine ⟨238331627690746843485986741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158887751793831228990657827 238331627690746843485986741)
      ·
        refine ⟨22343590096007516576811257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238331627690746843485986741 22343590096007516576811257)
        ·
          refine ⟨16757692572005637432608443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22343590096007516576811257 16757692572005637432608443)
          ·
            refine ⟨25136538858008456148912665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16757692572005637432608443 25136538858008456148912665)
            ·
              refine ⟨18852404143506342111684499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25136538858008456148912665 18852404143506342111684499)
              ·
                refine ⟨28278606215259513167526749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18852404143506342111684499 28278606215259513167526749)
                ·
                  refine ⟨10604477330722317437822531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28278606215259513167526749 10604477330722317437822531)
                  ·
                    refine ⟨15906715996083476156733797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10604477330722317437822531 15906715996083476156733797)
                    ·
                      refine ⟨2982509249265651779387587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15906715996083476156733797 2982509249265651779387587)
                      ·
                        rfl

theorem cell23_5808416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_5808416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808416 prefixEnd_5808416 := by exact prefixLift 5808416
  have htrace : WordTrace (prefixWord ++ tailWord_5808416) baseStart_5808416 baseEnd_5808416 := by
    simpa [prefixWord, tailWord_5808416, baseEnd_5808416] using wordTrace_append hprefix tailTrace_5808416
  have hstable : (prefixWord ++ tailWord_5808416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808416).length < 2 ^ (prefixWord ++ tailWord_5808416).sum := by decide
  have hdescent : baseEnd_5808416 < baseStart_5808416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808420 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_5808420 : Nat := 118140960795 + 5808420 * 2 ^ 59
def prefixEnd_5808420 : Nat := 4983230072969 + 3 ^ 40 * 5808420 * 2
def baseEnd_5808420 : Nat := 2982511303188269763737569

theorem tailTrace_5808420 : CollatzResearch.WordTrace tailWord_5808420 prefixEnd_5808420 2982511303188269763737569 := by
  unfold tailWord_5808420
  simp only [CollatzResearch.WordTrace]
  refine ⟨105925240808546907002011357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141233654411395876002681809 105925240808546907002011357)
  ·
    refine ⟨39721965303205090125754259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105925240808546907002011357 39721965303205090125754259)
    ·
      refine ⟨59582947954807635188631389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39721965303205090125754259 59582947954807635188631389)
      ·
        refine ⟨22343605483052863195736771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59582947954807635188631389 22343605483052863195736771)
        ·
          refine ⟨33515408224579294793605157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22343605483052863195736771 33515408224579294793605157)
          ·
            refine ⟨6284139042108617773800967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33515408224579294793605157 6284139042108617773800967)
            ·
              refine ⟨9426208563162926660701451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284139042108617773800967 9426208563162926660701451)
              ·
                refine ⟨14139312844744389991052177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426208563162926660701451 14139312844744389991052177)
                ·
                  refine ⟨10604484633558292493289133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14139312844744389991052177 10604484633558292493289133)
                  ·
                    refine ⟨3976681737584359684983425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10604484633558292493289133 3976681737584359684983425)
                    ·
                      refine ⟨2982511303188269763737569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976681737584359684983425 2982511303188269763737569)
                      ·
                        rfl

theorem cell23_5808420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_5808420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808420 prefixEnd_5808420 := by exact prefixLift 5808420
  have htrace : WordTrace (prefixWord ++ tailWord_5808420) baseStart_5808420 baseEnd_5808420 := by
    simpa [prefixWord, tailWord_5808420, baseEnd_5808420] using wordTrace_append hprefix tailTrace_5808420
  have hstable : (prefixWord ++ tailWord_5808420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808420).length < 2 ^ (prefixWord ++ tailWord_5808420).sum := by decide
  have hdescent : baseEnd_5808420 < baseStart_5808420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808430 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_5808430 : Nat := 118140960795 + 5808430 * 2 ^ 59
def prefixEnd_5808430 : Nat := 4983230072969 + 3 ^ 40 * 5808430 * 2
def baseEnd_5808430 : Nat := 994172145998271574870841

theorem tailTrace_5808430 : CollatzResearch.WordTrace tailWord_5808430 prefixEnd_5808430 994172145998271574870841 := by
  unfold tailWord_5808430
  simp only [CollatzResearch.WordTrace]
  refine ⟨26481355793382198213985843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141233897564705057141257829 26481355793382198213985843)
  ·
    refine ⟨39722033690073297320978765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26481355793382198213985843 39722033690073297320978765)
    ·
      refine ⟨14895762633777486495367037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39722033690073297320978765 14895762633777486495367037)
      ·
        refine ⟨5585910987666557435762639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14895762633777486495367037 5585910987666557435762639)
        ·
          refine ⟨8378866481499836153643959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5585910987666557435762639 8378866481499836153643959)
          ·
            refine ⟨12568299722249754230465939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378866481499836153643959 12568299722249754230465939)
            ·
              refine ⟨18852449583374631345698909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568299722249754230465939 18852449583374631345698909)
              ·
                refine ⟨7069668593765486754637091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18852449583374631345698909 7069668593765486754637091)
                ·
                  refine ⟨10604502890648230131955637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069668593765486754637091 10604502890648230131955637)
                  ·
                    refine ⟨994172145998271574870841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10604502890648230131955637 994172145998271574870841)
                    ·
                      rfl

theorem cell23_5808430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_5808430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808430 prefixEnd_5808430 := by exact prefixLift 5808430
  have htrace : WordTrace (prefixWord ++ tailWord_5808430) baseStart_5808430 baseEnd_5808430 := by
    simpa [prefixWord, tailWord_5808430, baseEnd_5808430] using wordTrace_append hprefix tailTrace_5808430
  have hstable : (prefixWord ++ tailWord_5808430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808430).length < 2 ^ (prefixWord ++ tailWord_5808430).sum := by decide
  have hdescent : baseEnd_5808430 < baseStart_5808430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808433 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 4]
def baseStart_5808433 : Nat := 118140960795 + 5808433 * 2 ^ 59
def prefixEnd_5808433 : Nat := 4983230072969 + 3 ^ 40 * 5808433 * 2
def baseEnd_5808433 : Nat := 2982517978436778212875009

theorem tailTrace_5808433 : CollatzResearch.WordTrace tailWord_5808433 prefixEnd_5808433 2982517978436778212875009 := by
  unfold tailWord_5808433
  simp only [CollatzResearch.WordTrace]
  refine ⟨211850955766046717224245953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141233970510697811482830635 211850955766046717224245953)
  ·
    refine ⟨158888216824535037918184465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211850955766046717224245953 158888216824535037918184465)
    ·
      refine ⟨119166162618401278438638349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158888216824535037918184465 119166162618401278438638349)
      ·
        refine ⟨44687310981900479414489381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119166162618401278438638349 44687310981900479414489381)
        ·
          refine ⟨8378870809106339890216759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44687310981900479414489381 8378870809106339890216759)
          ·
            refine ⟨12568306213659509835325139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378870809106339890216759 12568306213659509835325139)
            ·
              refine ⟨18852459320489264752987709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568306213659509835325139 18852459320489264752987709)
              ·
                refine ⟨7069672245183474282370391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18852459320489264752987709 7069672245183474282370391)
                ·
                  refine ⟨10604508367775211423555587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069672245183474282370391 10604508367775211423555587)
                  ·
                    refine ⟨15906762551662817135333381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10604508367775211423555587 15906762551662817135333381)
                    ·
                      refine ⟨2982517978436778212875009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15906762551662817135333381 2982517978436778212875009)
                      ·
                        rfl

theorem cell23_5808433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_5808433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808433 prefixEnd_5808433 := by exact prefixLift 5808433
  have htrace : WordTrace (prefixWord ++ tailWord_5808433) baseStart_5808433 baseEnd_5808433 := by
    simpa [prefixWord, tailWord_5808433, baseEnd_5808433] using wordTrace_append hprefix tailTrace_5808433
  have hstable : (prefixWord ++ tailWord_5808433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808433).length < 2 ^ (prefixWord ++ tailWord_5808433).sum := by decide
  have hdescent : baseEnd_5808433 < baseStart_5808433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808479 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_5808479 : Nat := 118140960795 + 5808479 * 2 ^ 59
def prefixEnd_5808479 : Nat := 4983230072969 + 3 ^ 40 * 5808479 * 2
def baseEnd_5808479 : Nat := 2982541598546885032899797

theorem tailTrace_5808479 : CollatzResearch.WordTrace tailWord_5808479 prefixEnd_5808479 2982541598546885032899797 := by
  unfold tailWord_5808479
  simp only [CollatzResearch.WordTrace]
  refine ⟨211852633523880067080420491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141235089015920044720280327 211852633523880067080420491)
  ·
    refine ⟨317778950285820100620630737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211852633523880067080420491 317778950285820100620630737)
    ·
      refine ⟨238334212714365075465473053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317778950285820100620630737 238334212714365075465473053)
      ·
        refine ⟨89375329767886903299552395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238334212714365075465473053 89375329767886903299552395)
        ·
          refine ⟨134062994651830354949328593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89375329767886903299552395 134062994651830354949328593)
          ·
            refine ⟨100547245988872766211996445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134062994651830354949328593 100547245988872766211996445)
            ·
              refine ⟨37705217245827287329498667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100547245988872766211996445 37705217245827287329498667)
              ·
                refine ⟨56557825868740930994248001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37705217245827287329498667 56557825868740930994248001)
                ·
                  refine ⟨42418369401555698245686001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56557825868740930994248001 42418369401555698245686001)
                  ·
                    refine ⟨31813777051166773684264501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42418369401555698245686001 31813777051166773684264501)
                    ·
                      refine ⟨2982541598546885032899797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31813777051166773684264501 2982541598546885032899797)
                      ·
                        rfl

theorem cell23_5808479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_5808479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808479 prefixEnd_5808479 := by exact prefixLift 5808479
  have htrace : WordTrace (prefixWord ++ tailWord_5808479) baseStart_5808479 baseEnd_5808479 := by
    simpa [prefixWord, tailWord_5808479, baseEnd_5808479] using wordTrace_append hprefix tailTrace_5808479
  have hstable : (prefixWord ++ tailWord_5808479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808479).length < 2 ^ (prefixWord ++ tailWord_5808479).sum := by decide
  have hdescent : baseEnd_5808479 < baseStart_5808479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808506 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2]
def baseStart_5808506 : Nat := 118140960795 + 5808506 * 2 ^ 59
def prefixEnd_5808506 : Nat := 4983230072969 + 3 ^ 40 * 5808506 * 2
def baseEnd_5808506 : Nat := 2982555462524556427262173

theorem tailTrace_5808506 : CollatzResearch.WordTrace tailWord_5808506 prefixEnd_5808506 2982555462524556427262173 := by
  unfold tailWord_5808506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52963404573695562672913343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141235745529854833794435581 52963404573695562672913343)
  ·
    refine ⟨79445106860543344009370015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52963404573695562672913343 79445106860543344009370015)
    ·
      refine ⟨119167660290815016014055023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79445106860543344009370015 119167660290815016014055023)
      ·
        refine ⟨178751490436222524021082535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119167660290815016014055023 178751490436222524021082535)
        ·
          refine ⟨268127235654333786031623803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178751490436222524021082535 268127235654333786031623803)
          ·
            refine ⟨402190853481500679047435705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268127235654333786031623803 402190853481500679047435705)
            ·
              refine ⟨301643140111125509285576779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402190853481500679047435705 301643140111125509285576779)
              ·
                refine ⟨452464710166688263928365169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301643140111125509285576779 452464710166688263928365169)
                ·
                  refine ⟨339348532625016197946273877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452464710166688263928365169 339348532625016197946273877)
                  ·
                    refine ⟨3976740616699408569682897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 339348532625016197946273877 3976740616699408569682897)
                    ·
                      refine ⟨2982555462524556427262173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976740616699408569682897 2982555462524556427262173)
                      ·
                        rfl

theorem cell23_5808506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_5808506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808506 prefixEnd_5808506 := by exact prefixLift 5808506
  have htrace : WordTrace (prefixWord ++ tailWord_5808506) baseStart_5808506 baseEnd_5808506 := by
    simpa [prefixWord, tailWord_5808506, baseEnd_5808506] using wordTrace_append hprefix tailTrace_5808506
  have hstable : (prefixWord ++ tailWord_5808506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808506).length < 2 ^ (prefixWord ++ tailWord_5808506).sum := by decide
  have hdescent : baseEnd_5808506 < baseStart_5808506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808534 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5808534 : Nat := 118140960795 + 5808534 * 2 ^ 59
def prefixEnd_5808534 : Nat := 4983230072969 + 3 ^ 40 * 5808534 * 2
def baseEnd_5808534 : Nat := 2982569839982882317712045

theorem tailTrace_5808534 : CollatzResearch.WordTrace tailWord_5808534 prefixEnd_5808534 2982569839982882317712045 := by
  unfold tailWord_5808534
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240914971167550717104541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141236426359120540982448437 13240914971167550717104541)
  ·
    refine ⟨4965343114187831518914203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13240914971167550717104541 4965343114187831518914203)
    ·
      refine ⟨7448014671281747278371305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4965343114187831518914203 7448014671281747278371305)
      ·
        refine ⟨5586011003461310458778479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7448014671281747278371305 5586011003461310458778479)
        ·
          refine ⟨8379016505191965688167719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5586011003461310458778479 8379016505191965688167719)
          ·
            refine ⟨12568524757787948532251579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379016505191965688167719 12568524757787948532251579)
            ·
              refine ⟨18852787136681922798377369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568524757787948532251579 18852787136681922798377369)
              ·
                refine ⟨14139590352511442098783027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18852787136681922798377369 14139590352511442098783027)
                ·
                  refine ⟨21209385528767163148174541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14139590352511442098783027 21209385528767163148174541)
                  ·
                    refine ⟨7953519573287686180565453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21209385528767163148174541 7953519573287686180565453)
                    ·
                      refine ⟨2982569839982882317712045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7953519573287686180565453 2982569839982882317712045)
                      ·
                        rfl

theorem cell23_5808534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5808534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808534 prefixEnd_5808534 := by exact prefixLift 5808534
  have htrace : WordTrace (prefixWord ++ tailWord_5808534) baseStart_5808534 baseEnd_5808534 := by
    simpa [prefixWord, tailWord_5808534, baseEnd_5808534] using wordTrace_append hprefix tailTrace_5808534
  have hstable : (prefixWord ++ tailWord_5808534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808534).length < 2 ^ (prefixWord ++ tailWord_5808534).sum := by decide
  have hdescent : baseEnd_5808534 < baseStart_5808534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808556 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_5808556 : Nat := 118140960795 + 5808556 * 2 ^ 59
def prefixEnd_5808556 : Nat := 4983230072969 + 3 ^ 40 * 5808556 * 2
def baseEnd_5808556 : Nat := 2982581136557281231636943

theorem tailTrace_5808556 : CollatzResearch.WordTrace tailWord_5808556 prefixEnd_5808556 2982581136557281231636943 := by
  unfold tailWord_5808556
  simp only [CollatzResearch.WordTrace]
  refine ⟨105927720972300554615486761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141236961296400739487315681 105927720972300554615486761)
  ·
    refine ⟨79445790729225415961615071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105927720972300554615486761 79445790729225415961615071)
    ·
      refine ⟨119168686093838123942422607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79445790729225415961615071 119168686093838123942422607)
      ·
        refine ⟨178753029140757185913633911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119168686093838123942422607 178753029140757185913633911)
        ·
          refine ⟨268129543711135778870450867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178753029140757185913633911 268129543711135778870450867)
          ·
            refine ⟨402194315566703668305676301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268129543711135778870450867 402194315566703668305676301)
            ·
              refine ⟨150822868337513875614628613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402194315566703668305676301 150822868337513875614628613)
              ·
                refine ⟨28279287813283851677742865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150822868337513875614628613 28279287813283851677742865)
                ·
                  refine ⟨21209465859962888758307149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28279287813283851677742865 21209465859962888758307149)
                  ·
                    refine ⟨7953549697486083284365181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21209465859962888758307149 7953549697486083284365181)
                    ·
                      refine ⟨2982581136557281231636943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7953549697486083284365181 2982581136557281231636943)
                      ·
                        rfl

theorem cell23_5808556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_5808556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808556 prefixEnd_5808556 := by exact prefixLift 5808556
  have htrace : WordTrace (prefixWord ++ tailWord_5808556) baseStart_5808556 baseEnd_5808556 := by
    simpa [prefixWord, tailWord_5808556, baseEnd_5808556] using wordTrace_append hprefix tailTrace_5808556
  have hstable : (prefixWord ++ tailWord_5808556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808556).length < 2 ^ (prefixWord ++ tailWord_5808556).sum := by decide
  have hdescent : baseEnd_5808556 < baseStart_5808556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808559 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 7]
def baseStart_5808559 : Nat := 118140960795 + 5808559 * 2 ^ 59
def prefixEnd_5808559 : Nat := 4983230072969 + 3 ^ 40 * 5808559 * 2
def baseEnd_5808559 : Nat := 994194225666414906633143

theorem tailTrace_5808559 : CollatzResearch.WordTrace tailWord_5808559 prefixEnd_5808559 994194225666414906633143 := by
  unfold tailWord_5808559
  simp only [CollatzResearch.WordTrace]
  refine ⟨211855551363590240743332731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141237034242393493828888487 211855551363590240743332731)
  ·
    refine ⟨317783327045385361114999097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211855551363590240743332731 317783327045385361114999097)
    ·
      refine ⟨238337495284039020836249323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317783327045385361114999097 238337495284039020836249323)
      ·
        refine ⟨357506242926058531254373985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238337495284039020836249323 357506242926058531254373985)
        ·
          refine ⟨268129682194543898440780489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357506242926058531254373985 268129682194543898440780489)
          ·
            refine ⟨201097261645907923830585367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268129682194543898440780489 201097261645907923830585367)
            ·
              refine ⟨301645892468861885745878051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201097261645907923830585367 301645892468861885745878051)
              ·
                refine ⟨452468838703292828618817077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301645892468861885745878051 452468838703292828618817077)
                ·
                  refine ⟨42418953628433702683014101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 452468838703292828618817077 42418953628433702683014101)
                  ·
                    refine ⟨994194225666414906633143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42418953628433702683014101 994194225666414906633143)
                    ·
                      rfl

theorem cell23_5808559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_5808559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808559 prefixEnd_5808559 := by exact prefixLift 5808559
  have htrace : WordTrace (prefixWord ++ tailWord_5808559) baseStart_5808559 baseEnd_5808559 := by
    simpa [prefixWord, tailWord_5808559, baseEnd_5808559] using wordTrace_append hprefix tailTrace_5808559
  have hstable : (prefixWord ++ tailWord_5808559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808559).length < 2 ^ (prefixWord ++ tailWord_5808559).sum := by decide
  have hdescent : baseEnd_5808559 < baseStart_5808559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808573 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_5808573 : Nat := 118140960795 + 5808573 * 2 ^ 59
def prefixEnd_5808573 : Nat := 4983230072969 + 3 ^ 40 * 5808573 * 2
def baseEnd_5808573 : Nat := 2982589865728407665124365

theorem tailTrace_5808573 : CollatzResearch.WordTrace tailWord_5808573 prefixEnd_5808573 2982589865728407665124365 := by
  unfold tailWord_5808573
  simp only [CollatzResearch.WordTrace]
  refine ⟨211856061985539521134342373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141237374657026347422894915 211856061985539521134342373)
  ·
    refine ⟨39723011622288660212689195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211856061985539521134342373 39723011622288660212689195)
    ·
      refine ⟨59584517433432990319033793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39723011622288660212689195 59584517433432990319033793)
      ·
        refine ⟨44688388075074742739275345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59584517433432990319033793 44688388075074742739275345)
        ·
          refine ⟨33516291056306057054456509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44688388075074742739275345 33516291056306057054456509)
          ·
            refine ⟨12568609146114771395421191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33516291056306057054456509 12568609146114771395421191)
            ·
              refine ⟨18852913719172157093131787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12568609146114771395421191 18852913719172157093131787)
              ·
                refine ⟨28279370578758235639697681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18852913719172157093131787 28279370578758235639697681)
                ·
                  refine ⟨21209527934068676729773261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28279370578758235639697681 21209527934068676729773261)
                  ·
                    refine ⟨7953572975275753773664973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21209527934068676729773261 7953572975275753773664973)
                    ·
                      refine ⟨2982589865728407665124365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7953572975275753773664973 2982589865728407665124365)
                      ·
                        rfl

theorem cell23_5808573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_5808573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808573 prefixEnd_5808573 := by exact prefixLift 5808573
  have htrace : WordTrace (prefixWord ++ tailWord_5808573) baseStart_5808573 baseEnd_5808573 := by
    simpa [prefixWord, tailWord_5808573, baseEnd_5808573] using wordTrace_append hprefix tailTrace_5808573
  have hstable : (prefixWord ++ tailWord_5808573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808573).length < 2 ^ (prefixWord ++ tailWord_5808573).sum := by decide
  have hdescent : baseEnd_5808573 < baseStart_5808573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808630 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5808630 : Nat := 118140960795 + 5808630 * 2 ^ 59
def prefixEnd_5808630 : Nat := 4983230072969 + 3 ^ 40 * 5808630 * 2
def baseEnd_5808630 : Nat := 2982619134125713942111603

theorem tailTrace_5808630 : CollatzResearch.WordTrace tailWord_5808630 prefixEnd_5808630 2982619134125713942111603 := by
  unfold tailWord_5808630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241133809145813741822959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141238760630888679912778229 13241133809145813741822959)
  ·
    refine ⟨19861700713718720612734439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241133809145813741822959 19861700713718720612734439)
    ·
      refine ⟨29792551070578080919101659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19861700713718720612734439 29792551070578080919101659)
      ·
        refine ⟨44688826605867121378652489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29792551070578080919101659 44688826605867121378652489)
        ·
          refine ⟨33516619954400341033989367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44688826605867121378652489 33516619954400341033989367)
          ·
            refine ⟨50274929931600511550984051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33516619954400341033989367 50274929931600511550984051)
            ·
              refine ⟨75412394897400767326476077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50274929931600511550984051 75412394897400767326476077)
              ·
                refine ⟨28279648086525287747428529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75412394897400767326476077 28279648086525287747428529)
                ·
                  refine ⟨21209736064893965810571397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28279648086525287747428529 21209736064893965810571397)
                  ·
                    refine ⟨3976825512167618589482137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21209736064893965810571397 3976825512167618589482137)
                    ·
                      refine ⟨2982619134125713942111603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976825512167618589482137 2982619134125713942111603)
                      ·
                        rfl

theorem cell23_5808630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5808630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808630 prefixEnd_5808630 := by exact prefixLift 5808630
  have htrace : WordTrace (prefixWord ++ tailWord_5808630) baseStart_5808630 baseEnd_5808630 := by
    simpa [prefixWord, tailWord_5808630, baseEnd_5808630] using wordTrace_append hprefix tailTrace_5808630
  have hstable : (prefixWord ++ tailWord_5808630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808630).length < 2 ^ (prefixWord ++ tailWord_5808630).sum := by decide
  have hdescent : baseEnd_5808630 < baseStart_5808630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808700 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_5808700 : Nat := 118140960795 + 5808700 * 2 ^ 59
def prefixEnd_5808700 : Nat := 4983230072969 + 3 ^ 40 * 5808700 * 2
def baseEnd_5808700 : Nat := 994218359257176222745427

theorem tailTrace_5808700 : CollatzResearch.WordTrace tailWord_5808700 prefixEnd_5808700 994218359257176222745427 := by
  unfold tailWord_5808700
  simp only [CollatzResearch.WordTrace]
  refine ⟨105930347028039710912107777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141240462704052947882810369 105930347028039710912107777)
  ·
    refine ⟨79447760271029783184080833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105930347028039710912107777 79447760271029783184080833)
    ·
      refine ⟨59585820203272337388060625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79447760271029783184080833 59585820203272337388060625)
      ·
        refine ⟨44689365152454253041045469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59585820203272337388060625 44689365152454253041045469)
        ·
          refine ⟨16758511932170344890392051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44689365152454253041045469 16758511932170344890392051)
          ·
            refine ⟨25137767898255517335588077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758511932170344890392051 25137767898255517335588077)
            ·
              refine ⟨9426662961845819000845529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25137767898255517335588077 9426662961845819000845529)
              ·
                refine ⟨7069997221384364250634147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9426662961845819000845529 7069997221384364250634147)
                ·
                  refine ⟨10604995832076546375951221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7069997221384364250634147 10604995832076546375951221)
                  ·
                    refine ⟨994218359257176222745427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10604995832076546375951221 994218359257176222745427)
                    ·
                      rfl

theorem cell23_5808700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_5808700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808700 prefixEnd_5808700 := by exact prefixLift 5808700
  have htrace : WordTrace (prefixWord ++ tailWord_5808700) baseStart_5808700 baseEnd_5808700 := by
    simpa [prefixWord, tailWord_5808700, baseEnd_5808700] using wordTrace_append hprefix tailTrace_5808700
  have hstable : (prefixWord ++ tailWord_5808700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808700).length < 2 ^ (prefixWord ++ tailWord_5808700).sum := by decide
  have hdescent : baseEnd_5808700 < baseStart_5808700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808703 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_5808703 : Nat := 118140960795 + 5808703 * 2 ^ 59
def prefixEnd_5808703 : Nat := 4983230072969 + 3 ^ 40 * 5808703 * 2
def baseEnd_5808703 : Nat := 2982656618213492156498767

theorem tailTrace_5808703 : CollatzResearch.WordTrace tailWord_5808703 prefixEnd_5808703 2982656618213492156498767 := by
  unfold tailWord_5808703
  simp only [CollatzResearch.WordTrace]
  refine ⟨211860803475068553336574763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141240535650045702224383175 211860803475068553336574763)
  ·
    refine ⟨317791205212602830004862145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211860803475068553336574763 317791205212602830004862145)
    ·
      refine ⟨238343403909452122503646609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317791205212602830004862145 238343403909452122503646609)
      ·
        refine ⟨178757552932089091877734957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238343403909452122503646609 178757552932089091877734957)
        ·
          refine ⟨67034082349533409454150609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178757552932089091877734957 67034082349533409454150609)
          ·
            refine ⟨50275561762150057090612957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67034082349533409454150609 50275561762150057090612957)
            ·
              refine ⟨18853335660806271408979859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50275561762150057090612957 18853335660806271408979859)
              ·
                refine ⟨28280003491209407113469789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18853335660806271408979859 28280003491209407113469789)
                ·
                  refine ⟨10605001309203527667551171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28280003491209407113469789 10605001309203527667551171)
                  ·
                    refine ⟨15907501963805291501326757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10605001309203527667551171 15907501963805291501326757)
                    ·
                      refine ⟨2982656618213492156498767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15907501963805291501326757 2982656618213492156498767)
                      ·
                        rfl

theorem cell23_5808703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_5808703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808703 prefixEnd_5808703 := by exact prefixLift 5808703
  have htrace : WordTrace (prefixWord ++ tailWord_5808703) baseStart_5808703 baseEnd_5808703 := by
    simpa [prefixWord, tailWord_5808703, baseEnd_5808703] using wordTrace_append hprefix tailTrace_5808703
  have hstable : (prefixWord ++ tailWord_5808703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808703).length < 2 ^ (prefixWord ++ tailWord_5808703).sum := by decide
  have hdescent : baseEnd_5808703 < baseStart_5808703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808720 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2]
def baseStart_5808720 : Nat := 118140960795 + 5808720 * 2 ^ 59
def prefixEnd_5808720 : Nat := 4983230072969 + 3 ^ 40 * 5808720 * 2
def baseEnd_5808720 : Nat := 2982665347384618589986189

theorem tailTrace_5808720 : CollatzResearch.WordTrace tailWord_5808720 prefixEnd_5808720 2982665347384618589986189 := by
  unfold tailWord_5808720
  simp only [CollatzResearch.WordTrace]
  refine ⟨105930711758003482619971807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141240949010671310159962409 105930711758003482619971807)
  ·
    refine ⟨158896067637005223929957711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105930711758003482619971807 158896067637005223929957711)
    ·
      refine ⟨238344101455507835894936567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158896067637005223929957711 238344101455507835894936567)
      ·
        refine ⟨357516152183261753842404851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238344101455507835894936567 357516152183261753842404851)
        ·
          refine ⟨536274228274892630763607277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357516152183261753842404851 536274228274892630763607277)
          ·
            refine ⟨201102835603084736536352729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536274228274892630763607277 201102835603084736536352729)
            ·
              refine ⟨150827126702313552402264547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201102835603084736536352729 150827126702313552402264547)
              ·
                refine ⟨226240690053470328603396821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150827126702313552402264547 226240690053470328603396821)
                ·
                  refine ⟨5302516173128210826642113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 226240690053470328603396821 5302516173128210826642113)
                  ·
                    refine ⟨3976887129846158119981585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302516173128210826642113 3976887129846158119981585)
                    ·
                      refine ⟨2982665347384618589986189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976887129846158119981585 2982665347384618589986189)
                      ·
                        rfl

theorem cell23_5808720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 7, 2, 2].length) (baseStart_5808720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808720 prefixEnd_5808720 := by exact prefixLift 5808720
  have htrace : WordTrace (prefixWord ++ tailWord_5808720) baseStart_5808720 baseEnd_5808720 := by
    simpa [prefixWord, tailWord_5808720, baseEnd_5808720] using wordTrace_append hprefix tailTrace_5808720
  have hstable : (prefixWord ++ tailWord_5808720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808720).length < 2 ^ (prefixWord ++ tailWord_5808720).sum := by decide
  have hdescent : baseEnd_5808720 < baseStart_5808720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808750 : List Nat := [4, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5808750 : Nat := 118140960795 + 5808750 * 2 ^ 59
def prefixEnd_5808750 : Nat := 4983230072969 + 3 ^ 40 * 5808750 * 2
def baseEnd_5808750 : Nat := 2982680751804253472611051

theorem tailTrace_5808750 : CollatzResearch.WordTrace tailWord_5808750 prefixEnd_5808750 2982680751804253472611051 := by
  unfold tailWord_5808750
  simp only [CollatzResearch.WordTrace]
  refine ⟨26482814713237285045441963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141241678470598853575690469 26482814713237285045441963)
  ·
    refine ⟨39724222069855927568162945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26482814713237285045441963 39724222069855927568162945)
    ·
      refine ⟨29793166552391945676122209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39724222069855927568162945 29793166552391945676122209)
      ·
        refine ⟨22344874914293959257091657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29793166552391945676122209 22344874914293959257091657)
        ·
          refine ⟨16758656185720469442818743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22344874914293959257091657 16758656185720469442818743)
          ·
            refine ⟨25137984278580704164228115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758656185720469442818743 25137984278580704164228115)
            ·
              refine ⟨37706976417871056246342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25137984278580704164228115 37706976417871056246342173)
              ·
                refine ⟨14140116156701646092378315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37706976417871056246342173 14140116156701646092378315)
                ·
                  refine ⟨21210174235052469138567473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14140116156701646092378315 21210174235052469138567473)
                  ·
                    refine ⟨15907630676289351853925605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21210174235052469138567473 15907630676289351853925605)
                    ·
                      refine ⟨2982680751804253472611051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15907630676289351853925605 2982680751804253472611051)
                      ·
                        rfl

theorem cell23_5808750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5808750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808750 prefixEnd_5808750 := by exact prefixLift 5808750
  have htrace : WordTrace (prefixWord ++ tailWord_5808750) baseStart_5808750 baseEnd_5808750 := by
    simpa [prefixWord, tailWord_5808750, baseEnd_5808750] using wordTrace_append hprefix tailTrace_5808750
  have hstable : (prefixWord ++ tailWord_5808750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808750).length < 2 ^ (prefixWord ++ tailWord_5808750).sum := by decide
  have hdescent : baseEnd_5808750 < baseStart_5808750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808754 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_5808754 : Nat := 118140960795 + 5808754 * 2 ^ 59
def prefixEnd_5808754 : Nat := 4983230072969 + 3 ^ 40 * 5808754 * 2
def baseEnd_5808754 : Nat := 2982682805726871456961033

theorem tailTrace_5808754 : CollatzResearch.WordTrace tailWord_5808754 prefixEnd_5808754 2982682805726871456961033 := by
  unfold tailWord_5808754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52965665899470947261670329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141241775731922526031120877 52965665899470947261670329)
  ·
    refine ⟨39724249424603210446252747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52965665899470947261670329 39724249424603210446252747)
    ·
      refine ⟨59586374136904815669379121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39724249424603210446252747 59586374136904815669379121)
      ·
        refine ⟨44689780602678611752034341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59586374136904815669379121 44689780602678611752034341)
        ·
          refine ⟨8379333863002239703506439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44689780602678611752034341 8379333863002239703506439)
          ·
            refine ⟨12569000794503359555259659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379333863002239703506439 12569000794503359555259659)
            ·
              refine ⟨18853501191755039332889489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12569000794503359555259659 18853501191755039332889489)
              ·
                refine ⟨14140125893816279499667117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18853501191755039332889489 14140125893816279499667117)
                ·
                  refine ⟨5302547210181104812375169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14140125893816279499667117 5302547210181104812375169)
                  ·
                    refine ⟨3976910407635828609281377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302547210181104812375169 3976910407635828609281377)
                    ·
                      refine ⟨2982682805726871456961033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976910407635828609281377 2982682805726871456961033)
                      ·
                        rfl

theorem cell23_5808754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_5808754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808754 prefixEnd_5808754 := by exact prefixLift 5808754
  have htrace : WordTrace (prefixWord ++ tailWord_5808754) baseStart_5808754 baseEnd_5808754 := by
    simpa [prefixWord, tailWord_5808754, baseEnd_5808754] using wordTrace_append hprefix tailTrace_5808754
  have hstable : (prefixWord ++ tailWord_5808754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808754).length < 2 ^ (prefixWord ++ tailWord_5808754).sum := by decide
  have hdescent : baseEnd_5808754 < baseStart_5808754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808780 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 5, 3, 2]
def baseStart_5808780 : Nat := 118140960795 + 5808780 * 2 ^ 59
def prefixEnd_5808780 : Nat := 4983230072969 + 3 ^ 40 * 5808780 * 2
def baseEnd_5808780 : Nat := 2982696156223888355235913

theorem tailTrace_5808780 : CollatzResearch.WordTrace tailWord_5808780 prefixEnd_5808780 2982696156223888355235913 := by
  unfold tailWord_5808780
  simp only [CollatzResearch.WordTrace]
  refine ⟨105931805947894797743563897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141242407930526396991418529 105931805947894797743563897)
  ·
    refine ⟨79448854460921098307672923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105931805947894797743563897 79448854460921098307672923)
    ·
      refine ⟨119173281691381647461509385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79448854460921098307672923 119173281691381647461509385)
      ·
        refine ⟨89379961268536235596132039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119173281691381647461509385 89379961268536235596132039)
        ·
          refine ⟨134069941902804353394198059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89379961268536235596132039 134069941902804353394198059)
          ·
            refine ⟨201104912854206530091297089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134069941902804353394198059 201104912854206530091297089)
            ·
              refine ⟨150828684640654897568472817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201104912854206530091297089 150828684640654897568472817)
              ·
                refine ⟨113121513480491173176354613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150828684640654897568472817 113121513480491173176354613)
                ·
                  refine ⟨10605141888796047485283245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113121513480491173176354613 10605141888796047485283245)
                  ·
                    refine ⟨3976928208298517806981217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10605141888796047485283245 3976928208298517806981217)
                    ·
                      refine ⟨2982696156223888355235913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976928208298517806981217 2982696156223888355235913)
                      ·
                        rfl

theorem cell23_5808780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_5808780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808780 prefixEnd_5808780 := by exact prefixLift 5808780
  have htrace : WordTrace (prefixWord ++ tailWord_5808780) baseStart_5808780 baseEnd_5808780 := by
    simpa [prefixWord, tailWord_5808780, baseEnd_5808780] using wordTrace_append hprefix tailTrace_5808780
  have hstable : (prefixWord ++ tailWord_5808780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808780).length < 2 ^ (prefixWord ++ tailWord_5808780).sum := by decide
  have hdescent : baseEnd_5808780 < baseStart_5808780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808804 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_5808804 : Nat := 118140960795 + 5808804 * 2 ^ 59
def prefixEnd_5808804 : Nat := 4983230072969 + 3 ^ 40 * 5808804 * 2
def baseEnd_5808804 : Nat := 2982708479759596261335803

theorem tailTrace_5808804 : CollatzResearch.WordTrace tailWord_5808804 prefixEnd_5808804 2982708479759596261335803 := by
  unfold tailWord_5808804
  simp only [CollatzResearch.WordTrace]
  refine ⟨105932243623851323793000733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141242991498468431724000977 105932243623851323793000733)
  ·
    refine ⟨39724591358944246422375275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105932243623851323793000733 39724591358944246422375275)
    ·
      refine ⟨59586887038416369633562913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39724591358944246422375275 59586887038416369633562913)
      ·
        refine ⟨44690165278812277225172185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59586887038416369633562913 44690165278812277225172185)
        ·
          refine ⟨33517623959109207918879139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44690165278812277225172185 33517623959109207918879139)
          ·
            refine ⟨50276435938663811878318709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33517623959109207918879139 50276435938663811878318709)
            ·
              refine ⟨4713415869249732363592379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50276435938663811878318709 4713415869249732363592379)
              ·
                refine ⟨7070123803874598545388569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4713415869249732363592379 7070123803874598545388569)
                ·
                  refine ⟨5302592852905948909041427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7070123803874598545388569 5302592852905948909041427)
                  ·
                    refine ⟨7953889279358923363562141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5302592852905948909041427 7953889279358923363562141)
                    ·
                      refine ⟨2982708479759596261335803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7953889279358923363562141 2982708479759596261335803)
                      ·
                        rfl

theorem cell23_5808804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_5808804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808804 prefixEnd_5808804 := by exact prefixLift 5808804
  have htrace : WordTrace (prefixWord ++ tailWord_5808804) baseStart_5808804 baseEnd_5808804 := by
    simpa [prefixWord, tailWord_5808804, baseEnd_5808804] using wordTrace_append hprefix tailTrace_5808804
  have hstable : (prefixWord ++ tailWord_5808804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808804).length < 2 ^ (prefixWord ++ tailWord_5808804).sum := by decide
  have hdescent : baseEnd_5808804 < baseStart_5808804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808822 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5808822 : Nat := 118140960795 + 5808822 * 2 ^ 59
def prefixEnd_5808822 : Nat := 4983230072969 + 3 ^ 40 * 5808822 * 2
def baseEnd_5808822 : Nat := 2982717722411377190910721

theorem tailTrace_5808822 : CollatzResearch.WordTrace tailWord_5808822 prefixEnd_5808822 2982717722411377190910721 := by
  unfold tailWord_5808822
  simp only [CollatzResearch.WordTrace]
  refine ⟨13241571485102339791259795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141243429174424957773437813 13241571485102339791259795)
  ·
    refine ⟨19862357227653509686889693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13241571485102339791259795 19862357227653509686889693)
    ·
      refine ⟨7448383960370066132583635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19862357227653509686889693 7448383960370066132583635)
      ·
        refine ⟨11172575940555099198875453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7448383960370066132583635 11172575940555099198875453)
        ·
          refine ⟨4189715977708162199578295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11172575940555099198875453 4189715977708162199578295)
          ·
            refine ⟨6284573966562243299367443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189715977708162199578295 6284573966562243299367443)
            ·
              refine ⟨9426860949843364949051165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284573966562243299367443 9426860949843364949051165)
              ·
                refine ⟨3535072856191261855894187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9426860949843364949051165 3535072856191261855894187)
                ·
                  refine ⟨5302609284286892783841281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535072856191261855894187 5302609284286892783841281)
                  ·
                    refine ⟨3976956963215169587880961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302609284286892783841281 3976956963215169587880961)
                    ·
                      refine ⟨2982717722411377190910721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976956963215169587880961 2982717722411377190910721)
                      ·
                        rfl

theorem cell23_5808822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5808822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808822 prefixEnd_5808822 := by exact prefixLift 5808822
  have htrace : WordTrace (prefixWord ++ tailWord_5808822) baseStart_5808822 baseEnd_5808822 := by
    simpa [prefixWord, tailWord_5808822, baseEnd_5808822] using wordTrace_append hprefix tailTrace_5808822
  have hstable : (prefixWord ++ tailWord_5808822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808822).length < 2 ^ (prefixWord ++ tailWord_5808822).sum := by decide
  have hdescent : baseEnd_5808822 < baseStart_5808822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808830 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5808830 : Nat := 118140960795 + 5808830 * 2 ^ 59
def prefixEnd_5808830 : Nat := 4983230072969 + 3 ^ 40 * 5808830 * 2
def baseEnd_5808830 : Nat := 2982721830256613159610683

theorem tailTrace_5808830 : CollatzResearch.WordTrace tailWord_5808830 prefixEnd_5808830 2982721830256613159610683 := by
  unfold tailWord_5808830
  simp only [CollatzResearch.WordTrace]
  refine ⟨26483179443201056753305993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141243623697072302684298629 26483179443201056753305993)
  ·
    refine ⟨19862384582400792564979495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26483179443201056753305993 19862384582400792564979495)
    ·
      refine ⟨29793576873601188847469243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19862384582400792564979495 29793576873601188847469243)
      ·
        refine ⟨44690365310401783271203865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29793576873601188847469243 44690365310401783271203865)
        ·
          refine ⟨33517773982801337453402899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44690365310401783271203865 33517773982801337453402899)
          ·
            refine ⟨50276660974202006180104349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33517773982801337453402899 50276660974202006180104349)
            ·
              refine ⟨18853747865325752317539131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50276660974202006180104349 18853747865325752317539131)
              ·
                refine ⟨28280621797988628476308697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18853747865325752317539131 28280621797988628476308697)
                ·
                  refine ⟨21210466348491471357231523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28280621797988628476308697 21210466348491471357231523)
                  ·
                    refine ⟨31815699522737207035847285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21210466348491471357231523 31815699522737207035847285)
                    ·
                      refine ⟨2982721830256613159610683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31815699522737207035847285 2982721830256613159610683)
                      ·
                        rfl

theorem cell23_5808830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5808830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808830 prefixEnd_5808830 := by exact prefixLift 5808830
  have htrace : WordTrace (prefixWord ++ tailWord_5808830) baseStart_5808830 baseEnd_5808830 := by
    simpa [prefixWord, tailWord_5808830, baseEnd_5808830] using wordTrace_append hprefix tailTrace_5808830
  have hstable : (prefixWord ++ tailWord_5808830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808830).length < 2 ^ (prefixWord ++ tailWord_5808830).sum := by decide
  have hdescent : baseEnd_5808830 < baseStart_5808830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808844 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5808844 : Nat := 118140960795 + 5808844 * 2 ^ 59
def prefixEnd_5808844 : Nat := 4983230072969 + 3 ^ 40 * 5808844 * 2
def baseEnd_5808844 : Nat := 2982729018985776104835619

theorem tailTrace_5808844 : CollatzResearch.WordTrace tailWord_5808844 prefixEnd_5808844 2982729018985776104835619 := by
  unfold tailWord_5808844
  simp only [CollatzResearch.WordTrace]
  refine ⟨105932973083778867208728793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141243964111705156278305057 105932973083778867208728793)
  ·
    refine ⟨79449729812834150406546595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105932973083778867208728793 79449729812834150406546595)
    ·
      refine ⟨119174594719251225609819893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79449729812834150406546595 119174594719251225609819893)
      ·
        refine ⟨11172618254929802400920615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119174594719251225609819893 11172618254929802400920615)
        ·
          refine ⟨16758927382394703601380923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11172618254929802400920615 16758927382394703601380923)
          ·
            refine ⟨25138391073592055402071385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758927382394703601380923 25138391073592055402071385)
            ·
              refine ⟨18853793305194041551553539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25138391073592055402071385 18853793305194041551553539)
              ·
                refine ⟨28280689957791062327330309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18853793305194041551553539 28280689957791062327330309)
                ·
                  refine ⟨5302629367085824186374433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28280689957791062327330309 5302629367085824186374433)
                  ·
                    refine ⟨3976972025314368139780825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302629367085824186374433 3976972025314368139780825)
                    ·
                      refine ⟨2982729018985776104835619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3976972025314368139780825 2982729018985776104835619)
                      ·
                        rfl

theorem cell23_5808844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5808844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808844 prefixEnd_5808844 := by exact prefixLift 5808844
  have htrace : WordTrace (prefixWord ++ tailWord_5808844) baseStart_5808844 baseEnd_5808844 := by
    simpa [prefixWord, tailWord_5808844, baseEnd_5808844] using wordTrace_append hprefix tailTrace_5808844
  have hstable : (prefixWord ++ tailWord_5808844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808844).length < 2 ^ (prefixWord ++ tailWord_5808844).sum := by decide
  have hdescent : baseEnd_5808844 < baseStart_5808844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808880 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_5808880 : Nat := 118140960795 + 5808880 * 2 ^ 59
def prefixEnd_5808880 : Nat := 4983230072969 + 3 ^ 40 * 5808880 * 2
def baseEnd_5808880 : Nat := 994249168096445987995151

theorem tailTrace_5808880 : CollatzResearch.WordTrace tailWord_5808880 prefixEnd_5808880 994249168096445987995151 := by
  unfold tailWord_5808880
  simp only [CollatzResearch.WordTrace]
  refine ⟨105933629597713656282884047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141244839463618208377178729 105933629597713656282884047)
  ·
    refine ⟨158900444396570484424326071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105933629597713656282884047 158900444396570484424326071)
    ·
      refine ⟨238350666594855726636489107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158900444396570484424326071 238350666594855726636489107)
      ·
        refine ⟨357525999892283589954733661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238350666594855726636489107 357525999892283589954733661)
        ·
          refine ⟨134072249959606346233025123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357525999892283589954733661 134072249959606346233025123)
          ·
            refine ⟨201108374939409519349537685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134072249959606346233025123 201108374939409519349537685)
            ·
              refine ⟨9426955075284821219509579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 201108374939409519349537685 9426955075284821219509579)
              ·
                refine ⟨14140432612927231829264369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9426955075284821219509579 14140432612927231829264369)
                ·
                  refine ⟨10605324459695423871948277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14140432612927231829264369 10605324459695423871948277)
                  ·
                    refine ⟨994249168096445987995151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10605324459695423871948277 994249168096445987995151)
                    ·
                      rfl

theorem cell23_5808880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_5808880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808880 prefixEnd_5808880 := by exact prefixLift 5808880
  have htrace : WordTrace (prefixWord ++ tailWord_5808880) baseStart_5808880 baseEnd_5808880 := by
    simpa [prefixWord, tailWord_5808880, baseEnd_5808880] using wordTrace_append hprefix tailTrace_5808880
  have hstable : (prefixWord ++ tailWord_5808880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808880).length < 2 ^ (prefixWord ++ tailWord_5808880).sum := by decide
  have hdescent : baseEnd_5808880 < baseStart_5808880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808917 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_5808917 : Nat := 118140960795 + 5808917 * 2 ^ 59
def prefixEnd_5808917 : Nat := 4983230072969 + 3 ^ 40 * 5808917 * 2
def baseEnd_5808917 : Nat := 2982766503073554319222783

theorem tailTrace_5808917 : CollatzResearch.WordTrace tailWord_5808917 prefixEnd_5808917 2982766503073554319222783 := by
  unfold tailWord_5808917
  simp only [CollatzResearch.WordTrace]
  refine ⟨211868608696293267884865005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141245739130862178589910003 211868608696293267884865005)
  ·
    refine ⟨79450728261109975456824377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211868608696293267884865005 79450728261109975456824377)
    ·
      refine ⟨59588046195832481592618283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79450728261109975456824377 59588046195832481592618283)
      ·
        refine ⟨89382069293748722388927425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59588046195832481592618283 89382069293748722388927425)
        ·
          refine ⟨67036551970311541791695569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89382069293748722388927425 67036551970311541791695569)
          ·
            refine ⟨50277413977733656343771677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67036551970311541791695569 50277413977733656343771677)
            ·
              refine ⟨18854030241650121128914379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50277413977733656343771677 18854030241650121128914379)
              ·
                refine ⟨28281045362475181693371569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18854030241650121128914379 28281045362475181693371569)
                ·
                  refine ⟨21210784021856386270028677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28281045362475181693371569 21210784021856386270028677)
                  ·
                    refine ⟨3977022004098072425630377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21210784021856386270028677 3977022004098072425630377)
                    ·
                      refine ⟨2982766503073554319222783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977022004098072425630377 2982766503073554319222783)
                      ·
                        rfl

theorem cell23_5808917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_5808917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808917 prefixEnd_5808917 := by exact prefixLift 5808917
  have htrace : WordTrace (prefixWord ++ tailWord_5808917) baseStart_5808917 baseEnd_5808917 := by
    simpa [prefixWord, tailWord_5808917, baseEnd_5808917] using wordTrace_append hprefix tailTrace_5808917
  have hstable : (prefixWord ++ tailWord_5808917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808917).length < 2 ^ (prefixWord ++ tailWord_5808917).sum := by decide
  have hdescent : baseEnd_5808917 < baseStart_5808917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808920 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_5808920 : Nat := 118140960795 + 5808920 * 2 ^ 59
def prefixEnd_5808920 : Nat := 4983230072969 + 3 ^ 40 * 5808920 * 2
def baseEnd_5808920 : Nat := 2982768043515517807485269

theorem tailTrace_5808920 : CollatzResearch.WordTrace tailWord_5808920 prefixEnd_5808920 2982768043515517807485269 := by
  unfold tailWord_5808920
  simp only [CollatzResearch.WordTrace]
  refine ⟨105934359057641199698612107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141245812076854932931482809 105934359057641199698612107)
  ·
    refine ⟨158901538586461799547918161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105934359057641199698612107 158901538586461799547918161)
    ·
      refine ⟨119176153939846349660938621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158901538586461799547918161 119176153939846349660938621)
      ·
        refine ⟨44691057727442381122851983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119176153939846349660938621 44691057727442381122851983)
        ·
          refine ⟨67036586591163571684277975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44691057727442381122851983 67036586591163571684277975)
          ·
            refine ⟨100554879886745357526416963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67036586591163571684277975 100554879886745357526416963)
            ·
              refine ⟨150832319830118036289625445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100554879886745357526416963 150832319830118036289625445)
              ·
                refine ⟨28281059968147131804304771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150832319830118036289625445 28281059968147131804304771)
                ·
                  refine ⟨42421589952220697706457157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28281059968147131804304771 42421589952220697706457157)
                  ·
                    refine ⟨7954048116041380819960717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42421589952220697706457157 7954048116041380819960717)
                    ·
                      refine ⟨2982768043515517807485269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954048116041380819960717 2982768043515517807485269)
                      ·
                        rfl

theorem cell23_5808920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_5808920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808920 prefixEnd_5808920 := by exact prefixLift 5808920
  have htrace : WordTrace (prefixWord ++ tailWord_5808920) baseStart_5808920 baseEnd_5808920 := by
    simpa [prefixWord, tailWord_5808920, baseEnd_5808920] using wordTrace_append hprefix tailTrace_5808920
  have hstable : (prefixWord ++ tailWord_5808920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808920).length < 2 ^ (prefixWord ++ tailWord_5808920).sum := by decide
  have hdescent : baseEnd_5808920 < baseStart_5808920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808927 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 3, 4]
def baseStart_5808927 : Nat := 118140960795 + 5808927 * 2 ^ 59
def prefixEnd_5808927 : Nat := 4983230072969 + 3 ^ 40 * 5808927 * 2
def baseEnd_5808927 : Nat := 994257212626699760032579

theorem tailTrace_5808927 : CollatzResearch.WordTrace tailWord_5808927 prefixEnd_5808927 994257212626699760032579 := by
  unfold tailWord_5808927
  simp only [CollatzResearch.WordTrace]
  refine ⟨211868973426257039592729035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141245982284171359728486023 211868973426257039592729035)
  ·
    refine ⟨317803460139385559389093553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211868973426257039592729035 317803460139385559389093553)
    ·
      refine ⟨238352595104539169541820165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317803460139385559389093553 238352595104539169541820165)
      ·
        refine ⟨44691111582101094289091281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238352595104539169541820165 44691111582101094289091281)
        ·
          refine ⟨33518333686575820716818461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44691111582101094289091281 33518333686575820716818461)
          ·
            refine ⟨12569375132465932768806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33518333686575820716818461 12569375132465932768806923)
            ·
              refine ⟨18854062698698899153210385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12569375132465932768806923 18854062698698899153210385)
              ·
                refine ⟨14140547024024174364907789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18854062698698899153210385 14140547024024174364907789)
                ·
                  refine ⟨5302705134009065386840421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14140547024024174364907789 5302705134009065386840421)
                  ·
                    refine ⟨994257212626699760032579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5302705134009065386840421 994257212626699760032579)
                    ·
                      rfl

theorem cell23_5808927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 4].length) (baseStart_5808927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808927 prefixEnd_5808927 := by exact prefixLift 5808927
  have htrace : WordTrace (prefixWord ++ tailWord_5808927) baseStart_5808927 baseEnd_5808927 := by
    simpa [prefixWord, tailWord_5808927, baseEnd_5808927] using wordTrace_append hprefix tailTrace_5808927
  have hstable : (prefixWord ++ tailWord_5808927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808927).length < 2 ^ (prefixWord ++ tailWord_5808927).sum := by decide
  have hdescent : baseEnd_5808927 < baseStart_5808927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808943 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_5808943 : Nat := 118140960795 + 5808943 * 2 ^ 59
def prefixEnd_5808943 : Nat := 4983230072969 + 3 ^ 40 * 5808943 * 2
def baseEnd_5808943 : Nat := 2982779853570571217497663

theorem tailTrace_5808943 : CollatzResearch.WordTrace tailWord_5808943 prefixEnd_5808943 2982779853570571217497663 := by
  unfold tailWord_5808943
  simp only [CollatzResearch.WordTrace]
  refine ⟨211869556994199074325311483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141246371329466049550207655 211869556994199074325311483)
  ·
    refine ⟨317804335491298611487967225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211869556994199074325311483 317804335491298611487967225)
    ·
      refine ⟨238353251618473958615975419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317804335491298611487967225 238353251618473958615975419)
      ·
        refine ⟨357529877427710937923963129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238353251618473958615975419 357529877427710937923963129)
        ·
          refine ⟨268147408070783203442972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357529877427710937923963129 268147408070783203442972347)
          ·
            refine ⟨402221112106174805164458521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268147408070783203442972347 402221112106174805164458521)
            ·
              refine ⟨301665834079631103873343891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402221112106174805164458521 301665834079631103873343891)
              ·
                refine ⟨452498751119446655810015837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301665834079631103873343891 452498751119446655810015837)
                ·
                  refine ⟨169687031669792495928755939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452498751119446655810015837 169687031669792495928755939)
                  ·
                    refine ⟨254530547504688743893133909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169687031669792495928755939 254530547504688743893133909)
                    ·
                      refine ⟨2982779853570571217497663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 254530547504688743893133909 2982779853570571217497663)
                      ·
                        rfl

theorem cell23_5808943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_5808943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808943 prefixEnd_5808943 := by exact prefixLift 5808943
  have htrace : WordTrace (prefixWord ++ tailWord_5808943) baseStart_5808943 baseEnd_5808943 := by
    simpa [prefixWord, tailWord_5808943, baseEnd_5808943] using wordTrace_append hprefix tailTrace_5808943
  have hstable : (prefixWord ++ tailWord_5808943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808943).length < 2 ^ (prefixWord ++ tailWord_5808943).sum := by decide
  have hdescent : baseEnd_5808943 < baseStart_5808943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808957 : List Nat := [1, 4, 1, 4, 2, 1, 1, 1, 8]
def baseStart_5808957 : Nat := 118140960795 + 5808957 * 2 ^ 59
def prefixEnd_5808957 : Nat := 4983230072969 + 3 ^ 40 * 5808957 * 2
def baseEnd_5808957 : Nat := 331420782477748240302511

theorem tailTrace_5808957 : CollatzResearch.WordTrace tailWord_5808957 prefixEnd_5808957 331420782477748240302511 := by
  unfold tailWord_5808957
  simp only [CollatzResearch.WordTrace]
  refine ⟨211870067616148354716321125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141246711744098903144214083 211870067616148354716321125)
  ·
    refine ⟨39725637678027816509310211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211870067616148354716321125 39725637678027816509310211)
    ·
      refine ⟨59588456517041724763965317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39725637678027816509310211 59588456517041724763965317)
      ·
        refine ⟨11172835596945323393243497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59588456517041724763965317 11172835596945323393243497)
        ·
          refine ⟨8379626697708992544932623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11172835596945323393243497 8379626697708992544932623)
          ·
            refine ⟨12569440046563488817398935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379626697708992544932623 12569440046563488817398935)
            ·
              refine ⟨18854160069845233226098403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12569440046563488817398935 18854160069845233226098403)
              ·
                refine ⟨28281240104767849839147605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18854160069845233226098403 28281240104767849839147605)
                ·
                  refine ⟨331420782477748240302511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28281240104767849839147605 331420782477748240302511)
                  ·
                    rfl

theorem cell23_5808957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_5808957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808957 prefixEnd_5808957 := by exact prefixLift 5808957
  have htrace : WordTrace (prefixWord ++ tailWord_5808957) baseStart_5808957 baseEnd_5808957 := by
    simpa [prefixWord, tailWord_5808957, baseEnd_5808957] using wordTrace_append hprefix tailTrace_5808957
  have hstable : (prefixWord ++ tailWord_5808957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808957).length < 2 ^ (prefixWord ++ tailWord_5808957).sum := by decide
  have hdescent : baseEnd_5808957 < baseStart_5808957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808961 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 3, 4]
def baseStart_5808961 : Nat := 118140960795 + 5808961 * 2 ^ 59
def prefixEnd_5808961 : Nat := 4983230072969 + 3 ^ 40 * 5808961 * 2
def baseEnd_5808961 : Nat := 994263032074117382357527

theorem tailTrace_5808961 : CollatzResearch.WordTrace tailWord_5808961 prefixEnd_5808961 994263032074117382357527 := by
  unfold tailWord_5808961
  simp only [CollatzResearch.WordTrace]
  refine ⟨211870213508133863399466737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141246809005422575599644491 211870213508133863399466737)
  ·
    refine ⟨158902660131100397549600053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211870213508133863399466737 158902660131100397549600053)
    ·
      refine ⟨14897124387290662270275005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158902660131100397549600053 14897124387290662270275005)
      ·
        refine ⟨5586421645233998351353127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14897124387290662270275005 5586421645233998351353127)
        ·
          refine ⟨8379632467850997527029691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5586421645233998351353127 8379632467850997527029691)
          ·
            refine ⟨12569448701776496290544537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8379632467850997527029691 12569448701776496290544537)
            ·
              refine ⟨9427086526332372217908403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12569448701776496290544537 9427086526332372217908403)
              ·
                refine ⟨14140629789498558326862605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9427086526332372217908403 14140629789498558326862605)
                ·
                  refine ⟨5302736171061959372573477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14140629789498558326862605 5302736171061959372573477)
                  ·
                    refine ⟨994263032074117382357527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5302736171061959372573477 994263032074117382357527)
                    ·
                      rfl

theorem cell23_5808961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_5808961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808961 prefixEnd_5808961 := by exact prefixLift 5808961
  have htrace : WordTrace (prefixWord ++ tailWord_5808961) baseStart_5808961 baseEnd_5808961 := by
    simpa [prefixWord, tailWord_5808961, baseEnd_5808961] using wordTrace_append hprefix tailTrace_5808961
  have hstable : (prefixWord ++ tailWord_5808961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808961).length < 2 ^ (prefixWord ++ tailWord_5808961).sum := by decide
  have hdescent : baseEnd_5808961 < baseStart_5808961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5808970 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_5808970 : Nat := 118140960795 + 5808970 * 2 ^ 59
def prefixEnd_5808970 : Nat := 4983230072969 + 3 ^ 40 * 5808970 * 2
def baseEnd_5808970 : Nat := 994264572516080870620013

theorem tailTrace_5808970 : CollatzResearch.WordTrace tailWord_5808970 prefixEnd_5808970 994264572516080870620013 := by
  unfold tailWord_5808970
  simp only [CollatzResearch.WordTrace]
  refine ⟨52967635441275314484136091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141247027843400838624362909 52967635441275314484136091)
  ·
    refine ⟨79451453161912971726204137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52967635441275314484136091 79451453161912971726204137)
    ·
      refine ⟨59588589871434728794653103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79451453161912971726204137 59588589871434728794653103)
      ·
        refine ⟨89382884807152093191979655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59588589871434728794653103 89382884807152093191979655)
        ·
          refine ⟨134074327210728139787969483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89382884807152093191979655 134074327210728139787969483)
          ·
            refine ⟨201111490816092209681954225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134074327210728139787969483 201111490816092209681954225)
            ·
              refine ⟨150833618112069157261465669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201111490816092209681954225 150833618112069157261465669)
              ·
                refine ⟨28281303396012966986524813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150833618112069157261465669 28281303396012966986524813)
                ·
                  refine ⟨10605488773504862619946805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28281303396012966986524813 10605488773504862619946805)
                  ·
                    refine ⟨994264572516080870620013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10605488773504862619946805 994264572516080870620013)
                    ·
                      rfl

theorem cell23_5808970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_5808970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5808970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5808970 prefixEnd_5808970 := by exact prefixLift 5808970
  have htrace : WordTrace (prefixWord ++ tailWord_5808970) baseStart_5808970 baseEnd_5808970 := by
    simpa [prefixWord, tailWord_5808970, baseEnd_5808970] using wordTrace_append hprefix tailTrace_5808970
  have hstable : (prefixWord ++ tailWord_5808970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5808970).length < 2 ^ (prefixWord ++ tailWord_5808970).sum := by decide
  have hdescent : baseEnd_5808970 < baseStart_5808970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5808970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809017 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 4, 4]
def baseStart_5809017 : Nat := 118140960795 + 5809017 * 2 ^ 59
def prefixEnd_5809017 : Nat := 4983230072969 + 3 ^ 40 * 5809017 * 2
def baseEnd_5809017 : Nat := 994272617046334642657441

theorem tailTrace_5809017 : CollatzResearch.WordTrace tailWord_5809017 prefixEnd_5809017 994272617046334642657441 := by
  unfold tailWord_5809017
  simp only [CollatzResearch.WordTrace]
  refine ⟨211872255995930984963505305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141248170663953989975670203 211872255995930984963505305)
  ·
    refine ⟨158904191996948238722628979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211872255995930984963505305 158904191996948238722628979)
    ·
      refine ⟨238356287995422358083943469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158904191996948238722628979 238356287995422358083943469)
      ·
        refine ⟨89383607998283384281478801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238356287995422358083943469 89383607998283384281478801)
        ·
          refine ⟨67037705998712538211109101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89383607998283384281478801 67037705998712538211109101)
          ·
            refine ⟨25139139749517201829165913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67037705998712538211109101 25139139749517201829165913)
            ·
              refine ⟨18854354812137901371874435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25139139749517201829165913 18854354812137901371874435)
              ·
                refine ⟨28281532218206852057811653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18854354812137901371874435 28281532218206852057811653)
                ·
                  refine ⟨5302787290913784760839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28281532218206852057811653 5302787290913784760839685)
                  ·
                    refine ⟨994272617046334642657441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5302787290913784760839685 994272617046334642657441)
                    ·
                      rfl

theorem cell23_5809017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 4].length) (baseStart_5809017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809017 prefixEnd_5809017 := by exact prefixLift 5809017
  have htrace : WordTrace (prefixWord ++ tailWord_5809017) baseStart_5809017 baseEnd_5809017 := by
    simpa [prefixWord, tailWord_5809017, baseEnd_5809017] using wordTrace_append hprefix tailTrace_5809017
  have hstable : (prefixWord ++ tailWord_5809017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809017).length < 2 ^ (prefixWord ++ tailWord_5809017).sum := by decide
  have hdescent : baseEnd_5809017 < baseStart_5809017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809024 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2]
def baseStart_5809024 : Nat := 118140960795 + 5809024 * 2 ^ 59
def prefixEnd_5809024 : Nat := 4983230072969 + 3 ^ 40 * 5809024 * 2
def baseEnd_5809024 : Nat := 2982821445503585400584791

theorem tailTrace_5809024 : CollatzResearch.WordTrace tailWord_5809024 prefixEnd_5809024 2982821445503585400584791 := by
  unfold tailWord_5809024
  simp only [CollatzResearch.WordTrace]
  refine ⟨105936255653452812579505063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141248340871270416772673417 105936255653452812579505063)
  ·
    refine ⟨158904383480179218869257595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105936255653452812579505063 158904383480179218869257595)
    ·
      refine ⟨238356575220268828303886393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158904383480179218869257595 238356575220268828303886393)
      ·
        refine ⟨178767431415201621227914795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238356575220268828303886393 178767431415201621227914795)
        ·
          refine ⟨268151147122802431841872193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178767431415201621227914795 268151147122802431841872193)
          ·
            refine ⟨201113360342101823881404145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268151147122802431841872193 201113360342101823881404145)
            ·
              refine ⟨150835020256576367911053109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201113360342101823881404145 150835020256576367911053109)
              ·
                refine ⟨14140783149054034491661229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150835020256576367911053109 14140783149054034491661229)
                ·
                  refine ⟨5302793680895262934372961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14140783149054034491661229 5302793680895262934372961)
                  ·
                    refine ⟨3977095260671447200779721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5302793680895262934372961 3977095260671447200779721)
                    ·
                      refine ⟨2982821445503585400584791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977095260671447200779721 2982821445503585400584791)
                      ·
                        rfl

theorem cell23_5809024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_5809024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809024 prefixEnd_5809024 := by exact prefixLift 5809024
  have htrace : WordTrace (prefixWord ++ tailWord_5809024) baseStart_5809024 baseEnd_5809024 := by
    simpa [prefixWord, tailWord_5809024, baseEnd_5809024] using wordTrace_append hprefix tailTrace_5809024
  have hstable : (prefixWord ++ tailWord_5809024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809024).length < 2 ^ (prefixWord ++ tailWord_5809024).sum := by decide
  have hdescent : baseEnd_5809024 < baseStart_5809024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809027 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3]
def baseStart_5809027 : Nat := 118140960795 + 5809027 * 2 ^ 59
def prefixEnd_5809027 : Nat := 4983230072969 + 3 ^ 40 * 5809027 * 2
def baseEnd_5809027 : Nat := 2982822985945548888847277

theorem tailTrace_5809027 : CollatzResearch.WordTrace tailWord_5809027 prefixEnd_5809027 2982822985945548888847277 := by
  unfold tailWord_5809027
  simp only [CollatzResearch.WordTrace]
  refine ⟨211872620725894756671369335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141248413817263171114246223 211872620725894756671369335)
  ·
    refine ⟨317808931088842135007054003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211872620725894756671369335 317808931088842135007054003)
    ·
      refine ⟨476713396633263202510581005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317808931088842135007054003 476713396633263202510581005)
      ·
        refine ⟨178767523737473700941467877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476713396633263202510581005 178767523737473700941467877)
        ·
          refine ⟨33518910700776318926525227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178767523737473700941467877 33518910700776318926525227)
          ·
            refine ⟨50278366051164478389787841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33518910700776318926525227 50278366051164478389787841)
            ·
              refine ⟨37708774538373358792340881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50278366051164478389787841 37708774538373358792340881)
              ·
                refine ⟨28281580903780019094255661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37708774538373358792340881 28281580903780019094255661)
                ·
                  refine ⟨10605592838917507160345873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28281580903780019094255661 10605592838917507160345873)
                  ·
                    refine ⟨7954194629188130370259405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10605592838917507160345873 7954194629188130370259405)
                    ·
                      refine ⟨2982822985945548888847277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954194629188130370259405 2982822985945548888847277)
                      ·
                        rfl

theorem cell23_5809027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_5809027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809027 prefixEnd_5809027 := by exact prefixLift 5809027
  have htrace : WordTrace (prefixWord ++ tailWord_5809027) baseStart_5809027 baseEnd_5809027 := by
    simpa [prefixWord, tailWord_5809027, baseEnd_5809027] using wordTrace_append hprefix tailTrace_5809027
  have hstable : (prefixWord ++ tailWord_5809027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809027).length < 2 ^ (prefixWord ++ tailWord_5809027).sum := by decide
  have hdescent : baseEnd_5809027 < baseStart_5809027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809044 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_5809044 : Nat := 118140960795 + 5809044 * 2 ^ 59
def prefixEnd_5809044 : Nat := 4983230072969 + 3 ^ 40 * 5809044 * 2
def baseEnd_5809044 : Nat := 2982831715116675322334699

theorem tailTrace_5809044 : CollatzResearch.WordTrace tailWord_5809044 prefixEnd_5809044 2982831715116675322334699 := by
  unfold tailWord_5809044
  simp only [CollatzResearch.WordTrace]
  refine ⟨105936620383416584287369093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141248827177888779049825457 105936620383416584287369093)
  ·
    refine ⟨19863116321890609553881705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105936620383416584287369093 19863116321890609553881705)
    ·
      refine ⟨14897337241417957165411279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19863116321890609553881705 14897337241417957165411279)
      ·
        refine ⟨22346005862126935748116919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14897337241417957165411279 22346005862126935748116919)
        ·
          refine ⟨33519008793190403622175379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22346005862126935748116919 33519008793190403622175379)
          ·
            refine ⟨50278513189785605433263069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33519008793190403622175379 50278513189785605433263069)
            ·
              refine ⟨18854442446169602037473651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50278513189785605433263069 18854442446169602037473651)
              ·
                refine ⟨28281663669254403056210477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18854442446169602037473651 28281663669254403056210477)
                ·
                  refine ⟨10605623875970401146078929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28281663669254403056210477 10605623875970401146078929)
                  ·
                    refine ⟨7954217906977800859559197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10605623875970401146078929 7954217906977800859559197)
                    ·
                      refine ⟨2982831715116675322334699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954217906977800859559197 2982831715116675322334699)
                      ·
                        rfl

theorem cell23_5809044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_5809044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809044 prefixEnd_5809044 := by exact prefixLift 5809044
  have htrace : WordTrace (prefixWord ++ tailWord_5809044) baseStart_5809044 baseEnd_5809044 := by
    simpa [prefixWord, tailWord_5809044, baseEnd_5809044] using wordTrace_append hprefix tailTrace_5809044
  have hstable : (prefixWord ++ tailWord_5809044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809044).length < 2 ^ (prefixWord ++ tailWord_5809044).sum := by decide
  have hdescent : baseEnd_5809044 < baseStart_5809044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809069 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5809069 : Nat := 118140960795 + 5809069 * 2 ^ 59
def prefixEnd_5809069 : Nat := 4983230072969 + 3 ^ 40 * 5809069 * 2
def baseEnd_5809069 : Nat := 2982844552133037724522085

theorem tailTrace_5809069 : CollatzResearch.WordTrace tailWord_5809069 prefixEnd_5809069 2982844552133037724522085 := by
  unfold tailWord_5809069
  simp only [CollatzResearch.WordTrace]
  refine ⟨211874152591742597844398261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141249435061161731896265507 211874152591742597844398261)
  ·
    refine ⟨19863201805475868547912337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211874152591742597844398261 19863201805475868547912337)
    ·
      refine ⟨14897401354106901410934253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19863201805475868547912337 14897401354106901410934253)
      ·
        refine ⟨5586525507790088029100345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14897401354106901410934253 5586525507790088029100345)
        ·
          refine ⟨4189894130842566021825259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5586525507790088029100345 4189894130842566021825259)
          ·
            refine ⟨6284841196263849032737889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189894130842566021825259 6284841196263849032737889)
            ·
              refine ⟨4713630897197886774553417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6284841196263849032737889 4713630897197886774553417)
              ·
                refine ⟨3535223172898415080915063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713630897197886774553417 3535223172898415080915063)
                ·
                  refine ⟨5302834759347622621372595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535223172898415080915063 5302834759347622621372595)
                  ·
                    refine ⟨7954252139021433932058893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5302834759347622621372595 7954252139021433932058893)
                    ·
                      refine ⟨2982844552133037724522085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954252139021433932058893 2982844552133037724522085)
                      ·
                        rfl

theorem cell23_5809069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5809069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809069 prefixEnd_5809069 := by exact prefixLift 5809069
  have htrace : WordTrace (prefixWord ++ tailWord_5809069) baseStart_5809069 baseEnd_5809069 := by
    simpa [prefixWord, tailWord_5809069, baseEnd_5809069] using wordTrace_append hprefix tailTrace_5809069
  have hstable : (prefixWord ++ tailWord_5809069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809069).length < 2 ^ (prefixWord ++ tailWord_5809069).sum := by decide
  have hdescent : baseEnd_5809069 < baseStart_5809069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809125 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5809125 : Nat := 118140960795 + 5809125 * 2 ^ 59
def prefixEnd_5809125 : Nat := 4983230072969 + 3 ^ 40 * 5809125 * 2
def baseEnd_5809125 : Nat := 2982873307049689505421827

theorem tailTrace_5809125 : CollatzResearch.WordTrace tailWord_5809125 prefixEnd_5809125 2982873307049689505421827 := by
  unfold tailWord_5809125
  simp only [CollatzResearch.WordTrace]
  refine ⟨211876195079539719408436829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141250796719693146272291219 211876195079539719408436829)
  ·
    refine ⟨79453573154827394778163811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211876195079539719408436829 79453573154827394778163811)
    ·
      refine ⟨119180359732241092167245717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79453573154827394778163811 119180359732241092167245717)
      ·
        refine ⟨5586579362448801195339643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119180359732241092167245717 5586579362448801195339643)
        ·
          refine ⟨8379869043673201793009465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5586579362448801195339643 8379869043673201793009465)
          ·
            refine ⟨6284901782754901344757099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8379869043673201793009465 6284901782754901344757099)
            ·
              refine ⟨9427352674132352017135649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6284901782754901344757099 9427352674132352017135649)
              ·
                refine ⟨7070514505599264012851737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9427352674132352017135649 7070514505599264012851737)
                ·
                  refine ⟨5302885879199448009638803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7070514505599264012851737 5302885879199448009638803)
                  ·
                    refine ⟨7954328818799172014458205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5302885879199448009638803 7954328818799172014458205)
                    ·
                      refine ⟨2982873307049689505421827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954328818799172014458205 2982873307049689505421827)
                      ·
                        rfl

theorem cell23_5809125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5809125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809125 prefixEnd_5809125 := by exact prefixLift 5809125
  have htrace : WordTrace (prefixWord ++ tailWord_5809125) baseStart_5809125 baseEnd_5809125 := by
    simpa [prefixWord, tailWord_5809125, baseEnd_5809125] using wordTrace_append hprefix tailTrace_5809125
  have hstable : (prefixWord ++ tailWord_5809125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809125).length < 2 ^ (prefixWord ++ tailWord_5809125).sum := by decide
  have hdescent : baseEnd_5809125 < baseStart_5809125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809137 : List Nat := [1, 2, 2, 2, 4, 1, 1, 3, 7]
def baseStart_5809137 : Nat := 118140960795 + 5809137 * 2 ^ 59
def prefixEnd_5809137 : Nat := 4983230072969 + 3 ^ 40 * 5809137 * 2
def baseEnd_5809137 : Nat := 331431052090838162052419

theorem tailTrace_5809137 : CollatzResearch.WordTrace tailWord_5809137 prefixEnd_5809137 331431052090838162052419 := by
  unfold tailWord_5809137
  simp only [CollatzResearch.WordTrace]
  refine ⟨211876632755496245457873665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141251088503664163638582443 211876632755496245457873665)
  ·
    refine ⟨158907474566622184093405249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211876632755496245457873665 158907474566622184093405249)
    ·
      refine ⟨119180605924966638070053937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158907474566622184093405249 119180605924966638070053937)
      ·
        refine ⟨89385454443724978552540453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119180605924966638070053937 89385454443724978552540453)
        ·
          refine ⟨16759772708198433478601335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89385454443724978552540453 16759772708198433478601335)
          ·
            refine ⟨25139659062297650217902003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16759772708198433478601335 25139659062297650217902003)
            ·
              refine ⟨37709488593446475326853005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25139659062297650217902003 37709488593446475326853005)
              ·
                refine ⟨14141058222542428247569877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37709488593446475326853005 14141058222542428247569877)
                ·
                  refine ⟨331431052090838162052419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14141058222542428247569877 331431052090838162052419)
                  ·
                    rfl

theorem cell23_5809137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 3, 7].length) (baseStart_5809137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809137 prefixEnd_5809137 := by exact prefixLift 5809137
  have htrace : WordTrace (prefixWord ++ tailWord_5809137) baseStart_5809137 baseEnd_5809137 := by
    simpa [prefixWord, tailWord_5809137, baseEnd_5809137] using wordTrace_append hprefix tailTrace_5809137
  have hstable : (prefixWord ++ tailWord_5809137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809137).length < 2 ^ (prefixWord ++ tailWord_5809137).sum := by decide
  have hdescent : baseEnd_5809137 < baseStart_5809137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809188 : List Nat := [2, 3, 1, 4, 1, 2, 3, 2, 5]
def baseStart_5809188 : Nat := 118140960795 + 5809188 * 2 ^ 59
def prefixEnd_5809188 : Nat := 4983230072969 + 3 ^ 40 * 5809188 * 2
def baseEnd_5809188 : Nat := 331433961814546973214893

theorem tailTrace_5809188 : CollatzResearch.WordTrace tailWord_5809188 prefixEnd_5809188 331433961814546973214893 := by
  unfold tailWord_5809188
  simp only [CollatzResearch.WordTrace]
  refine ⟨105939246439155740583990109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141252328585540987445320145 105939246439155740583990109)
  ·
    refine ⟨39727217414683402718996291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105939246439155740583990109 39727217414683402718996291)
    ·
      refine ⟨59590826122025104078494437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39727217414683402718996291 59590826122025104078494437)
      ·
        refine ⟨11173279897879707014717707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59590826122025104078494437 11173279897879707014717707)
        ·
          refine ⟨16759919846819560522076561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11173279897879707014717707 16759919846819560522076561)
          ·
            refine ⟨12569939885114670391557421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16759919846819560522076561 12569939885114670391557421)
            ·
              refine ⟨4713727456918001396834033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12569939885114670391557421 4713727456918001396834033)
              ·
                refine ⟨3535295592688501047625525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4713727456918001396834033 3535295592688501047625525)
                ·
                  refine ⟨331433961814546973214893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535295592688501047625525 331433961814546973214893)
                  ·
                    rfl

theorem cell23_5809188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_5809188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809188 prefixEnd_5809188 := by exact prefixLift 5809188
  have htrace : WordTrace (prefixWord ++ tailWord_5809188) baseStart_5809188 baseEnd_5809188 := by
    simpa [prefixWord, tailWord_5809188, baseEnd_5809188] using wordTrace_append hprefix tailTrace_5809188
  have hstable : (prefixWord ++ tailWord_5809188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809188).length < 2 ^ (prefixWord ++ tailWord_5809188).sum := by decide
  have hdescent : baseEnd_5809188 < baseStart_5809188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809247 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6]
def baseStart_5809247 : Nat := 118140960795 + 5809247 * 2 ^ 59
def prefixEnd_5809247 : Nat := 4983230072969 + 3 ^ 40 * 5809247 * 2
def baseEnd_5809247 : Nat := 2982935951689538028096265

theorem tailTrace_5809247 : CollatzResearch.WordTrace tailWord_5809247 prefixEnd_5809247 2982935951689538028096265 := by
  unfold tailWord_5809247
  simp only [CollatzResearch.WordTrace]
  refine ⟨211880644785097734244377995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141253763190065156162918663 211880644785097734244377995)
  ·
    refine ⟨317820967177646601366566993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211880644785097734244377995 317820967177646601366566993)
    ·
      refine ⟨238365725383234951024925245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317820967177646601366566993 238365725383234951024925245)
      ·
        refine ⟨89387147018713106634346967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238365725383234951024925245 89387147018713106634346967)
        ·
          refine ⟨134080720528069659951520451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89387147018713106634346967 134080720528069659951520451)
          ·
            refine ⟨201121080792104489927280677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134080720528069659951520451 201121080792104489927280677)
            ·
              refine ⟨37710202648519591861365127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201121080792104489927280677 37710202648519591861365127)
              ·
                refine ⟨56565303972779387792047691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37710202648519591861365127 56565303972779387792047691)
                ·
                  refine ⟨84847955959169081688071537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56565303972779387792047691 84847955959169081688071537)
                  ·
                    refine ⟨63635966969376811266053653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84847955959169081688071537 63635966969376811266053653)
                    ·
                      refine ⟨2982935951689538028096265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63635966969376811266053653 2982935951689538028096265)
                      ·
                        rfl

theorem cell23_5809247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_5809247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809247 prefixEnd_5809247 := by exact prefixLift 5809247
  have htrace : WordTrace (prefixWord ++ tailWord_5809247) baseStart_5809247 baseEnd_5809247 := by
    simpa [prefixWord, tailWord_5809247, baseEnd_5809247] using wordTrace_append hprefix tailTrace_5809247
  have hstable : (prefixWord ++ tailWord_5809247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809247).length < 2 ^ (prefixWord ++ tailWord_5809247).sum := by decide
  have hdescent : baseEnd_5809247 < baseStart_5809247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809271 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 3]
def baseStart_5809271 : Nat := 118140960795 + 5809271 * 2 ^ 59
def prefixEnd_5809271 : Nat := 4983230072969 + 3 ^ 40 * 5809271 * 2
def baseEnd_5809271 : Nat := 2982948275225245934196155

theorem tailTrace_5809271 : CollatzResearch.WordTrace tailWord_5809271 prefixEnd_5809271 2982948275225245934196155 := by
  unfold tailWord_5809271
  simp only [CollatzResearch.WordTrace]
  refine ⟨211881520137010786343251667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141254346758007190895501111 211881520137010786343251667)
  ·
    refine ⟨317822280205516179514877501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211881520137010786343251667 317822280205516179514877501)
    ·
      refine ⟨119183355077068567318079063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317822280205516179514877501 119183355077068567318079063)
      ·
        refine ⟨178775032615602850977118595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119183355077068567318079063 178775032615602850977118595)
        ·
          refine ⟨268162548923404276465677893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178775032615602850977118595 268162548923404276465677893)
          ·
            refine ⟨50280477923138301837314605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268162548923404276465677893 50280477923138301837314605)
            ·
              refine ⟨18855179221176863188992977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50280477923138301837314605 18855179221176863188992977)
              ·
                refine ⟨14141384415882647391744733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18855179221176863188992977 14141384415882647391744733)
                ·
                  refine ⟨5303019155955992771904275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14141384415882647391744733 5303019155955992771904275)
                  ·
                    refine ⟨7954528733933989157856413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5303019155955992771904275 7954528733933989157856413)
                    ·
                      refine ⟨2982948275225245934196155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954528733933989157856413 2982948275225245934196155)
                      ·
                        rfl

theorem cell23_5809271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 1, 3].length) (baseStart_5809271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809271 prefixEnd_5809271 := by exact prefixLift 5809271
  have htrace : WordTrace (prefixWord ++ tailWord_5809271) baseStart_5809271 baseEnd_5809271 := by
    simpa [prefixWord, tailWord_5809271, baseEnd_5809271] using wordTrace_append hprefix tailTrace_5809271
  have hstable : (prefixWord ++ tailWord_5809271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809271).length < 2 ^ (prefixWord ++ tailWord_5809271).sum := by decide
  have hdescent : baseEnd_5809271 < baseStart_5809271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809324 : List Nat := [2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_5809324 : Nat := 118140960795 + 5809324 * 2 ^ 59
def prefixEnd_5809324 : Nat := 4983230072969 + 3 ^ 40 * 5809324 * 2
def baseEnd_5809324 : Nat := 2982975489699934226833411

theorem tailTrace_5809324 : CollatzResearch.WordTrace tailWord_5809324 prefixEnd_5809324 2982975489699934226833411 := by
  unfold tailWord_5809324
  simp only [CollatzResearch.WordTrace]
  refine ⟨105941726602909388197465513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141255635470545850929954017 105941726602909388197465513)
  ·
    refine ⟨79456294952182041148099135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105941726602909388197465513 79456294952182041148099135)
    ·
      refine ⟨119184442428273061722148703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79456294952182041148099135 119184442428273061722148703)
      ·
        refine ⟨178776663642409592583223055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119184442428273061722148703 178776663642409592583223055)
        ·
          refine ⟨268164995463614388874834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178776663642409592583223055 268164995463614388874834583)
          ·
            refine ⟨402247493195421583312251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268164995463614388874834583 402247493195421583312251875)
            ·
              refine ⟨603371239793132374968377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402247493195421583312251875 603371239793132374968377813)
              ·
                refine ⟨14141513432651540038321355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 603371239793132374968377813 14141513432651540038321355)
                ·
                  refine ⟨21212270148977310057482033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14141513432651540038321355 21212270148977310057482033)
                  ·
                    refine ⟨15909202611732982543111525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21212270148977310057482033 15909202611732982543111525)
                    ·
                      refine ⟨2982975489699934226833411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15909202611732982543111525 2982975489699934226833411)
                      ·
                        rfl

theorem cell23_5809324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_5809324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809324 prefixEnd_5809324 := by exact prefixLift 5809324
  have htrace : WordTrace (prefixWord ++ tailWord_5809324) baseStart_5809324 baseEnd_5809324 := by
    simpa [prefixWord, tailWord_5809324, baseEnd_5809324] using wordTrace_append hprefix tailTrace_5809324
  have hstable : (prefixWord ++ tailWord_5809324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809324).length < 2 ^ (prefixWord ++ tailWord_5809324).sum := by decide
  have hdescent : baseEnd_5809324 < baseStart_5809324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809331 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 3]
def baseStart_5809331 : Nat := 118140960795 + 5809331 * 2 ^ 59
def prefixEnd_5809331 : Nat := 4983230072969 + 3 ^ 40 * 5809331 * 2
def baseEnd_5809331 : Nat := 2982979084064515699445879

theorem tailTrace_5809331 : CollatzResearch.WordTrace tailWord_5809331 prefixEnd_5809331 2982979084064515699445879 := by
  unfold tailWord_5809331
  simp only [CollatzResearch.WordTrace]
  refine ⟨211883708516793416590435847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141255805677862277726957231 211883708516793416590435847)
  ·
    refine ⟨317825562775190124885653771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211883708516793416590435847 317825562775190124885653771)
    ·
      refine ⟨476738344162785187328480657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317825562775190124885653771 476738344162785187328480657)
      ·
        refine ⟨357553758122088890496360493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476738344162785187328480657 357553758122088890496360493)
        ·
          refine ⟨134082659295783333936135185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357553758122088890496360493 134082659295783333936135185)
          ·
            refine ⟨100561994471837500452101389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134082659295783333936135185 100561994471837500452101389)
            ·
              refine ⟨37710747926939062669538021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100561994471837500452101389 37710747926939062669538021)
              ·
                refine ⟨7070765236301074250538379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37710747926939062669538021 7070765236301074250538379)
                ·
                  refine ⟨10606147854451611375807569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7070765236301074250538379 10606147854451611375807569)
                  ·
                    refine ⟨7954610890838708531855677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10606147854451611375807569 7954610890838708531855677)
                    ·
                      refine ⟨2982979084064515699445879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7954610890838708531855677 2982979084064515699445879)
                      ·
                        rfl

theorem cell23_5809331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_5809331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809331 prefixEnd_5809331 := by exact prefixLift 5809331
  have htrace : WordTrace (prefixWord ++ tailWord_5809331) baseStart_5809331 baseEnd_5809331 := by
    simpa [prefixWord, tailWord_5809331, baseEnd_5809331] using wordTrace_append hprefix tailTrace_5809331
  have hstable : (prefixWord ++ tailWord_5809331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809331).length < 2 ^ (prefixWord ++ tailWord_5809331).sum := by decide
  have hdescent : baseEnd_5809331 < baseStart_5809331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809348 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_5809348 : Nat := 118140960795 + 5809348 * 2 ^ 59
def prefixEnd_5809348 : Nat := 4983230072969 + 3 ^ 40 * 5809348 * 2
def baseEnd_5809348 : Nat := 2982987813235642132933301

theorem tailTrace_5809348 : CollatzResearch.WordTrace tailWord_5809348 prefixEnd_5809348 2982987813235642132933301 := by
  unfold tailWord_5809348
  simp only [CollatzResearch.WordTrace]
  refine ⟨105942164278865914246902349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141256219038487885662536465 105942164278865914246902349)
  ·
    refine ⟨39728311604574717842588381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105942164278865914246902349 39728311604574717842588381)
    ·
      refine ⟨14898116851715519190970643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39728311604574717842588381 14898116851715519190970643)
      ·
        refine ⟨22347175277573278786455965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14898116851715519190970643 22347175277573278786455965)
        ·
          refine ⟨8380190729089979544920987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22347175277573278786455965 8380190729089979544920987)
          ·
            refine ⟨12570286093634969317381481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8380190729089979544920987 12570286093634969317381481)
            ·
              refine ⟨9427714570226226988036111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12570286093634969317381481 9427714570226226988036111)
              ·
                refine ⟨14141571855339340482054167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9427714570226226988036111 14141571855339340482054167)
                ·
                  refine ⟨21212357783009010723081251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14141571855339340482054167 21212357783009010723081251)
                  ·
                    refine ⟨31818536674513516084621877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21212357783009010723081251 31818536674513516084621877)
                    ·
                      refine ⟨2982987813235642132933301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31818536674513516084621877 2982987813235642132933301)
                      ·
                        rfl

theorem cell23_5809348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_5809348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809348 prefixEnd_5809348 := by exact prefixLift 5809348
  have htrace : WordTrace (prefixWord ++ tailWord_5809348) baseStart_5809348 baseEnd_5809348 := by
    simpa [prefixWord, tailWord_5809348, baseEnd_5809348] using wordTrace_append hprefix tailTrace_5809348
  have hstable : (prefixWord ++ tailWord_5809348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809348).length < 2 ^ (prefixWord ++ tailWord_5809348).sum := by decide
  have hdescent : baseEnd_5809348 < baseStart_5809348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809388 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 3, 3, 2]
def baseStart_5809388 : Nat := 118140960795 + 5809388 * 2 ^ 59
def prefixEnd_5809388 : Nat := 4983230072969 + 3 ^ 40 * 5809388 * 2
def baseEnd_5809388 : Nat := 2983008352461821976433117

theorem tailTrace_5809388 : CollatzResearch.WordTrace tailWord_5809388 prefixEnd_5809388 2983008352461821976433117 := by
  unfold tailWord_5809388
  simp only [CollatzResearch.WordTrace]
  refine ⟨105942893738793457662630409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141257191651724610216840545 105942893738793457662630409)
  ·
    refine ⟨79457170304095093246972807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105942893738793457662630409 79457170304095093246972807)
    ·
      refine ⟨119185755456142639870459211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79457170304095093246972807 119185755456142639870459211)
      ·
        refine ⟨178778633184213959805688817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119185755456142639870459211 178778633184213959805688817)
        ·
          refine ⟨134083974888160469854266613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178778633184213959805688817 134083974888160469854266613)
          ·
            refine ⟨12570372645765044048837495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134083974888160469854266613 12570372645765044048837495)
            ·
              refine ⟨18855558968647566073256243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12570372645765044048837495 18855558968647566073256243)
              ·
                refine ⟨28283338452971349109884365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18855558968647566073256243 28283338452971349109884365)
                ·
                  refine ⟨10606251919864255916206637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28283338452971349109884365 10606251919864255916206637)
                  ·
                    refine ⟨3977344469949095968577489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10606251919864255916206637 3977344469949095968577489)
                    ·
                      refine ⟨2983008352461821976433117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977344469949095968577489 2983008352461821976433117)
                      ·
                        rfl

theorem cell23_5809388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 3, 2].length) (baseStart_5809388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809388 prefixEnd_5809388 := by exact prefixLift 5809388
  have htrace : WordTrace (prefixWord ++ tailWord_5809388) baseStart_5809388 baseEnd_5809388 := by
    simpa [prefixWord, tailWord_5809388, baseEnd_5809388] using wordTrace_append hprefix tailTrace_5809388
  have hstable : (prefixWord ++ tailWord_5809388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809388).length < 2 ^ (prefixWord ++ tailWord_5809388).sum := by decide
  have hdescent : baseEnd_5809388 < baseStart_5809388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809431 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5809431 : Nat := 118140960795 + 5809431 * 2 ^ 59
def prefixEnd_5809431 : Nat := 4983230072969 + 3 ^ 40 * 5809431 * 2
def baseEnd_5809431 : Nat := 2983030432129965308195419

theorem tailTrace_5809431 : CollatzResearch.WordTrace tailWord_5809431 prefixEnd_5809431 2983030432129965308195419 := by
  unfold tailWord_5809431
  simp only [CollatzResearch.WordTrace]
  refine ⟨211887355816431133669076147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141258237210954089112717431 211887355816431133669076147)
  ·
    refine ⟨317831033724646700503614221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211887355816431133669076147 317831033724646700503614221)
    ·
      refine ⟨119186637646742512688855333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317831033724646700503614221 119186637646742512688855333)
      ·
        refine ⟨22347494558764221129160375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119186637646742512688855333 22347494558764221129160375)
        ·
          refine ⟨33521241838146331693740563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22347494558764221129160375 33521241838146331693740563)
          ·
            refine ⟨50281862757219497540610845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33521241838146331693740563 50281862757219497540610845)
            ·
              refine ⟨18855698533957311577729067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50281862757219497540610845 18855698533957311577729067)
              ·
                refine ⟨28283547800935967366593601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18855698533957311577729067 28283547800935967366593601)
                ·
                  refine ⟨21212660850701975524945201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28283547800935967366593601 21212660850701975524945201)
                  ·
                    refine ⟨15909495638026481643708901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21212660850701975524945201 15909495638026481643708901)
                    ·
                      refine ⟨2983030432129965308195419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15909495638026481643708901 2983030432129965308195419)
                      ·
                        rfl

theorem cell23_5809431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5809431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809431 prefixEnd_5809431 := by exact prefixLift 5809431
  have htrace : WordTrace (prefixWord ++ tailWord_5809431) baseStart_5809431 baseEnd_5809431 := by
    simpa [prefixWord, tailWord_5809431, baseEnd_5809431] using wordTrace_append hprefix tailTrace_5809431
  have hstable : (prefixWord ++ tailWord_5809431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809431).length < 2 ^ (prefixWord ++ tailWord_5809431).sum := by decide
  have hdescent : baseEnd_5809431 < baseStart_5809431 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809458 : List Nat := [3, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_5809458 : Nat := 118140960795 + 5809458 * 2 ^ 59
def prefixEnd_5809458 : Nat := 4983230072969 + 3 ^ 40 * 5809458 * 2
def baseEnd_5809458 : Nat := 331449366234181855839755

theorem tailTrace_5809458 : CollatzResearch.WordTrace tailWord_5809458 prefixEnd_5809458 331449366234181855839755 := by
  unfold tailWord_5809458
  simp only [CollatzResearch.WordTrace]
  refine ⟨52972085146833329320077257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141258893724888878186872685 52972085146833329320077257)
  ·
    refine ⟨39729063860124996990057943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52972085146833329320077257 39729063860124996990057943)
    ·
      refine ⟨59593595790187495485086915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39729063860124996990057943 59593595790187495485086915)
      ·
        refine ⟨89390393685281243227630373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59593595790187495485086915 89390393685281243227630373)
        ·
          refine ⟨16760698815990233105180695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89390393685281243227630373 16760698815990233105180695)
          ·
            refine ⟨25141048223985349657771043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16760698815990233105180695 25141048223985349657771043)
            ·
              refine ⟨37711572335978024486656565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25141048223985349657771043 37711572335978024486656565)
              ·
                refine ⟨3535459906497939795624053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37711572335978024486656565 3535459906497939795624053)
                ·
                  refine ⟨331449366234181855839755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535459906497939795624053 331449366234181855839755)
                  ·
                    rfl

theorem cell23_5809458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_5809458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809458 prefixEnd_5809458 := by exact prefixLift 5809458
  have htrace : WordTrace (prefixWord ++ tailWord_5809458) baseStart_5809458 baseEnd_5809458 := by
    simpa [prefixWord, tailWord_5809458, baseEnd_5809458] using wordTrace_append hprefix tailTrace_5809458
  have hstable : (prefixWord ++ tailWord_5809458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809458).length < 2 ^ (prefixWord ++ tailWord_5809458).sum := by decide
  have hdescent : baseEnd_5809458 < baseStart_5809458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809525 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_5809525 : Nat := 118140960795 + 5809525 * 2 ^ 59
def prefixEnd_5809525 : Nat := 4983230072969 + 3 ^ 40 * 5809525 * 2
def baseEnd_5809525 : Nat := 2983078699311487940419987

theorem tailTrace_5809525 : CollatzResearch.WordTrace tailWord_5809525 prefixEnd_5809525 2983078699311487940419987 := by
  unfold tailWord_5809525
  simp only [CollatzResearch.WordTrace]
  refine ⟨211890784278090587722998029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141260522852060391815332019 211890784278090587722998029)
  ·
    refine ⟨79459044104283970396124261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211890784278090587722998029 79459044104283970396124261)
    ·
      refine ⟨14898570769553244449273299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79459044104283970396124261 14898570769553244449273299)
      ·
        refine ⟨22347856154329866673909949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14898570769553244449273299 22347856154329866673909949)
        ·
          refine ⟨8380446057873700002716231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22347856154329866673909949 8380446057873700002716231)
          ·
            refine ⟨12570669086810550004074347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8380446057873700002716231 12570669086810550004074347)
            ·
              refine ⟨18856003630215825006111521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12570669086810550004074347 18856003630215825006111521)
              ·
                refine ⟨14142002722661868754583641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18856003630215825006111521 14142002722661868754583641)
                ·
                  refine ⟨10606502041996401565937731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14142002722661868754583641 10606502041996401565937731)
                  ·
                    refine ⟨15909753062994602348906597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10606502041996401565937731 15909753062994602348906597)
                    ·
                      refine ⟨2983078699311487940419987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15909753062994602348906597 2983078699311487940419987)
                      ·
                        rfl

theorem cell23_5809525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_5809525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809525 prefixEnd_5809525 := by exact prefixLift 5809525
  have htrace : WordTrace (prefixWord ++ tailWord_5809525) baseStart_5809525 baseEnd_5809525 := by
    simpa [prefixWord, tailWord_5809525, baseEnd_5809525] using wordTrace_append hprefix tailTrace_5809525
  have hstable : (prefixWord ++ tailWord_5809525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809525).length < 2 ^ (prefixWord ++ tailWord_5809525).sum := by decide
  have hdescent : baseEnd_5809525 < baseStart_5809525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809531 : List Nat := [1, 1, 1, 1, 1, 6, 2, 4, 6]
def baseStart_5809531 : Nat := 118140960795 + 5809531 * 2 ^ 59
def prefixEnd_5809531 : Nat := 4983230072969 + 3 ^ 40 * 5809531 * 2
def baseEnd_5809531 : Nat := 331453531132823879660551

theorem tailTrace_5809531 : CollatzResearch.WordTrace tailWord_5809531 prefixEnd_5809531 331453531132823879660551 := by
  unfold tailWord_5809531
  simp only [CollatzResearch.WordTrace]
  refine ⟨211891003116068850747716447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141260668744045900498477631 211891003116068850747716447)
  ·
    refine ⟨317836504674103276121574671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211891003116068850747716447 317836504674103276121574671)
    ·
      refine ⟨476754757011154914182362007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317836504674103276121574671 476754757011154914182362007)
      ·
        refine ⟨715132135516732371273543011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476754757011154914182362007 715132135516732371273543011)
        ·
          refine ⟨1072698203275098556910314517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715132135516732371273543011 1072698203275098556910314517)
          ·
            refine ⟨50282728278520244855170993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1072698203275098556910314517 50282728278520244855170993)
            ·
              refine ⟨37712046208890183641378245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50282728278520244855170993 37712046208890183641378245)
              ·
                refine ⟨7071008664166909432758421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37712046208890183641378245 7071008664166909432758421)
                ·
                  refine ⟨331453531132823879660551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7071008664166909432758421 331453531132823879660551)
                  ·
                    rfl

theorem cell23_5809531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 4, 6].length) (baseStart_5809531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809531 prefixEnd_5809531 := by exact prefixLift 5809531
  have htrace : WordTrace (prefixWord ++ tailWord_5809531) baseStart_5809531 baseEnd_5809531 := by
    simpa [prefixWord, tailWord_5809531, baseEnd_5809531] using wordTrace_append hprefix tailTrace_5809531
  have hstable : (prefixWord ++ tailWord_5809531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809531).length < 2 ^ (prefixWord ++ tailWord_5809531).sum := by decide
  have hdescent : baseEnd_5809531 < baseStart_5809531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809585 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_5809585 : Nat := 118140960795 + 5809585 * 2 ^ 59
def prefixEnd_5809585 : Nat := 4983230072969 + 3 ^ 40 * 5809585 * 2
def baseEnd_5809585 : Nat := 2983109508150757705669711

theorem tailTrace_5809585 : CollatzResearch.WordTrace tailWord_5809585 prefixEnd_5809585 2983109508150757705669711 := by
  unfold tailWord_5809585
  simp only [CollatzResearch.WordTrace]
  refine ⟨211892972657873217970182209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141261981771915478646788139 211892972657873217970182209)
  ·
    refine ⟨158919729493404913477636657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211892972657873217970182209 158919729493404913477636657)
    ·
      refine ⟨119189797120053685108227493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158919729493404913477636657 119189797120053685108227493)
      ·
        refine ⟨22348086960010065957792655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119189797120053685108227493 22348086960010065957792655)
        ·
          refine ⟨33522130440015098936688983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22348086960010065957792655 33522130440015098936688983)
          ·
            refine ⟨50283195660022648405033475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33522130440015098936688983 50283195660022648405033475)
            ·
              refine ⟨75424793490033972607550213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50283195660022648405033475 75424793490033972607550213)
              ·
                refine ⟨14142148779381369863915665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75424793490033972607550213 14142148779381369863915665)
                ·
                  refine ⟨10606611584536027397936749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14142148779381369863915665 10606611584536027397936749)
                  ·
                    refine ⟨3977479344201010274226281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10606611584536027397936749 3977479344201010274226281)
                    ·
                      refine ⟨2983109508150757705669711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977479344201010274226281 2983109508150757705669711)
                      ·
                        rfl

theorem cell23_5809585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_5809585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809585 prefixEnd_5809585 := by exact prefixLift 5809585
  have htrace : WordTrace (prefixWord ++ tailWord_5809585) baseStart_5809585 baseEnd_5809585 := by
    simpa [prefixWord, tailWord_5809585, baseEnd_5809585] using wordTrace_append hprefix tailTrace_5809585
  have hstable : (prefixWord ++ tailWord_5809585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809585).length < 2 ^ (prefixWord ++ tailWord_5809585).sum := by decide
  have hdescent : baseEnd_5809585 < baseStart_5809585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809591 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 6]
def baseStart_5809591 : Nat := 118140960795 + 5809591 * 2 ^ 59
def prefixEnd_5809591 : Nat := 4983230072969 + 3 ^ 40 * 5809591 * 2
def baseEnd_5809591 : Nat := 994370863011561560731561

theorem tailTrace_5809591 : CollatzResearch.WordTrace tailWord_5809591 prefixEnd_5809591 994370863011561560731561 := by
  unfold tailWord_5809591
  simp only [CollatzResearch.WordTrace]
  refine ⟨211893191495851480994900627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141262127663900987329933751 211893191495851480994900627)
  ·
    refine ⟨317839787243777221492350941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211893191495851480994900627 317839787243777221492350941)
    ·
      refine ⟨119189920216416458059631603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317839787243777221492350941 119189920216416458059631603)
      ·
        refine ⟨178784880324624687089447405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119189920216416458059631603 178784880324624687089447405)
        ·
          refine ⟨67044330121734257658542777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178784880324624687089447405 67044330121734257658542777)
          ·
            refine ⟨50283247591300693243907083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67044330121734257658542777 50283247591300693243907083)
            ·
              refine ⟨75424871386951039865860625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50283247591300693243907083 75424871386951039865860625)
              ·
                refine ⟨56568653540213279899395469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75424871386951039865860625 56568653540213279899395469)
                ·
                  refine ⟨21213245077579979962273301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56568653540213279899395469 21213245077579979962273301)
                  ·
                    refine ⟨994370863011561560731561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21213245077579979962273301 994370863011561560731561)
                    ·
                      rfl

theorem cell23_5809591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_5809591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809591 prefixEnd_5809591 := by exact prefixLift 5809591
  have htrace : WordTrace (prefixWord ++ tailWord_5809591) baseStart_5809591 baseEnd_5809591 := by
    simpa [prefixWord, tailWord_5809591, baseEnd_5809591] using wordTrace_append hprefix tailTrace_5809591
  have hstable : (prefixWord ++ tailWord_5809591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809591).length < 2 ^ (prefixWord ++ tailWord_5809591).sum := by decide
  have hdescent : baseEnd_5809591 < baseStart_5809591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809608 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_5809608 : Nat := 118140960795 + 5809608 * 2 ^ 59
def prefixEnd_5809608 : Nat := 4983230072969 + 3 ^ 40 * 5809608 * 2
def baseEnd_5809608 : Nat := 994373772735270371894035

theorem tailTrace_5809608 : CollatzResearch.WordTrace tailWord_5809608 prefixEnd_5809608 994373772735270371894035 := by
  unfold tailWord_5809608
  simp only [CollatzResearch.WordTrace]
  refine ⟨105946905768394946449134739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141262541024526595265512985 105946905768394946449134739)
  ·
    refine ⟨158920358652592419673702109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105946905768394946449134739 158920358652592419673702109)
    ·
      refine ⟨59595134494722157377638291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158920358652592419673702109 59595134494722157377638291)
      ·
        refine ⟨89392701742083236066457437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59595134494722157377638291 89392701742083236066457437)
        ·
          refine ⟨33522263153281213524921539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89392701742083236066457437 33522263153281213524921539)
          ·
            refine ⟨50283394729921820287382309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33522263153281213524921539 50283394729921820287382309)
            ·
              refine ⟨9428136511860341303884183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50283394729921820287382309 9428136511860341303884183)
              ·
                refine ⟨14142204767790511955826275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9428136511860341303884183 14142204767790511955826275)
                ·
                  refine ⟨21213307151685767933739413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14142204767790511955826275 21213307151685767933739413)
                  ·
                    refine ⟨994373772735270371894035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21213307151685767933739413 994373772735270371894035)
                    ·
                      rfl

theorem cell23_5809608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_5809608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809608 prefixEnd_5809608 := by exact prefixLift 5809608
  have htrace : WordTrace (prefixWord ++ tailWord_5809608) baseStart_5809608 baseEnd_5809608 := by
    simpa [prefixWord, tailWord_5809608, baseEnd_5809608] using wordTrace_append hprefix tailTrace_5809608
  have hstable : (prefixWord ++ tailWord_5809608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809608).length < 2 ^ (prefixWord ++ tailWord_5809608).sum := by decide
  have hdescent : baseEnd_5809608 < baseStart_5809608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809611 : List Nat := [1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_5809611 : Nat := 118140960795 + 5809611 * 2 ^ 59
def prefixEnd_5809611 : Nat := 4983230072969 + 3 ^ 40 * 5809611 * 2
def baseEnd_5809611 : Nat := 2983122858647774603944591

theorem tailTrace_5809611 : CollatzResearch.WordTrace tailWord_5809611 prefixEnd_5809611 2983122858647774603944591 := by
  unfold tailWord_5809611
  simp only [CollatzResearch.WordTrace]
  refine ⟨211893920955779024410628687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141262613970519349607085791 211893920955779024410628687)
  ·
    refine ⟨317840881433668536615943031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211893920955779024410628687 317840881433668536615943031)
    ·
      refine ⟨476761322150502804923914547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317840881433668536615943031 476761322150502804923914547)
      ·
        refine ⟨715141983225754207385871821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476761322150502804923914547 715141983225754207385871821)
        ·
          refine ⟨268178243709657827769701933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 715141983225754207385871821 268178243709657827769701933)
          ·
            refine ⟨100566841391121685413638225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268178243709657827769701933 100566841391121685413638225)
            ·
              refine ⟨75425131043341264060228669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100566841391121685413638225 75425131043341264060228669)
              ·
                refine ⟨28284424141252974022585751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75425131043341264060228669 28284424141252974022585751)
                ·
                  refine ⟨42426636211879461033878627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28284424141252974022585751 42426636211879461033878627)
                  ·
                    refine ⟨63639954317819191550817941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42426636211879461033878627 63639954317819191550817941)
                    ·
                      refine ⟨2983122858647774603944591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63639954317819191550817941 2983122858647774603944591)
                      ·
                        rfl

theorem cell23_5809611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_5809611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809611 prefixEnd_5809611 := by exact prefixLift 5809611
  have htrace : WordTrace (prefixWord ++ tailWord_5809611) baseStart_5809611 baseEnd_5809611 := by
    simpa [prefixWord, tailWord_5809611, baseEnd_5809611] using wordTrace_append hprefix tailTrace_5809611
  have hstable : (prefixWord ++ tailWord_5809611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809611).length < 2 ^ (prefixWord ++ tailWord_5809611).sum := by decide
  have hdescent : baseEnd_5809611 < baseStart_5809611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809615 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 5, 2, 2]
def baseStart_5809615 : Nat := 118140960795 + 5809615 * 2 ^ 59
def prefixEnd_5809615 : Nat := 4983230072969 + 3 ^ 40 * 5809615 * 2
def baseEnd_5809615 : Nat := 2983124912570392588294573

theorem tailTrace_5809615 : CollatzResearch.WordTrace tailWord_5809615 prefixEnd_5809615 2983124912570392588294573 := by
  unfold tailWord_5809615
  simp only [CollatzResearch.WordTrace]
  refine ⟨211894066847764533093774299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141262711231843022062516199 211894066847764533093774299)
  ·
    refine ⟨317841100271646799640661449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211894066847764533093774299 317841100271646799640661449)
    ·
      refine ⟨238380825203735099730496087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317841100271646799640661449 238380825203735099730496087)
      ·
        refine ⟨357571237805602649595744131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238380825203735099730496087 357571237805602649595744131)
        ·
          refine ⟨536356856708403974393616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357571237805602649595744131 536356856708403974393616197)
          ·
            refine ⟨100566910632825745198803037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 536356856708403974393616197 100566910632825745198803037)
            ·
              refine ⟨37712591487309654449551139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100566910632825745198803037 37712591487309654449551139)
              ·
                refine ⟨56568887230964481674326709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37712591487309654449551139 56568887230964481674326709)
                ·
                  refine ⟨5303333177902920156968129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56568887230964481674326709 5303333177902920156968129)
                  ·
                    refine ⟨3977499883427190117726097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303333177902920156968129 3977499883427190117726097)
                    ·
                      refine ⟨2983124912570392588294573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977499883427190117726097 2983124912570392588294573)
                      ·
                        rfl

theorem cell23_5809615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2, 2].length) (baseStart_5809615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809615 prefixEnd_5809615 := by exact prefixLift 5809615
  have htrace : WordTrace (prefixWord ++ tailWord_5809615) baseStart_5809615 baseEnd_5809615 := by
    simpa [prefixWord, tailWord_5809615, baseEnd_5809615] using wordTrace_append hprefix tailTrace_5809615
  have hstable : (prefixWord ++ tailWord_5809615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809615).length < 2 ^ (prefixWord ++ tailWord_5809615).sum := by decide
  have hdescent : baseEnd_5809615 < baseStart_5809615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809649 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_5809649 : Nat := 118140960795 + 5809649 * 2 ^ 59
def prefixEnd_5809649 : Nat := 4983230072969 + 3 ^ 40 * 5809649 * 2
def baseEnd_5809649 : Nat := 2983142370912645455269417

theorem tailTrace_5809649 : CollatzResearch.WordTrace tailWord_5809649 prefixEnd_5809649 2983142370912645455269417 := by
  unfold tailWord_5809649
  simp only [CollatzResearch.WordTrace]
  refine ⟨211895306929641356900512001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141263537953094237933674667 211895306929641356900512001)
  ·
    refine ⟨158921480197231017675384001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211895306929641356900512001 158921480197231017675384001)
    ·
      refine ⟨119191110147923263256538001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158921480197231017675384001 119191110147923263256538001)
      ·
        refine ⟨89393332610942447442403501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119191110147923263256538001 89393332610942447442403501)
        ·
          refine ⟨33522499729103417790901313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89393332610942447442403501 33522499729103417790901313)
          ·
            refine ⟨25141874796827563343175985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33522499729103417790901313 25141874796827563343175985)
            ·
              refine ⟨18856406097620672507381989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25141874796827563343175985 18856406097620672507381989)
              ·
                refine ⟨3535576143303876095134123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18856406097620672507381989 3535576143303876095134123)
                ·
                  refine ⟨5303364214955814142701185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535576143303876095134123 5303364214955814142701185)
                  ·
                    refine ⟨3977523161216860607025889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303364214955814142701185 3977523161216860607025889)
                    ·
                      refine ⟨2983142370912645455269417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977523161216860607025889 2983142370912645455269417)
                      ·
                        rfl

theorem cell23_5809649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_5809649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809649 prefixEnd_5809649 := by exact prefixLift 5809649
  have htrace : WordTrace (prefixWord ++ tailWord_5809649) baseStart_5809649 baseEnd_5809649 := by
    simpa [prefixWord, tailWord_5809649, baseEnd_5809649] using wordTrace_append hprefix tailTrace_5809649
  have hstable : (prefixWord ++ tailWord_5809649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809649).length < 2 ^ (prefixWord ++ tailWord_5809649).sum := by decide
  have hdescent : baseEnd_5809649 < baseStart_5809649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809651 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 7]
def baseStart_5809651 : Nat := 118140960795 + 5809651 * 2 ^ 59
def prefixEnd_5809651 : Nat := 4983230072969 + 3 ^ 40 * 5809651 * 2
def baseEnd_5809651 : Nat := 994381132624651482481469

theorem tailTrace_5809651 : CollatzResearch.WordTrace tailWord_5809651 prefixEnd_5809651 994381132624651482481469 := by
  unfold tailWord_5809651
  simp only [CollatzResearch.WordTrace]
  refine ⟨211895379875634111242084807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141263586583756074161389871 211895379875634111242084807)
  ·
    refine ⟨317843069813451166863127211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211895379875634111242084807 317843069813451166863127211)
    ·
      refine ⟨476764604720176750294690817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317843069813451166863127211 476764604720176750294690817)
      ·
        refine ⟨357573453540132562721018113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476764604720176750294690817 357573453540132562721018113)
        ·
          refine ⟨268180090155099422040763585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357573453540132562721018113 268180090155099422040763585)
          ·
            refine ⟨201135067616324566530572689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268180090155099422040763585 201135067616324566530572689)
            ·
              refine ⟨150851300712243424897929517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201135067616324566530572689 150851300712243424897929517)
              ·
                refine ⟨56569237767091284336723569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150851300712243424897929517 56569237767091284336723569)
                ·
                  refine ⟨42426928325318463252542677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56569237767091284336723569 42426928325318463252542677)
                  ·
                    refine ⟨994381132624651482481469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42426928325318463252542677 994381132624651482481469)
                    ·
                      rfl

theorem cell23_5809651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_5809651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809651 prefixEnd_5809651 := by exact prefixLift 5809651
  have htrace : WordTrace (prefixWord ++ tailWord_5809651) baseStart_5809651 baseEnd_5809651 := by
    simpa [prefixWord, tailWord_5809651, baseEnd_5809651] using wordTrace_append hprefix tailTrace_5809651
  have hstable : (prefixWord ++ tailWord_5809651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809651).length < 2 ^ (prefixWord ++ tailWord_5809651).sum := by decide
  have hdescent : baseEnd_5809651 < baseStart_5809651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809662 : List Nat := [4, 2, 2, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5809662 : Nat := 118140960795 + 5809662 * 2 ^ 59
def prefixEnd_5809662 : Nat := 4983230072969 + 3 ^ 40 * 5809662 * 2
def baseEnd_5809662 : Nat := 2983149046161153904406857

theorem tailTrace_5809662 : CollatzResearch.WordTrace tailWord_5809662 prefixEnd_5809662 2983149046161153904406857 := by
  unfold tailWord_5809662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26486972634824282515091905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141263854052396173413823493 26486972634824282515091905)
  ·
    refine ⟨19865229476118211886318929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26486972634824282515091905 19865229476118211886318929)
    ·
      refine ⟨14898922107088658914739197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19865229476118211886318929 14898922107088658914739197)
      ·
        refine ⟨5587095790158247093027199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14898922107088658914739197 5587095790158247093027199)
        ·
          refine ⟨8380643685237370639540799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587095790158247093027199 8380643685237370639540799)
          ·
            refine ⟨12570965527856055959311199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8380643685237370639540799 12570965527856055959311199)
            ·
              refine ⟨18856448291784083938966799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12570965527856055959311199 18856448291784083938966799)
              ·
                refine ⟨28284672437676125908450199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18856448291784083938966799 28284672437676125908450199)
                ·
                  refine ⟨42427008656514188862675299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28284672437676125908450199 42427008656514188862675299)
                  ·
                    refine ⟨63640512984771283294012949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42427008656514188862675299 63640512984771283294012949)
                    ·
                      refine ⟨2983149046161153904406857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63640512984771283294012949 2983149046161153904406857)
                      ·
                        rfl

theorem cell23_5809662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5809662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809662 prefixEnd_5809662 := by exact prefixLift 5809662
  have htrace : WordTrace (prefixWord ++ tailWord_5809662) baseStart_5809662 baseEnd_5809662 := by
    simpa [prefixWord, tailWord_5809662, baseEnd_5809662] using wordTrace_append hprefix tailTrace_5809662
  have hstable : (prefixWord ++ tailWord_5809662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809662).length < 2 ^ (prefixWord ++ tailWord_5809662).sum := by decide
  have hdescent : baseEnd_5809662 < baseStart_5809662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809692 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_5809692 : Nat := 118140960795 + 5809692 * 2 ^ 59
def prefixEnd_5809692 : Nat := 4983230072969 + 3 ^ 40 * 5809692 * 2
def baseEnd_5809692 : Nat := 2983164450580788787031719

theorem tailTrace_5809692 : CollatzResearch.WordTrace tailWord_5809692 prefixEnd_5809692 2983164450580788787031719 := by
  unfold tailWord_5809692
  simp only [CollatzResearch.WordTrace]
  refine ⟨105948437634242787622163665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141264583512323716829551553 105948437634242787622163665)
  ·
    refine ⟨79461328225682090716622749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105948437634242787622163665 79461328225682090716622749)
    ·
      refine ⟨29797998084630784018733531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79461328225682090716622749 29797998084630784018733531)
      ·
        refine ⟨44696997126946176028100297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29797998084630784018733531 44696997126946176028100297)
        ·
          refine ⟨33522747845209632021075223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44696997126946176028100297 33522747845209632021075223)
          ·
            refine ⟨50284121767814448031612835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33522747845209632021075223 50284121767814448031612835)
            ·
              refine ⟨75426182651721672047419253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50284121767814448031612835 75426182651721672047419253)
              ·
                refine ⟨7071204623598906754445555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75426182651721672047419253 7071204623598906754445555)
                ·
                  refine ⟨10606806935398360131668333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7071204623598906754445555 10606806935398360131668333)
                  ·
                    refine ⟨3977552600774385049375625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10606806935398360131668333 3977552600774385049375625)
                    ·
                      refine ⟨2983164450580788787031719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977552600774385049375625 2983164450580788787031719)
                      ·
                        rfl

theorem cell23_5809692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_5809692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809692 prefixEnd_5809692 := by exact prefixLift 5809692
  have htrace : WordTrace (prefixWord ++ tailWord_5809692) baseStart_5809692 baseEnd_5809692 := by
    simpa [prefixWord, tailWord_5809692, baseEnd_5809692] using wordTrace_append hprefix tailTrace_5809692
  have hstable : (prefixWord ++ tailWord_5809692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809692).length < 2 ^ (prefixWord ++ tailWord_5809692).sum := by decide
  have hdescent : baseEnd_5809692 < baseStart_5809692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809698 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_5809698 : Nat := 118140960795 + 5809698 * 2 ^ 59
def prefixEnd_5809698 : Nat := 4983230072969 + 3 ^ 40 * 5809698 * 2
def baseEnd_5809698 : Nat := 994389177154905254518897

theorem tailTrace_5809698 : CollatzResearch.WordTrace tailWord_5809698 prefixEnd_5809698 994389177154905254518897 := by
  unfold tailWord_5809698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52974273526615959567261437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141264729404309225512697165 52974273526615959567261437)
  ·
    refine ⟨19865352572480984837723039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52974273526615959567261437 19865352572480984837723039)
    ·
      refine ⟨29798028858721477256584559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19865352572480984837723039 29798028858721477256584559)
      ·
        refine ⟨44697043288082215884876839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29798028858721477256584559 44697043288082215884876839)
        ·
          refine ⟨67045564932123323827315259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44697043288082215884876839 67045564932123323827315259)
          ·
            refine ⟨100568347398184985740972889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67045564932123323827315259 100568347398184985740972889)
            ·
              refine ⟨75426260548638739305729667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100568347398184985740972889 75426260548638739305729667)
              ·
                refine ⟨113139390822958108958594501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75426260548638739305729667 113139390822958108958594501)
                ·
                  refine ⟨21213635779304645429736469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113139390822958108958594501 21213635779304645429736469)
                  ·
                    refine ⟨994389177154905254518897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21213635779304645429736469 994389177154905254518897)
                    ·
                      rfl

theorem cell23_5809698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_5809698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809698 prefixEnd_5809698 := by exact prefixLift 5809698
  have htrace : WordTrace (prefixWord ++ tailWord_5809698) baseStart_5809698 baseEnd_5809698 := by
    simpa [prefixWord, tailWord_5809698, baseEnd_5809698] using wordTrace_append hprefix tailTrace_5809698
  have hstable : (prefixWord ++ tailWord_5809698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809698).length < 2 ^ (prefixWord ++ tailWord_5809698).sum := by decide
  have hdescent : baseEnd_5809698 < baseStart_5809698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809745 : List Nat := [1, 2, 2, 1, 3, 2, 2, 5, 5]
def baseStart_5809745 : Nat := 118140960795 + 5809745 * 2 ^ 59
def prefixEnd_5809745 : Nat := 4983230072969 + 3 ^ 40 * 5809745 * 2
def baseEnd_5809745 : Nat := 331465740561719675518775

theorem tailTrace_5809745 : CollatzResearch.WordTrace tailWord_5809745 prefixEnd_5809745 331465740561719675518775 := by
  unfold tailWord_5809745
  simp only [CollatzResearch.WordTrace]
  refine ⟨211898808337293565296006689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141265872224862376864004459 211898808337293565296006689)
  ·
    refine ⟨158924106252970173972005017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211898808337293565296006689 158924106252970173972005017)
    ·
      refine ⟨119193079689727630479003763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158924106252970173972005017 119193079689727630479003763)
      ·
        refine ⟨178789619534591445718505645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119193079689727630479003763 178789619534591445718505645)
        ·
          refine ⟨67046107325471792144439617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178789619534591445718505645 67046107325471792144439617)
          ·
            refine ⟨50284580494103844108329713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67046107325471792144439617 50284580494103844108329713)
            ·
              refine ⟨37713435370577883081247285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50284580494103844108329713 37713435370577883081247285)
              ·
                refine ⟨3535634565991676538866933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37713435370577883081247285 3535634565991676538866933)
                ·
                  refine ⟨331465740561719675518775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535634565991676538866933 331465740561719675518775)
                  ·
                    rfl

theorem cell23_5809745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 5, 5].length) (baseStart_5809745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809745 prefixEnd_5809745 := by exact prefixLift 5809745
  have htrace : WordTrace (prefixWord ++ tailWord_5809745) baseStart_5809745 baseEnd_5809745 := by
    simpa [prefixWord, tailWord_5809745, baseEnd_5809745] using wordTrace_append hprefix tailTrace_5809745
  have hstable : (prefixWord ++ tailWord_5809745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809745).length < 2 ^ (prefixWord ++ tailWord_5809745).sum := by decide
  have hdescent : baseEnd_5809745 < baseStart_5809745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809756 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5809756 : Nat := 118140960795 + 5809756 * 2 ^ 59
def prefixEnd_5809756 : Nat := 4983230072969 + 3 ^ 40 * 5809756 * 2
def baseEnd_5809756 : Nat := 2983197313342676536631425

theorem tailTrace_5809756 : CollatzResearch.WordTrace tailWord_5809756 prefixEnd_5809756 2983197313342676536631425 := by
  unfold tailWord_5809756
  simp only [CollatzResearch.WordTrace]
  refine ⟨105949604770126857087328561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141266139693502476116438081 105949604770126857087328561)
  ·
    refine ⟨79462203577595142815496421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105949604770126857087328561 79462203577595142815496421)
    ·
      refine ⟨14899163170799089277905579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79462203577595142815496421 14899163170799089277905579)
      ·
        refine ⟨22348744756198633916858369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14899163170799089277905579 22348744756198633916858369)
        ·
          refine ⟨16761558567148975437643777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22348744756198633916858369 16761558567148975437643777)
          ·
            refine ⟨12571168925361731578232833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16761558567148975437643777 12571168925361731578232833)
            ·
              refine ⟨9428376694021298683674625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12571168925361731578232833 9428376694021298683674625)
              ·
                refine ⟨7071282520515974012755969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9428376694021298683674625 7071282520515974012755969)
                ·
                  refine ⟨5303461890386980509566977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071282520515974012755969 5303461890386980509566977)
                  ·
                    refine ⟨3977596417790235382175233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303461890386980509566977 3977596417790235382175233)
                    ·
                      refine ⟨2983197313342676536631425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977596417790235382175233 2983197313342676536631425)
                      ·
                        rfl

theorem cell23_5809756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5809756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809756 prefixEnd_5809756 := by exact prefixLift 5809756
  have htrace : WordTrace (prefixWord ++ tailWord_5809756) baseStart_5809756 baseEnd_5809756 := by
    simpa [prefixWord, tailWord_5809756, baseEnd_5809756] using wordTrace_append hprefix tailTrace_5809756
  have hstable : (prefixWord ++ tailWord_5809756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809756).length < 2 ^ (prefixWord ++ tailWord_5809756).sum := by decide
  have hdescent : baseEnd_5809756 < baseStart_5809756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809795 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 6, 2]
def baseStart_5809795 : Nat := 118140960795 + 5809795 * 2 ^ 59
def prefixEnd_5809795 : Nat := 4983230072969 + 3 ^ 40 * 5809795 * 2
def baseEnd_5809795 : Nat := 2983217339088201884043745

theorem tailTrace_5809795 : CollatzResearch.WordTrace tailWord_5809795 prefixEnd_5809795 2983217339088201884043745 := by
  unfold tailWord_5809795
  simp only [CollatzResearch.WordTrace]
  refine ⟨211900631987112423835326839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141267087991408282556884559 211900631987112423835326839)
  ·
    refine ⟨317850947980668635752990259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211900631987112423835326839 317850947980668635752990259)
    ·
      refine ⟨476776421971002953629485389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317850947980668635752990259 476776421971002953629485389)
      ·
        refine ⟨178791158239126107611057021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 476776421971002953629485389 178791158239126107611057021)
        ·
          refine ⟨67046684339672290354146383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178791158239126107611057021 67046684339672290354146383)
          ·
            refine ⟨100570026509508435531219575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67046684339672290354146383 100570026509508435531219575)
            ·
              refine ⟨150855039764262653296829363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100570026509508435531219575 150855039764262653296829363)
              ·
                refine ⟨226282559646393979945244045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150855039764262653296829363 226282559646393979945244045)
                ·
                  refine ⟨84855959867397742479466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 226282559646393979945244045 84855959867397742479466517)
                  ·
                    refine ⟨3977623118784269178724993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84855959867397742479466517 3977623118784269178724993)
                    ·
                      refine ⟨2983217339088201884043745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977623118784269178724993 2983217339088201884043745)
                      ·
                        rfl

theorem cell23_5809795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6, 2].length) (baseStart_5809795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809795 prefixEnd_5809795 := by exact prefixLift 5809795
  have htrace : WordTrace (prefixWord ++ tailWord_5809795) baseStart_5809795 baseEnd_5809795 := by
    simpa [prefixWord, tailWord_5809795, baseEnd_5809795] using wordTrace_append hprefix tailTrace_5809795
  have hstable : (prefixWord ++ tailWord_5809795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809795).length < 2 ^ (prefixWord ++ tailWord_5809795).sum := by decide
  have hdescent : baseEnd_5809795 < baseStart_5809795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809808 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_5809808 : Nat := 118140960795 + 5809808 * 2 ^ 59
def prefixEnd_5809808 : Nat := 4983230072969 + 3 ^ 40 * 5809808 * 2
def baseEnd_5809808 : Nat := 2983224014336710333181185

theorem tailTrace_5809808 : CollatzResearch.WordTrace tailWord_5809808 prefixEnd_5809808 2983224014336710333181185 := by
  unfold tailWord_5809808
  simp only [CollatzResearch.WordTrace]
  refine ⟨105950553068032663527775039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141267404090710218037033385 105950553068032663527775039)
  ·
    refine ⟨158925829602048995291662559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105950553068032663527775039 158925829602048995291662559)
    ·
      refine ⟨238388744403073492937493839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158925829602048995291662559 238388744403073492937493839)
      ·
        refine ⟨357583116604610239406240759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238388744403073492937493839 357583116604610239406240759)
        ·
          refine ⟨536374674906915359109361139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357583116604610239406240759 536374674906915359109361139)
          ·
            refine ⟨804562012360373038664041709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536374674906915359109361139 804562012360373038664041709)
            ·
              refine ⟨301710754635139889499015641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804562012360373038664041709 301710754635139889499015641)
              ·
                refine ⟨226283065976354917124261731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301710754635139889499015641 226283065976354917124261731)
                ·
                  refine ⟨339424598964532375686392597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226283065976354917124261731 339424598964532375686392597)
                  ·
                    refine ⟨15910528076462455110299653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 339424598964532375686392597 15910528076462455110299653)
                    ·
                      refine ⟨2983224014336710333181185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15910528076462455110299653 2983224014336710333181185)
                      ·
                        rfl

theorem cell23_5809808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_5809808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809808 prefixEnd_5809808 := by exact prefixLift 5809808
  have htrace : WordTrace (prefixWord ++ tailWord_5809808) baseStart_5809808 baseEnd_5809808 := by
    simpa [prefixWord, tailWord_5809808, baseEnd_5809808] using wordTrace_append hprefix tailTrace_5809808
  have hstable : (prefixWord ++ tailWord_5809808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809808).length < 2 ^ (prefixWord ++ tailWord_5809808).sum := by decide
  have hdescent : baseEnd_5809808 < baseStart_5809808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809848 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_5809848 : Nat := 118140960795 + 5809848 * 2 ^ 59
def prefixEnd_5809848 : Nat := 4983230072969 + 3 ^ 40 * 5809848 * 2
def baseEnd_5809848 : Nat := 994414851187630058893667

theorem tailTrace_5809848 : CollatzResearch.WordTrace tailWord_5809848 prefixEnd_5809848 994414851187630058893667 := by
  unfold tailWord_5809848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105951282527960206943503099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141268376703946942591337465 105951282527960206943503099)
  ·
    refine ⟨158926923791940310415254649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105951282527960206943503099 158926923791940310415254649)
    ·
      refine ⟨119195192843955232811440987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158926923791940310415254649 119195192843955232811440987)
      ·
        refine ⟨178792789265932849217161481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119195192843955232811440987 178792789265932849217161481)
        ·
          refine ⟨134094591949449636912871111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178792789265932849217161481 134094591949449636912871111)
          ·
            refine ⟨201141887924174455369306667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134094591949449636912871111 201141887924174455369306667)
            ·
              refine ⟨301712831886261683053960001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201141887924174455369306667 301712831886261683053960001)
              ·
                refine ⟨226284623914696262290470001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301712831886261683053960001 226284623914696262290470001)
                ·
                  refine ⟨169713467936022196717852501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226284623914696262290470001 169713467936022196717852501)
                  ·
                    refine ⟨994414851187630058893667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 169713467936022196717852501 994414851187630058893667)
                    ·
                      rfl

theorem cell23_5809848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_5809848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809848 prefixEnd_5809848 := by exact prefixLift 5809848
  have htrace : WordTrace (prefixWord ++ tailWord_5809848) baseStart_5809848 baseEnd_5809848 := by
    simpa [prefixWord, tailWord_5809848, baseEnd_5809848] using wordTrace_append hprefix tailTrace_5809848
  have hstable : (prefixWord ++ tailWord_5809848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809848).length < 2 ^ (prefixWord ++ tailWord_5809848).sum := by decide
  have hdescent : baseEnd_5809848 < baseStart_5809848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809902 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_5809902 : Nat := 118140960795 + 5809902 * 2 ^ 59
def prefixEnd_5809902 : Nat := 4983230072969 + 3 ^ 40 * 5809902 * 2
def baseEnd_5809902 : Nat := 2983272281518232965405753

theorem tailTrace_5809902 : CollatzResearch.WordTrace tailWord_5809902 prefixEnd_5809902 2983272281518232965405753 := by
  unfold tailWord_5809902
  simp only [CollatzResearch.WordTrace]
  refine ⟨26488066824715597638683995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141269689731816520739647973 26488066824715597638683995)
  ·
    refine ⟨39732100237073396458025993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26488066824715597638683995 39732100237073396458025993)
    ·
      refine ⟨29799075177805047343519495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39732100237073396458025993 29799075177805047343519495)
      ·
        refine ⟨44698612766707571015279243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29799075177805047343519495 44698612766707571015279243)
        ·
          refine ⟨67047919150061356522918865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44698612766707571015279243 67047919150061356522918865)
          ·
            refine ⟨50285939362546017392189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67047919150061356522918865 50285939362546017392189149)
            ·
              refine ⟨18857227260954756522070931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50285939362546017392189149 18857227260954756522070931)
              ·
                refine ⟨28285840891432134783106397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18857227260954756522070931 28285840891432134783106397)
                ·
                  refine ⟨10607190334287050543664899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28285840891432134783106397 10607190334287050543664899)
                  ·
                    refine ⟨15910785501430575815497349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10607190334287050543664899 15910785501430575815497349)
                    ·
                      refine ⟨2983272281518232965405753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15910785501430575815497349 2983272281518232965405753)
                      ·
                        rfl

theorem cell23_5809902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_5809902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809902 prefixEnd_5809902 := by exact prefixLift 5809902
  have htrace : WordTrace (prefixWord ++ tailWord_5809902) baseStart_5809902 baseEnd_5809902 := by
    simpa [prefixWord, tailWord_5809902, baseEnd_5809902] using wordTrace_append hprefix tailTrace_5809902
  have hstable : (prefixWord ++ tailWord_5809902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809902).length < 2 ^ (prefixWord ++ tailWord_5809902).sum := by decide
  have hdescent : baseEnd_5809902 < baseStart_5809902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809973 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_5809973 : Nat := 118140960795 + 5809973 * 2 ^ 59
def prefixEnd_5809973 : Nat := 4983230072969 + 3 ^ 40 * 5809973 * 2
def baseEnd_5809973 : Nat := 2983308738644702187617927

theorem tailTrace_5809973 : CollatzResearch.WordTrace tailWord_5809973 prefixEnd_5809973 2983308738644702187617927 := by
  unfold tailWord_5809973
  simp only [CollatzResearch.WordTrace]
  refine ⟨211907124180467560235306573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141271416120311706823537715 211907124180467560235306573)
  ·
    refine ⟨79465171567675335088239965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211907124180467560235306573 79465171567675335088239965)
    ·
      refine ⟨29799439337878250658089987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79465171567675335088239965 29799439337878250658089987)
      ·
        refine ⟨44699159006817375987134981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29799439337878250658089987 44699159006817375987134981)
        ·
          refine ⟨8381092313778257997587809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44699159006817375987134981 8381092313778257997587809)
          ·
            refine ⟨6285819235333693498190857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8381092313778257997587809 6285819235333693498190857)
            ·
              refine ⟨4714364426500270123643143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285819235333693498190857 4714364426500270123643143)
              ·
                refine ⟨7071546639750405185464715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714364426500270123643143 7071546639750405185464715)
                ·
                  refine ⟨10607319959625607778197073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7071546639750405185464715 10607319959625607778197073)
                  ·
                    refine ⟨7955489969719205833647805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10607319959625607778197073 7955489969719205833647805)
                    ·
                      refine ⟨2983308738644702187617927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7955489969719205833647805 2983308738644702187617927)
                      ·
                        rfl

theorem cell23_5809973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_5809973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809973 prefixEnd_5809973 := by exact prefixLift 5809973
  have htrace : WordTrace (prefixWord ++ tailWord_5809973) baseStart_5809973 baseEnd_5809973 := by
    simpa [prefixWord, tailWord_5809973, baseEnd_5809973] using wordTrace_append hprefix tailTrace_5809973
  have hstable : (prefixWord ++ tailWord_5809973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809973).length < 2 ^ (prefixWord ++ tailWord_5809973).sum := by decide
  have hdescent : baseEnd_5809973 < baseStart_5809973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5809975 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4]
def baseStart_5809975 : Nat := 118140960795 + 5809975 * 2 ^ 59
def prefixEnd_5809975 : Nat := 4983230072969 + 3 ^ 40 * 5809975 * 2
def baseEnd_5809975 : Nat := 2983309765606011179792917

theorem tailTrace_5809975 : CollatzResearch.WordTrace tailWord_5809975 prefixEnd_5809975 2983309765606011179792917 := by
  unfold tailWord_5809975
  simp only [CollatzResearch.WordTrace]
  refine ⟨211907197126460314576879379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141271464750973543051252919 211907197126460314576879379)
  ·
    refine ⟨317860795689690471865319069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211907197126460314576879379 317860795689690471865319069)
    ·
      refine ⟨119197798383633926949494651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317860795689690471865319069 119197798383633926949494651)
      ·
        refine ⟨178796697575450890424241977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119197798383633926949494651 178796697575450890424241977)
        ·
          refine ⟨134097523181588167818181483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178796697575450890424241977 134097523181588167818181483)
          ·
            refine ⟨201146284772382251727272225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134097523181588167818181483 201146284772382251727272225)
            ·
              refine ⟨150859713579286688795454169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201146284772382251727272225 150859713579286688795454169)
              ·
                refine ⟨113144785184465016596590627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150859713579286688795454169 113144785184465016596590627)
                ·
                  refine ⟨169717177776697524894885941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113144785184465016596590627 169717177776697524894885941)
                  ·
                    refine ⟨15910985416565392958895557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169717177776697524894885941 15910985416565392958895557)
                    ·
                      refine ⟨2983309765606011179792917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15910985416565392958895557 2983309765606011179792917)
                      ·
                        rfl

theorem cell23_5809975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_5809975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5809975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5809975 prefixEnd_5809975 := by exact prefixLift 5809975
  have htrace : WordTrace (prefixWord ++ tailWord_5809975) baseStart_5809975 baseEnd_5809975 := by
    simpa [prefixWord, tailWord_5809975, baseEnd_5809975] using wordTrace_append hprefix tailTrace_5809975
  have hstable : (prefixWord ++ tailWord_5809975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5809975).length < 2 ^ (prefixWord ++ tailWord_5809975).sum := by decide
  have hdescent : baseEnd_5809975 < baseStart_5809975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5809975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810002 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_5810002 : Nat := 118140960795 + 5810002 * 2 ^ 59
def prefixEnd_5810002 : Nat := 4983230072969 + 3 ^ 40 * 5810002 * 2
def baseEnd_5810002 : Nat := 994441209861227524718431

theorem tailTrace_5810002 : CollatzResearch.WordTrace tailWord_5810002 prefixEnd_5810002 994441209861227524718431 := by
  unfold tailWord_5810002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977045474340624547028065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141272121264908332125408173 52977045474340624547028065)
  ·
    refine ⟨39732784105755468410271049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52977045474340624547028065 39732784105755468410271049)
    ·
      refine ⟨29799588079316601307703287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39732784105755468410271049 29799588079316601307703287)
      ·
        refine ⟨44699382118974901961554931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29799588079316601307703287 44699382118974901961554931)
        ·
          refine ⟨67049073178462352942332397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44699382118974901961554931 67049073178462352942332397)
          ·
            refine ⟨25143402441923382353374649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67049073178462352942332397 25143402441923382353374649)
            ·
              refine ⟨18857551831442536765030987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25143402441923382353374649 18857551831442536765030987)
              ·
                refine ⟨28286327747163805147546481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18857551831442536765030987 28286327747163805147546481)
                ·
                  refine ⟨21214745810372853860659861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28286327747163805147546481 21214745810372853860659861)
                  ·
                    refine ⟨994441209861227524718431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21214745810372853860659861 994441209861227524718431)
                    ·
                      rfl

theorem cell23_5810002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_5810002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810002 prefixEnd_5810002 := by exact prefixLift 5810002
  have htrace : WordTrace (prefixWord ++ tailWord_5810002) baseStart_5810002 baseEnd_5810002 := by
    simpa [prefixWord, tailWord_5810002, baseEnd_5810002] using wordTrace_append hprefix tailTrace_5810002
  have hstable : (prefixWord ++ tailWord_5810002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810002).length < 2 ^ (prefixWord ++ tailWord_5810002).sum := by decide
  have hdescent : baseEnd_5810002 < baseStart_5810002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810042 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3]
def baseStart_5810042 : Nat := 118140960795 + 5810042 * 2 ^ 59
def prefixEnd_5810042 : Nat := 4983230072969 + 3 ^ 40 * 5810042 * 2
def baseEnd_5810042 : Nat := 2983344168809862417655109

theorem tailTrace_5810042 : CollatzResearch.WordTrace tailWord_5810042 prefixEnd_5810042 2983344168809862417655109 := by
  unfold tailWord_5810042
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977410204304396254892095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141273093878145056679712253 52977410204304396254892095)
  ·
    refine ⟨79466115306456594382338143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52977410204304396254892095 79466115306456594382338143)
    ·
      refine ⟨119199172959684891573507215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79466115306456594382338143 119199172959684891573507215)
      ·
        refine ⟨178798759439527337360260823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119199172959684891573507215 178798759439527337360260823)
        ·
          refine ⟨268198139159291006040391235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178798759439527337360260823 268198139159291006040391235)
          ·
            refine ⟨402297208738936509060586853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268198139159291006040391235 402297208738936509060586853)
            ·
              refine ⟨75430726638550595448860035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 402297208738936509060586853 75430726638550595448860035)
              ·
                refine ⟨113146089957825893173290053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75430726638550595448860035 113146089957825893173290053)
                ·
                  refine ⟨21214891867092354969991885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113146089957825893173290053 21214891867092354969991885)
                  ·
                    refine ⟨7955584450159633113746957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21214891867092354969991885 7955584450159633113746957)
                    ·
                      refine ⟨2983344168809862417655109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7955584450159633113746957 2983344168809862417655109)
                      ·
                        rfl

theorem cell23_5810042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_5810042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810042 prefixEnd_5810042 := by exact prefixLift 5810042
  have htrace : WordTrace (prefixWord ++ tailWord_5810042) baseStart_5810042 baseEnd_5810042 := by
    simpa [prefixWord, tailWord_5810042, baseEnd_5810042] using wordTrace_append hprefix tailTrace_5810042
  have hstable : (prefixWord ++ tailWord_5810042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810042).length < 2 ^ (prefixWord ++ tailWord_5810042).sum := by decide
  have hdescent : baseEnd_5810042 < baseStart_5810042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810094 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5810094 : Nat := 118140960795 + 5810094 * 2 ^ 59
def prefixEnd_5810094 : Nat := 4983230072969 + 3 ^ 40 * 5810094 * 2
def baseEnd_5810094 : Nat := 2983370869803896214204871

theorem tailTrace_5810094 : CollatzResearch.WordTrace tailWord_5810094 prefixEnd_5810094 2983370869803896214204871 := by
  unfold tailWord_5810094
  simp only [CollatzResearch.WordTrace]
  refine ⟨26488942176628649737557667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141274358275352798600307557 26488942176628649737557667)
  ·
    refine ⟨39733413264942974606336501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26488942176628649737557667 39733413264942974606336501)
    ·
      refine ⟨3725007493588403869344047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39733413264942974606336501 3725007493588403869344047)
      ·
        refine ⟨5587511240382605804016071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725007493588403869344047 5587511240382605804016071)
        ·
          refine ⟨8381266860573908706024107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587511240382605804016071 8381266860573908706024107)
          ·
            refine ⟨12571900290860863059036161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381266860573908706024107 12571900290860863059036161)
            ·
              refine ⟨9428925218145647294277121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12571900290860863059036161 9428925218145647294277121)
              ·
                refine ⟨7071693913609235470707841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9428925218145647294277121 7071693913609235470707841)
                ·
                  refine ⟨5303770435206926603030881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071693913609235470707841 5303770435206926603030881)
                  ·
                    refine ⟨3977827826405194952273161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303770435206926603030881 3977827826405194952273161)
                    ·
                      refine ⟨2983370869803896214204871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977827826405194952273161 2983370869803896214204871)
                      ·
                        rfl

theorem cell23_5810094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5810094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810094 prefixEnd_5810094 := by exact prefixLift 5810094
  have htrace : WordTrace (prefixWord ++ tailWord_5810094) baseStart_5810094 baseEnd_5810094 := by
    simpa [prefixWord, tailWord_5810094, baseEnd_5810094] using wordTrace_append hprefix tailTrace_5810094
  have hstable : (prefixWord ++ tailWord_5810094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810094).length < 2 ^ (prefixWord ++ tailWord_5810094).sum := by decide
  have hdescent : baseEnd_5810094 < baseStart_5810094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810099 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 2, 4, 2]
def baseStart_5810099 : Nat := 118140960795 + 5810099 * 2 ^ 59
def prefixEnd_5810099 : Nat := 4983230072969 + 3 ^ 40 * 5810099 * 2
def baseEnd_5810099 : Nat := 2983373437207168694642347

theorem tailTrace_5810099 : CollatzResearch.WordTrace tailWord_5810099 prefixEnd_5810099 2983373437207168694642347 := by
  unfold tailWord_5810099
  simp only [CollatzResearch.WordTrace]
  refine ⟨211911719778011083754393351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141274479852007389169595567 211911719778011083754393351)
  ·
    refine ⟨317867579667016625631590027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211911719778011083754393351 317867579667016625631590027)
    ·
      refine ⟨476801369500524938447385041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317867579667016625631590027 476801369500524938447385041)
      ·
        refine ⟨357601027125393703835538781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476801369500524938447385041 357601027125393703835538781)
        ·
          refine ⟨134100385172022638938327043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357601027125393703835538781 134100385172022638938327043)
          ·
            refine ⟨201150577758033958407490565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134100385172022638938327043 201150577758033958407490565)
            ·
              refine ⟨37715733329631367201404481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201150577758033958407490565 37715733329631367201404481)
              ·
                refine ⟨28286799997223525401053361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37715733329631367201404481 28286799997223525401053361)
                ·
                  refine ⟨21215099997917644050790021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28286799997223525401053361 21215099997917644050790021)
                  ·
                    refine ⟨3977831249609558259523129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21215099997917644050790021 3977831249609558259523129)
                    ·
                      refine ⟨2983373437207168694642347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977831249609558259523129 2983373437207168694642347)
                      ·
                        rfl

theorem cell23_5810099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4, 2].length) (baseStart_5810099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810099 prefixEnd_5810099 := by exact prefixLift 5810099
  have htrace : WordTrace (prefixWord ++ tailWord_5810099) baseStart_5810099 baseEnd_5810099 := by
    simpa [prefixWord, tailWord_5810099, baseEnd_5810099] using wordTrace_append hprefix tailTrace_5810099
  have hstable : (prefixWord ++ tailWord_5810099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810099).length < 2 ^ (prefixWord ++ tailWord_5810099).sum := by decide
  have hdescent : baseEnd_5810099 < baseStart_5810099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810143 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 1, 4]
def baseStart_5810143 : Nat := 118140960795 + 5810143 * 2 ^ 59
def prefixEnd_5810143 : Nat := 4983230072969 + 3 ^ 40 * 5810143 * 2
def baseEnd_5810143 : Nat := 994465343451988840830715

theorem tailTrace_5810143 : CollatzResearch.WordTrace tailWord_5810143 prefixEnd_5810143 994465343451988840830715 := by
  unfold tailWord_5810143
  simp only [CollatzResearch.WordTrace]
  refine ⟨211913324589851679268995083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141275549726567786179330055 211913324589851679268995083)
  ·
    refine ⟨317869986884777518903492625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211913324589851679268995083 317869986884777518903492625)
    ·
      refine ⟨238402490163583139177619469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317869986884777518903492625 238402490163583139177619469)
      ·
        refine ⟨89400933811343677191607301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238402490163583139177619469 89400933811343677191607301)
        ·
          refine ⟨16762675089626939473426369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89400933811343677191607301 16762675089626939473426369)
          ·
            refine ⟨12572006317220204605069777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16762675089626939473426369 12572006317220204605069777)
            ·
              refine ⟨9429004737915153453802333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12572006317220204605069777 9429004737915153453802333)
              ·
                refine ⟨3535876776718182545175875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9429004737915153453802333 3535876776718182545175875)
                ·
                  refine ⟨5303815165077273817763813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535876776718182545175875 5303815165077273817763813)
                  ·
                    refine ⟨994465343451988840830715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303815165077273817763813 994465343451988840830715)
                    ·
                      rfl

theorem cell23_5810143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 4].length) (baseStart_5810143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810143 prefixEnd_5810143 := by exact prefixLift 5810143
  have htrace : WordTrace (prefixWord ++ tailWord_5810143) baseStart_5810143 baseEnd_5810143 := by
    simpa [prefixWord, tailWord_5810143, baseEnd_5810143] using wordTrace_append hprefix tailTrace_5810143
  have hstable : (prefixWord ++ tailWord_5810143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810143).length < 2 ^ (prefixWord ++ tailWord_5810143).sum := by decide
  have hdescent : baseEnd_5810143 < baseStart_5810143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810233 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 2, 4]
def baseStart_5810233 : Nat := 118140960795 + 5810233 * 2 ^ 59
def prefixEnd_5810233 : Nat := 4983230072969 + 3 ^ 40 * 5810233 * 2
def baseEnd_5810233 : Nat := 994480747871623723455577

theorem tailTrace_5810233 : CollatzResearch.WordTrace tailWord_5810233 prefixEnd_5810233 994480747871623723455577 := by
  unfold tailWord_5810233
  simp only [CollatzResearch.WordTrace]
  refine ⟨211916607159525624639771353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141277738106350416426514235 211916607159525624639771353)
  ·
    refine ⟨158937455369644218479828515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211916607159525624639771353 158937455369644218479828515)
    ·
      refine ⟨238406183054466327719742773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158937455369644218479828515 238406183054466327719742773)
      ·
        refine ⟨22350579661356218223725885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238406183054466327719742773 22350579661356218223725885)
        ·
          refine ⟨8381467373008581833897207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22350579661356218223725885 8381467373008581833897207)
          ·
            refine ⟨12572201059512872750845811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381467373008581833897207 12572201059512872750845811)
            ·
              refine ⟨18858301589269309126268717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572201059512872750845811 18858301589269309126268717)
              ·
                refine ⟨7071863095975990922350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18858301589269309126268717 7071863095975990922350769)
                ·
                  refine ⟨5303897321981993191763077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071863095975990922350769 5303897321981993191763077)
                  ·
                    refine ⟨994480747871623723455577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5303897321981993191763077 994480747871623723455577)
                    ·
                      rfl

theorem cell23_5810233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 4].length) (baseStart_5810233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810233 prefixEnd_5810233 := by exact prefixLift 5810233
  have htrace : WordTrace (prefixWord ++ tailWord_5810233) baseStart_5810233 baseEnd_5810233 := by
    simpa [prefixWord, tailWord_5810233, baseEnd_5810233] using wordTrace_append hprefix tailTrace_5810233
  have hstable : (prefixWord ++ tailWord_5810233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810233).length < 2 ^ (prefixWord ++ tailWord_5810233).sum := by decide
  have hdescent : baseEnd_5810233 < baseStart_5810233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810246 : List Nat := [6, 1, 1, 1, 1, 1, 1, 11]
def baseStart_5810246 : Nat := 118140960795 + 5810246 * 2 ^ 59
def prefixEnd_5810246 : Nat := 4983230072969 + 3 ^ 40 * 5810246 * 2
def baseEnd_5810246 : Nat := 110498108106051097018673

theorem tailTrace_5810246 : CollatzResearch.WordTrace tailWord_5810246 prefixEnd_5810246 110498108106051097018673 := by
  unfold tailWord_5810246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6622408790889953995624831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 141278054205652351906663061 6622408790889953995624831)
  ·
    refine ⟨9933613186334930993437247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6622408790889953995624831 9933613186334930993437247)
    ·
      refine ⟨14900419779502396490155871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9933613186334930993437247 14900419779502396490155871)
      ·
        refine ⟨22350629669253594735233807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14900419779502396490155871 22350629669253594735233807)
        ·
          refine ⟨33525944503880392102850711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22350629669253594735233807 33525944503880392102850711)
          ·
            refine ⟨50288916755820588154276067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33525944503880392102850711 50288916755820588154276067)
            ·
              refine ⟨75433375133730882231414101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50288916755820588154276067 75433375133730882231414101)
              ·
                refine ⟨110498108106051097018673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75433375133730882231414101 110498108106051097018673)
                ·
                  rfl

theorem cell23_5810246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_5810246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810246 prefixEnd_5810246 := by exact prefixLift 5810246
  have htrace : WordTrace (prefixWord ++ tailWord_5810246) baseStart_5810246 baseEnd_5810246 := by
    simpa [prefixWord, tailWord_5810246, baseEnd_5810246] using wordTrace_append hprefix tailTrace_5810246
  have hstable : (prefixWord ++ tailWord_5810246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810246).length < 2 ^ (prefixWord ++ tailWord_5810246).sum := by decide
  have hdescent : baseEnd_5810246 < baseStart_5810246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810274 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_5810274 : Nat := 118140960795 + 5810274 * 2 ^ 59
def prefixEnd_5810274 : Nat := 4983230072969 + 3 ^ 40 * 5810274 * 2
def baseEnd_5810274 : Nat := 2983463296321705509954043

theorem tailTrace_5810274 : CollatzResearch.WordTrace tailWord_5810274 prefixEnd_5810274 2983463296321705509954043 := by
  unfold tailWord_5810274
  simp only [CollatzResearch.WordTrace]
  refine ⟨52979525638094272160503469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141278735034918059094675917 52979525638094272160503469)
  ·
    refine ⟨19867322114285352060188801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52979525638094272160503469 19867322114285352060188801)
    ·
      refine ⟨14900491585714014045141601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19867322114285352060188801 14900491585714014045141601)
      ·
        refine ⟨11175368689285510533856201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14900491585714014045141601 11175368689285510533856201)
        ·
          refine ⟨8381526516964132900392151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11175368689285510533856201 8381526516964132900392151)
          ·
            refine ⟨12572289775446199350588227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381526516964132900392151 12572289775446199350588227)
            ·
              refine ⟨18858434663169299025882341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572289775446199350588227 18858434663169299025882341)
              ·
                refine ⟨3535956499344243567352939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18858434663169299025882341 3535956499344243567352939)
                ·
                  refine ⟨5303934749016365351029409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3535956499344243567352939 5303934749016365351029409)
                  ·
                    refine ⟨3977951061762274013272057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303934749016365351029409 3977951061762274013272057)
                    ·
                      refine ⟨2983463296321705509954043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977951061762274013272057 2983463296321705509954043)
                      ·
                        rfl

theorem cell23_5810274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_5810274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810274 prefixEnd_5810274 := by exact prefixLift 5810274
  have htrace : WordTrace (prefixWord ++ tailWord_5810274) baseStart_5810274 baseEnd_5810274 := by
    simpa [prefixWord, tailWord_5810274, baseEnd_5810274] using wordTrace_append hprefix tailTrace_5810274
  have hstable : (prefixWord ++ tailWord_5810274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810274).length < 2 ^ (prefixWord ++ tailWord_5810274).sum := by decide
  have hdescent : baseEnd_5810274 < baseStart_5810274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810279 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_5810279 : Nat := 118140960795 + 5810279 * 2 ^ 59
def prefixEnd_5810279 : Nat := 4983230072969 + 3 ^ 40 * 5810279 * 2
def baseEnd_5810279 : Nat := 2983465863724977990391519

theorem tailTrace_5810279 : CollatzResearch.WordTrace tailWord_5810279 prefixEnd_5810279 2983465863724977990391519 := by
  unfold tailWord_5810279
  simp only [CollatzResearch.WordTrace]
  refine ⟨211918284917358974495945891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141278856611572649663963927 211918284917358974495945891)
  ·
    refine ⟨317877427376038461743918837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211918284917358974495945891 317877427376038461743918837)
    ·
      refine ⟨29801008816503605788492391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317877427376038461743918837 29801008816503605788492391)
      ·
        refine ⟨44701513224755408682738587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29801008816503605788492391 44701513224755408682738587)
        ·
          refine ⟨67052269837133113024107881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44701513224755408682738587 67052269837133113024107881)
          ·
            refine ⟨50289202377849834768080911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67052269837133113024107881 50289202377849834768080911)
            ·
              refine ⟨75433803566774752152121367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50289202377849834768080911 75433803566774752152121367)
              ·
                refine ⟨113150705350162128228182051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75433803566774752152121367 113150705350162128228182051)
                ·
                  refine ⟨169726058025243192342273077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113150705350162128228182051 169726058025243192342273077)
                  ·
                    refine ⟨15911817939866549282088101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 169726058025243192342273077 15911817939866549282088101)
                    ·
                      refine ⟨2983465863724977990391519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15911817939866549282088101 2983465863724977990391519)
                      ·
                        rfl

theorem cell23_5810279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_5810279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810279 prefixEnd_5810279 := by exact prefixLift 5810279
  have htrace : WordTrace (prefixWord ++ tailWord_5810279) baseStart_5810279 baseEnd_5810279 := by
    simpa [prefixWord, tailWord_5810279, baseEnd_5810279] using wordTrace_append hprefix tailTrace_5810279
  have hstable : (prefixWord ++ tailWord_5810279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810279).length < 2 ^ (prefixWord ++ tailWord_5810279).sum := by decide
  have hdescent : baseEnd_5810279 < baseStart_5810279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810289 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 6]
def baseStart_5810289 : Nat := 118140960795 + 5810289 * 2 ^ 59
def prefixEnd_5810289 : Nat := 4983230072969 + 3 ^ 40 * 5810289 * 2
def baseEnd_5810289 : Nat := 994490332843840983755491

theorem tailTrace_5810289 : CollatzResearch.WordTrace tailWord_5810289 prefixEnd_5810289 994490332843840983755491 := by
  unfold tailWord_5810289
  simp only [CollatzResearch.WordTrace]
  refine ⟨211918649647322746203809921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141279099764881830802539947 211918649647322746203809921)
  ·
    refine ⟨158938987235492059652857441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211918649647322746203809921 158938987235492059652857441)
    ·
      refine ⟨119204240426619044739643081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158938987235492059652857441 119204240426619044739643081)
      ·
        refine ⟨89403180319964283554732311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119204240426619044739643081 89403180319964283554732311)
        ·
          refine ⟨134104770479946425332098467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89403180319964283554732311 134104770479946425332098467)
          ·
            refine ⟨201157155719919637998147701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134104770479946425332098467 201157155719919637998147701)
            ·
              refine ⟨18858483348742466062326347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201157155719919637998147701 18858483348742466062326347)
              ·
                refine ⟨28287725023113699093489521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18858483348742466062326347 28287725023113699093489521)
                ·
                  refine ⟨21215793767335274320117141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28287725023113699093489521 21215793767335274320117141)
                  ·
                    refine ⟨994490332843840983755491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21215793767335274320117141 994490332843840983755491)
                    ·
                      rfl

theorem cell23_5810289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_5810289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810289 prefixEnd_5810289 := by exact prefixLift 5810289
  have htrace : WordTrace (prefixWord ++ tailWord_5810289) baseStart_5810289 baseEnd_5810289 := by
    simpa [prefixWord, tailWord_5810289, baseEnd_5810289] using wordTrace_append hprefix tailTrace_5810289
  have hstable : (prefixWord ++ tailWord_5810289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810289).length < 2 ^ (prefixWord ++ tailWord_5810289).sum := by decide
  have hdescent : baseEnd_5810289 < baseStart_5810289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810313 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 4, 2, 2]
def baseStart_5810313 : Nat := 118140960795 + 5810313 * 2 ^ 59
def prefixEnd_5810313 : Nat := 4983230072969 + 3 ^ 40 * 5810313 * 2
def baseEnd_5810313 : Nat := 2983483322067230857366363

theorem tailTrace_5810313 : CollatzResearch.WordTrace tailWord_5810313 prefixEnd_5810313 2983483322067230857366363 := by
  unfold tailWord_5810313
  simp only [CollatzResearch.WordTrace]
  refine ⟨211919524999235798302683593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141279683332823865535122395 211919524999235798302683593)
  ·
    refine ⟨158939643749426848727012695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211919524999235798302683593 158939643749426848727012695)
    ·
      refine ⟨238409465624140273090519043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158939643749426848727012695 238409465624140273090519043)
      ·
        refine ⟨357614198436210409635778565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238409465624140273090519043 357614198436210409635778565)
        ·
          refine ⟨67052662206789451806708481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357614198436210409635778565 67052662206789451806708481)
          ·
            refine ⟨50289496655092088855031361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67052662206789451806708481 50289496655092088855031361)
            ·
              refine ⟨37717122491319066641273521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50289496655092088855031361 37717122491319066641273521)
              ·
                refine ⟨28287841868489299980955141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37717122491319066641273521 28287841868489299980955141)
                ·
                  refine ⟨5303970350341743746429089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28287841868489299980955141 5303970350341743746429089)
                  ·
                    refine ⟨3977977762756307809821817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5303970350341743746429089 3977977762756307809821817)
                    ·
                      refine ⟨2983483322067230857366363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3977977762756307809821817 2983483322067230857366363)
                      ·
                        rfl

theorem cell23_5810313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2, 2].length) (baseStart_5810313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810313 prefixEnd_5810313 := by exact prefixLift 5810313
  have htrace : WordTrace (prefixWord ++ tailWord_5810313) baseStart_5810313 baseEnd_5810313 := by
    simpa [prefixWord, tailWord_5810313, baseEnd_5810313] using wordTrace_append hprefix tailTrace_5810313
  have hstable : (prefixWord ++ tailWord_5810313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810313).length < 2 ^ (prefixWord ++ tailWord_5810313).sum := by decide
  have hdescent : baseEnd_5810313 < baseStart_5810313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810324 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_5810324 : Nat := 118140960795 + 5810324 * 2 ^ 59
def prefixEnd_5810324 : Nat := 4983230072969 + 3 ^ 40 * 5810324 * 2
def baseEnd_5810324 : Nat := 2983488970354430314328813

theorem tailTrace_5810324 : CollatzResearch.WordTrace tailWord_5810324 prefixEnd_5810324 2983488970354430314328813 := by
  unfold tailWord_5810324
  simp only [CollatzResearch.WordTrace]
  refine ⟨105959963101097973590667013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141279950801463964787556017 105959963101097973590667013)
  ·
    refine ⟨19867493081455870048250065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105959963101097973590667013 19867493081455870048250065)
    ·
      refine ⟨14900619811091902536187549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19867493081455870048250065 14900619811091902536187549)
      ·
        refine ⟨5587732429159463451070331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14900619811091902536187549 5587732429159463451070331)
        ·
          refine ⟨8381598643739195176605497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5587732429159463451070331 8381598643739195176605497)
          ·
            refine ⟨6286198982804396382454123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8381598643739195176605497 6286198982804396382454123)
            ·
              refine ⟨9429298474206594573681185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286198982804396382454123 9429298474206594573681185)
              ·
                refine ⟨7071973855654945930260889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9429298474206594573681185 7071973855654945930260889)
                ·
                  refine ⟨5303980391741209447695667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7071973855654945930260889 5303980391741209447695667)
                  ·
                    refine ⟨7955970587611814171543501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5303980391741209447695667 7955970587611814171543501)
                    ·
                      refine ⟨2983488970354430314328813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7955970587611814171543501 2983488970354430314328813)
                      ·
                        rfl

theorem cell23_5810324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_5810324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810324 prefixEnd_5810324 := by exact prefixLift 5810324
  have htrace : WordTrace (prefixWord ++ tailWord_5810324) baseStart_5810324 baseEnd_5810324 := by
    simpa [prefixWord, tailWord_5810324, baseEnd_5810324] using wordTrace_append hprefix tailTrace_5810324
  have hstable : (prefixWord ++ tailWord_5810324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810324).length < 2 ^ (prefixWord ++ tailWord_5810324).sum := by decide
  have hdescent : baseEnd_5810324 < baseStart_5810324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810336 : List Nat := [2, 1, 1, 4, 2, 3, 2, 1, 7]
def baseStart_5810336 : Nat := 118140960795 + 5810336 * 2 ^ 59
def prefixEnd_5810336 : Nat := 4983230072969 + 3 ^ 40 * 5810336 * 2
def baseEnd_5810336 : Nat := 331499459124698251930973

theorem tailTrace_5810336 : CollatzResearch.WordTrace tailWord_5810336 prefixEnd_5810336 331499459124698251930973 := by
  unfold tailWord_5810336
  simp only [CollatzResearch.WordTrace]
  refine ⟨105960181939076236615385431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141280242585434982153847241 105960181939076236615385431)
  ·
    refine ⟨158940272908614354923078147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105960181939076236615385431 158940272908614354923078147)
    ·
      refine ⟨238410409362921532384617221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158940272908614354923078147 238410409362921532384617221)
      ·
        refine ⟨44701951755547787322115729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238410409362921532384617221 44701951755547787322115729)
        ·
          refine ⟨33526463816660840491586797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44701951755547787322115729 33526463816660840491586797)
          ·
            refine ⟨12572423931247815184345049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33526463816660840491586797 12572423931247815184345049)
            ·
              refine ⟨9429317948435861388258787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12572423931247815184345049 9429317948435861388258787)
              ·
                refine ⟨14143976922653792082388181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429317948435861388258787 14143976922653792082388181)
                ·
                  refine ⟨331499459124698251930973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14143976922653792082388181 331499459124698251930973)
                  ·
                    rfl

theorem cell23_5810336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_5810336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810336 prefixEnd_5810336 := by exact prefixLift 5810336
  have htrace : WordTrace (prefixWord ++ tailWord_5810336) baseStart_5810336 baseEnd_5810336 := by
    simpa [prefixWord, tailWord_5810336, baseEnd_5810336] using wordTrace_append hprefix tailTrace_5810336
  have hstable : (prefixWord ++ tailWord_5810336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810336).length < 2 ^ (prefixWord ++ tailWord_5810336).sum := by decide
  have hdescent : baseEnd_5810336 < baseStart_5810336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810446 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5810446 : Nat := 118140960795 + 5810446 * 2 ^ 59
def prefixEnd_5810446 : Nat := 4983230072969 + 3 ^ 40 * 5810446 * 2
def baseEnd_5810446 : Nat := 2983551614994278837003251

theorem tailTrace_5810446 : CollatzResearch.WordTrace tailWord_5810446 prefixEnd_5810446 2983551614994278837003251 := by
  unfold tailWord_5810446
  simp only [CollatzResearch.WordTrace]
  refine ⟨26490546988469245252159399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141282917271835974678183461 26490546988469245252159399)
  ·
    refine ⟨39735820482703867878239099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26490546988469245252159399 39735820482703867878239099)
    ·
      refine ⟨59603730724055801817358649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39735820482703867878239099 59603730724055801817358649)
      ·
        refine ⟨44702798043041851363018987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59603730724055801817358649 44702798043041851363018987)
        ·
          refine ⟨67054197064562777044528481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44702798043041851363018987 67054197064562777044528481)
          ·
            refine ⟨50290647798422082783396361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67054197064562777044528481 50290647798422082783396361)
            ·
              refine ⟨37717985848816562087547271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50290647798422082783396361 37717985848816562087547271)
              ·
                refine ⟨56576978773224843131320907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37717985848816562087547271 56576978773224843131320907)
                ·
                  refine ⟨84865468159837264696981361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56576978773224843131320907 84865468159837264696981361)
                  ·
                    refine ⟨63649101119877948522736021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84865468159837264696981361 63649101119877948522736021)
                    ·
                      refine ⟨2983551614994278837003251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63649101119877948522736021 2983551614994278837003251)
                      ·
                        rfl

theorem cell23_5810446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5810446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810446 prefixEnd_5810446 := by exact prefixLift 5810446
  have htrace : WordTrace (prefixWord ++ tailWord_5810446) baseStart_5810446 baseEnd_5810446 := by
    simpa [prefixWord, tailWord_5810446, baseEnd_5810446] using wordTrace_append hprefix tailTrace_5810446
  have hstable : (prefixWord ++ tailWord_5810446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810446).length < 2 ^ (prefixWord ++ tailWord_5810446).sum := by decide
  have hdescent : baseEnd_5810446 < baseStart_5810446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810456 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_5810456 : Nat := 118140960795 + 5810456 * 2 ^ 59
def prefixEnd_5810456 : Nat := 4983230072969 + 3 ^ 40 * 5810456 * 2
def baseEnd_5810456 : Nat := 994518916600274599292735

theorem tailTrace_5810456 : CollatzResearch.WordTrace tailWord_5810456 prefixEnd_5810456 994518916600274599292735 := by
  unfold tailWord_5810456
  simp only [CollatzResearch.WordTrace]
  refine ⟨105962370318858866862569611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141283160425145155816759481 105962370318858866862569611)
  ·
    refine ⟨158943555478288300293854417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105962370318858866862569611 158943555478288300293854417)
    ·
      refine ⟨119207666608716225220390813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158943555478288300293854417 119207666608716225220390813)
      ·
        refine ⟨44702874978268584457646555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119207666608716225220390813 44702874978268584457646555)
        ·
          refine ⟨67054312467402876686469833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44702874978268584457646555 67054312467402876686469833)
          ·
            refine ⟨50290734350552157514852375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67054312467402876686469833 50290734350552157514852375)
            ·
              refine ⟨75436101525828236272278563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50290734350552157514852375 75436101525828236272278563)
              ·
                refine ⟨113154152288742354408417845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75436101525828236272278563 113154152288742354408417845)
                ·
                  refine ⟨10608201777069595725789173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113154152288742354408417845 10608201777069595725789173)
                  ·
                    refine ⟨994518916600274599292735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10608201777069595725789173 994518916600274599292735)
                    ·
                      rfl

theorem cell23_5810456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_5810456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810456 prefixEnd_5810456 := by exact prefixLift 5810456
  have htrace : WordTrace (prefixWord ++ tailWord_5810456) baseStart_5810456 baseEnd_5810456 := by
    simpa [prefixWord, tailWord_5810456, baseEnd_5810456] using wordTrace_append hprefix tailTrace_5810456
  have hstable : (prefixWord ++ tailWord_5810456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810456).length < 2 ^ (prefixWord ++ tailWord_5810456).sum := by decide
  have hdescent : baseEnd_5810456 < baseStart_5810456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810471 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5810471 : Nat := 118140960795 + 5810471 * 2 ^ 59
def prefixEnd_5810471 : Nat := 4983230072969 + 3 ^ 40 * 5810471 * 2
def baseEnd_5810471 : Nat := 2983564452010641239190637

theorem tailTrace_5810471 : CollatzResearch.WordTrace tailWord_5810471 prefixEnd_5810471 2983564452010641239190637 := by
  unfold tailWord_5810471
  simp only [CollatzResearch.WordTrace]
  refine ⟨211925287732663391286935267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141283525155108927524623511 211925287732663391286935267)
  ·
    refine ⟨317887931598995086930402901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211925287732663391286935267 317887931598995086930402901)
    ·
      refine ⟨3725249198425723674965659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 317887931598995086930402901 3725249198425723674965659)
      ·
        refine ⟨5587873797638585512448489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725249198425723674965659 5587873797638585512448489)
        ·
          refine ⟨4190905348228939134336367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5587873797638585512448489 4190905348228939134336367)
          ·
            refine ⟨6286358022343408701504551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190905348228939134336367 6286358022343408701504551)
            ·
              refine ⟨9429537033515113052256827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286358022343408701504551 9429537033515113052256827)
              ·
                refine ⟨14144305550272669578385241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429537033515113052256827 14144305550272669578385241)
                ·
                  refine ⟨10608229162704502183788931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14144305550272669578385241 10608229162704502183788931)
                  ·
                    refine ⟨15912343744056753275683397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10608229162704502183788931 15912343744056753275683397)
                    ·
                      refine ⟨2983564452010641239190637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15912343744056753275683397 2983564452010641239190637)
                      ·
                        rfl

theorem cell23_5810471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5810471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810471 prefixEnd_5810471 := by exact prefixLift 5810471
  have htrace : WordTrace (prefixWord ++ tailWord_5810471) baseStart_5810471 baseEnd_5810471 := by
    simpa [prefixWord, tailWord_5810471, baseEnd_5810471] using wordTrace_append hprefix tailTrace_5810471
  have hstable : (prefixWord ++ tailWord_5810471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810471).length < 2 ^ (prefixWord ++ tailWord_5810471).sum := by decide
  have hdescent : baseEnd_5810471 < baseStart_5810471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810474 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5810474 : Nat := 118140960795 + 5810474 * 2 ^ 59
def prefixEnd_5810474 : Nat := 4983230072969 + 3 ^ 40 * 5810474 * 2
def baseEnd_5810474 : Nat := 2983565992452604727453123

theorem tailTrace_5810474 : CollatzResearch.WordTrace tailWord_5810474 prefixEnd_5810474 2983565992452604727453123 := by
  unfold tailWord_5810474
  simp only [CollatzResearch.WordTrace]
  refine ⟨52981349287913130699823619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141283598101101681866196317 52981349287913130699823619)
  ·
    refine ⟨79472023931869696049735429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52981349287913130699823619 79472023931869696049735429)
    ·
      refine ⟨14901004487225568009325393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79472023931869696049735429 14901004487225568009325393)
      ·
        refine ⟨11175753365419176006994045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14901004487225568009325393 11175753365419176006994045)
        ·
          refine ⟨4190907512032191002622767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11175753365419176006994045 4190907512032191002622767)
          ·
            refine ⟨6286361268048286503934151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190907512032191002622767 6286361268048286503934151)
            ·
              refine ⟨9429541902072429755901227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286361268048286503934151 9429541902072429755901227)
              ·
                refine ⟨14144312853108644633851841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9429541902072429755901227 14144312853108644633851841)
                ·
                  refine ⟨10608234639831483475388881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14144312853108644633851841 10608234639831483475388881)
                  ·
                    refine ⟨7956175979873612606541661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10608234639831483475388881 7956175979873612606541661)
                    ·
                      refine ⟨2983565992452604727453123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7956175979873612606541661 2983565992452604727453123)
                      ·
                        rfl

theorem cell23_5810474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5810474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810474 prefixEnd_5810474 := by exact prefixLift 5810474
  have htrace : WordTrace (prefixWord ++ tailWord_5810474) baseStart_5810474 baseEnd_5810474 := by
    simpa [prefixWord, tailWord_5810474, baseEnd_5810474] using wordTrace_append hprefix tailTrace_5810474
  have hstable : (prefixWord ++ tailWord_5810474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810474).length < 2 ^ (prefixWord ++ tailWord_5810474).sum := by decide
  have hdescent : baseEnd_5810474 < baseStart_5810474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810490 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_5810490 : Nat := 118140960795 + 5810490 * 2 ^ 59
def prefixEnd_5810490 : Nat := 4983230072969 + 3 ^ 40 * 5810490 * 2
def baseEnd_5810490 : Nat := 994524736047692221617683

theorem tailTrace_5810490 : CollatzResearch.WordTrace tailWord_5810490 prefixEnd_5810490 994524736047692221617683 := by
  unfold tailWord_5810490
  simp only [CollatzResearch.WordTrace]
  refine ⟨52981495179898639382969231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141283987146396371687917949 52981495179898639382969231)
  ·
    refine ⟨79472242769847959074453847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52981495179898639382969231 79472242769847959074453847)
    ·
      refine ⟨119208364154771938611680771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79472242769847959074453847 119208364154771938611680771)
      ·
        refine ⟨178812546232157907917521157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119208364154771938611680771 178812546232157907917521157)
        ·
          refine ⟨33527352418529607734535217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178812546232157907917521157 33527352418529607734535217)
          ·
            refine ⟨25145514313897205800901413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33527352418529607734535217 25145514313897205800901413)
            ·
              refine ⟨4714783933855726087669015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25145514313897205800901413 4714783933855726087669015)
              ·
                refine ⟨7072175900783589131503523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714783933855726087669015 7072175900783589131503523)
                ·
                  refine ⟨10608263851175383697255285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7072175900783589131503523 10608263851175383697255285)
                  ·
                    refine ⟨994524736047692221617683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10608263851175383697255285 994524736047692221617683)
                    ·
                      rfl

theorem cell23_5810490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_5810490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810490 prefixEnd_5810490 := by exact prefixLift 5810490
  have htrace : WordTrace (prefixWord ++ tailWord_5810490) baseStart_5810490 baseEnd_5810490 := by
    simpa [prefixWord, tailWord_5810490, baseEnd_5810490] using wordTrace_append hprefix tailTrace_5810490
  have hstable : (prefixWord ++ tailWord_5810490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810490).length < 2 ^ (prefixWord ++ tailWord_5810490).sum := by decide
  have hdescent : baseEnd_5810490 < baseStart_5810490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810503 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 4, 4]
def baseStart_5810503 : Nat := 118140960795 + 5810503 * 2 ^ 59
def prefixEnd_5810503 : Nat := 4983230072969 + 3 ^ 40 * 5810503 * 2
def baseEnd_5810503 : Nat := 994526961130528371330163

theorem tailTrace_5810503 : CollatzResearch.WordTrace tailWord_5810503 prefixEnd_5810503 994526961130528371330163 := by
  unfold tailWord_5810503
  simp only [CollatzResearch.WordTrace]
  refine ⟨211926454868547460752100163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141284303245698307168066775 211926454868547460752100163)
  ·
    refine ⟨317889682302821191128150245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211926454868547460752100163 317889682302821191128150245)
    ·
      refine ⟨59604315431778973336528171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 317889682302821191128150245 59604315431778973336528171)
      ·
        refine ⟨89406473147668460004792257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59604315431778973336528171 89406473147668460004792257)
        ·
          refine ⟨67054854860751345003594193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89406473147668460004792257 67054854860751345003594193)
          ·
            refine ⟨50291141145563508752695645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67054854860751345003594193 50291141145563508752695645)
            ·
              refine ⟨18859177929586315782260867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50291141145563508752695645 18859177929586315782260867)
              ·
                refine ⟨28288766894379473673391301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18859177929586315782260867 28288766894379473673391301)
                ·
                  refine ⟨5304143792696151313760869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28288766894379473673391301 5304143792696151313760869)
                  ·
                    refine ⟨994526961130528371330163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304143792696151313760869 994526961130528371330163)
                    ·
                      rfl

theorem cell23_5810503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_5810503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810503 prefixEnd_5810503 := by exact prefixLift 5810503
  have htrace : WordTrace (prefixWord ++ tailWord_5810503) baseStart_5810503 baseEnd_5810503 := by
    simpa [prefixWord, tailWord_5810503, baseEnd_5810503] using wordTrace_append hprefix tailTrace_5810503
  have hstable : (prefixWord ++ tailWord_5810503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810503).length < 2 ^ (prefixWord ++ tailWord_5810503).sum := by decide
  have hdescent : baseEnd_5810503 < baseStart_5810503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810506 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_5810506 : Nat := 118140960795 + 5810506 * 2 ^ 59
def prefixEnd_5810506 : Nat := 4983230072969 + 3 ^ 40 * 5810506 * 2
def baseEnd_5810506 : Nat := 2983582423833548602252975

theorem tailTrace_5810506 : CollatzResearch.WordTrace tailWord_5810506 prefixEnd_5810506 2983582423833548602252975 := by
  unfold tailWord_5810506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52981641071884148066114843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141284376191691061509639581 52981641071884148066114843)
  ·
    refine ⟨79472461607826222099172265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52981641071884148066114843 79472461607826222099172265)
    ·
      refine ⟨59604346205869666574379199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79472461607826222099172265 59604346205869666574379199)
      ·
        refine ⟨89406519308804499861568799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59604346205869666574379199 89406519308804499861568799)
        ·
          refine ⟨134109778963206749792353199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89406519308804499861568799 134109778963206749792353199)
          ·
            refine ⟨201164668444810124688529799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134109778963206749792353199 201164668444810124688529799)
            ·
              refine ⟨301747002667215187032794699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201164668444810124688529799 301747002667215187032794699)
              ·
                refine ⟨452620504000822780549192049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301747002667215187032794699 452620504000822780549192049)
                ·
                  refine ⟨339465378000617085411894037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452620504000822780549192049 339465378000617085411894037)
                  ·
                    refine ⟨15912439593778925878682533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 339465378000617085411894037 15912439593778925878682533)
                    ·
                      refine ⟨2983582423833548602252975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15912439593778925878682533 2983582423833548602252975)
                      ·
                        rfl

theorem cell23_5810506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_5810506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810506 prefixEnd_5810506 := by exact prefixLift 5810506
  have htrace : WordTrace (prefixWord ++ tailWord_5810506) baseStart_5810506 baseEnd_5810506 := by
    simpa [prefixWord, tailWord_5810506, baseEnd_5810506] using wordTrace_append hprefix tailTrace_5810506
  have hstable : (prefixWord ++ tailWord_5810506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810506).length < 2 ^ (prefixWord ++ tailWord_5810506).sum := by decide
  have hdescent : baseEnd_5810506 < baseStart_5810506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810513 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_5810513 : Nat := 118140960795 + 5810513 * 2 ^ 59
def prefixEnd_5810513 : Nat := 4983230072969 + 3 ^ 40 * 5810513 * 2
def baseEnd_5810513 : Nat := 2983586018198130074865443

theorem tailTrace_5810513 : CollatzResearch.WordTrace tailWord_5810513 prefixEnd_5810513 2983586018198130074865443 := by
  unfold tailWord_5810513
  simp only [CollatzResearch.WordTrace]
  refine ⟨211926819598511232459964193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141284546399007488306642795 211926819598511232459964193)
  ·
    refine ⟨158945114698883424344973145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211926819598511232459964193 158945114698883424344973145)
    ·
      refine ⟨119208836024162568258729859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158945114698883424344973145 119208836024162568258729859)
      ·
        refine ⟨178813254036243852388094789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119208836024162568258729859 178813254036243852388094789)
        ·
          refine ⟨33527485131795722322767773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178813254036243852388094789 33527485131795722322767773)
          ·
            refine ⟨12572806924423395871037915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33527485131795722322767773 12572806924423395871037915)
            ·
              refine ⟨18859210386635093806556873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12572806924423395871037915 18859210386635093806556873)
              ·
                refine ⟨14144407789976320354917655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18859210386635093806556873 14144407789976320354917655)
                ·
                  refine ⟨21216611684964480532376483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14144407789976320354917655 21216611684964480532376483)
                  ·
                    refine ⟨31824917527446720798564725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21216611684964480532376483 31824917527446720798564725)
                    ·
                      refine ⟨2983586018198130074865443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31824917527446720798564725 2983586018198130074865443)
                      ·
                        rfl

theorem cell23_5810513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_5810513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810513 prefixEnd_5810513 := by exact prefixLift 5810513
  have htrace : WordTrace (prefixWord ++ tailWord_5810513) baseStart_5810513 baseEnd_5810513 := by
    simpa [prefixWord, tailWord_5810513, baseEnd_5810513] using wordTrace_append hprefix tailTrace_5810513
  have hstable : (prefixWord ++ tailWord_5810513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810513).length < 2 ^ (prefixWord ++ tailWord_5810513).sum := by decide
  have hdescent : baseEnd_5810513 < baseStart_5810513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810533 : List Nat := [1, 3, 1, 3, 1, 3, 4, 7]
def baseStart_5810533 : Nat := 118140960795 + 5810533 * 2 ^ 59
def prefixEnd_5810533 : Nat := 4983230072969 + 3 ^ 40 * 5810533 * 2
def baseEnd_5810533 : Nat := 110503566215230370245013

theorem tailTrace_5810533 : CollatzResearch.WordTrace tailWord_5810533 prefixEnd_5810533 110503566215230370245013 := by
  unfold tailWord_5810533
  simp only [CollatzResearch.WordTrace]
  refine ⟨211927549058438775875692253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141285032705625850583794835 211927549058438775875692253)
  ·
    refine ⟨79472830896914540953384595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211927549058438775875692253 79472830896914540953384595)
    ·
      refine ⟨119209246345371811430076893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79472830896914540953384595 119209246345371811430076893)
      ·
        refine ⟨44703467379514429286278835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119209246345371811430076893 44703467379514429286278835)
        ·
          refine ⟨67055201069271643929418253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44703467379514429286278835 67055201069271643929418253)
          ·
            refine ⟨25145700400976866473531845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67055201069271643929418253 25145700400976866473531845)
            ·
              refine ⟨4714818825183162463787221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25145700400976866473531845 4714818825183162463787221)
              ·
                refine ⟨110503566215230370245013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4714818825183162463787221 110503566215230370245013)
                ·
                  rfl

theorem cell23_5810533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 7].length) (baseStart_5810533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810533 prefixEnd_5810533 := by exact prefixLift 5810533
  have htrace : WordTrace (prefixWord ++ tailWord_5810533) baseStart_5810533 baseEnd_5810533 := by
    simpa [prefixWord, tailWord_5810533, baseEnd_5810533] using wordTrace_append hprefix tailTrace_5810533
  have hstable : (prefixWord ++ tailWord_5810533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810533).length < 2 ^ (prefixWord ++ tailWord_5810533).sum := by decide
  have hdescent : baseEnd_5810533 < baseStart_5810533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810544 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 1, 2, 2]
def baseStart_5810544 : Nat := 118140960795 + 5810544 * 2 ^ 59
def prefixEnd_5810544 : Nat := 4983230072969 + 3 ^ 40 * 5810544 * 2
def baseEnd_5810544 : Nat := 2983601936098419453577801

theorem tailTrace_5810544 : CollatzResearch.WordTrace tailWord_5810544 prefixEnd_5810544 2983601936098419453577801 := by
  unfold tailWord_5810544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105963975130699462377171343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141285300174265949836228457 105963975130699462377171343)
  ·
    refine ⟨158945962696049193565757015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105963975130699462377171343 158945962696049193565757015)
    ·
      refine ⟨238418944044073790348635523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158945962696049193565757015 238418944044073790348635523)
      ·
        refine ⟨357628416066110685522953285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238418944044073790348635523 357628416066110685522953285)
        ·
          refine ⟨67055328012395753535553741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357628416066110685522953285 67055328012395753535553741)
          ·
            refine ⟨25145748004648407575832653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67055328012395753535553741 25145748004648407575832653)
            ·
              refine ⟨9429655501743152840937245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25145748004648407575832653 9429655501743152840937245)
              ·
                refine ⟨3536120813153682315351467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9429655501743152840937245 3536120813153682315351467)
                ·
                  refine ⟨5304181219730523473027201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536120813153682315351467 5304181219730523473027201)
                  ·
                    refine ⟨3978135914797892604770401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5304181219730523473027201 3978135914797892604770401)
                    ·
                      refine ⟨2983601936098419453577801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978135914797892604770401 2983601936098419453577801)
                      ·
                        rfl

theorem cell23_5810544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 1, 2, 2].length) (baseStart_5810544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810544 prefixEnd_5810544 := by exact prefixLift 5810544
  have htrace : WordTrace (prefixWord ++ tailWord_5810544) baseStart_5810544 baseEnd_5810544 := by
    simpa [prefixWord, tailWord_5810544, baseEnd_5810544] using wordTrace_append hprefix tailTrace_5810544
  have hstable : (prefixWord ++ tailWord_5810544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810544).length < 2 ^ (prefixWord ++ tailWord_5810544).sum := by decide
  have hdescent : baseEnd_5810544 < baseStart_5810544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810612 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 1, 2, 2]
def baseStart_5810612 : Nat := 118140960795 + 5810612 * 2 ^ 59
def prefixEnd_5810612 : Nat := 4983230072969 + 3 ^ 40 * 5810612 * 2
def baseEnd_5810612 : Nat := 2983636852782925187527489

theorem tailTrace_5810612 : CollatzResearch.WordTrace tailWord_5810612 prefixEnd_5810612 2983636852782925187527489 := by
  unfold tailWord_5810612
  simp only [CollatzResearch.WordTrace]
  refine ⟨105965215212576286183909045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141286953616768381578545393 105965215212576286183909045)
  ·
    refine ⟨9934238926179026829741473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105965215212576286183909045 9934238926179026829741473)
    ·
      refine ⟨7450679194634270122306105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9934238926179026829741473 7450679194634270122306105)
      ·
        refine ⟨5588009395975702591729579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450679194634270122306105 5588009395975702591729579)
        ·
          refine ⟨8382014093963553887594369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588009395975702591729579 8382014093963553887594369)
          ·
            refine ⟨6286510570472665415695777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382014093963553887594369 6286510570472665415695777)
            ·
              refine ⟨4714882927854499061771833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6286510570472665415695777 4714882927854499061771833)
              ·
                refine ⟨3536162195890874296328875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4714882927854499061771833 3536162195890874296328875)
                ·
                  refine ⟨5304243293836311444493313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536162195890874296328875 5304243293836311444493313)
                  ·
                    refine ⟨3978182470377233583369985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5304243293836311444493313 3978182470377233583369985)
                    ·
                      refine ⟨2983636852782925187527489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978182470377233583369985 2983636852782925187527489)
                      ·
                        rfl

theorem cell23_5810612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_5810612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810612 prefixEnd_5810612 := by exact prefixLift 5810612
  have htrace : WordTrace (prefixWord ++ tailWord_5810612) baseStart_5810612 baseEnd_5810612 := by
    simpa [prefixWord, tailWord_5810612, baseEnd_5810612] using wordTrace_append hprefix tailTrace_5810612
  have hstable : (prefixWord ++ tailWord_5810612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810612).length < 2 ^ (prefixWord ++ tailWord_5810612).sum := by decide
  have hdescent : baseEnd_5810612 < baseStart_5810612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810620 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_5810620 : Nat := 118140960795 + 5810620 * 2 ^ 59
def prefixEnd_5810620 : Nat := 4983230072969 + 3 ^ 40 * 5810620 * 2
def baseEnd_5810620 : Nat := 2983640960628161156227451

theorem tailTrace_5810620 : CollatzResearch.WordTrace tailWord_5810620 prefixEnd_5810620 2983640960628161156227451 := by
  unfold tailWord_5810620
  simp only [CollatzResearch.WordTrace]
  refine ⟨105965361104561794867054657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141287148139415726489406209 105965361104561794867054657)
  ·
    refine ⟨79474020828421346150290993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105965361104561794867054657 79474020828421346150290993)
    ·
      refine ⟨59605515621316009612718245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79474020828421346150290993 59605515621316009612718245)
      ·
        refine ⟨11176034178996751802384671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59605515621316009612718245 11176034178996751802384671)
        ·
          refine ⟨16764051268495127703577007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11176034178996751802384671 16764051268495127703577007)
          ·
            refine ⟨25146076902742691555365511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16764051268495127703577007 25146076902742691555365511)
            ·
              refine ⟨37719115354114037333048267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25146076902742691555365511 37719115354114037333048267)
              ·
                refine ⟨56578673031171055999572401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37719115354114037333048267 56578673031171055999572401)
                ·
                  refine ⟨42434004773378291999679301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56578673031171055999572401 42434004773378291999679301)
                  ·
                    refine ⟨7956375895008429749939869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42434004773378291999679301 7956375895008429749939869)
                    ·
                      refine ⟨2983640960628161156227451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7956375895008429749939869 2983640960628161156227451)
                      ·
                        rfl

theorem cell23_5810620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_5810620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810620 prefixEnd_5810620 := by exact prefixLift 5810620
  have htrace : WordTrace (prefixWord ++ tailWord_5810620) baseStart_5810620 baseEnd_5810620 := by
    simpa [prefixWord, tailWord_5810620, baseEnd_5810620] using wordTrace_append hprefix tailTrace_5810620
  have hstable : (prefixWord ++ tailWord_5810620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810620).length < 2 ^ (prefixWord ++ tailWord_5810620).sum := by decide
  have hdescent : baseEnd_5810620 < baseStart_5810620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810633 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_5810633 : Nat := 118140960795 + 5810633 * 2 ^ 59
def prefixEnd_5810633 : Nat := 4983230072969 + 3 ^ 40 * 5810633 * 2
def baseEnd_5810633 : Nat := 2983647635876669605364891

theorem tailTrace_5810633 : CollatzResearch.WordTrace tailWord_5810633 prefixEnd_5810633 2983647635876669605364891 := by
  unfold tailWord_5810633
  simp only [CollatzResearch.WordTrace]
  refine ⟨211931196358076492954332553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141287464238717661969555035 211931196358076492954332553)
  ·
    refine ⟨158948397268557369715749415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211931196358076492954332553 158948397268557369715749415)
    ·
      refine ⟨238422595902836054573624123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158948397268557369715749415 238422595902836054573624123)
      ·
        refine ⟨357633893854254081860436185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238422595902836054573624123 357633893854254081860436185)
        ·
          refine ⟨268225420390690561395327139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357633893854254081860436185 268225420390690561395327139)
          ·
            refine ⟨402338130586035842092990709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268225420390690561395327139 402338130586035842092990709)
            ·
              refine ⟨37719199742440860196217879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402338130586035842092990709 37719199742440860196217879)
              ·
                refine ⟨56578799613661290294326819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37719199742440860196217879 56578799613661290294326819)
                ·
                  refine ⟨84868199420491935441490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56578799613661290294326819 84868199420491935441490229)
                  ·
                    refine ⟨7956393695671118947639709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 84868199420491935441490229 7956393695671118947639709)
                    ·
                      refine ⟨2983647635876669605364891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7956393695671118947639709 2983647635876669605364891)
                      ·
                        rfl

theorem cell23_5810633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_5810633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810633 prefixEnd_5810633 := by exact prefixLift 5810633
  have htrace : WordTrace (prefixWord ++ tailWord_5810633) baseStart_5810633 baseEnd_5810633 := by
    simpa [prefixWord, tailWord_5810633, baseEnd_5810633] using wordTrace_append hprefix tailTrace_5810633
  have hstable : (prefixWord ++ tailWord_5810633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810633).length < 2 ^ (prefixWord ++ tailWord_5810633).sum := by decide
  have hdescent : baseEnd_5810633 < baseStart_5810633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810724 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5810724 : Nat := 118140960795 + 5810724 * 2 ^ 59
def prefixEnd_5810724 : Nat := 4983230072969 + 3 ^ 40 * 5810724 * 2
def baseEnd_5810724 : Nat := 2983694362616228749326973

theorem tailTrace_5810724 : CollatzResearch.WordTrace tailWord_5810724 prefixEnd_5810724 2983694362616228749326973 := by
  unfold tailWord_5810724
  simp only [CollatzResearch.WordTrace]
  refine ⟨105967257700373407747947613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141289676933831210330596817 105967257700373407747947613)
  ·
    refine ⟨39737721637640027905480355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105967257700373407747947613 39737721637640027905480355)
    ·
      refine ⟨59606582456460041858220533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39737721637640027905480355 59606582456460041858220533)
      ·
        refine ⟨5588117105293128924208175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59606582456460041858220533 5588117105293128924208175)
        ·
          refine ⟨8382175657939693386312263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588117105293128924208175 8382175657939693386312263)
          ·
            refine ⟨12573263486909540079468395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382175657939693386312263 12573263486909540079468395)
            ·
              refine ⟨18859895230364310119202593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12573263486909540079468395 18859895230364310119202593)
              ·
                refine ⟨14144921422773232589401945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18859895230364310119202593 14144921422773232589401945)
                ·
                  refine ⟨10608691067079924442051459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14144921422773232589401945 10608691067079924442051459)
                  ·
                    refine ⟨15913036600619886663077189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10608691067079924442051459 15913036600619886663077189)
                    ·
                      refine ⟨2983694362616228749326973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15913036600619886663077189 2983694362616228749326973)
                      ·
                        rfl

theorem cell23_5810724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5810724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810724 prefixEnd_5810724 := by exact prefixLift 5810724
  have htrace : WordTrace (prefixWord ++ tailWord_5810724) baseStart_5810724 baseEnd_5810724 := by
    simpa [prefixWord, tailWord_5810724, baseEnd_5810724] using wordTrace_append hprefix tailTrace_5810724
  have hstable : (prefixWord ++ tailWord_5810724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810724).length < 2 ^ (prefixWord ++ tailWord_5810724).sum := by decide
  have hdescent : baseEnd_5810724 < baseStart_5810724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810730 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_5810730 : Nat := 118140960795 + 5810730 * 2 ^ 59
def prefixEnd_5810730 : Nat := 4983230072969 + 3 ^ 40 * 5810730 * 2
def baseEnd_5810730 : Nat := 331521938166683969539105

theorem tailTrace_5810730 : CollatzResearch.WordTrace tailWord_5810730 prefixEnd_5810730 331521938166683969539105 := by
  unfold tailWord_5810730
  simp only [CollatzResearch.WordTrace]
  refine ⟨52983683559681269630153411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141289822825816719013742429 52983683559681269630153411)
  ·
    refine ⟨79475525339521904445230117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52983683559681269630153411 79475525339521904445230117)
    ·
      refine ⟨14901661001160357083480647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79475525339521904445230117 14901661001160357083480647)
      ·
        refine ⟨22352491501740535625220971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14901661001160357083480647 22352491501740535625220971)
        ·
          refine ⟨33528737252610803437831457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22352491501740535625220971 33528737252610803437831457)
          ·
            refine ⟨25146552939458102578373593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33528737252610803437831457 25146552939458102578373593)
            ·
              refine ⟨18859914704593576933780195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25146552939458102578373593 18859914704593576933780195)
              ·
                refine ⟨28289872056890365400670293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18859914704593576933780195 28289872056890365400670293)
                ·
                  refine ⟨331521938166683969539105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28289872056890365400670293 331521938166683969539105)
                  ·
                    rfl

theorem cell23_5810730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_5810730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810730 prefixEnd_5810730 := by exact prefixLift 5810730
  have htrace : WordTrace (prefixWord ++ tailWord_5810730) baseStart_5810730 baseEnd_5810730 := by
    simpa [prefixWord, tailWord_5810730, baseEnd_5810730] using wordTrace_append hprefix tailTrace_5810730
  have hstable : (prefixWord ++ tailWord_5810730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810730).length < 2 ^ (prefixWord ++ tailWord_5810730).sum := by decide
  have hdescent : baseEnd_5810730 < baseStart_5810730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810767 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 2, 3, 2]
def baseStart_5810767 : Nat := 118140960795 + 5810767 * 2 ^ 59
def prefixEnd_5810767 : Nat := 4983230072969 + 3 ^ 40 * 5810767 * 2
def baseEnd_5810767 : Nat := 2983716442284372081089275

theorem tailTrace_5810767 : CollatzResearch.WordTrace tailWord_5810767 prefixEnd_5810767 2983716442284372081089275 := by
  unfold tailWord_5810767
  simp only [CollatzResearch.WordTrace]
  refine ⟨211936083739591033839710555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141290722493060689226473703 211936083739591033839710555)
  ·
    refine ⟨317904125609386550759565833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211936083739591033839710555 317904125609386550759565833)
    ·
      refine ⟨238428094207039913069674375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317904125609386550759565833 238428094207039913069674375)
      ·
        refine ⟨357642141310559869604511563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238428094207039913069674375 357642141310559869604511563)
        ·
          refine ⟨536463211965839804406767345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357642141310559869604511563 536463211965839804406767345)
          ·
            refine ⟨402347408974379853305075509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536463211965839804406767345 402347408974379853305075509)
            ·
              refine ⟨37720069591348111247350829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402347408974379853305075509 37720069591348111247350829)
              ·
                refine ⟨14145026096755541717756561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37720069591348111247350829 14145026096755541717756561)
                ·
                  refine ⟨10608769572566656288317421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14145026096755541717756561 10608769572566656288317421)
                  ·
                    refine ⟨3978288589712496108119033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10608769572566656288317421 3978288589712496108119033)
                    ·
                      refine ⟨2983716442284372081089275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978288589712496108119033 2983716442284372081089275)
                      ·
                        rfl

theorem cell23_5810767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3, 2].length) (baseStart_5810767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810767 prefixEnd_5810767 := by exact prefixLift 5810767
  have htrace : WordTrace (prefixWord ++ tailWord_5810767) baseStart_5810767 baseEnd_5810767 := by
    simpa [prefixWord, tailWord_5810767, baseEnd_5810767] using wordTrace_append hprefix tailTrace_5810767
  have hstable : (prefixWord ++ tailWord_5810767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810767).length < 2 ^ (prefixWord ++ tailWord_5810767).sum := by decide
  have hdescent : baseEnd_5810767 < baseStart_5810767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810797 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5810797 : Nat := 118140960795 + 5810797 * 2 ^ 59
def prefixEnd_5810797 : Nat := 4983230072969 + 3 ^ 40 * 5810797 * 2
def baseEnd_5810797 : Nat := 2983731846704006963714137

theorem tailTrace_5810797 : CollatzResearch.WordTrace tailWord_5810797 prefixEnd_5810797 2983731846704006963714137 := by
  unfold tailWord_5810797
  simp only [CollatzResearch.WordTrace]
  refine ⟨211937177929482348963302645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141291451952988232642201763 211937177929482348963302645)
  ·
    refine ⟨19869110430888970215309623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211937177929482348963302645 19869110430888970215309623)
    ·
      refine ⟨29803665646333455322964435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19869110430888970215309623 29803665646333455322964435)
      ·
        refine ⟨44705498469500182984446653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29803665646333455322964435 44705498469500182984446653)
        ·
          refine ⟨16764561926062568619167495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44705498469500182984446653 16764561926062568619167495)
          ·
            refine ⟨25146842889093852928751243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16764561926062568619167495 25146842889093852928751243)
            ·
              refine ⟨37720264333640779393126865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25146842889093852928751243 37720264333640779393126865)
              ·
                refine ⟨28290198250230584544845149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37720264333640779393126865 28290198250230584544845149)
                ·
                  refine ⟨10608824343836469204316931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28290198250230584544845149 10608824343836469204316931)
                  ·
                    refine ⟨15913236515754703806475397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10608824343836469204316931 15913236515754703806475397)
                    ·
                      refine ⟨2983731846704006963714137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15913236515754703806475397 2983731846704006963714137)
                      ·
                        rfl

theorem cell23_5810797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5810797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810797 prefixEnd_5810797 := by exact prefixLift 5810797
  have htrace : WordTrace (prefixWord ++ tailWord_5810797) baseStart_5810797 baseEnd_5810797 := by
    simpa [prefixWord, tailWord_5810797, baseEnd_5810797] using wordTrace_append hprefix tailTrace_5810797
  have hstable : (prefixWord ++ tailWord_5810797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810797).length < 2 ^ (prefixWord ++ tailWord_5810797).sum := by decide
  have hdescent : baseEnd_5810797 < baseStart_5810797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810803 : List Nat := [1, 1, 1, 2, 2, 1, 1, 14]
def baseStart_5810803 : Nat := 118140960795 + 5810803 * 2 ^ 59
def prefixEnd_5810803 : Nat := 4983230072969 + 3 ^ 40 * 5810803 * 2
def baseEnd_5810803 : Nat := 110508701021775331119967

theorem tailTrace_5810803 : CollatzResearch.WordTrace tailWord_5810803 prefixEnd_5810803 110508701021775331119967 := by
  unfold tailWord_5810803
  simp only [CollatzResearch.WordTrace]
  refine ⟨211937396767460611988021063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141291597844973741325347375 211937396767460611988021063)
  ·
    refine ⟨317906095151190917982031595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211937396767460611988021063 317906095151190917982031595)
    ·
      refine ⟨476859142726786376973047393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317906095151190917982031595 476859142726786376973047393)
      ·
        refine ⟨357644357045089782729785545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476859142726786376973047393 357644357045089782729785545)
        ·
          refine ⟨268233267783817337047339159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357644357045089782729785545 268233267783817337047339159)
          ·
            refine ⟨402349901675726005571008739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268233267783817337047339159 402349901675726005571008739)
            ·
              refine ⟨603524852513589008356513109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402349901675726005571008739 603524852513589008356513109)
              ·
                refine ⟨110508701021775331119967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 603524852513589008356513109 110508701021775331119967)
                ·
                  rfl

theorem cell23_5810803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 14].length) (baseStart_5810803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810803 prefixEnd_5810803 := by exact prefixLift 5810803
  have htrace : WordTrace (prefixWord ++ tailWord_5810803) baseStart_5810803 baseEnd_5810803 := by
    simpa [prefixWord, tailWord_5810803, baseEnd_5810803] using wordTrace_append hprefix tailTrace_5810803
  have hstable : (prefixWord ++ tailWord_5810803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810803).length < 2 ^ (prefixWord ++ tailWord_5810803).sum := by decide
  have hdescent : baseEnd_5810803 < baseStart_5810803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810807 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 2, 4]
def baseStart_5810807 : Nat := 118140960795 + 5810807 * 2 ^ 59
def prefixEnd_5810807 : Nat := 4983230072969 + 3 ^ 40 * 5810807 * 2
def baseEnd_5810807 : Nat := 994578993836850641529697

theorem tailTrace_5810807 : CollatzResearch.WordTrace tailWord_5810807 prefixEnd_5810807 994578993836850641529697 := by
  unfold tailWord_5810807
  simp only [CollatzResearch.WordTrace]
  refine ⟨211937542659446120671166675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141291695106297413780777783 211937542659446120671166675)
  ·
    refine ⟨317906313989169181006750013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211937542659446120671166675 317906313989169181006750013)
    ·
      refine ⟨119214867745938442877531255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317906313989169181006750013 119214867745938442877531255)
      ·
        refine ⟨178822301618907664316296883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119214867745938442877531255 178822301618907664316296883)
        ·
          refine ⟨268233452428361496474445325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178822301618907664316296883 268233452428361496474445325)
          ·
            refine ⟨100587544660635561177916997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268233452428361496474445325 100587544660635561177916997)
            ·
              refine ⟨18860164623869167720859437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100587544660635561177916997 18860164623869167720859437)
              ·
                refine ⟨7072561733950937895322289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18860164623869167720859437 7072561733950937895322289)
                ·
                  refine ⟨5304421300463203421491717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7072561733950937895322289 5304421300463203421491717)
                  ·
                    refine ⟨994578993836850641529697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304421300463203421491717 994578993836850641529697)
                    ·
                      rfl

theorem cell23_5810807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_5810807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810807 prefixEnd_5810807 := by exact prefixLift 5810807
  have htrace : WordTrace (prefixWord ++ tailWord_5810807) baseStart_5810807 baseEnd_5810807 := by
    simpa [prefixWord, tailWord_5810807, baseEnd_5810807] using wordTrace_append hprefix tailTrace_5810807
  have hstable : (prefixWord ++ tailWord_5810807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810807).length < 2 ^ (prefixWord ++ tailWord_5810807).sum := by decide
  have hdescent : baseEnd_5810807 < baseStart_5810807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810817 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_5810817 : Nat := 118140960795 + 5810817 * 2 ^ 59
def prefixEnd_5810817 : Nat := 4983230072969 + 3 ^ 40 * 5810817 * 2
def baseEnd_5810817 : Nat := 2983742116317096885464045

theorem tailTrace_5810817 : CollatzResearch.WordTrace tailWord_5810817 prefixEnd_5810817 2983742116317096885464045 := by
  unfold tailWord_5810817
  simp only [CollatzResearch.WordTrace]
  refine ⟨211937907389409892379030705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141291938259606594919353803 211937907389409892379030705)
  ·
    refine ⟨158953430542057419284273029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211937907389409892379030705 158953430542057419284273029)
    ·
      refine ⟨29803768226635766115801193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158953430542057419284273029 29803768226635766115801193)
      ·
        refine ⟨22352826169976824586850895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29803768226635766115801193 22352826169976824586850895)
        ·
          refine ⟨33529239254965236880276343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22352826169976824586850895 33529239254965236880276343)
          ·
            refine ⟨50293858882447855320414515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33529239254965236880276343 50293858882447855320414515)
            ·
              refine ⟨75440788323671782980621773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50293858882447855320414515 75440788323671782980621773)
              ·
                refine ⟨28290295621376918617733165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75440788323671782980621773 28290295621376918617733165)
                ·
                  refine ⟨10608860858016344481649937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28290295621376918617733165 10608860858016344481649937)
                  ·
                    refine ⟨7956645643512258361237453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10608860858016344481649937 7956645643512258361237453)
                    ·
                      refine ⟨2983742116317096885464045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7956645643512258361237453 2983742116317096885464045)
                      ·
                        rfl

theorem cell23_5810817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_5810817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810817 prefixEnd_5810817 := by exact prefixLift 5810817
  have htrace : WordTrace (prefixWord ++ tailWord_5810817) baseStart_5810817 baseEnd_5810817 := by
    simpa [prefixWord, tailWord_5810817, baseEnd_5810817] using wordTrace_append hprefix tailTrace_5810817
  have hstable : (prefixWord ++ tailWord_5810817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810817).length < 2 ^ (prefixWord ++ tailWord_5810817).sum := by decide
  have hdescent : baseEnd_5810817 < baseStart_5810817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810858 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5810858 : Nat := 118140960795 + 5810858 * 2 ^ 59
def prefixEnd_5810858 : Nat := 4983230072969 + 3 ^ 40 * 5810858 * 2
def baseEnd_5810858 : Nat := 994587723007977075017119

theorem tailTrace_5810858 : CollatzResearch.WordTrace tailWord_5810858 prefixEnd_5810858 994587723007977075017119 := by
  unfold tailWord_5810858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52984850695565339095318307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141292935188174237587515485 52984850695565339095318307)
  ·
    refine ⟨79477276043348008642977461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52984850695565339095318307 79477276043348008642977461)
    ·
      refine ⟨7450994629063875810279137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79477276043348008642977461 7450994629063875810279137)
      ·
        refine ⟨5588245971797906857709353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7450994629063875810279137 5588245971797906857709353)
        ·
          refine ⟨4191184478848430143282015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5588245971797906857709353 4191184478848430143282015)
          ·
            refine ⟨6286776718272645214923023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4191184478848430143282015 6286776718272645214923023)
            ·
              refine ⟨9430165077408967822384535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286776718272645214923023 9430165077408967822384535)
              ·
                refine ⟨14145247616113451733576803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9430165077408967822384535 14145247616113451733576803)
                ·
                  refine ⟨21217871424170177600365205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14145247616113451733576803 21217871424170177600365205)
                  ·
                    refine ⟨994587723007977075017119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21217871424170177600365205 994587723007977075017119)
                    ·
                      rfl

theorem cell23_5810858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5810858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810858 prefixEnd_5810858 := by exact prefixLift 5810858
  have htrace : WordTrace (prefixWord ++ tailWord_5810858) baseStart_5810858 baseEnd_5810858 := by
    simpa [prefixWord, tailWord_5810858, baseEnd_5810858] using wordTrace_append hprefix tailTrace_5810858
  have hstable : (prefixWord ++ tailWord_5810858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810858).length < 2 ^ (prefixWord ++ tailWord_5810858).sum := by decide
  have hdescent : baseEnd_5810858 < baseStart_5810858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810977 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5810977 : Nat := 118140960795 + 5810977 * 2 ^ 59
def prefixEnd_5810977 : Nat := 4983230072969 + 3 ^ 40 * 5810977 * 2
def baseEnd_5810977 : Nat := 2983824273221816259463309

theorem tailTrace_5810977 : CollatzResearch.WordTrace tailWord_5810977 prefixEnd_5810977 2983824273221816259463309 := by
  unfold tailWord_5810977
  simp only [CollatzResearch.WordTrace]
  refine ⟨211943743068830239704855185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141295828712553493136570123 211943743068830239704855185)
  ·
    refine ⟨158957807301622679778641389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211943743068830239704855185 158957807301622679778641389)
    ·
      refine ⟨59609177738108504916990521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158957807301622679778641389 59609177738108504916990521)
      ·
        refine ⟨44706883303581378687742891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59609177738108504916990521 44706883303581378687742891)
        ·
          refine ⟨67060324955372068031614337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44706883303581378687742891 67060324955372068031614337)
          ·
            refine ⟨50295243716529051023710753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67060324955372068031614337 50295243716529051023710753)
            ·
              refine ⟨37721432787396788267783065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50295243716529051023710753 37721432787396788267783065)
              ·
                refine ⟨28291074590547591200837299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37721432787396788267783065 28291074590547591200837299)
                ·
                  refine ⟨42436611885821386801255949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28291074590547591200837299 42436611885821386801255949)
                  ·
                    refine ⟨15913729457183020050470981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42436611885821386801255949 15913729457183020050470981)
                    ·
                      refine ⟨2983824273221816259463309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15913729457183020050470981 2983824273221816259463309)
                      ·
                        rfl

theorem cell23_5810977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5810977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810977 prefixEnd_5810977 := by exact prefixLift 5810977
  have htrace : WordTrace (prefixWord ++ tailWord_5810977) baseStart_5810977 baseEnd_5810977 := by
    simpa [prefixWord, tailWord_5810977, baseEnd_5810977] using wordTrace_append hprefix tailTrace_5810977
  have hstable : (prefixWord ++ tailWord_5810977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810977).length < 2 ^ (prefixWord ++ tailWord_5810977).sum := by decide
  have hdescent : baseEnd_5810977 < baseStart_5810977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810987 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 5, 4]
def baseStart_5810987 : Nat := 118140960795 + 5810987 * 2 ^ 59
def prefixEnd_5810987 : Nat := 4983230072969 + 3 ^ 40 * 5810987 * 2
def baseEnd_5810987 : Nat := 994609802676120406779421

theorem tailTrace_5810987 : CollatzResearch.WordTrace tailWord_5810987 prefixEnd_5810987 994609802676120406779421 := by
  unfold tailWord_5810987
  simp only [CollatzResearch.WordTrace]
  refine ⟨211944107798794011412719215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141296071865862674275146143 211944107798794011412719215)
  ·
    refine ⟨317916161698191017119078823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211944107798794011412719215 317916161698191017119078823)
    ·
      refine ⟨476874242547286525678618235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317916161698191017119078823 476874242547286525678618235)
      ·
        refine ⟨715311363820929788517927353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476874242547286525678618235 715311363820929788517927353)
        ·
          refine ⟨536483522865697341388445515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 715311363820929788517927353 536483522865697341388445515)
          ·
            refine ⟨804725284298546012082668273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536483522865697341388445515 804725284298546012082668273)
            ·
              refine ⟨603543963223909509062001205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 804725284298546012082668273 603543963223909509062001205)
              ·
                refine ⟨56582246552241516474562613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603543963223909509062001205 56582246552241516474562613)
                ·
                  refine ⟨5304585614272642169490245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56582246552241516474562613 5304585614272642169490245)
                  ·
                    refine ⟨994609802676120406779421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304585614272642169490245 994609802676120406779421)
                    ·
                      rfl

theorem cell23_5810987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 4].length) (baseStart_5810987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810987 prefixEnd_5810987 := by exact prefixLift 5810987
  have htrace : WordTrace (prefixWord ++ tailWord_5810987) baseStart_5810987 baseEnd_5810987 := by
    simpa [prefixWord, tailWord_5810987, baseEnd_5810987] using wordTrace_append hprefix tailTrace_5810987
  have hstable : (prefixWord ++ tailWord_5810987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810987).length < 2 ^ (prefixWord ++ tailWord_5810987).sum := by decide
  have hdescent : baseEnd_5810987 < baseStart_5810987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5810994 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_5810994 : Nat := 118140960795 + 5810994 * 2 ^ 59
def prefixEnd_5810994 : Nat := 4983230072969 + 3 ^ 40 * 5810994 * 2
def baseEnd_5810994 : Nat := 2983833002392942692950731

theorem tailTrace_5810994 : CollatzResearch.WordTrace tailWord_5810994 prefixEnd_5810994 2983833002392942692950731 := by
  unfold tailWord_5810994
  simp only [CollatzResearch.WordTrace]
  refine ⟨52986090777442162902056009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141296242073179101072149357 52986090777442162902056009)
  ·
    refine ⟨39739568083081622176542007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52986090777442162902056009 39739568083081622176542007)
    ·
      refine ⟨59609352124622433264813011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39739568083081622176542007 59609352124622433264813011)
      ·
        refine ⟨89414028186933649897219517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59609352124622433264813011 89414028186933649897219517)
        ·
          refine ⟨33530260570100118711457319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89414028186933649897219517 33530260570100118711457319)
          ·
            refine ⟨50295390855150178067185979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33530260570100118711457319 50295390855150178067185979)
            ·
              refine ⟨75443086282725267100778969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50295390855150178067185979 75443086282725267100778969)
              ·
                refine ⟨56582314712043950325584227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75443086282725267100778969 56582314712043950325584227)
                ·
                  refine ⟨84873472068065925488376341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56582314712043950325584227 84873472068065925488376341)
                  ·
                    refine ⟨3978444003190590257267641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84873472068065925488376341 3978444003190590257267641)
                    ·
                      refine ⟨2983833002392942692950731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978444003190590257267641 2983833002392942692950731)
                      ·
                        rfl

theorem cell23_5810994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_5810994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5810994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5810994 prefixEnd_5810994 := by exact prefixLift 5810994
  have htrace : WordTrace (prefixWord ++ tailWord_5810994) baseStart_5810994 baseEnd_5810994 := by
    simpa [prefixWord, tailWord_5810994, baseEnd_5810994] using wordTrace_append hprefix tailTrace_5810994
  have hstable : (prefixWord ++ tailWord_5810994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5810994).length < 2 ^ (prefixWord ++ tailWord_5810994).sum := by decide
  have hdescent : baseEnd_5810994 < baseStart_5810994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5810994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811007 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_5811007 : Nat := 118140960795 + 5811007 * 2 ^ 59
def prefixEnd_5811007 : Nat := 4983230072969 + 3 ^ 40 * 5811007 * 2
def baseEnd_5811007 : Nat := 2983839677641451142088171

theorem tailTrace_5811007 : CollatzResearch.WordTrace tailWord_5811007 prefixEnd_5811007 2983839677641451142088171 := by
  unfold tailWord_5811007
  simp only [CollatzResearch.WordTrace]
  refine ⟨211944837258721554828447275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141296558172481036552298183 211944837258721554828447275)
  ·
    refine ⟨317917255888082332242670913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211944837258721554828447275 317917255888082332242670913)
    ·
      refine ⟨238437941916061749182003185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317917255888082332242670913 238437941916061749182003185)
      ·
        refine ⟨178828456437046311886502389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238437941916061749182003185 178828456437046311886502389)
        ·
          refine ⟨16765167790973091739359599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 178828456437046311886502389 16765167790973091739359599)
          ·
            refine ⟨25147751686459637609039399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16765167790973091739359599 25147751686459637609039399)
            ·
              refine ⟨37721627529689456413559099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25147751686459637609039399 37721627529689456413559099)
              ·
                refine ⟨56582441294534184620338649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37721627529689456413559099 56582441294534184620338649)
                ·
                  refine ⟨42436830970900638465253987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56582441294534184620338649 42436830970900638465253987)
                  ·
                    refine ⟨63655246456350957697880981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42436830970900638465253987 63655246456350957697880981)
                    ·
                      refine ⟨2983839677641451142088171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63655246456350957697880981 2983839677641451142088171)
                      ·
                        rfl

theorem cell23_5811007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_5811007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811007 prefixEnd_5811007 := by exact prefixLift 5811007
  have htrace : WordTrace (prefixWord ++ tailWord_5811007) baseStart_5811007 baseEnd_5811007 := by
    simpa [prefixWord, tailWord_5811007, baseEnd_5811007] using wordTrace_append hprefix tailTrace_5811007
  have hstable : (prefixWord ++ tailWord_5811007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811007).length < 2 ^ (prefixWord ++ tailWord_5811007).sum := by decide
  have hdescent : baseEnd_5811007 < baseStart_5811007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811017 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 8]
def baseStart_5811017 : Nat := 118140960795 + 5811017 * 2 ^ 59
def prefixEnd_5811017 : Nat := 4983230072969 + 3 ^ 40 * 5811017 * 2
def baseEnd_5811017 : Nat := 331538312494221789218125

theorem tailTrace_5811017 : CollatzResearch.WordTrace tailWord_5811017 prefixEnd_5811017 331538312494221789218125 := by
  unfold tailWord_5811017
  simp only [CollatzResearch.WordTrace]
  refine ⟨211945201988685326536311305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141296801325790217690874203 211945201988685326536311305)
  ·
    refine ⟨158958901491513994902233479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211945201988685326536311305 158958901491513994902233479)
    ·
      refine ⟨238438352237270992353350219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158958901491513994902233479 238438352237270992353350219)
      ·
        refine ⟨357657528355906488530025329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238438352237270992353350219 357657528355906488530025329)
        ·
          refine ⟨268243146266929866397518997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357657528355906488530025329 268243146266929866397518997)
          ·
            refine ⟨12573897481262337487383703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 268243146266929866397518997 12573897481262337487383703)
            ·
              refine ⟨18860846221893506231075555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12573897481262337487383703 18860846221893506231075555)
              ·
                refine ⟨28291269332840259346613333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18860846221893506231075555 28291269332840259346613333)
                ·
                  refine ⟨331538312494221789218125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28291269332840259346613333 331538312494221789218125)
                  ·
                    rfl

theorem cell23_5811017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_5811017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811017 prefixEnd_5811017 := by exact prefixLift 5811017
  have htrace : WordTrace (prefixWord ++ tailWord_5811017) baseStart_5811017 baseEnd_5811017 := by
    simpa [prefixWord, tailWord_5811017, baseEnd_5811017] using wordTrace_append hprefix tailTrace_5811017
  have hstable : (prefixWord ++ tailWord_5811017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811017).length < 2 ^ (prefixWord ++ tailWord_5811017).sum := by decide
  have hdescent : baseEnd_5811017 < baseStart_5811017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811098 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_5811098 : Nat := 118140960795 + 5811098 * 2 ^ 59
def prefixEnd_5811098 : Nat := 4983230072969 + 3 ^ 40 * 5811098 * 2
def baseEnd_5811098 : Nat := 994628801460336762016751

theorem tailTrace_5811098 : CollatzResearch.WordTrace tailWord_5811098 prefixEnd_5811098 994628801460336762016751 := by
  unfold tailWord_5811098
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987039075347969342502487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141298770867594584913339965 52987039075347969342502487)
  ·
    refine ⟨79480558613021954013753731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52987039075347969342502487 79480558613021954013753731)
    ·
      refine ⟨119220837919532931020630597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79480558613021954013753731 119220837919532931020630597)
      ·
        refine ⟨22353907109912424566368237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119220837919532931020630597 22353907109912424566368237)
        ·
          refine ⟨8382715166217159212388089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22353907109912424566368237 8382715166217159212388089)
          ·
            refine ⟨6287036374662869409291067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382715166217159212388089 6287036374662869409291067)
            ·
              refine ⟨9430554561994304113936601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287036374662869409291067 9430554561994304113936601)
              ·
                refine ⟨7072915921495728085452451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9430554561994304113936601 7072915921495728085452451)
                ·
                  refine ⟨10609373882243592128178677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7072915921495728085452451 10609373882243592128178677)
                  ·
                    refine ⟨994628801460336762016751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10609373882243592128178677 994628801460336762016751)
                    ·
                      rfl

theorem cell23_5811098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_5811098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811098 prefixEnd_5811098 := by exact prefixLift 5811098
  have htrace : WordTrace (prefixWord ++ tailWord_5811098) baseStart_5811098 baseEnd_5811098 := by
    simpa [prefixWord, tailWord_5811098, baseEnd_5811098] using wordTrace_append hprefix tailTrace_5811098
  have hstable : (prefixWord ++ tailWord_5811098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811098).length < 2 ^ (prefixWord ++ tailWord_5811098).sum := by decide
  have hdescent : baseEnd_5811098 < baseStart_5811098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811107 : List Nat := [1, 1, 1, 4, 1, 2, 4, 9]
def baseStart_5811107 : Nat := 118140960795 + 5811107 * 2 ^ 59
def prefixEnd_5811107 : Nat := 4983230072969 + 3 ^ 40 * 5811107 * 2
def baseEnd_5811107 : Nat := 110514482433588916697693

theorem tailTrace_5811107 : CollatzResearch.WordTrace tailWord_5811107 prefixEnd_5811107 110514482433588916697693 := by
  unfold tailWord_5811107
  simp only [CollatzResearch.WordTrace]
  refine ⟨211948484558359271907087575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141298989705572847938058383 211948484558359271907087575)
  ·
    refine ⟨317922726837538907860631363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211948484558359271907087575 317922726837538907860631363)
    ·
      refine ⟨476884090256308361790947045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317922726837538907860631363 476884090256308361790947045)
      ·
        refine ⟨89415766923057817835802571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 476884090256308361790947045 89415766923057817835802571)
        ·
          refine ⟨134123650384586726753703857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89415766923057817835802571 134123650384586726753703857)
          ·
            refine ⟨100592737788440045065277893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134123650384586726753703857 100592737788440045065277893)
            ·
              refine ⟨18861138335332508449739605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100592737788440045065277893 18861138335332508449739605)
              ·
                refine ⟨110514482433588916697693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18861138335332508449739605 110514482433588916697693)
                ·
                  rfl

theorem cell23_5811107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 9].length) (baseStart_5811107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811107 prefixEnd_5811107 := by exact prefixLift 5811107
  have htrace : WordTrace (prefixWord ++ tailWord_5811107) baseStart_5811107 baseEnd_5811107 := by
    simpa [prefixWord, tailWord_5811107, baseEnd_5811107] using wordTrace_append hprefix tailTrace_5811107
  have hstable : (prefixWord ++ tailWord_5811107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811107).length < 2 ^ (prefixWord ++ tailWord_5811107).sum := by decide
  have hdescent : baseEnd_5811107 < baseStart_5811107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811111 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5811111 : Nat := 118140960795 + 5811111 * 2 ^ 59
def prefixEnd_5811111 : Nat := 4983230072969 + 3 ^ 40 * 5811111 * 2
def baseEnd_5811111 : Nat := 994631026543172911729231

theorem tailTrace_5811111 : CollatzResearch.WordTrace tailWord_5811111 prefixEnd_5811111 994631026543172911729231 := by
  unfold tailWord_5811111
  simp only [CollatzResearch.WordTrace]
  refine ⟨211948630450344780590233187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141299086966896520393488791 211948630450344780590233187)
  ·
    refine ⟨317922945675517170885349781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211948630450344780590233187 317922945675517170885349781)
    ·
      refine ⟨14902638078539867385250771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 317922945675517170885349781 14902638078539867385250771)
      ·
        refine ⟨22353957117809801077876157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902638078539867385250771 22353957117809801077876157)
        ·
          refine ⟨8382733919178675404203559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22353957117809801077876157 8382733919178675404203559)
          ·
            refine ⟨12574100878768013106305339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382733919178675404203559 12574100878768013106305339)
            ·
              refine ⟨18861151318152019659458009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12574100878768013106305339 18861151318152019659458009)
              ·
                refine ⟨14145863488614014744593507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18861151318152019659458009 14145863488614014744593507)
                ·
                  refine ⟨21218795232921022116890261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14145863488614014744593507 21218795232921022116890261)
                  ·
                    refine ⟨994631026543172911729231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21218795232921022116890261 994631026543172911729231)
                    ·
                      rfl

theorem cell23_5811111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5811111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811111 prefixEnd_5811111 := by exact prefixLift 5811111
  have htrace : WordTrace (prefixWord ++ tailWord_5811111) baseStart_5811111 baseEnd_5811111 := by
    simpa [prefixWord, tailWord_5811111, baseEnd_5811111] using wordTrace_append hprefix tailTrace_5811111
  have hstable : (prefixWord ++ tailWord_5811111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811111).length < 2 ^ (prefixWord ++ tailWord_5811111).sum := by decide
  have hdescent : baseEnd_5811111 < baseStart_5811111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811151 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_5811151 : Nat := 118140960795 + 5811151 * 2 ^ 59
def prefixEnd_5811151 : Nat := 4983230072969 + 3 ^ 40 * 5811151 * 2
def baseEnd_5811151 : Nat := 2983913618855698578687509

theorem tailTrace_5811151 : CollatzResearch.WordTrace tailWord_5811151 prefixEnd_5811151 2983913618855698578687509 := by
  unfold tailWord_5811151
  simp only [CollatzResearch.WordTrace]
  refine ⟨211950089370199867421689307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141300059580133244947792871 211950089370199867421689307)
  ·
    refine ⟨317925134055299801132533961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211950089370199867421689307 317925134055299801132533961)
    ·
      refine ⟨238443850541474850849400471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317925134055299801132533961 238443850541474850849400471)
      ·
        refine ⟨357665775812212276274100707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238443850541474850849400471 357665775812212276274100707)
        ·
          refine ⟨536498663718318414411151061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357665775812212276274100707 536498663718318414411151061)
          ·
            refine ⟨12574187430898087837761353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 536498663718318414411151061 12574187430898087837761353)
            ·
              refine ⟨9430640573173565878321015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12574187430898087837761353 9430640573173565878321015)
              ·
                refine ⟨14145960859760348817481523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9430640573173565878321015 14145960859760348817481523)
                ·
                  refine ⟨21218941289640523226222285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14145960859760348817481523 21218941289640523226222285)
                  ·
                    refine ⟨7957102983615196209833357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21218941289640523226222285 7957102983615196209833357)
                    ·
                      refine ⟨2983913618855698578687509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957102983615196209833357 2983913618855698578687509)
                      ·
                        rfl

theorem cell23_5811151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_5811151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811151 prefixEnd_5811151 := by exact prefixLift 5811151
  have htrace : WordTrace (prefixWord ++ tailWord_5811151) baseStart_5811151 baseEnd_5811151 := by
    simpa [prefixWord, tailWord_5811151, baseEnd_5811151] using wordTrace_append hprefix tailTrace_5811151
  have hstable : (prefixWord ++ tailWord_5811151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811151).length < 2 ^ (prefixWord ++ tailWord_5811151).sum := by decide
  have hdescent : baseEnd_5811151 < baseStart_5811151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811158 : List Nat := [5, 2, 1, 1, 2, 2, 3, 7]
def baseStart_5811158 : Nat := 118140960795 + 5811158 * 2 ^ 59
def prefixEnd_5811158 : Nat := 4983230072969 + 3 ^ 40 * 5811158 * 2
def baseEnd_5811158 : Nat := 110515452341491853751851

theorem tailTrace_5811158 : CollatzResearch.WordTrace tailWord_5811158 prefixEnd_5811158 110515452341491853751851 := by
  unfold tailWord_5811158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246896542573406726074633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141300229787449671744796085 13246896542573406726074633)
  ·
    refine ⟨9935172406930055044555975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13246896542573406726074633 9935172406930055044555975)
    ·
      refine ⟨14902758610395082566833963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935172406930055044555975 14902758610395082566833963)
      ·
        refine ⟨22354137915592623850250945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902758610395082566833963 22354137915592623850250945)
        ·
          refine ⟨16765603436694467887688209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22354137915592623850250945 16765603436694467887688209)
          ·
            refine ⟨12574202577520850915766157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16765603436694467887688209 12574202577520850915766157)
            ·
              refine ⟨4715325966570319093412309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12574202577520850915766157 4715325966570319093412309)
              ·
                refine ⟨110515452341491853751851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4715325966570319093412309 110515452341491853751851)
                ·
                  rfl

theorem cell23_5811158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_5811158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811158 prefixEnd_5811158 := by exact prefixLift 5811158
  have htrace : WordTrace (prefixWord ++ tailWord_5811158) baseStart_5811158 baseEnd_5811158 := by
    simpa [prefixWord, tailWord_5811158, baseEnd_5811158] using wordTrace_append hprefix tailTrace_5811158
  have hstable : (prefixWord ++ tailWord_5811158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811158).length < 2 ^ (prefixWord ++ tailWord_5811158).sum := by decide
  have hdescent : baseEnd_5811158 < baseStart_5811158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811185 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_5811185 : Nat := 118140960795 + 5811185 * 2 ^ 59
def prefixEnd_5811185 : Nat := 4983230072969 + 3 ^ 40 * 5811185 * 2
def baseEnd_5811185 : Nat := 2983931077197951445662353

theorem tailTrace_5811185 : CollatzResearch.WordTrace tailWord_5811185 prefixEnd_5811185 2983931077197951445662353 := by
  unfold tailWord_5811185
  simp only [CollatzResearch.WordTrace]
  refine ⟨211951329452076691228427009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141300886301384460818951339 211951329452076691228427009)
  ·
    refine ⟨158963497089057518421320257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211951329452076691228427009 158963497089057518421320257)
    ·
      refine ⟨119222622816793138815990193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158963497089057518421320257 119222622816793138815990193)
      ·
        refine ⟨89416967112594854111992645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119222622816793138815990193 89416967112594854111992645)
        ·
          refine ⟨16765681333611535145998621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89416967112594854111992645 16765681333611535145998621)
          ·
            refine ⟨6287130500104325679749483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16765681333611535145998621 6287130500104325679749483)
            ·
              refine ⟨9430695750156488519624225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287130500104325679749483 9430695750156488519624225)
              ·
                refine ⟨7073021812617366389718169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9430695750156488519624225 7073021812617366389718169)
                ·
                  refine ⟨5304766359463024792288627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7073021812617366389718169 5304766359463024792288627)
                  ·
                    refine ⟨7957149539194537188432941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5304766359463024792288627 7957149539194537188432941)
                    ·
                      refine ⟨2983931077197951445662353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957149539194537188432941 2983931077197951445662353)
                      ·
                        rfl

theorem cell23_5811185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_5811185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811185 prefixEnd_5811185 := by exact prefixLift 5811185
  have htrace : WordTrace (prefixWord ++ tailWord_5811185) baseStart_5811185 baseEnd_5811185 := by
    simpa [prefixWord, tailWord_5811185, baseEnd_5811185] using wordTrace_append hprefix tailTrace_5811185
  have hstable : (prefixWord ++ tailWord_5811185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811185).length < 2 ^ (prefixWord ++ tailWord_5811185).sum := by decide
  have hdescent : baseEnd_5811185 < baseStart_5811185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3]
def baseStart_5811194 : Nat := 118140960795 + 5811194 * 2 ^ 59
def prefixEnd_5811194 : Nat := 4983230072969 + 3 ^ 40 * 5811194 * 2
def baseEnd_5811194 : Nat := 2983935698523841910449811

theorem tailTrace_5811194 : CollatzResearch.WordTrace tailWord_5811194 prefixEnd_5811194 2983935698523841910449811 := by
  unfold tailWord_5811194
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987914427261021441376159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141301105139362723843669757 52987914427261021441376159)
  ·
    refine ⟨79481871640891532162064239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52987914427261021441376159 79481871640891532162064239)
    ·
      refine ⟨119222807461337298243096359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79481871640891532162064239 119222807461337298243096359)
      ·
        refine ⟨178834211192005947364644539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119222807461337298243096359 178834211192005947364644539)
        ·
          refine ⟨268251316788008921046966809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178834211192005947364644539 268251316788008921046966809)
          ·
            refine ⟨201188487591006690785225107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268251316788008921046966809 201188487591006690785225107)
            ·
              refine ⟨301782731386510036177837661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201188487591006690785225107 301782731386510036177837661)
              ·
                refine ⟨113168524269941263566689123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301782731386510036177837661 113168524269941263566689123)
                ·
                  refine ⟨169752786404911895350033685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113168524269941263566689123 169752786404911895350033685)
                  ·
                    refine ⟨7957161862730245094532829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 169752786404911895350033685 7957161862730245094532829)
                    ·
                      refine ⟨2983935698523841910449811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957161862730245094532829 2983935698523841910449811)
                      ·
                        rfl

theorem cell23_5811194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_5811194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811194 prefixEnd_5811194 := by exact prefixLift 5811194
  have htrace : WordTrace (prefixWord ++ tailWord_5811194) baseStart_5811194 baseEnd_5811194 := by
    simpa [prefixWord, tailWord_5811194, baseEnd_5811194] using wordTrace_append hprefix tailTrace_5811194
  have hstable : (prefixWord ++ tailWord_5811194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811194).length < 2 ^ (prefixWord ++ tailWord_5811194).sum := by decide
  have hdescent : baseEnd_5811194 < baseStart_5811194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811202 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5811202 : Nat := 118140960795 + 5811202 * 2 ^ 59
def prefixEnd_5811202 : Nat := 4983230072969 + 3 ^ 40 * 5811202 * 2
def baseEnd_5811202 : Nat := 2983939806369077879149775

theorem tailTrace_5811202 : CollatzResearch.WordTrace tailWord_5811202 prefixEnd_5811202 2983939806369077879149775 := by
  unfold tailWord_5811202
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987987373253775782948965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141301299662010068754530573 52987987373253775782948965)
  ·
    refine ⟨9935247632485082959302931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52987987373253775782948965 9935247632485082959302931)
    ·
      refine ⟨14902871448727624438954397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935247632485082959302931 14902871448727624438954397)
      ·
        refine ⟨5588576793272859164607899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14902871448727624438954397 5588576793272859164607899)
        ·
          refine ⟨8382865189909288746911849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588576793272859164607899 8382865189909288746911849)
          ·
            refine ⟨6287148892431966560183887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382865189909288746911849 6287148892431966560183887)
            ·
              refine ⟨9430723338647949840275831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6287148892431966560183887 9430723338647949840275831)
              ·
                refine ⟨14146085007971924760413747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9430723338647949840275831 14146085007971924760413747)
                ·
                  refine ⟨21219127511957887140620621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14146085007971924760413747 21219127511957887140620621)
                  ·
                    refine ⟨7957172816984207677732733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21219127511957887140620621 7957172816984207677732733)
                    ·
                      refine ⟨2983939806369077879149775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957172816984207677732733 2983939806369077879149775)
                      ·
                        rfl

theorem cell23_5811202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5811202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811202 prefixEnd_5811202 := by exact prefixLift 5811202
  have htrace : WordTrace (prefixWord ++ tailWord_5811202) baseStart_5811202 baseEnd_5811202 := by
    simpa [prefixWord, tailWord_5811202, baseEnd_5811202] using wordTrace_append hprefix tailTrace_5811202
  have hstable : (prefixWord ++ tailWord_5811202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811202).length < 2 ^ (prefixWord ++ tailWord_5811202).sum := by decide
  have hdescent : baseEnd_5811202 < baseStart_5811202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811208 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_5811208 : Nat := 118140960795 + 5811208 * 2 ^ 59
def prefixEnd_5811208 : Nat := 4983230072969 + 3 ^ 40 * 5811208 * 2
def baseEnd_5811208 : Nat := 2983942887253004855674747

theorem tailTrace_5811208 : CollatzResearch.WordTrace tailWord_5811208 prefixEnd_5811208 2983942887253004855674747 := by
  unfold tailWord_5811208
  simp only [CollatzResearch.WordTrace]
  refine ⟨105976084165496683078257139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141301445553995577437676185 105976084165496683078257139)
  ·
    refine ⟨158964126248245024617385709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105976084165496683078257139 158964126248245024617385709)
    ·
      refine ⟨59611547343091884231519641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158964126248245024617385709 59611547343091884231519641)
      ·
        refine ⟨44708660507318913173639731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59611547343091884231519641 44708660507318913173639731)
        ·
          refine ⟨67062990760978369760459597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44708660507318913173639731 67062990760978369760459597)
          ·
            refine ⟨25148621535366888660172349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67062990760978369760459597 25148621535366888660172349)
            ·
              refine ⟨9430733075762583247564631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25148621535366888660172349 9430733075762583247564631)
              ·
                refine ⟨14146099613643874871346947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9430733075762583247564631 14146099613643874871346947)
                ·
                  refine ⟨21219149420465812307020421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14146099613643874871346947 21219149420465812307020421)
                  ·
                    refine ⟨3978590516337339807566329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21219149420465812307020421 3978590516337339807566329)
                    ·
                      refine ⟨2983942887253004855674747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978590516337339807566329 2983942887253004855674747)
                      ·
                        rfl

theorem cell23_5811208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_5811208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811208 prefixEnd_5811208 := by exact prefixLift 5811208
  have htrace : WordTrace (prefixWord ++ tailWord_5811208) baseStart_5811208 baseEnd_5811208 := by
    simpa [prefixWord, tailWord_5811208, baseEnd_5811208] using wordTrace_append hprefix tailTrace_5811208
  have hstable : (prefixWord ++ tailWord_5811208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811208).length < 2 ^ (prefixWord ++ tailWord_5811208).sum := by decide
  have hdescent : baseEnd_5811208 < baseStart_5811208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811248 : List Nat := [2, 1, 1, 1, 2, 4, 5, 2, 5]
def baseStart_5811248 : Nat := 118140960795 + 5811248 * 2 ^ 59
def prefixEnd_5811248 : Nat := 4983230072969 + 3 ^ 40 * 5811248 * 2
def baseEnd_5811248 : Nat := 331551491831020522130507

theorem tailTrace_5811248 : CollatzResearch.WordTrace tailWord_5811248 prefixEnd_5811248 331551491831020522130507 := by
  unfold tailWord_5811248
  simp only [CollatzResearch.WordTrace]
  refine ⟨105976813625424226493985199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141302418167232301991980265 105976813625424226493985199)
  ·
    refine ⟨158965220438136339740977799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105976813625424226493985199 158965220438136339740977799)
    ·
      refine ⟨238447830657204509611466699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158965220438136339740977799 238447830657204509611466699)
      ·
        refine ⟨357671745985806764417200049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238447830657204509611466699 357671745985806764417200049)
        ·
          refine ⟨268253809489355073312900037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357671745985806764417200049 268253809489355073312900037)
          ·
            refine ⟨50297589279254076246168757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 268253809489355073312900037 50297589279254076246168757)
            ·
              refine ⟨4715398994930069648078321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50297589279254076246168757 4715398994930069648078321)
              ·
                refine ⟨3536549246197552236058741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715398994930069648078321 3536549246197552236058741)
                ·
                  refine ⟨331551491831020522130507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536549246197552236058741 331551491831020522130507)
                  ·
                    rfl

theorem cell23_5811248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 2, 5].length) (baseStart_5811248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811248 prefixEnd_5811248 := by exact prefixLift 5811248
  have htrace : WordTrace (prefixWord ++ tailWord_5811248) baseStart_5811248 baseEnd_5811248 := by
    simpa [prefixWord, tailWord_5811248, baseEnd_5811248] using wordTrace_append hprefix tailTrace_5811248
  have hstable : (prefixWord ++ tailWord_5811248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811248).length < 2 ^ (prefixWord ++ tailWord_5811248).sum := by decide
  have hdescent : baseEnd_5811248 < baseStart_5811248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811251 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 2, 5, 2]
def baseStart_5811251 : Nat := 118140960795 + 5811251 * 2 ^ 59
def prefixEnd_5811251 : Nat := 4983230072969 + 3 ^ 40 * 5811251 * 2
def baseEnd_5811251 : Nat := 2983964966921148187437049

theorem tailTrace_5811251 : CollatzResearch.WordTrace tailWord_5811251 prefixEnd_5811251 2983964966921148187437049 := by
  unfold tailWord_5811251
  simp only [CollatzResearch.WordTrace]
  refine ⟨211953736669837584500329607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141302491113225056333553071 211953736669837584500329607)
  ·
    refine ⟨317930605004756376750494411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211953736669837584500329607 317930605004756376750494411)
    ·
      refine ⟨476895907507134565125741617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317930605004756376750494411 476895907507134565125741617)
      ·
        refine ⟨357671930630350923844306213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476895907507134565125741617 357671930630350923844306213)
        ·
          refine ⟨67063486993190798220807415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357671930630350923844306213 67063486993190798220807415)
          ·
            refine ⟨100595230489786197331211123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67063486993190798220807415 100595230489786197331211123)
            ·
              refine ⟨150892845734679295996816685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100595230489786197331211123 150892845734679295996816685)
              ·
                refine ⟨56584817150504735998806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150892845734679295996816685 56584817150504735998806257)
                ·
                  refine ⟨42438612862878551999104693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56584817150504735998806257 42438612862878551999104693)
                  ·
                    refine ⟨3978619955894864249916065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42438612862878551999104693 3978619955894864249916065)
                    ·
                      refine ⟨2983964966921148187437049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978619955894864249916065 2983964966921148187437049)
                      ·
                        rfl

theorem cell23_5811251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5, 2].length) (baseStart_5811251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811251 prefixEnd_5811251 := by exact prefixLift 5811251
  have htrace : WordTrace (prefixWord ++ tailWord_5811251) baseStart_5811251 baseEnd_5811251 := by
    simpa [prefixWord, tailWord_5811251, baseEnd_5811251] using wordTrace_append hprefix tailTrace_5811251
  have hstable : (prefixWord ++ tailWord_5811251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811251).length < 2 ^ (prefixWord ++ tailWord_5811251).sum := by decide
  have hdescent : baseEnd_5811251 < baseStart_5811251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811274 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_5811274 : Nat := 118140960795 + 5811274 * 2 ^ 59
def prefixEnd_5811274 : Nat := 4983230072969 + 3 ^ 40 * 5811274 * 2
def baseEnd_5811274 : Nat := 994658925658733865816481

theorem tailTrace_5811274 : CollatzResearch.WordTrace tailWord_5811274 prefixEnd_5811274 994658925658733865816481 := by
  unfold tailWord_5811274
  simp only [CollatzResearch.WordTrace]
  refine ⟨52988643887188564857104219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141303050365836172952277917 52988643887188564857104219)
  ·
    refine ⟨79482965830782847285656329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52988643887188564857104219 79482965830782847285656329)
    ·
      refine ⟨59612224373087135464242247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79482965830782847285656329 59612224373087135464242247)
      ·
        refine ⟨89418336559630703196363371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59612224373087135464242247 89418336559630703196363371)
        ·
          refine ⟨134127504839446054794545057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89418336559630703196363371 134127504839446054794545057)
          ·
            refine ⟨100595628629584541095908793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134127504839446054794545057 100595628629584541095908793)
            ·
              refine ⟨75446721472188405821931595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100595628629584541095908793 75446721472188405821931595)
              ·
                refine ⟨113170082208282608732897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75446721472188405821931595 113170082208282608732897393)
                ·
                  refine ⟨84877561656211956549673045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113170082208282608732897393 84877561656211956549673045)
                  ·
                    refine ⟨994658925658733865816481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84877561656211956549673045 994658925658733865816481)
                    ·
                      rfl

theorem cell23_5811274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_5811274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811274 prefixEnd_5811274 := by exact prefixLift 5811274
  have htrace : WordTrace (prefixWord ++ tailWord_5811274) baseStart_5811274 baseEnd_5811274 := by
    simpa [prefixWord, tailWord_5811274, baseEnd_5811274] using wordTrace_append hprefix tailTrace_5811274
  have hstable : (prefixWord ++ tailWord_5811274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811274).length < 2 ^ (prefixWord ++ tailWord_5811274).sum := by decide
  have hdescent : baseEnd_5811274 < baseStart_5811274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811281 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_5811281 : Nat := 118140960795 + 5811281 * 2 ^ 59
def prefixEnd_5811281 : Nat := 4983230072969 + 3 ^ 40 * 5811281 * 2
def baseEnd_5811281 : Nat := 2983980371340783070061911

theorem tailTrace_5811281 : CollatzResearch.WordTrace tailWord_5811281 prefixEnd_5811281 2983980371340783070061911 := by
  unfold tailWord_5811281
  simp only [CollatzResearch.WordTrace]
  refine ⟨211954830859728899623921697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141303220573152599749281131 211954830859728899623921697)
  ·
    refine ⟨158966123144796674717941273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211954830859728899623921697 158966123144796674717941273)
    ·
      refine ⟨119224592358597506038455955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158966123144796674717941273 119224592358597506038455955)
      ·
        refine ⟨178836888537896259057683933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119224592358597506038455955 178836888537896259057683933)
        ·
          refine ⟨67063833201711097146631475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178836888537896259057683933 67063833201711097146631475)
          ·
            refine ⟨100595749802566645719947213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67063833201711097146631475 100595749802566645719947213)
            ·
              refine ⟨37723406175962492144980205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100595749802566645719947213 37723406175962492144980205)
              ·
                refine ⟨14146277315985934554367577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37723406175962492144980205 14146277315985934554367577)
                ·
                  refine ⟨10609707986989450915775683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14146277315985934554367577 10609707986989450915775683)
                  ·
                    refine ⟨15914561980484176373663525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10609707986989450915775683 15914561980484176373663525)
                    ·
                      refine ⟨2983980371340783070061911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15914561980484176373663525 2983980371340783070061911)
                      ·
                        rfl

theorem cell23_5811281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_5811281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811281 prefixEnd_5811281 := by exact prefixLift 5811281
  have htrace : WordTrace (prefixWord ++ tailWord_5811281) baseStart_5811281 baseEnd_5811281 := by
    simpa [prefixWord, tailWord_5811281, baseEnd_5811281] using wordTrace_append hprefix tailTrace_5811281
  have hstable : (prefixWord ++ tailWord_5811281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811281).length < 2 ^ (prefixWord ++ tailWord_5811281).sum := by decide
  have hdescent : baseEnd_5811281 < baseStart_5811281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811318 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5811318 : Nat := 118140960795 + 5811318 * 2 ^ 59
def prefixEnd_5811318 : Nat := 4983230072969 + 3 ^ 40 * 5811318 * 2
def baseEnd_5811318 : Nat := 2983999370124999425299241

theorem tailTrace_5811318 : CollatzResearch.WordTrace tailWord_5811318 prefixEnd_5811318 2983999370124999425299241 := by
  unfold tailWord_5811318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13247261272537178433938663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141304120240396569962012405 13247261272537178433938663)
  ·
    refine ⟨19870891908805767650907995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13247261272537178433938663 19870891908805767650907995)
    ·
      refine ⟨29806337863208651476361993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19870891908805767650907995 29806337863208651476361993)
      ·
        refine ⟨22354753397406488607271495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29806337863208651476361993 22354753397406488607271495)
        ·
          refine ⟨33532130096109732910907243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22354753397406488607271495 33532130096109732910907243)
          ·
            refine ⟨50298195144164599366360865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33532130096109732910907243 50298195144164599366360865)
            ·
              refine ⟨37723646358123449524770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50298195144164599366360865 37723646358123449524770649)
              ·
                refine ⟨28292734768592587143577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37723646358123449524770649 28292734768592587143577987)
                ·
                  refine ⟨42439102152888880715366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28292734768592587143577987 42439102152888880715366981)
                  ·
                    refine ⟨7957331653666665134131309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42439102152888880715366981 7957331653666665134131309)
                    ·
                      refine ⟨2983999370124999425299241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957331653666665134131309 2983999370124999425299241)
                      ·
                        rfl

theorem cell23_5811318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5811318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811318 prefixEnd_5811318 := by exact prefixLift 5811318
  have htrace : WordTrace (prefixWord ++ tailWord_5811318) baseStart_5811318 baseEnd_5811318 := by
    simpa [prefixWord, tailWord_5811318, baseEnd_5811318] using wordTrace_append hprefix tailTrace_5811318
  have hstable : (prefixWord ++ tailWord_5811318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811318).length < 2 ^ (prefixWord ++ tailWord_5811318).sum := by decide
  have hdescent : baseEnd_5811318 < baseStart_5811318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811342 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_5811342 : Nat := 118140960795 + 5811342 * 2 ^ 59
def prefixEnd_5811342 : Nat := 4983230072969 + 3 ^ 40 * 5811342 * 2
def baseEnd_5811342 : Nat := 994670564553569110466377

theorem tailTrace_5811342 : CollatzResearch.WordTrace tailWord_5811342 prefixEnd_5811342 994670564553569110466377 := by
  unfold tailWord_5811342
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494631964063488380236535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141304703808338604694594853 26494631964063488380236535)
  ·
    refine ⟨39741947946095232570354803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26494631964063488380236535 39741947946095232570354803)
    ·
      refine ⟨59612921919142848855532205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39741947946095232570354803 59612921919142848855532205)
      ·
        refine ⟨22354845719678568320824577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59612921919142848855532205 22354845719678568320824577)
        ·
          refine ⟨16766134289758926240618433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22354845719678568320824577 16766134289758926240618433)
          ·
            refine ⟨12574600717319194680463825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16766134289758926240618433 12574600717319194680463825)
            ·
              refine ⟨9430950537989396010347869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12574600717319194680463825 9430950537989396010347869)
              ·
                refine ⟨3536606451746023503880451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9430950537989396010347869 3536606451746023503880451)
                ·
                  refine ⟨5304909677619035255820677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3536606451746023503880451 5304909677619035255820677)
                  ·
                    refine ⟨994670564553569110466377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5304909677619035255820677 994670564553569110466377)
                    ·
                      rfl

theorem cell23_5811342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_5811342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811342 prefixEnd_5811342 := by exact prefixLift 5811342
  have htrace : WordTrace (prefixWord ++ tailWord_5811342) baseStart_5811342 baseEnd_5811342 := by
    simpa [prefixWord, tailWord_5811342, baseEnd_5811342] using wordTrace_append hprefix tailTrace_5811342
  have hstable : (prefixWord ++ tailWord_5811342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811342).length < 2 ^ (prefixWord ++ tailWord_5811342).sum := by decide
  have hdescent : baseEnd_5811342 < baseStart_5811342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811358 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5811358 : Nat := 118140960795 + 5811358 * 2 ^ 59
def prefixEnd_5811358 : Nat := 4983230072969 + 3 ^ 40 * 5811358 * 2
def baseEnd_5811358 : Nat := 2984019909351179268799057

theorem tailTrace_5811358 : CollatzResearch.WordTrace tailWord_5811358 prefixEnd_5811358 2984019909351179268799057 := by
  unfold tailWord_5811358
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494704910056242721809341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141305092853633294516316485 26494704910056242721809341)
  ·
    refine ⟨9935514341271091020678503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26494704910056242721809341 9935514341271091020678503)
    ·
      refine ⟨14903271511906636531017755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9935514341271091020678503 14903271511906636531017755)
      ·
        refine ⟨22354907267859954796526633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14903271511906636531017755 22354907267859954796526633)
        ·
          refine ⟨16766180450894966097394975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22354907267859954796526633 16766180450894966097394975)
          ·
            refine ⟨25149270676342449146092463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16766180450894966097394975 25149270676342449146092463)
            ·
              refine ⟨37723906014513673719138695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25149270676342449146092463 37723906014513673719138695)
              ·
                refine ⟨56585859021770510578708043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37723906014513673719138695 56585859021770510578708043)
                ·
                  refine ⟨84878788532655765868062065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56585859021770510578708043 84878788532655765868062065)
                  ·
                    refine ⟨63659091399491824401046549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84878788532655765868062065 63659091399491824401046549)
                    ·
                      refine ⟨2984019909351179268799057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63659091399491824401046549 2984019909351179268799057)
                      ·
                        rfl

theorem cell23_5811358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5811358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811358 prefixEnd_5811358 := by exact prefixLift 5811358
  have htrace : WordTrace (prefixWord ++ tailWord_5811358) baseStart_5811358 baseEnd_5811358 := by
    simpa [prefixWord, tailWord_5811358, baseEnd_5811358] using wordTrace_append hprefix tailTrace_5811358
  have hstable : (prefixWord ++ tailWord_5811358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811358).length < 2 ^ (prefixWord ++ tailWord_5811358).sum := by decide
  have hdescent : baseEnd_5811358 < baseStart_5811358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811365 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_5811365 : Nat := 118140960795 + 5811365 * 2 ^ 59
def prefixEnd_5811365 : Nat := 4983230072969 + 3 ^ 40 * 5811365 * 2
def baseEnd_5811365 : Nat := 2984023503715760741411525

theorem tailTrace_5811365 : CollatzResearch.WordTrace tailWord_5811365 prefixEnd_5811365 2984023503715760741411525 := by
  unfold tailWord_5811365
  simp only [CollatzResearch.WordTrace]
  refine ⟨211957894591424581969979549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141305263060949721313319699 211957894591424581969979549)
  ·
    refine ⟨79484210471784218238742331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211957894591424581969979549 79484210471784218238742331)
    ·
      refine ⟨119226315707676327358113497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79484210471784218238742331 119226315707676327358113497)
      ·
        refine ⟨89419736780757245518585123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119226315707676327358113497 89419736780757245518585123)
        ·
          refine ⟨134129605171135868277877685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89419736780757245518585123 134129605171135868277877685)
          ·
            refine ⟨12574650484793987651051033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134129605171135868277877685 12574650484793987651051033)
            ·
              refine ⟨9430987863595490738288275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12574650484793987651051033 9430987863595490738288275)
              ·
                refine ⟨14146481795393236107432413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9430987863595490738288275 14146481795393236107432413)
                ·
                  refine ⟨5304930673272463540287155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14146481795393236107432413 5304930673272463540287155)
                  ·
                    refine ⟨7957396009908695310430733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5304930673272463540287155 7957396009908695310430733)
                    ·
                      refine ⟨2984023503715760741411525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7957396009908695310430733 2984023503715760741411525)
                      ·
                        rfl

theorem cell23_5811365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_5811365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811365 prefixEnd_5811365 := by exact prefixLift 5811365
  have htrace : WordTrace (prefixWord ++ tailWord_5811365) baseStart_5811365 baseEnd_5811365 := by
    simpa [prefixWord, tailWord_5811365, baseEnd_5811365] using wordTrace_append hprefix tailTrace_5811365
  have hstable : (prefixWord ++ tailWord_5811365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811365).length < 2 ^ (prefixWord ++ tailWord_5811365).sum := by decide
  have hdescent : baseEnd_5811365 < baseStart_5811365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811511 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_5811511 : Nat := 118140960795 + 5811511 * 2 ^ 59
def prefixEnd_5811511 : Nat := 4983230072969 + 3 ^ 40 * 5811511 * 2
def baseEnd_5811511 : Nat := 2984098471891317170185853

theorem tailTrace_5811511 : CollatzResearch.WordTrace tailWord_5811511 prefixEnd_5811511 2984098471891317170185853 := by
  unfold tailWord_5811511
  simp only [CollatzResearch.WordTrace]
  refine ⟨211963219648895648904794387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141308813099263765936529591 211963219648895648904794387)
  ·
    refine ⟨317944829473343473357191581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211963219648895648904794387 317944829473343473357191581)
    ·
      refine ⟨119229311052503802508946843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317944829473343473357191581 119229311052503802508946843)
      ·
        refine ⟨178843966578755703763420265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119229311052503802508946843 178843966578755703763420265)
        ·
          refine ⟨134132974934066777822565199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178843966578755703763420265 134132974934066777822565199)
          ·
            refine ⟨201199462401100166733847799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134132974934066777822565199 201199462401100166733847799)
            ·
              refine ⟨301799193601650250100771699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201199462401100166733847799 301799193601650250100771699)
              ·
                refine ⟨452698790402475375151157549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301799193601650250100771699 452698790402475375151157549)
                ·
                  refine ⟨169762046400928265681684081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452698790402475375151157549 169762046400928265681684081)
                  ·
                    refine ⟨127321534800696199261263061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169762046400928265681684081 127321534800696199261263061)
                    ·
                      refine ⟨2984098471891317170185853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127321534800696199261263061 2984098471891317170185853)
                      ·
                        rfl

theorem cell23_5811511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_5811511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811511 prefixEnd_5811511 := by exact prefixLift 5811511
  have htrace : WordTrace (prefixWord ++ tailWord_5811511) baseStart_5811511 baseEnd_5811511 := by
    simpa [prefixWord, tailWord_5811511, baseEnd_5811511] using wordTrace_append hprefix tailTrace_5811511
  have hstable : (prefixWord ++ tailWord_5811511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811511).length < 2 ^ (prefixWord ++ tailWord_5811511).sum := by decide
  have hdescent : baseEnd_5811511 < baseStart_5811511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811518 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_5811518 : Nat := 118140960795 + 5811518 * 2 ^ 59
def prefixEnd_5811518 : Nat := 4983230072969 + 3 ^ 40 * 5811518 * 2
def baseEnd_5811518 : Nat := 331566896250655404755369

theorem tailTrace_5811518 : CollatzResearch.WordTrace tailWord_5811518 prefixEnd_5811518 331566896250655404755369 := by
  unfold tailWord_5811518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26495434369983786137537401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141308983306580192733532805 26495434369983786137537401)
  ·
    refine ⟨19871575777487839603153051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26495434369983786137537401 19871575777487839603153051)
    ·
      refine ⟨29807363666231759404729577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19871575777487839603153051 29807363666231759404729577)
      ·
        refine ⟨22355522749673819553547183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29807363666231759404729577 22355522749673819553547183)
        ·
          refine ⟨33533284124510729330320775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22355522749673819553547183 33533284124510729330320775)
          ·
            refine ⟨50299926186766093995481163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33533284124510729330320775 50299926186766093995481163)
            ·
              refine ⟨75449889280149140993221745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50299926186766093995481163 75449889280149140993221745)
              ·
                refine ⟨56587416960111855744916309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75449889280149140993221745 56587416960111855744916309)
                ·
                  refine ⟨331566896250655404755369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56587416960111855744916309 331566896250655404755369)
                  ·
                    rfl

theorem cell23_5811518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_5811518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811518 prefixEnd_5811518 := by exact prefixLift 5811518
  have htrace : WordTrace (prefixWord ++ tailWord_5811518) baseStart_5811518 baseEnd_5811518 := by
    simpa [prefixWord, tailWord_5811518, baseEnd_5811518] using wordTrace_append hprefix tailTrace_5811518
  have hstable : (prefixWord ++ tailWord_5811518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811518).length < 2 ^ (prefixWord ++ tailWord_5811518).sum := by decide
  have hdescent : baseEnd_5811518 < baseStart_5811518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811568 : List Nat := [2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4]
def baseStart_5811568 : Nat := 118140960795 + 5811568 * 2 ^ 59
def prefixEnd_5811568 : Nat := 4983230072969 + 3 ^ 40 * 5811568 * 2
def baseEnd_5811568 : Nat := 2984127740288623447173091

theorem tailTrace_5811568 : CollatzResearch.WordTrace tailWord_5811568 prefixEnd_5811568 2984127740288623447173091 := by
  unfold tailWord_5811568
  simp only [CollatzResearch.WordTrace]
  refine ⟨105982649304844573819809679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141310199073126098426412905 105982649304844573819809679)
  ·
    refine ⟨158973973957266860729714519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105982649304844573819809679 158973973957266860729714519)
    ·
      refine ⟨238460960935900291094571779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158973973957266860729714519 238460960935900291094571779)
      ·
        refine ⟨357691441403850436641857669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238460960935900291094571779 357691441403850436641857669)
        ·
          refine ⟨67067145263221956870348313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 357691441403850436641857669 67067145263221956870348313)
          ·
            refine ⟨50300358947416467652761235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67067145263221956870348313 50300358947416467652761235)
            ·
              refine ⟨75450538421124701479141853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50300358947416467652761235 75450538421124701479141853)
              ·
                refine ⟨28293951907921763054678195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75450538421124701479141853 28293951907921763054678195)
                ·
                  refine ⟨42440927861882644582017293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28293951907921763054678195 42440927861882644582017293)
                  ·
                    refine ⟨15915347948205991718256485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42440927861882644582017293 15915347948205991718256485)
                    ·
                      refine ⟨2984127740288623447173091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15915347948205991718256485 2984127740288623447173091)
                      ·
                        rfl

theorem cell23_5811568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 4].length) (baseStart_5811568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811568 prefixEnd_5811568 := by exact prefixLift 5811568
  have htrace : WordTrace (prefixWord ++ tailWord_5811568) baseStart_5811568 baseEnd_5811568 := by
    simpa [prefixWord, tailWord_5811568, baseEnd_5811568] using wordTrace_append hprefix tailTrace_5811568
  have hstable : (prefixWord ++ tailWord_5811568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811568).length < 2 ^ (prefixWord ++ tailWord_5811568).sum := by decide
  have hdescent : baseEnd_5811568 < baseStart_5811568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811586 : List Nat := [3, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_5811586 : Nat := 118140960795 + 5811586 * 2 ^ 59
def prefixEnd_5811586 : Nat := 4983230072969 + 3 ^ 40 * 5811586 * 2
def baseEnd_5811586 : Nat := 331570775882267152972001

theorem tailTrace_5811586 : CollatzResearch.WordTrace tailWord_5811586 prefixEnd_5811586 331570775882267152972001 := by
  unfold tailWord_5811586
  simp only [CollatzResearch.WordTrace]
  refine ⟨52991488780905984178443653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141310636749082624475849741 52991488780905984178443653)
  ·
    refine ⟨9935904146419872033458185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52991488780905984178443653 9935904146419872033458185)
    ·
      refine ⟨7451928109814904025093639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9935904146419872033458185 7451928109814904025093639)
      ·
        refine ⟨11177892164722356037640459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7451928109814904025093639 11177892164722356037640459)
        ·
          refine ⟨16766838247083534056460689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11177892164722356037640459 16766838247083534056460689)
          ·
            refine ⟨12575128685312650542345517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16766838247083534056460689 12575128685312650542345517)
            ·
              refine ⟨4715673256992243953379569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12575128685312650542345517 4715673256992243953379569)
              ·
                refine ⟨3536754942744182965034677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4715673256992243953379569 3536754942744182965034677)
                ·
                  refine ⟨331570775882267152972001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536754942744182965034677 331570775882267152972001)
                  ·
                    rfl

theorem cell23_5811586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_5811586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811586 prefixEnd_5811586 := by exact prefixLift 5811586
  have htrace : WordTrace (prefixWord ++ tailWord_5811586) baseStart_5811586 baseEnd_5811586 := by
    simpa [prefixWord, tailWord_5811586, baseEnd_5811586] using wordTrace_append hprefix tailTrace_5811586
  have hstable : (prefixWord ++ tailWord_5811586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811586).length < 2 ^ (prefixWord ++ tailWord_5811586).sum := by decide
  have hdescent : baseEnd_5811586 < baseStart_5811586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811662 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2]
def baseStart_5811662 : Nat := 118140960795 + 5811662 * 2 ^ 59
def prefixEnd_5811662 : Nat := 4983230072969 + 3 ^ 40 * 5811662 * 2
def baseEnd_5811662 : Nat := 2984176007470146079397659

theorem tailTrace_5811662 : CollatzResearch.WordTrace tailWord_5811662 prefixEnd_5811662 2984176007470146079397659 := by
  unfold tailWord_5811662
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496090883918575211692655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141312484714232401129027493 26496090883918575211692655)
  ·
    refine ⟨39744136325877862817538983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26496090883918575211692655 39744136325877862817538983)
    ·
      refine ⟨59616204488816794226308475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39744136325877862817538983 59616204488816794226308475)
      ·
        refine ⟨89424306733225191339462713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59616204488816794226308475 89424306733225191339462713)
        ·
          refine ⟨67068230049918893504597035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89424306733225191339462713 67068230049918893504597035)
          ·
            refine ⟨100602345074878340256895553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67068230049918893504597035 100602345074878340256895553)
            ·
              refine ⟨75451758806158755192671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100602345074878340256895553 75451758806158755192671665)
              ·
                refine ⟨56588819104619066394503749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75451758806158755192671665 56588819104619066394503749)
                ·
                  refine ⟨10610403582116074948969453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56588819104619066394503749 10610403582116074948969453)
                  ·
                    refine ⟨3978901343293528105863545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10610403582116074948969453 3978901343293528105863545)
                    ·
                      refine ⟨2984176007470146079397659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978901343293528105863545 2984176007470146079397659)
                      ·
                        rfl

theorem cell23_5811662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_5811662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811662 prefixEnd_5811662 := by exact prefixLift 5811662
  have htrace : WordTrace (prefixWord ++ tailWord_5811662) baseStart_5811662 baseEnd_5811662 := by
    simpa [prefixWord, tailWord_5811662, baseEnd_5811662] using wordTrace_append hprefix tailTrace_5811662
  have hstable : (prefixWord ++ tailWord_5811662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811662).length < 2 ^ (prefixWord ++ tailWord_5811662).sum := by decide
  have hdescent : baseEnd_5811662 < baseStart_5811662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 6, 2]
def baseStart_5811675 : Nat := 118140960795 + 5811675 * 2 ^ 59
def prefixEnd_5811675 : Nat := 4983230072969 + 3 ^ 40 * 5811675 * 2
def baseEnd_5811675 : Nat := 2984182682718654528535099

theorem tailTrace_5811675 : CollatzResearch.WordTrace tailWord_5811675 prefixEnd_5811675 2984182682718654528535099 := by
  unfold tailWord_5811675
  simp only [CollatzResearch.WordTrace]
  refine ⟨211969201220301504913764479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141312800813534336609176319 211969201220301504913764479)
  ·
    refine ⟨317953801830452257370646719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211969201220301504913764479 317953801830452257370646719)
    ·
      refine ⟨476930702745678386055970079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317953801830452257370646719 476930702745678386055970079)
      ·
        refine ⟨715396054118517579083955119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476930702745678386055970079 715396054118517579083955119)
        ·
          refine ⟨1073094081177776368625932679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715396054118517579083955119 1073094081177776368625932679)
          ·
            refine ⟨1609641121766664552938899019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073094081177776368625932679 1609641121766664552938899019)
            ·
              refine ⟨2414461682649996829408348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1609641121766664552938899019 2414461682649996829408348529)
              ·
                refine ⟨1810846261987497622056261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2414461682649996829408348529 1810846261987497622056261397)
                ·
                  refine ⟨84883418530663951033887253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1810846261987497622056261397 84883418530663951033887253)
                  ·
                    refine ⟨3978910243624872704713465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84883418530663951033887253 3978910243624872704713465)
                    ·
                      refine ⟨2984182682718654528535099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978910243624872704713465 2984182682718654528535099)
                      ·
                        rfl

theorem cell23_5811675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6, 2].length) (baseStart_5811675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811675 prefixEnd_5811675 := by exact prefixLift 5811675
  have htrace : WordTrace (prefixWord ++ tailWord_5811675) baseStart_5811675 baseEnd_5811675 := by
    simpa [prefixWord, tailWord_5811675, baseEnd_5811675] using wordTrace_append hprefix tailTrace_5811675
  have hstable : (prefixWord ++ tailWord_5811675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811675).length < 2 ^ (prefixWord ++ tailWord_5811675).sum := by decide
  have hdescent : baseEnd_5811675 < baseStart_5811675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811709 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 3, 2, 2]
def baseStart_5811709 : Nat := 118140960795 + 5811709 * 2 ^ 59
def prefixEnd_5811709 : Nat := 4983230072969 + 3 ^ 40 * 5811709 * 2
def baseEnd_5811709 : Nat := 2984200141060907395509943

theorem tailTrace_5811709 : CollatzResearch.WordTrace tailWord_5811709 prefixEnd_5811709 2984200141060907395509943 := by
  unfold tailWord_5811709
  simp only [CollatzResearch.WordTrace]
  refine ⟨211970441302178328720502181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141313627534785552480334787 211970441302178328720502181)
  ·
    refine ⟨39744457744158436635094159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 211970441302178328720502181 39744457744158436635094159)
    ·
      refine ⟨59616686616237654952641239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39744457744158436635094159 59616686616237654952641239)
      ·
        refine ⟨89425029924356482428961859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59616686616237654952641239 89425029924356482428961859)
        ·
          refine ⟨134137544886534723643442789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89425029924356482428961859 134137544886534723643442789)
          ·
            refine ⟨25150789666225260683145523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134137544886534723643442789 25150789666225260683145523)
            ·
              refine ⟨37726184499337891024718285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25150789666225260683145523 37726184499337891024718285)
              ·
                refine ⟨14147319187251709134269357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37726184499337891024718285 14147319187251709134269357)
                ·
                  refine ⟨5305244695219390925351009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14147319187251709134269357 5305244695219390925351009)
                  ·
                    refine ⟨3978933521414543194013257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305244695219390925351009 3978933521414543194013257)
                    ·
                      refine ⟨2984200141060907395509943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978933521414543194013257 2984200141060907395509943)
                      ·
                        rfl

theorem cell23_5811709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_5811709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811709 prefixEnd_5811709 := by exact prefixLift 5811709
  have htrace : WordTrace (prefixWord ++ tailWord_5811709) baseStart_5811709 baseEnd_5811709 := by
    simpa [prefixWord, tailWord_5811709, baseEnd_5811709] using wordTrace_append hprefix tailTrace_5811709
  have hstable : (prefixWord ++ tailWord_5811709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811709).length < 2 ^ (prefixWord ++ tailWord_5811709).sum := by decide
  have hdescent : baseEnd_5811709 < baseStart_5811709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811722 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4]
def baseStart_5811722 : Nat := 118140960795 + 5811722 * 2 ^ 59
def prefixEnd_5811722 : Nat := 4983230072969 + 3 ^ 40 * 5811722 * 2
def baseEnd_5811722 : Nat := 2984206816309415844647383

theorem tailTrace_5811722 : CollatzResearch.WordTrace tailWord_5811722 prefixEnd_5811722 2984206816309415844647383 := by
  unfold tailWord_5811722
  simp only [CollatzResearch.WordTrace]
  refine ⟨52992728862782807985181355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141313943634087487960483613 52992728862782807985181355)
  ·
    refine ⟨79489093294174211977772033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52992728862782807985181355 79489093294174211977772033)
    ·
      refine ⟨59616819970630658983329025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79489093294174211977772033 59616819970630658983329025)
      ·
        refine ⟨44712614977972994237496769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59616819970630658983329025 44712614977972994237496769)
        ·
          refine ⟨33534461233479745678122577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44712614977972994237496769 33534461233479745678122577)
          ·
            refine ⟨25150845925109809258591933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33534461233479745678122577 25150845925109809258591933)
            ·
              refine ⟨9431567221916178471971975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25150845925109809258591933 9431567221916178471971975)
              ·
                refine ⟨14147350832874267707957963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9431567221916178471971975 14147350832874267707957963)
                ·
                  refine ⟨21221026249311401561936945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14147350832874267707957963 21221026249311401561936945)
                  ·
                    refine ⟨15915769686983551171452709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21221026249311401561936945 15915769686983551171452709)
                    ·
                      refine ⟨2984206816309415844647383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15915769686983551171452709 2984206816309415844647383)
                      ·
                        rfl

theorem cell23_5811722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_5811722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811722 prefixEnd_5811722 := by exact prefixLift 5811722
  have htrace : WordTrace (prefixWord ++ tailWord_5811722) baseStart_5811722 baseEnd_5811722 := by
    simpa [prefixWord, tailWord_5811722, baseEnd_5811722] using wordTrace_append hprefix tailTrace_5811722
  have hstable : (prefixWord ++ tailWord_5811722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811722).length < 2 ^ (prefixWord ++ tailWord_5811722).sum := by decide
  have hdescent : baseEnd_5811722 < baseStart_5811722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811799 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 1, 4, 2]
def baseStart_5811799 : Nat := 118140960795 + 5811799 * 2 ^ 59
def prefixEnd_5811799 : Nat := 4983230072969 + 3 ^ 40 * 5811799 * 2
def baseEnd_5811799 : Nat := 2984246354319812043384529

theorem tailTrace_5811799 : CollatzResearch.WordTrace tailWord_5811799 prefixEnd_5811799 2984246354319812043384529 := by
  unfold tailWord_5811799
  simp only [CollatzResearch.WordTrace]
  refine ⟨211973723871852274091278451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141315815914568182727518967 211973723871852274091278451)
  ·
    refine ⟨317960585807778411136917677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211973723871852274091278451 317960585807778411136917677)
    ·
      refine ⟨119235219677916904176344129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317960585807778411136917677 119235219677916904176344129)
      ·
        refine ⟨89426414758437678132258097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119235219677916904176344129 89426414758437678132258097)
        ·
          refine ⟨67069811068828258599193573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89426414758437678132258097 67069811068828258599193573)
          ·
            refine ⟨12575589575405298487348795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67069811068828258599193573 12575589575405298487348795)
            ·
              refine ⟨18863384363107947731023193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12575589575405298487348795 18863384363107947731023193)
              ·
                refine ⟨14147538272330960798267395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18863384363107947731023193 14147538272330960798267395)
                ·
                  refine ⟨21221307408496441197401093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14147538272330960798267395 21221307408496441197401093)
                  ·
                    refine ⟨3978995139093082724512705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21221307408496441197401093 3978995139093082724512705)
                    ·
                      refine ⟨2984246354319812043384529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3978995139093082724512705 2984246354319812043384529)
                      ·
                        rfl

theorem cell23_5811799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4, 2].length) (baseStart_5811799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811799 prefixEnd_5811799 := by exact prefixLift 5811799
  have htrace : WordTrace (prefixWord ++ tailWord_5811799) baseStart_5811799 baseEnd_5811799 := by
    simpa [prefixWord, tailWord_5811799, baseEnd_5811799] using wordTrace_append hprefix tailTrace_5811799
  have hstable : (prefixWord ++ tailWord_5811799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811799).length < 2 ^ (prefixWord ++ tailWord_5811799).sum := by decide
  have hdescent : baseEnd_5811799 < baseStart_5811799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811815 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_5811815 : Nat := 118140960795 + 5811815 * 2 ^ 59
def prefixEnd_5811815 : Nat := 4983230072969 + 3 ^ 40 * 5811815 * 2
def baseEnd_5811815 : Nat := 2984254570010283980784455

theorem tailTrace_5811815 : CollatzResearch.WordTrace tailWord_5811815 prefixEnd_5811815 2984254570010283980784455 := by
  unfold tailWord_5811815
  simp only [CollatzResearch.WordTrace]
  refine ⟨211974307439794308823860899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141316204959862872549240599 211974307439794308823860899)
  ·
    refine ⟨317961461159691463235791349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211974307439794308823860899 317961461159691463235791349)
    ·
      refine ⟨29808886983721074678355439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 317961461159691463235791349 29808886983721074678355439)
      ·
        refine ⟨44713330475581612017533159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29808886983721074678355439 44713330475581612017533159)
        ·
          refine ⟨67069995713372418026299739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44713330475581612017533159 67069995713372418026299739)
          ·
            refine ⟨100604993570058627039449609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67069995713372418026299739 100604993570058627039449609)
            ·
              refine ⟨75453745177543970279587207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100604993570058627039449609 75453745177543970279587207)
              ·
                refine ⟨113180617766315955419380811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75453745177543970279587207 113180617766315955419380811)
                ·
                  refine ⟨169770926649473933129071217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113180617766315955419380811 169770926649473933129071217)
                  ·
                    refine ⟨127328194987105449846803413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169770926649473933129071217 127328194987105449846803413)
                    ·
                      refine ⟨2984254570010283980784455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127328194987105449846803413 2984254570010283980784455)
                      ·
                        rfl

theorem cell23_5811815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_5811815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811815 prefixEnd_5811815 := by exact prefixLift 5811815
  have htrace : WordTrace (prefixWord ++ tailWord_5811815) baseStart_5811815 baseEnd_5811815 := by
    simpa [prefixWord, tailWord_5811815, baseEnd_5811815] using wordTrace_append hprefix tailTrace_5811815
  have hstable : (prefixWord ++ tailWord_5811815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811815).length < 2 ^ (prefixWord ++ tailWord_5811815).sum := by decide
  have hdescent : baseEnd_5811815 < baseStart_5811815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811829 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5811829 : Nat := 118140960795 + 5811829 * 2 ^ 59
def prefixEnd_5811829 : Nat := 4983230072969 + 3 ^ 40 * 5811829 * 2
def baseEnd_5811829 : Nat := 2984261758739446926009391

theorem tailTrace_5811829 : CollatzResearch.WordTrace tailWord_5811829 prefixEnd_5811829 2984261758739446926009391 := by
  unfold tailWord_5811829
  simp only [CollatzResearch.WordTrace]
  refine ⟨211974818061743589214870541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141316545374495726143247027 211974818061743589214870541)
  ·
    refine ⟨79490556773153845955576453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211974818061743589214870541 79490556773153845955576453)
    ·
      refine ⟨14904479394966346116670585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79490556773153845955576453 14904479394966346116670585)
      ·
        refine ⟨11178359546224759587502939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14904479394966346116670585 11178359546224759587502939)
        ·
          refine ⟨16767539319337139381254409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11178359546224759587502939 16767539319337139381254409)
          ·
            refine ⟨12575654489502854535940807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16767539319337139381254409 12575654489502854535940807)
            ·
              refine ⟨18863481734254281803911211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12575654489502854535940807 18863481734254281803911211)
              ·
                refine ⟨28295222601381422705866817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18863481734254281803911211 28295222601381422705866817)
                ·
                  refine ⟨21221416951036067029400113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28295222601381422705866817 21221416951036067029400113)
                  ·
                    refine ⟨15916062713277050272050085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21221416951036067029400113 15916062713277050272050085)
                    ·
                      refine ⟨2984261758739446926009391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15916062713277050272050085 2984261758739446926009391)
                      ·
                        rfl

theorem cell23_5811829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5811829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811829 prefixEnd_5811829 := by exact prefixLift 5811829
  have htrace : WordTrace (prefixWord ++ tailWord_5811829) baseStart_5811829 baseEnd_5811829 := by
    simpa [prefixWord, tailWord_5811829, baseEnd_5811829] using wordTrace_append hprefix tailTrace_5811829
  have hstable : (prefixWord ++ tailWord_5811829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811829).length < 2 ^ (prefixWord ++ tailWord_5811829).sum := by decide
  have hdescent : baseEnd_5811829 < baseStart_5811829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811835 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 7]
def baseStart_5811835 : Nat := 118140960795 + 5811835 * 2 ^ 59
def prefixEnd_5811835 : Nat := 4983230072969 + 3 ^ 40 * 5811835 * 2
def baseEnd_5811835 : Nat := 994754946541124634178121

theorem tailTrace_5811835 : CollatzResearch.WordTrace tailWord_5811835 prefixEnd_5811835 994754946541124634178121 := by
  unfold tailWord_5811835
  simp only [CollatzResearch.WordTrace]
  refine ⟨211975036899721852239588959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141316691266481234826392639 211975036899721852239588959)
  ·
    refine ⟨317962555349582778359383439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211975036899721852239588959 317962555349582778359383439)
    ·
      refine ⟨476943833024374167539075159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317962555349582778359383439 476943833024374167539075159)
      ·
        refine ⟨715415749536561251308612739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476943833024374167539075159 715415749536561251308612739)
        ·
          refine ⟨1073123624304841876962919109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715415749536561251308612739 1073123624304841876962919109)
          ·
            refine ⟨201210679557157851930547333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1073123624304841876962919109 201210679557157851930547333)
            ·
              refine ⟨37727002416967097236977625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201210679557157851930547333 37727002416967097236977625)
              ·
                refine ⟨28295251812725322927733219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37727002416967097236977625 28295251812725322927733219)
                ·
                  refine ⟨42442877719087984391599829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28295251812725322927733219 42442877719087984391599829)
                  ·
                    refine ⟨994754946541124634178121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42442877719087984391599829 994754946541124634178121)
                    ·
                      rfl

theorem cell23_5811835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_5811835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811835 prefixEnd_5811835 := by exact prefixLift 5811835
  have htrace : WordTrace (prefixWord ++ tailWord_5811835) baseStart_5811835 baseEnd_5811835 := by
    simpa [prefixWord, tailWord_5811835, baseEnd_5811835] using wordTrace_append hprefix tailTrace_5811835
  have hstable : (prefixWord ++ tailWord_5811835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811835).length < 2 ^ (prefixWord ++ tailWord_5811835).sum := by decide
  have hdescent : baseEnd_5811835 < baseStart_5811835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811959 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 1, 5]
def baseStart_5811959 : Nat := 118140960795 + 5811959 * 2 ^ 59
def prefixEnd_5811959 : Nat := 4983230072969 + 3 ^ 40 * 5811959 * 2
def baseEnd_5811959 : Nat := 994776170408177139127931

theorem tailTrace_5811959 : CollatzResearch.WordTrace tailWord_5811959 prefixEnd_5811959 994776170408177139127931 := by
  unfold tailWord_5811959
  simp only [CollatzResearch.WordTrace]
  refine ⟨211979559551272621417102931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141319706367515080944735287 211979559551272621417102931)
  ·
    refine ⟨317969339326908932125654397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211979559551272621417102931 317969339326908932125654397)
    ·
      refine ⟨119238502247590849547120399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317969339326908932125654397 119238502247590849547120399)
      ·
        refine ⟨178857753371386274320680599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119238502247590849547120399 178857753371386274320680599)
        ·
          refine ⟨268286630057079411481020899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178857753371386274320680599 268286630057079411481020899)
          ·
            refine ⟨402429945085619117221531349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268286630057079411481020899 402429945085619117221531349)
            ·
              refine ⟨9431951837944198059879641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 402429945085619117221531349 9431951837944198059879641)
              ·
                refine ⟨7073963878458148544909731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9431951837944198059879641 7073963878458148544909731)
                ·
                  refine ⟨10610945817687222817364597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073963878458148544909731 10610945817687222817364597)
                  ·
                    refine ⟨994776170408177139127931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10610945817687222817364597 994776170408177139127931)
                    ·
                      rfl

theorem cell23_5811959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_5811959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811959 prefixEnd_5811959 := by exact prefixLift 5811959
  have htrace : WordTrace (prefixWord ++ tailWord_5811959) baseStart_5811959 baseEnd_5811959 := by
    simpa [prefixWord, tailWord_5811959, baseEnd_5811959] using wordTrace_append hprefix tailTrace_5811959
  have hstable : (prefixWord ++ tailWord_5811959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811959).length < 2 ^ (prefixWord ++ tailWord_5811959).sum := by decide
  have hdescent : baseEnd_5811959 < baseStart_5811959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811976 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_5811976 : Nat := 118140960795 + 5811976 * 2 ^ 59
def prefixEnd_5811976 : Nat := 4983230072969 + 3 ^ 40 * 5811976 * 2
def baseEnd_5811976 : Nat := 994779080131885950290405

theorem tailTrace_5811976 : CollatzResearch.WordTrace tailWord_5811976 prefixEnd_5811976 994779080131885950290405 := by
  unfold tailWord_5811976
  simp only [CollatzResearch.WordTrace]
  refine ⟨105990089796105516660235891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141320119728140688880314521 105990089796105516660235891)
  ·
    refine ⟨158985134694158274990353837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105990089796105516660235891 158985134694158274990353837)
    ·
      refine ⟨59619425510309353121382689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158985134694158274990353837 59619425510309353121382689)
      ·
        refine ⟨44714569132732014841037017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59619425510309353121382689 44714569132732014841037017)
        ·
          refine ⟨33535926849549011130777763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44714569132732014841037017 33535926849549011130777763)
          ·
            refine ⟨50303890274323516696166645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33535926849549011130777763 50303890274323516696166645)
            ·
              refine ⟨4715989713217829690265623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50303890274323516696166645 4715989713217829690265623)
              ·
                refine ⟨7073984569826744535398435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4715989713217829690265623 7073984569826744535398435)
                ·
                  refine ⟨10610976854740116803097653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073984569826744535398435 10610976854740116803097653)
                  ·
                    refine ⟨994779080131885950290405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10610976854740116803097653 994779080131885950290405)
                    ·
                      rfl

theorem cell23_5811976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_5811976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811976 prefixEnd_5811976 := by exact prefixLift 5811976
  have htrace : WordTrace (prefixWord ++ tailWord_5811976) baseStart_5811976 baseEnd_5811976 := by
    simpa [prefixWord, tailWord_5811976, baseEnd_5811976] using wordTrace_append hprefix tailTrace_5811976
  have hstable : (prefixWord ++ tailWord_5811976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811976).length < 2 ^ (prefixWord ++ tailWord_5811976).sum := by decide
  have hdescent : baseEnd_5811976 < baseStart_5811976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811979 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 4]
def baseStart_5811979 : Nat := 118140960795 + 5811979 * 2 ^ 59
def prefixEnd_5811979 : Nat := 4983230072969 + 3 ^ 40 * 5811979 * 2
def baseEnd_5811979 : Nat := 2984338780837621339133701

theorem tailTrace_5811979 : CollatzResearch.WordTrace tailWord_5811979 prefixEnd_5811979 2984338780837621339133701 := by
  unfold tailWord_5811979
  simp only [CollatzResearch.WordTrace]
  refine ⟨211980289011200164832830991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141320192674133443221887327 211980289011200164832830991)
  ·
    refine ⟨317970433516800247249246487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211980289011200164832830991 317970433516800247249246487)
    ·
      refine ⟨476955650275200370873869731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317970433516800247249246487 476955650275200370873869731)
      ·
        refine ⟨715433475412800556310804597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476955650275200370873869731 715433475412800556310804597)
        ·
          refine ⟨67071888319950052154137931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 715433475412800556310804597 67071888319950052154137931)
          ·
            refine ⟨100607832479925078231206897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67071888319950052154137931 100607832479925078231206897)
            ·
              refine ⟨75455874359943808673405173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100607832479925078231206897 75455874359943808673405173)
              ·
                refine ⟨7073988221244732063131735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75455874359943808673405173 7073988221244732063131735)
                ·
                  refine ⟨10610982331867098094697603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7073988221244732063131735 10610982331867098094697603)
                  ·
                    refine ⟨15916473497800647142046405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10610982331867098094697603 15916473497800647142046405)
                    ·
                      refine ⟨2984338780837621339133701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15916473497800647142046405 2984338780837621339133701)
                      ·
                        rfl

theorem cell23_5811979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 4].length) (baseStart_5811979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811979 prefixEnd_5811979 := by exact prefixLift 5811979
  have htrace : WordTrace (prefixWord ++ tailWord_5811979) baseStart_5811979 baseEnd_5811979 := by
    simpa [prefixWord, tailWord_5811979, baseEnd_5811979] using wordTrace_append hprefix tailTrace_5811979
  have hstable : (prefixWord ++ tailWord_5811979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811979).length < 2 ^ (prefixWord ++ tailWord_5811979).sum := by decide
  have hdescent : baseEnd_5811979 < baseStart_5811979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811992 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5811992 : Nat := 118140960795 + 5811992 * 2 ^ 59
def prefixEnd_5811992 : Nat := 4983230072969 + 3 ^ 40 * 5811992 * 2
def baseEnd_5811992 : Nat := 2984345456086129788271141

theorem tailTrace_5811992 : CollatzResearch.WordTrace tailWord_5811992 prefixEnd_5811992 2984345456086129788271141 := by
  unfold tailWord_5811992
  simp only [CollatzResearch.WordTrace]
  refine ⟨105990381580076534026527115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141320508773435378702036153 105990381580076534026527115)
  ·
    refine ⟨158985572370114801039790673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105990381580076534026527115 158985572370114801039790673)
    ·
      refine ⟨119239179277586100779843005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158985572370114801039790673 119239179277586100779843005)
      ·
        refine ⟨44714692229094787792441127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119239179277586100779843005 44714692229094787792441127)
        ·
          refine ⟨67072038343642181688661691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44714692229094787792441127 67072038343642181688661691)
          ·
            refine ⟨100608057515463272532992537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67072038343642181688661691 100608057515463272532992537)
            ·
              refine ⟨75456043136597454399744403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100608057515463272532992537 75456043136597454399744403)
              ·
                refine ⟨113184064704896181599616605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75456043136597454399744403 113184064704896181599616605)
                ·
                  refine ⟨42444024264336068099856227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113184064704896181599616605 42444024264336068099856227)
                  ·
                    refine ⟨63666036396504102149784341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42444024264336068099856227 63666036396504102149784341)
                    ·
                      refine ⟨2984345456086129788271141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63666036396504102149784341 2984345456086129788271141)
                      ·
                        rfl

theorem cell23_5811992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5811992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811992 prefixEnd_5811992 := by exact prefixLift 5811992
  have htrace : WordTrace (prefixWord ++ tailWord_5811992) baseStart_5811992 baseEnd_5811992 := by
    simpa [prefixWord, tailWord_5811992, baseEnd_5811992] using wordTrace_append hprefix tailTrace_5811992
  have hstable : (prefixWord ++ tailWord_5811992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811992).length < 2 ^ (prefixWord ++ tailWord_5811992).sum := by decide
  have hdescent : baseEnd_5811992 < baseStart_5811992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5811999 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_5811999 : Nat := 118140960795 + 5811999 * 2 ^ 59
def prefixEnd_5811999 : Nat := 4983230072969 + 3 ^ 40 * 5811999 * 2
def baseEnd_5811999 : Nat := 2984349050450711260883609

theorem tailTrace_5811999 : CollatzResearch.WordTrace tailWord_5811999 prefixEnd_5811999 2984349050450711260883609 := by
  unfold tailWord_5811999
  simp only [CollatzResearch.WordTrace]
  refine ⟨211981018471127708248559051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141320678980751805499039367 211981018471127708248559051)
  ·
    refine ⟨317971527706691562372838577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211981018471127708248559051 317971527706691562372838577)
    ·
      refine ⟨238478645780018671779628933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317971527706691562372838577 238478645780018671779628933)
      ·
        refine ⟨44714746083753500958680425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238478645780018671779628933 44714746083753500958680425)
        ·
          refine ⟨33536059562815125719010319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44714746083753500958680425 33536059562815125719010319)
          ·
            refine ⟨50304089344222688578515479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33536059562815125719010319 50304089344222688578515479)
            ·
              refine ⟨75456134016334032867773219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50304089344222688578515479 75456134016334032867773219)
              ·
                refine ⟨113184201024501049301659829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75456134016334032867773219 113184201024501049301659829)
                ·
                  refine ⟨10611018846046973372030609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113184201024501049301659829 10611018846046973372030609)
                  ·
                    refine ⟨7958264134535230029022957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10611018846046973372030609 7958264134535230029022957)
                    ·
                      refine ⟨2984349050450711260883609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7958264134535230029022957 2984349050450711260883609)
                      ·
                        rfl

theorem cell23_5811999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_5811999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5811999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5811999 prefixEnd_5811999 := by exact prefixLift 5811999
  have htrace : WordTrace (prefixWord ++ tailWord_5811999) baseStart_5811999 baseEnd_5811999 := by
    simpa [prefixWord, tailWord_5811999, baseEnd_5811999] using wordTrace_append hprefix tailTrace_5811999
  have hstable : (prefixWord ++ tailWord_5811999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5811999).length < 2 ^ (prefixWord ++ tailWord_5811999).sum := by decide
  have hdescent : baseEnd_5811999 < baseStart_5811999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5811999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812030 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 1, 1, 4]
def baseStart_5812030 : Nat := 118140960795 + 5812030 * 2 ^ 59
def prefixEnd_5812030 : Nat := 4983230072969 + 3 ^ 40 * 5812030 * 2
def baseEnd_5812030 : Nat := 2984364968351000639595967

theorem tailTrace_5812030 : CollatzResearch.WordTrace tailWord_5812030 prefixEnd_5812030 2984364968351000639595967 := by
  unfold tailWord_5812030
  simp only [CollatzResearch.WordTrace]
  refine ⟨26497768641751925067867193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141321432756010267028625029 26497768641751925067867193)
  ·
    refine ⟨19873326481313943800900395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26497768641751925067867193 19873326481313943800900395)
    ·
      refine ⟨29809989721970915701350593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19873326481313943800900395 29809989721970915701350593)
      ·
        refine ⟨22357492291478186776012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29809989721970915701350593 22357492291478186776012945)
        ·
          refine ⟨16768119218608640082009709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22357492291478186776012945 16768119218608640082009709)
          ·
            refine ⟨6288044706978240030753641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16768119218608640082009709 6288044706978240030753641)
            ·
              refine ⟨4716033530233680023065231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288044706978240030753641 4716033530233680023065231)
              ·
                refine ⟨7074050295350520034597847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716033530233680023065231 7074050295350520034597847)
                ·
                  refine ⟨10611075443025780051896771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7074050295350520034597847 10611075443025780051896771)
                  ·
                    refine ⟨15916613164538670077845157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10611075443025780051896771 15916613164538670077845157)
                    ·
                      refine ⟨2984364968351000639595967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15916613164538670077845157 2984364968351000639595967)
                      ·
                        rfl

theorem cell23_5812030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_5812030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812030 prefixEnd_5812030 := by exact prefixLift 5812030
  have htrace : WordTrace (prefixWord ++ tailWord_5812030) baseStart_5812030 baseEnd_5812030 := by
    simpa [prefixWord, tailWord_5812030, baseEnd_5812030] using wordTrace_append hprefix tailTrace_5812030
  have hstable : (prefixWord ++ tailWord_5812030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812030).length < 2 ^ (prefixWord ++ tailWord_5812030).sum := by decide
  have hdescent : baseEnd_5812030 < baseStart_5812030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812060 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5812060 : Nat := 118140960795 + 5812060 * 2 ^ 59
def prefixEnd_5812060 : Nat := 4983230072969 + 3 ^ 40 * 5812060 * 2
def baseEnd_5812060 : Nat := 2984380372770635522220829

theorem tailTrace_5812060 : CollatzResearch.WordTrace tailWord_5812060 prefixEnd_5812060 2984380372770635522220829 := by
  unfold tailWord_5812060
  simp only [CollatzResearch.WordTrace]
  refine ⟨105991621661953357833264817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141322162215937810444353089 105991621661953357833264817)
  ·
    refine ⟨79493716246465018374948613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105991621661953357833264817 79493716246465018374948613)
    ·
      refine ⟨14905071796212190945302865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79493716246465018374948613 14905071796212190945302865)
      ·
        refine ⟨11178803847159143208977149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14905071796212190945302865 11178803847159143208977149)
        ·
          refine ⟨4192051442684678703366431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11178803847159143208977149 4192051442684678703366431)
          ·
            refine ⟨6288077164027018055049647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192051442684678703366431 6288077164027018055049647)
            ·
              refine ⟨9432115746040527082574471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288077164027018055049647 9432115746040527082574471)
              ·
                refine ⟨14148173619060790623861707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9432115746040527082574471 14148173619060790623861707)
                ·
                  refine ⟨21222260428591185935792561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14148173619060790623861707 21222260428591185935792561)
                  ·
                    refine ⟨15916695321443389451844421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21222260428591185935792561 15916695321443389451844421)
                    ·
                      refine ⟨2984380372770635522220829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15916695321443389451844421 2984380372770635522220829)
                      ·
                        rfl

theorem cell23_5812060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5812060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812060 prefixEnd_5812060 := by exact prefixLift 5812060
  have htrace : WordTrace (prefixWord ++ tailWord_5812060) baseStart_5812060 baseEnd_5812060 := by
    simpa [prefixWord, tailWord_5812060, baseEnd_5812060] using wordTrace_append hprefix tailTrace_5812060
  have hstable : (prefixWord ++ tailWord_5812060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812060).length < 2 ^ (prefixWord ++ tailWord_5812060).sum := by decide
  have hdescent : baseEnd_5812060 < baseStart_5812060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812089 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_5812089 : Nat := 118140960795 + 5812089 * 2 ^ 59
def prefixEnd_5812089 : Nat := 4983230072969 + 3 ^ 40 * 5812089 * 2
def baseEnd_5812089 : Nat := 2984395263709615908758195

theorem tailTrace_5812089 : CollatzResearch.WordTrace tailWord_5812089 prefixEnd_5812089 2984395263709615908758195 := by
  unfold tailWord_5812089
  simp only [CollatzResearch.WordTrace]
  refine ⟨211984301040801653619335321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141322867360534435746223547 211984301040801653619335321)
  ·
    refine ⟨158988225780601240214501491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211984301040801653619335321 158988225780601240214501491)
    ·
      refine ⟨238482338670901860321752237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158988225780601240214501491 238482338670901860321752237)
      ·
        refine ⟨89430877001588197620657089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238482338670901860321752237 89430877001588197620657089)
        ·
          refine ⟨67073157751191148215492817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89430877001588197620657089 67073157751191148215492817)
          ·
            refine ⟨50304868313393361161619613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67073157751191148215492817 50304868313393361161619613)
            ·
              refine ⟨18864325617522510435607355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50304868313393361161619613 18864325617522510435607355)
              ·
                refine ⟨28296488426283765653411033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18864325617522510435607355 28296488426283765653411033)
                ·
                  refine ⟨21222366319712824240058275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28296488426283765653411033 21222366319712824240058275)
                  ·
                    refine ⟨31833549479569236360087413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21222366319712824240058275 31833549479569236360087413)
                    ·
                      refine ⟨2984395263709615908758195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31833549479569236360087413 2984395263709615908758195)
                      ·
                        rfl

theorem cell23_5812089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_5812089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812089 prefixEnd_5812089 := by exact prefixLift 5812089
  have htrace : WordTrace (prefixWord ++ tailWord_5812089) baseStart_5812089 baseEnd_5812089 := by
    simpa [prefixWord, tailWord_5812089, baseEnd_5812089] using wordTrace_append hprefix tailTrace_5812089
  have hstable : (prefixWord ++ tailWord_5812089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812089).length < 2 ^ (prefixWord ++ tailWord_5812089).sum := by decide
  have hdescent : baseEnd_5812089 < baseStart_5812089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812146 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2]
def baseStart_5812146 : Nat := 118140960795 + 5812146 * 2 ^ 59
def prefixEnd_5812146 : Nat := 4983230072969 + 3 ^ 40 * 5812146 * 2
def baseEnd_5812146 : Nat := 2984424532106922185745433

theorem tailTrace_5812146 : CollatzResearch.WordTrace tailWord_5812146 prefixEnd_5812146 2984424532106922185745433 := by
  unfold tailWord_5812146
  simp only [CollatzResearch.WordTrace]
  refine ⟨52996595000398788088540073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141324253334396768236106861 52996595000398788088540073)
  ·
    refine ⟨39747446250299091066405055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52996595000398788088540073 39747446250299091066405055)
    ·
      refine ⟨59621169375448636599607583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39747446250299091066405055 59621169375448636599607583)
      ·
        refine ⟨89431754063172954899411375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59621169375448636599607583 89431754063172954899411375)
        ·
          refine ⟨134147631094759432349117063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89431754063172954899411375 134147631094759432349117063)
          ·
            refine ⟨201221446642139148523675595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134147631094759432349117063 201221446642139148523675595)
            ·
              refine ⟨301832169963208722785513393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201221446642139148523675595 301832169963208722785513393)
              ·
                refine ⟨226374127472406542089135045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301832169963208722785513393 226374127472406542089135045)
                ·
                  refine ⟨42445148901076226641712821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 226374127472406542089135045 42445148901076226641712821)
                  ·
                    refine ⟨3979232709475896247660577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42445148901076226641712821 3979232709475896247660577)
                    ·
                      refine ⟨2984424532106922185745433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979232709475896247660577 2984424532106922185745433)
                      ·
                        rfl

theorem cell23_5812146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2].length) (baseStart_5812146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812146 prefixEnd_5812146 := by exact prefixLift 5812146
  have htrace : WordTrace (prefixWord ++ tailWord_5812146) baseStart_5812146 baseEnd_5812146 := by
    simpa [prefixWord, tailWord_5812146, baseEnd_5812146] using wordTrace_append hprefix tailTrace_5812146
  have hstable : (prefixWord ++ tailWord_5812146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812146).length < 2 ^ (prefixWord ++ tailWord_5812146).sum := by decide
  have hdescent : baseEnd_5812146 < baseStart_5812146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812176 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2]
def baseStart_5812176 : Nat := 118140960795 + 5812176 * 2 ^ 59
def prefixEnd_5812176 : Nat := 4983230072969 + 3 ^ 40 * 5812176 * 2
def baseEnd_5812176 : Nat := 2984439936526557068370295

theorem tailTrace_5812176 : CollatzResearch.WordTrace tailWord_5812176 prefixEnd_5812176 2984439936526557068370295 := by
  unfold tailWord_5812176
  simp only [CollatzResearch.WordTrace]
  refine ⟨105993737095743233738876191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141324982794324311651834921 105993737095743233738876191)
  ·
    refine ⟨158990605643614850608314287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105993737095743233738876191 158990605643614850608314287)
    ·
      refine ⟨238485908465422275912471431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158990605643614850608314287 238485908465422275912471431)
      ·
        refine ⟨357728862698133413868707147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238485908465422275912471431 357728862698133413868707147)
        ·
          refine ⟨536593294047200120803060721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357728862698133413868707147 536593294047200120803060721)
          ·
            refine ⟨402444970535400090602295541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536593294047200120803060721 402444970535400090602295541)
            ·
              refine ⟨37729215987693758493965207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402444970535400090602295541 37729215987693758493965207)
              ·
                refine ⟨56593823981540637740947811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37729215987693758493965207 56593823981540637740947811)
                ·
                  refine ⟨84890735972310956611421717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56593823981540637740947811 84890735972310956611421717)
                  ·
                    refine ⟨3979253248702076091160393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84890735972310956611421717 3979253248702076091160393)
                    ·
                      refine ⟨2984439936526557068370295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979253248702076091160393 2984439936526557068370295)
                      ·
                        rfl

theorem cell23_5812176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 6, 2].length) (baseStart_5812176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812176 prefixEnd_5812176 := by exact prefixLift 5812176
  have htrace : WordTrace (prefixWord ++ tailWord_5812176) baseStart_5812176 baseEnd_5812176 := by
    simpa [prefixWord, tailWord_5812176, baseEnd_5812176] using wordTrace_append hprefix tailTrace_5812176
  have hstable : (prefixWord ++ tailWord_5812176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812176).length < 2 ^ (prefixWord ++ tailWord_5812176).sum := by decide
  have hdescent : baseEnd_5812176 < baseStart_5812176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812196 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 4, 3]
def baseStart_5812196 : Nat := 118140960795 + 5812196 * 2 ^ 59
def prefixEnd_5812196 : Nat := 4983230072969 + 3 ^ 40 * 5812196 * 2
def baseEnd_5812196 : Nat := 2984450206139646990120203

theorem tailTrace_5812196 : CollatzResearch.WordTrace tailWord_5812196 prefixEnd_5812196 2984450206139646990120203 := by
  unfold tailWord_5812196
  simp only [CollatzResearch.WordTrace]
  refine ⟨105994101825707005446740221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141325469100942673928986961 105994101825707005446740221)
  ·
    refine ⟨39747788184640127042527583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105994101825707005446740221 39747788184640127042527583)
    ·
      refine ⟨59621682276960190563791375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39747788184640127042527583 59621682276960190563791375)
      ·
        refine ⟨89432523415440285845687063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59621682276960190563791375 89432523415440285845687063)
        ·
          refine ⟨134148785123160428768530595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89432523415440285845687063 134148785123160428768530595)
          ·
            refine ⟨201223177684740643152795893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134148785123160428768530595 201223177684740643152795893)
            ·
              refine ⟨18864672907944435295574615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 201223177684740643152795893 18864672907944435295574615)
              ·
                refine ⟨28297009361916652943361923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18864672907944435295574615 28297009361916652943361923)
                ·
                  refine ⟨42445514042874979415042885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28297009361916652943361923 42445514042874979415042885)
                  ·
                    refine ⟨7958533883039058640320541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42445514042874979415042885 7958533883039058640320541)
                    ·
                      refine ⟨2984450206139646990120203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7958533883039058640320541 2984450206139646990120203)
                      ·
                        rfl

theorem cell23_5812196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_5812196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812196 prefixEnd_5812196 := by exact prefixLift 5812196
  have htrace : WordTrace (prefixWord ++ tailWord_5812196) baseStart_5812196 baseEnd_5812196 := by
    simpa [prefixWord, tailWord_5812196, baseEnd_5812196] using wordTrace_append hprefix tailTrace_5812196
  have hstable : (prefixWord ++ tailWord_5812196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812196).length < 2 ^ (prefixWord ++ tailWord_5812196).sum := by decide
  have hdescent : baseEnd_5812196 < baseStart_5812196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812206 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_5812206 : Nat := 118140960795 + 5812206 * 2 ^ 59
def prefixEnd_5812206 : Nat := 4983230072969 + 3 ^ 40 * 5812206 * 2
def baseEnd_5812206 : Nat := 2984455340946191950995157

theorem tailTrace_5812206 : CollatzResearch.WordTrace tailWord_5812206 prefixEnd_5812206 2984455340946191950995157 := by
  unfold tailWord_5812206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26498571047672222825168059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141325712254251855067562981 26498571047672222825168059)
  ·
    refine ⟨39747856571508334237752089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26498571047672222825168059 39747856571508334237752089)
    ·
      refine ⟨29810892428631250678314067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39747856571508334237752089 29810892428631250678314067)
      ·
        refine ⟨44716338642946876017471101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29810892428631250678314067 44716338642946876017471101)
        ·
          refine ⟨16768626991105078506551663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44716338642946876017471101 16768626991105078506551663)
          ·
            refine ⟨25152940486657617759827495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16768626991105078506551663 25152940486657617759827495)
            ·
              refine ⟨37729410729986426639741243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25152940486657617759827495 37729410729986426639741243)
              ·
                refine ⟨56594116094979639959611865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37729410729986426639741243 56594116094979639959611865)
                ·
                  refine ⟨42445587071234729969708899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56594116094979639959611865 42445587071234729969708899)
                  ·
                    refine ⟨63668380606852094954563349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42445587071234729969708899 63668380606852094954563349)
                    ·
                      refine ⟨2984455340946191950995157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63668380606852094954563349 2984455340946191950995157)
                      ·
                        rfl

theorem cell23_5812206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_5812206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812206 prefixEnd_5812206 := by exact prefixLift 5812206
  have htrace : WordTrace (prefixWord ++ tailWord_5812206) baseStart_5812206 baseEnd_5812206 := by
    simpa [prefixWord, tailWord_5812206, baseEnd_5812206] using wordTrace_append hprefix tailTrace_5812206
  have hstable : (prefixWord ++ tailWord_5812206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812206).length < 2 ^ (prefixWord ++ tailWord_5812206).sum := by decide
  have hdescent : baseEnd_5812206 < baseStart_5812206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812216 : List Nat := [2, 1, 2, 1, 1, 3, 5, 2, 6]
def baseStart_5812216 : Nat := 118140960795 + 5812216 * 2 ^ 59
def prefixEnd_5812216 : Nat := 4983230072969 + 3 ^ 40 * 5812216 * 2
def baseEnd_5812216 : Nat := 331606719528081879096679

theorem tailTrace_5812216 : CollatzResearch.WordTrace tailWord_5812216 prefixEnd_5812216 331606719528081879096679 := by
  unfold tailWord_5812216
  simp only [CollatzResearch.WordTrace]
  refine ⟨105994466555670777154604251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141325955407561036206139001 105994466555670777154604251)
  ·
    refine ⟨158991699833506165731906377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105994466555670777154604251 158991699833506165731906377)
    ·
      refine ⟨119243774875129624298929783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158991699833506165731906377 119243774875129624298929783)
      ·
        refine ⟨178865662312694436448394675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119243774875129624298929783 178865662312694436448394675)
        ·
          refine ⟨268298493469041654672592013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178865662312694436448394675 268298493469041654672592013)
          ·
            refine ⟨100611935050890620502222005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 268298493469041654672592013 100611935050890620502222005)
            ·
              refine ⟨9432368911020995672083313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100611935050890620502222005 9432368911020995672083313)
              ·
                refine ⟨7074276683265746754062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9432368911020995672083313 7074276683265746754062485)
                ·
                  refine ⟨331606719528081879096679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7074276683265746754062485 331606719528081879096679)
                  ·
                    rfl

theorem cell23_5812216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_5812216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812216 prefixEnd_5812216 := by exact prefixLift 5812216
  have htrace : WordTrace (prefixWord ++ tailWord_5812216) baseStart_5812216 baseEnd_5812216 := by
    simpa [prefixWord, tailWord_5812216, baseEnd_5812216] using wordTrace_append hprefix tailTrace_5812216
  have hstable : (prefixWord ++ tailWord_5812216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812216).length < 2 ^ (prefixWord ++ tailWord_5812216).sum := by decide
  have hdescent : baseEnd_5812216 < baseStart_5812216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812219 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_5812219 : Nat := 118140960795 + 5812219 * 2 ^ 59
def prefixEnd_5812219 : Nat := 4983230072969 + 3 ^ 40 * 5812219 * 2
def baseEnd_5812219 : Nat := 2984462016194700400132597

theorem tailTrace_5812219 : CollatzResearch.WordTrace tailWord_5812219 prefixEnd_5812219 2984462016194700400132597 := by
  unfold tailWord_5812219
  simp only [CollatzResearch.WordTrace]
  refine ⟨211989042530330685821567711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141326028353553790547711807 211989042530330685821567711)
  ·
    refine ⟨317983563795496028732351567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211989042530330685821567711 317983563795496028732351567)
    ·
      refine ⟨476975345693244043098527351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317983563795496028732351567 476975345693244043098527351)
      ·
        refine ⟨715463018539866064647791027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476975345693244043098527351 715463018539866064647791027)
        ·
          refine ⟨1073194527809799096971686541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715463018539866064647791027 1073194527809799096971686541)
          ·
            refine ⟨402447947928674661364382453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1073194527809799096971686541 402447947928674661364382453)
            ·
              refine ⟨37729495118313249502910855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402447947928674661364382453 37729495118313249502910855)
              ·
                refine ⟨56594242677469874254366283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37729495118313249502910855 56594242677469874254366283)
                ·
                  refine ⟨84891364016204811381549425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56594242677469874254366283 84891364016204811381549425)
                  ·
                    refine ⟨63668523012153608536162069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84891364016204811381549425 63668523012153608536162069)
                    ·
                      refine ⟨2984462016194700400132597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63668523012153608536162069 2984462016194700400132597)
                      ·
                        rfl

theorem cell23_5812219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_5812219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812219 prefixEnd_5812219 := by exact prefixLift 5812219
  have htrace : WordTrace (prefixWord ++ tailWord_5812219) baseStart_5812219 baseEnd_5812219 := by
    simpa [prefixWord, tailWord_5812219, baseEnd_5812219] using wordTrace_append hprefix tailTrace_5812219
  have hstable : (prefixWord ++ tailWord_5812219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812219).length < 2 ^ (prefixWord ++ tailWord_5812219).sum := by decide
  have hdescent : baseEnd_5812219 < baseStart_5812219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812243 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 3]
def baseStart_5812243 : Nat := 118140960795 + 5812243 * 2 ^ 59
def prefixEnd_5812243 : Nat := 4983230072969 + 3 ^ 40 * 5812243 * 2
def baseEnd_5812243 : Nat := 2984474339730408306232487

theorem tailTrace_5812243 : CollatzResearch.WordTrace tailWord_5812243 prefixEnd_5812243 2984474339730408306232487 := by
  unfold tailWord_5812243
  simp only [CollatzResearch.WordTrace]
  refine ⟨211989917882243737920441383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141326611921495825280294255 211989917882243737920441383)
  ·
    refine ⟨317984876823365606880662075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211989917882243737920441383 317984876823365606880662075)
    ·
      refine ⟨476977315235048410320993113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317984876823365606880662075 476977315235048410320993113)
      ·
        refine ⟨357732986426286307740744835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 476977315235048410320993113 357732986426286307740744835)
        ·
          refine ⟨536599479639429461611117253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357732986426286307740744835 536599479639429461611117253)
          ·
            refine ⟨100612402432393024052084485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 536599479639429461611117253 100612402432393024052084485)
            ·
              refine ⟨18864825456073692009765841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100612402432393024052084485 18864825456073692009765841)
              ·
                refine ⟨14148619092055269007324381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18864825456073692009765841 14148619092055269007324381)
                ·
                  refine ⟨5305732159520725877746643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14148619092055269007324381 5305732159520725877746643)
                  ·
                    refine ⟨7958598239281088816619965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5305732159520725877746643 7958598239281088816619965)
                    ·
                      refine ⟨2984474339730408306232487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7958598239281088816619965 2984474339730408306232487)
                      ·
                        rfl

theorem cell23_5812243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_5812243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812243 prefixEnd_5812243 := by exact prefixLift 5812243
  have htrace : WordTrace (prefixWord ++ tailWord_5812243) baseStart_5812243 baseEnd_5812243 := by
    simpa [prefixWord, tailWord_5812243, baseEnd_5812243] using wordTrace_append hprefix tailTrace_5812243
  have hstable : (prefixWord ++ tailWord_5812243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812243).length < 2 ^ (prefixWord ++ tailWord_5812243).sum := by decide
  have hdescent : baseEnd_5812243 < baseStart_5812243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812270 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_5812270 : Nat := 118140960795 + 5812270 * 2 ^ 59
def prefixEnd_5812270 : Nat := 4983230072969 + 3 ^ 40 * 5812270 * 2
def baseEnd_5812270 : Nat := 2984488203708079700594863

theorem tailTrace_5812270 : CollatzResearch.WordTrace tailWord_5812270 prefixEnd_5812270 2984488203708079700594863 := by
  unfold tailWord_5812270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26498862831643240191459283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141327268435430614354449509 26498862831643240191459283)
  ·
    refine ⟨39748294247464860287188925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26498862831643240191459283 39748294247464860287188925)
    ·
      refine ⟨14905610342799322607695847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39748294247464860287188925 14905610342799322607695847)
      ·
        refine ⟨22358415514198983911543771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14905610342799322607695847 22358415514198983911543771)
        ·
          refine ⟨33537623271298475867315657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22358415514198983911543771 33537623271298475867315657)
          ·
            refine ⟨25153217453473856900486743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33537623271298475867315657 25153217453473856900486743)
            ·
              refine ⟨37729826180210785350730115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25153217453473856900486743 37729826180210785350730115)
              ·
                refine ⟨56594739270316178026095173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37729826180210785350730115 56594739270316178026095173)
                ·
                  refine ⟨10611513613184283379892845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56594739270316178026095173 10611513613184283379892845)
                  ·
                    refine ⟨3979317604944106267459817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10611513613184283379892845 3979317604944106267459817)
                    ·
                      refine ⟨2984488203708079700594863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979317604944106267459817 2984488203708079700594863)
                      ·
                        rfl

theorem cell23_5812270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_5812270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812270 prefixEnd_5812270 := by exact prefixLift 5812270
  have htrace : WordTrace (prefixWord ++ tailWord_5812270) baseStart_5812270 baseEnd_5812270 := by
    simpa [prefixWord, tailWord_5812270, baseEnd_5812270] using wordTrace_append hprefix tailTrace_5812270
  have hstable : (prefixWord ++ tailWord_5812270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812270).length < 2 ^ (prefixWord ++ tailWord_5812270).sum := by decide
  have hdescent : baseEnd_5812270 < baseStart_5812270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812300 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 3, 2, 2]
def baseStart_5812300 : Nat := 118140960795 + 5812300 * 2 ^ 59
def prefixEnd_5812300 : Nat := 4983230072969 + 3 ^ 40 * 5812300 * 2
def baseEnd_5812300 : Nat := 2984503608127714583219725

theorem tailTrace_5812300 : CollatzResearch.WordTrace tailWord_5812300 prefixEnd_5812300 2984503608127714583219725 := by
  unfold tailWord_5812300
  simp only [CollatzResearch.WordTrace]
  refine ⟨105995998421518618327633177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141327997895358157770177569 105995998421518618327633177)
  ·
    refine ⟨79496998816138963745724883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105995998421518618327633177 79496998816138963745724883)
    ·
      refine ⟨119245498224208445618587325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79496998816138963745724883 119245498224208445618587325)
      ·
        refine ⟨44717061834078167106970247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119245498224208445618587325 44717061834078167106970247)
        ·
          refine ⟨67075592751117250660455371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44717061834078167106970247 67075592751117250660455371)
          ·
            refine ⟨100613389126675875990683057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67075592751117250660455371 100613389126675875990683057)
            ·
              refine ⟨75460041845006906993012293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100613389126675875990683057 75460041845006906993012293)
              ·
                refine ⟨14148757845938795061189805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75460041845006906993012293 14148757845938795061189805)
                ·
                  refine ⟨5305784192227048147946177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14148757845938795061189805 5305784192227048147946177)
                  ·
                    refine ⟨3979338144170286110959633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305784192227048147946177 3979338144170286110959633)
                    ·
                      refine ⟨2984503608127714583219725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979338144170286110959633 2984503608127714583219725)
                      ·
                        rfl

theorem cell23_5812300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_5812300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812300 prefixEnd_5812300 := by exact prefixLift 5812300
  have htrace : WordTrace (prefixWord ++ tailWord_5812300) baseStart_5812300 baseEnd_5812300 := by
    simpa [prefixWord, tailWord_5812300, baseEnd_5812300] using wordTrace_append hprefix tailTrace_5812300
  have hstable : (prefixWord ++ tailWord_5812300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812300).length < 2 ^ (prefixWord ++ tailWord_5812300).sum := by decide
  have hdescent : baseEnd_5812300 < baseStart_5812300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812310 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_5812310 : Nat := 118140960795 + 5812310 * 2 ^ 59
def prefixEnd_5812310 : Nat := 4983230072969 + 3 ^ 40 * 5812310 * 2
def baseEnd_5812310 : Nat := 994836247644753181364893

theorem tailTrace_5812310 : CollatzResearch.WordTrace tailWord_5812310 prefixEnd_5812310 994836247644753181364893 := by
  unfold tailWord_5812310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249522598312563022695649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141328241048667338908753589 13249522598312563022695649)
  ·
    refine ⟨9937141948734422267021737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13249522598312563022695649 9937141948734422267021737)
    ·
      refine ⟨7452856461550816700266303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9937141948734422267021737 7452856461550816700266303)
      ·
        refine ⟨11179284692326225050399455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7452856461550816700266303 11179284692326225050399455)
        ·
          refine ⟨16768927038489337575599183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11179284692326225050399455 16768927038489337575599183)
          ·
            refine ⟨25153390557734006363398775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16768927038489337575599183 25153390557734006363398775)
            ·
              refine ⟨37730085836601009545098163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25153390557734006363398775 37730085836601009545098163)
              ·
                refine ⟨56595128754901514317647245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37730085836601009545098163 56595128754901514317647245)
                ·
                  refine ⟨21223173283088067869117717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56595128754901514317647245 21223173283088067869117717)
                  ·
                    refine ⟨994836247644753181364893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21223173283088067869117717 994836247644753181364893)
                    ·
                      rfl

theorem cell23_5812310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_5812310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812310 prefixEnd_5812310 := by exact prefixLift 5812310
  have htrace : WordTrace (prefixWord ++ tailWord_5812310) baseStart_5812310 baseEnd_5812310 := by
    simpa [prefixWord, tailWord_5812310, baseEnd_5812310] using wordTrace_append hprefix tailTrace_5812310
  have hstable : (prefixWord ++ tailWord_5812310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812310).length < 2 ^ (prefixWord ++ tailWord_5812310).sum := by decide
  have hdescent : baseEnd_5812310 < baseStart_5812310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812333 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_5812333 : Nat := 118140960795 + 5812333 * 2 ^ 59
def prefixEnd_5812333 : Nat := 4983230072969 + 3 ^ 40 * 5812333 * 2
def baseEnd_5812333 : Nat := 2984520552989312954107073

theorem tailTrace_5812333 : CollatzResearch.WordTrace tailWord_5812333 prefixEnd_5812333 2984520552989312954107073 := by
  unfold tailWord_5812333
  simp only [CollatzResearch.WordTrace]
  refine ⟨211993200451917683291217653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141328800301278455527478435 211993200451917683291217653)
  ·
    refine ⟨19874362542367282808551655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 211993200451917683291217653 19874362542367282808551655)
    ·
      refine ⟨29811543813550924212827483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19874362542367282808551655 29811543813550924212827483)
      ·
        refine ⟨44717315720326386319241225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29811543813550924212827483 44717315720326386319241225)
        ·
          refine ⟨33537986790244789739430919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44717315720326386319241225 33537986790244789739430919)
          ·
            refine ⟨50306980185367184609146379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33537986790244789739430919 50306980185367184609146379)
            ·
              refine ⟨75460470278050776913719569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50306980185367184609146379 75460470278050776913719569)
              ·
                refine ⟨56595352708538082685289677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75460470278050776913719569 56595352708538082685289677)
                ·
                  refine ⟨21223257265701781006983629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56595352708538082685289677 21223257265701781006983629)
                  ·
                    refine ⟨7958721474638167877618861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21223257265701781006983629 7958721474638167877618861)
                    ·
                      refine ⟨2984520552989312954107073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7958721474638167877618861 2984520552989312954107073)
                      ·
                        rfl

theorem cell23_5812333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_5812333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812333 prefixEnd_5812333 := by exact prefixLift 5812333
  have htrace : WordTrace (prefixWord ++ tailWord_5812333) baseStart_5812333 baseEnd_5812333 := by
    simpa [prefixWord, tailWord_5812333, baseEnd_5812333] using wordTrace_append hprefix tailTrace_5812333
  have hstable : (prefixWord ++ tailWord_5812333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812333).length < 2 ^ (prefixWord ++ tailWord_5812333).sum := by decide
  have hdescent : baseEnd_5812333 < baseStart_5812333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812334 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2]
def baseStart_5812334 : Nat := 118140960795 + 5812334 * 2 ^ 59
def prefixEnd_5812334 : Nat := 4983230072969 + 3 ^ 40 * 5812334 * 2
def baseEnd_5812334 : Nat := 2984521066469967450194569

theorem tailTrace_5812334 : CollatzResearch.WordTrace tailWord_5812334 prefixEnd_5812334 2984521066469967450194569 := by
  unfold tailWord_5812334
  simp only [CollatzResearch.WordTrace]
  refine ⟨26499154615614257557750507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141328824616609373641336037 26499154615614257557750507)
  ·
    refine ⟨39748731923421386336625761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26499154615614257557750507 39748731923421386336625761)
    ·
      refine ⟨29811548942566039752469321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39748731923421386336625761 29811548942566039752469321)
      ·
        refine ⟨22358661706924529814351991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29811548942566039752469321 22358661706924529814351991)
        ·
          refine ⟨33537992560386794721527987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22358661706924529814351991 33537992560386794721527987)
          ·
            refine ⟨50306988840580192082291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33537992560386794721527987 50306988840580192082291981)
            ·
              refine ⟨18865120815217572030859493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50306988840580192082291981 18865120815217572030859493)
              ·
                refine ⟨3537210152853294755786155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18865120815217572030859493 3537210152853294755786155)
                ·
                  refine ⟨5305815229279942133679233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537210152853294755786155 5305815229279942133679233)
                  ·
                    refine ⟨3979361421959956600259425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5305815229279942133679233 3979361421959956600259425)
                    ·
                      refine ⟨2984521066469967450194569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979361421959956600259425 2984521066469967450194569)
                      ·
                        rfl

theorem cell23_5812334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_5812334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812334 prefixEnd_5812334 := by exact prefixLift 5812334
  have htrace : WordTrace (prefixWord ++ tailWord_5812334) baseStart_5812334 baseEnd_5812334 := by
    simpa [prefixWord, tailWord_5812334, baseEnd_5812334] using wordTrace_append hprefix tailTrace_5812334
  have hstable : (prefixWord ++ tailWord_5812334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812334).length < 2 ^ (prefixWord ++ tailWord_5812334).sum := by decide
  have hdescent : baseEnd_5812334 < baseStart_5812334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812336 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_5812336 : Nat := 118140960795 + 5812336 * 2 ^ 59
def prefixEnd_5812336 : Nat := 4983230072969 + 3 ^ 40 * 5812336 * 2
def baseEnd_5812336 : Nat := 994840697810425480789853

theorem tailTrace_5812336 : CollatzResearch.WordTrace tailWord_5812336 prefixEnd_5812336 994840697810425480789853 := by
  unfold tailWord_5812336
  simp only [CollatzResearch.WordTrace]
  refine ⟨105996654935453407401788431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141328873247271209869051241 105996654935453407401788431)
  ·
    refine ⟨158994982403180111102682647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105996654935453407401788431 158994982403180111102682647)
    ·
      refine ⟨238492473604770166654023971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158994982403180111102682647 238492473604770166654023971)
      ·
        refine ⟨357738710407155249981035957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238492473604770166654023971 357738710407155249981035957)
        ·
          refine ⟨33538004100670804685722121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 357738710407155249981035957 33538004100670804685722121)
          ·
            refine ⟨25153503075503103514291591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33538004100670804685722121 25153503075503103514291591)
            ·
              refine ⟨37730254613254655271437387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25153503075503103514291591 37730254613254655271437387)
              ·
                refine ⟨56595381919881982907156081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37730254613254655271437387 56595381919881982907156081)
                ·
                  refine ⟨42446536439911487180367061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56595381919881982907156081 42446536439911487180367061)
                  ·
                    refine ⟨994840697810425480789853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42446536439911487180367061 994840697810425480789853)
                    ·
                      rfl

theorem cell23_5812336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_5812336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812336 prefixEnd_5812336 := by exact prefixLift 5812336
  have htrace : WordTrace (prefixWord ++ tailWord_5812336) baseStart_5812336 baseEnd_5812336 := by
    simpa [prefixWord, tailWord_5812336, baseEnd_5812336] using wordTrace_append hprefix tailTrace_5812336
  have hstable : (prefixWord ++ tailWord_5812336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812336).length < 2 ^ (prefixWord ++ tailWord_5812336).sum := by decide
  have hdescent : baseEnd_5812336 < baseStart_5812336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812374 : List Nat := [5, 3, 2, 1, 1, 1, 10]
def baseStart_5812374 : Nat := 118140960795 + 5812374 * 2 ^ 59
def prefixEnd_5812374 : Nat := 4983230072969 + 3 ^ 40 * 5812374 * 2
def baseEnd_5812374 : Nat := 36846192662915398687585

theorem tailTrace_5812374 : CollatzResearch.WordTrace tailWord_5812374 prefixEnd_5812374 36846192662915398687585 := by
  unfold tailWord_5812374
  simp only [CollatzResearch.WordTrace]
  refine ⟨13249668490298071705841261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 141329797229846098195640117 13249668490298071705841261)
  ·
    refine ⟨4968625683861776889690473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13249668490298071705841261 4968625683861776889690473)
    ·
      refine ⟨3726469262896332667267855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4968625683861776889690473 3726469262896332667267855)
      ·
        refine ⟨5589703894344499000901783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726469262896332667267855 5589703894344499000901783)
        ·
          refine ⟨8384555841516748501352675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589703894344499000901783 8384555841516748501352675)
          ·
            refine ⟨12576833762275122752029013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8384555841516748501352675 12576833762275122752029013)
            ·
              refine ⟨36846192662915398687585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12576833762275122752029013 36846192662915398687585)
              ·
                rfl

theorem cell23_5812374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 10].length) (baseStart_5812374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812374 prefixEnd_5812374 := by exact prefixLift 5812374
  have htrace : WordTrace (prefixWord ++ tailWord_5812374) baseStart_5812374 baseEnd_5812374 := by
    simpa [prefixWord, tailWord_5812374, baseEnd_5812374] using wordTrace_append hprefix tailTrace_5812374
  have hstable : (prefixWord ++ tailWord_5812374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812374).length < 2 ^ (prefixWord ++ tailWord_5812374).sum := by decide
  have hdescent : baseEnd_5812374 < baseStart_5812374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812383 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 2, 6]
def baseStart_5812383 : Nat := 118140960795 + 5812383 * 2 ^ 59
def prefixEnd_5812383 : Nat := 4983230072969 + 3 ^ 40 * 5812383 * 2
def baseEnd_5812383 : Nat := 994848742340679252827281

theorem tailTrace_5812383 : CollatzResearch.WordTrace tailWord_5812383 prefixEnd_5812383 994848742340679252827281 := by
  unfold tailWord_5812383
  simp only [CollatzResearch.WordTrace]
  refine ⟨211995024101736541830537803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141330016067824361220358535 211995024101736541830537803)
  ·
    refine ⟨317992536152604812745806705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211995024101736541830537803 317992536152604812745806705)
    ·
      refine ⟨238494402114453609559355029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 317992536152604812745806705 238494402114453609559355029)
      ·
        refine ⟨11179425099115012948094767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238494402114453609559355029 11179425099115012948094767)
        ·
          refine ⟨16769137648672519422142151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11179425099115012948094767 16769137648672519422142151)
          ·
            refine ⟨25153706473008779133213227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16769137648672519422142151 25153706473008779133213227)
            ·
              refine ⟨37730559709513168699819841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25153706473008779133213227 37730559709513168699819841)
              ·
                refine ⟨28297919782134876524864881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37730559709513168699819841 28297919782134876524864881)
                ·
                  refine ⟨21223439836601157393648661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28297919782134876524864881 21223439836601157393648661)
                  ·
                    refine ⟨994848742340679252827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21223439836601157393648661 994848742340679252827281)
                    ·
                      rfl

theorem cell23_5812383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_5812383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812383 prefixEnd_5812383 := by exact prefixLift 5812383
  have htrace : WordTrace (prefixWord ++ tailWord_5812383) baseStart_5812383 baseEnd_5812383 := by
    simpa [prefixWord, tailWord_5812383, baseEnd_5812383] using wordTrace_append hprefix tailTrace_5812383
  have hstable : (prefixWord ++ tailWord_5812383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812383).length < 2 ^ (prefixWord ++ tailWord_5812383).sum := by decide
  have hdescent : baseEnd_5812383 < baseStart_5812383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812407 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 1, 4, 2]
def baseStart_5812407 : Nat := 118140960795 + 5812407 * 2 ^ 59
def prefixEnd_5812407 : Nat := 4983230072969 + 3 ^ 40 * 5812407 * 2
def baseEnd_5812407 : Nat := 2984558550557745664581733

theorem tailTrace_5812407 : CollatzResearch.WordTrace tailWord_5812407 prefixEnd_5812407 2984558550557745664581733 := by
  unfold tailWord_5812407
  simp only [CollatzResearch.WordTrace]
  refine ⟨211995899453649593929411475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141330599635766395952940983 211995899453649593929411475)
  ·
    refine ⟨317993849180474390894117213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 211995899453649593929411475 317993849180474390894117213)
    ·
      refine ⟨119247693442677896585293955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 317993849180474390894117213 119247693442677896585293955)
      ·
        refine ⟨178871540164016844877940933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119247693442677896585293955 178871540164016844877940933)
        ·
          refine ⟨33538413780753158414613925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178871540164016844877940933 33538413780753158414613925)
          ·
            refine ⟨6288452583891217202740111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33538413780753158414613925 6288452583891217202740111)
            ·
              refine ⟨9432678875836825804110167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288452583891217202740111 9432678875836825804110167)
              ·
                refine ⟨14149018313755238706165251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9432678875836825804110167 14149018313755238706165251)
                ·
                  refine ⟨21223527470632858059247877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14149018313755238706165251 21223527470632858059247877)
                  ·
                    refine ⟨3979411400743660886108977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21223527470632858059247877 3979411400743660886108977)
                    ·
                      refine ⟨2984558550557745664581733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979411400743660886108977 2984558550557745664581733)
                      ·
                        rfl

theorem cell23_5812407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 4, 2].length) (baseStart_5812407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812407 prefixEnd_5812407 := by exact prefixLift 5812407
  have htrace : WordTrace (prefixWord ++ tailWord_5812407) baseStart_5812407 baseEnd_5812407 := by
    simpa [prefixWord, tailWord_5812407, baseEnd_5812407] using wordTrace_append hprefix tailTrace_5812407
  have hstable : (prefixWord ++ tailWord_5812407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812407).length < 2 ^ (prefixWord ++ tailWord_5812407).sum := by decide
  have hdescent : baseEnd_5812407 < baseStart_5812407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812453 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_5812453 : Nat := 118140960795 + 5812453 * 2 ^ 59
def prefixEnd_5812453 : Nat := 4983230072969 + 3 ^ 40 * 5812453 * 2
def baseEnd_5812453 : Nat := 2984582170667852484606521

theorem tailTrace_5812453 : CollatzResearch.WordTrace tailWord_5812453 prefixEnd_5812453 2984582170667852484606521 := by
  unfold tailWord_5812453
  simp only [CollatzResearch.WordTrace]
  refine ⟨211997577211482943785586013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141331718140988629190390675 211997577211482943785586013)
  ·
    refine ⟨79499091454306103919594755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 211997577211482943785586013 79499091454306103919594755)
    ·
      refine ⟨119248637181459155879392133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79499091454306103919594755 119248637181459155879392133)
      ·
        refine ⟨22359119471523591727386025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119248637181459155879392133 22359119471523591727386025)
        ·
          refine ⟨16769339603642693795539519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22359119471523591727386025 16769339603642693795539519)
          ·
            refine ⟨25154009405464040693309279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16769339603642693795539519 25154009405464040693309279)
            ·
              refine ⟨37731014108196061039963919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25154009405464040693309279 37731014108196061039963919)
              ·
                refine ⟨56596521162294091559945879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37731014108196061039963919 56596521162294091559945879)
                ·
                  refine ⟨84894781743441137339918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56596521162294091559945879 84894781743441137339918819)
                  ·
                    refine ⟨127342172615161706009878229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84894781743441137339918819 127342172615161706009878229)
                    ·
                      refine ⟨2984582170667852484606521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 127342172615161706009878229 2984582170667852484606521)
                      ·
                        rfl

theorem cell23_5812453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_5812453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812453 prefixEnd_5812453 := by exact prefixLift 5812453
  have htrace : WordTrace (prefixWord ++ tailWord_5812453) baseStart_5812453 baseEnd_5812453 := by
    simpa [prefixWord, tailWord_5812453, baseEnd_5812453] using wordTrace_append hprefix tailTrace_5812453
  have hstable : (prefixWord ++ tailWord_5812453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812453).length < 2 ^ (prefixWord ++ tailWord_5812453).sum := by decide
  have hdescent : baseEnd_5812453 < baseStart_5812453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812564 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_5812564 : Nat := 118140960795 + 5812564 * 2 ^ 59
def prefixEnd_5812564 : Nat := 4983230072969 + 3 ^ 40 * 5812564 * 2
def baseEnd_5812564 : Nat := 2984639167020501550318511

theorem tailTrace_5812564 : CollatzResearch.WordTrace tailWord_5812564 prefixEnd_5812564 2984639167020501550318511 := by
  unfold tailWord_5812564
  simp only [CollatzResearch.WordTrace]
  refine ⟨106000812857040404871438373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141334417142720539828584497 106000812857040404871438373)
  ·
    refine ⟨19875152410695075913394695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106000812857040404871438373 19875152410695075913394695)
    ·
      refine ⟨29812728616042613870092043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19875152410695075913394695 29812728616042613870092043)
      ·
        refine ⟨44719092924063920805138065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29812728616042613870092043 44719092924063920805138065)
        ·
          refine ⟨33539319693047940603853549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44719092924063920805138065 33539319693047940603853549)
          ·
            refine ⟨12577244884892977726445081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33539319693047940603853549 12577244884892977726445081)
            ·
              refine ⟨9432933663669733294833811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12577244884892977726445081 9432933663669733294833811)
              ·
                refine ⟨14149400495504599942250717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9432933663669733294833811 14149400495504599942250717)
                ·
                  refine ⟨5306025185814224978344019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14149400495504599942250717 5306025185814224978344019)
                  ·
                    refine ⟨7959037778721337467516029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306025185814224978344019 7959037778721337467516029)
                    ·
                      refine ⟨2984639167020501550318511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7959037778721337467516029 2984639167020501550318511)
                      ·
                        rfl

theorem cell23_5812564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_5812564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812564 prefixEnd_5812564 := by exact prefixLift 5812564
  have htrace : WordTrace (prefixWord ++ tailWord_5812564) baseStart_5812564 baseEnd_5812564 := by
    simpa [prefixWord, tailWord_5812564, baseEnd_5812564] using wordTrace_append hprefix tailTrace_5812564
  have hstable : (prefixWord ++ tailWord_5812564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812564).length < 2 ^ (prefixWord ++ tailWord_5812564).sum := by decide
  have hdescent : baseEnd_5812564 < baseStart_5812564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812597 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_5812597 : Nat := 118140960795 + 5812597 * 2 ^ 59
def prefixEnd_5812597 : Nat := 4983230072969 + 3 ^ 40 * 5812597 * 2
def baseEnd_5812597 : Nat := 994885370627366640401953

theorem tailTrace_5812597 : CollatzResearch.WordTrace tailWord_5812597 prefixEnd_5812597 994885370627366640401953 := by
  unfold tailWord_5812597
  simp only [CollatzResearch.WordTrace]
  refine ⟨212002829322961256378828045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141335219548640837585885363 212002829322961256378828045)
  ·
    refine ⟨79501060996110471142060517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 212002829322961256378828045 79501060996110471142060517)
    ·
      refine ⟨14906448936770713339136347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79501060996110471142060517 14906448936770713339136347)
      ·
        refine ⟨22359673405156070008704521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14906448936770713339136347 22359673405156070008704521)
        ·
          refine ⟨16769755053867052506528391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22359673405156070008704521 16769755053867052506528391)
          ·
            refine ⟨25154632580800578759792587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16769755053867052506528391 25154632580800578759792587)
            ·
              refine ⟨37731948871200868139688881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25154632580800578759792587 37731948871200868139688881)
              ·
                refine ⟨28298961653400651104766661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37731948871200868139688881 28298961653400651104766661)
                ·
                  refine ⟨5306055310012622082143749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28298961653400651104766661 5306055310012622082143749)
                  ·
                    refine ⟨994885370627366640401953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306055310012622082143749 994885370627366640401953)
                    ·
                      rfl

theorem cell23_5812597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_5812597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812597 prefixEnd_5812597 := by exact prefixLift 5812597
  have htrace : WordTrace (prefixWord ++ tailWord_5812597) baseStart_5812597 baseEnd_5812597 := by
    simpa [prefixWord, tailWord_5812597, baseEnd_5812597] using wordTrace_append hprefix tailTrace_5812597
  have hstable : (prefixWord ++ tailWord_5812597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812597).length < 2 ^ (prefixWord ++ tailWord_5812597).sum := by decide
  have hdescent : baseEnd_5812597 < baseStart_5812597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812767 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_5812767 : Nat := 118140960795 + 5812767 * 2 ^ 59
def prefixEnd_5812767 : Nat := 4983230072969 + 3 ^ 40 * 5812767 * 2
def baseEnd_5812767 : Nat := 2984743403593364256080077

theorem tailTrace_5812767 : CollatzResearch.WordTrace tailWord_5812767 prefixEnd_5812767 2984743403593364256080077 := by
  unfold tailWord_5812767
  simp only [CollatzResearch.WordTrace]
  refine ⟨212009029732345375412516555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141339353154896916941677703 212009029732345375412516555)
  ·
    refine ⟨318013544598518063118774833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212009029732345375412516555 318013544598518063118774833)
    ·
      refine ⟨238510158448888547339081125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318013544598518063118774833 238510158448888547339081125)
      ·
        refine ⟨44720654709166602626077711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 238510158448888547339081125 44720654709166602626077711)
        ·
          refine ⟨67080982063749903939116567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44720654709166602626077711 67080982063749903939116567)
          ·
            refine ⟨100621473095624855908674851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67080982063749903939116567 100621473095624855908674851)
            ·
              refine ⟨150932209643437283863012277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100621473095624855908674851 150932209643437283863012277)
              ·
                refine ⟨14149894654072245362157401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150932209643437283863012277 14149894654072245362157401)
                ·
                  refine ⟨10612420990554184021618051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14149894654072245362157401 10612420990554184021618051)
                  ·
                    refine ⟨15918631485831276032427077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10612420990554184021618051 15918631485831276032427077)
                    ·
                      refine ⟨2984743403593364256080077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15918631485831276032427077 2984743403593364256080077)
                      ·
                        rfl

theorem cell23_5812767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_5812767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812767 prefixEnd_5812767 := by exact prefixLift 5812767
  have htrace : WordTrace (prefixWord ++ tailWord_5812767) baseStart_5812767 baseEnd_5812767 := by
    simpa [prefixWord, tailWord_5812767, baseEnd_5812767] using wordTrace_append hprefix tailTrace_5812767
  have hstable : (prefixWord ++ tailWord_5812767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812767).length < 2 ^ (prefixWord ++ tailWord_5812767).sum := by decide
  have hdescent : baseEnd_5812767 < baseStart_5812767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812768 : List Nat := [2, 1, 1, 6, 3, 1, 1, 3, 5]
def baseStart_5812768 : Nat := 118140960795 + 5812768 * 2 ^ 59
def prefixEnd_5812768 : Nat := 4983230072969 + 3 ^ 40 * 5812768 * 2
def baseEnd_5812768 : Nat := 331638213008224305796397

theorem tailTrace_5812768 : CollatzResearch.WordTrace tailWord_5812768 prefixEnd_5812768 331638213008224305796397 := by
  unfold tailWord_5812768
  simp only [CollatzResearch.WordTrace]
  refine ⟨106004533102670876291651479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141339377470227835055535305 106004533102670876291651479)
  ·
    refine ⟨159006799654006314437477219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106004533102670876291651479 159006799654006314437477219)
    ·
      refine ⟨238510199481009471656215829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159006799654006314437477219 238510199481009471656215829)
      ·
        refine ⟨11180165600672318983885117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238510199481009471656215829 11180165600672318983885117)
        ·
          refine ⟨4192562100252119618956919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11180165600672318983885117 4192562100252119618956919)
          ·
            refine ⟨6288843150378179428435379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192562100252119618956919 6288843150378179428435379)
            ·
              refine ⟨9433264725567269142653069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6288843150378179428435379 9433264725567269142653069)
              ·
                refine ⟨3537474272087725928494901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9433264725567269142653069 3537474272087725928494901)
                ·
                  refine ⟨331638213008224305796397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3537474272087725928494901 331638213008224305796397)
                  ·
                    rfl

theorem cell23_5812768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 3, 5].length) (baseStart_5812768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812768 prefixEnd_5812768 := by exact prefixLift 5812768
  have htrace : WordTrace (prefixWord ++ tailWord_5812768) baseStart_5812768 baseEnd_5812768 := by
    simpa [prefixWord, tailWord_5812768, baseEnd_5812768] using wordTrace_append hprefix tailTrace_5812768
  have hstable : (prefixWord ++ tailWord_5812768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812768).length < 2 ^ (prefixWord ++ tailWord_5812768).sum := by decide
  have hdescent : baseEnd_5812768 < baseStart_5812768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812780 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_5812780 : Nat := 118140960795 + 5812780 * 2 ^ 59
def prefixEnd_5812780 : Nat := 4983230072969 + 3 ^ 40 * 5812780 * 2
def baseEnd_5812780 : Nat := 2984750078841872705217517

theorem tailTrace_5812780 : CollatzResearch.WordTrace tailWord_5812780 prefixEnd_5812780 2984750078841872705217517 := by
  unfold tailWord_5812780
  simp only [CollatzResearch.WordTrace]
  refine ⟨106004751940649139316369897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141339669254198852421826529 106004751940649139316369897)
  ·
    refine ⟨79503563955486854487277423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106004751940649139316369897 79503563955486854487277423)
    ·
      refine ⟨119255345933230281730916135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79503563955486854487277423 119255345933230281730916135)
      ·
        refine ⟨178883018899845422596374203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119255345933230281730916135 178883018899845422596374203)
        ·
          refine ⟨268324528349768133894561305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178883018899845422596374203 268324528349768133894561305)
          ·
            refine ⟨201243396262326100420920979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268324528349768133894561305 201243396262326100420920979)
            ·
              refine ⟨301865094393489150631381469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201243396262326100420920979 301865094393489150631381469)
              ·
                refine ⟨113199410397558431486768051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301865094393489150631381469 113199410397558431486768051)
                ·
                  refine ⟨169799115596337647230152077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113199410397558431486768051 169799115596337647230152077)
                  ·
                    refine ⟨63674668348626617711307029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 169799115596337647230152077 63674668348626617711307029)
                    ·
                      refine ⟨2984750078841872705217517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63674668348626617711307029 2984750078841872705217517)
                      ·
                        rfl

theorem cell23_5812780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_5812780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812780 prefixEnd_5812780 := by exact prefixLift 5812780
  have htrace : WordTrace (prefixWord ++ tailWord_5812780) baseStart_5812780 baseEnd_5812780 := by
    simpa [prefixWord, tailWord_5812780, baseEnd_5812780] using wordTrace_append hprefix tailTrace_5812780
  have hstable : (prefixWord ++ tailWord_5812780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812780).length < 2 ^ (prefixWord ++ tailWord_5812780).sum := by decide
  have hdescent : baseEnd_5812780 < baseStart_5812780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812794 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_5812794 : Nat := 118140960795 + 5812794 * 2 ^ 59
def prefixEnd_5812794 : Nat := 4983230072969 + 3 ^ 40 * 5812794 * 2
def baseEnd_5812794 : Nat := 994919089190345216814151

theorem tailTrace_5812794 : CollatzResearch.WordTrace tailWord_5812794 prefixEnd_5812794 994919089190345216814151 := by
  unfold tailWord_5812794
  simp only [CollatzResearch.WordTrace]
  refine ⟨53002503625811889755937359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141340009668831706015832957 53002503625811889755937359)
  ·
    refine ⟨79503755438717834633906039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53002503625811889755937359 79503755438717834633906039)
    ·
      refine ⟨119255633158076751950859059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79503755438717834633906039 119255633158076751950859059)
      ·
        refine ⟨178883449737115127926288589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119255633158076751950859059 178883449737115127926288589)
        ·
          refine ⟨67081293651418172972358221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178883449737115127926288589 67081293651418172972358221)
          ·
            refine ⟨25155485119281814864634333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67081293651418172972358221 25155485119281814864634333)
            ·
              refine ⟨9433306919730680574237875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25155485119281814864634333 9433306919730680574237875)
              ·
                refine ⟨14149960379596020861356813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433306919730680574237875 14149960379596020861356813)
                ·
                  refine ⟨5306235142348507823008805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14149960379596020861356813 5306235142348507823008805)
                  ·
                    refine ⟨994919089190345216814151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306235142348507823008805 994919089190345216814151)
                    ·
                      rfl

theorem cell23_5812794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_5812794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812794 prefixEnd_5812794 := by exact prefixLift 5812794
  have htrace : WordTrace (prefixWord ++ tailWord_5812794) baseStart_5812794 baseEnd_5812794 := by
    simpa [prefixWord, tailWord_5812794, baseEnd_5812794] using wordTrace_append hprefix tailTrace_5812794
  have hstable : (prefixWord ++ tailWord_5812794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812794).length < 2 ^ (prefixWord ++ tailWord_5812794).sum := by decide
  have hdescent : baseEnd_5812794 < baseStart_5812794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812845 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_5812845 : Nat := 118140960795 + 5812845 * 2 ^ 59
def prefixEnd_5812845 : Nat := 4983230072969 + 3 ^ 40 * 5812845 * 2
def baseEnd_5812845 : Nat := 994927818361471650301573

theorem tailTrace_5812845 : CollatzResearch.WordTrace tailWord_5812845 prefixEnd_5812845 994927818361471650301573 := by
  unfold tailWord_5812845
  simp only [CollatzResearch.WordTrace]
  refine ⟨212011874626062794733855989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141341249750708529822570659 212011874626062794733855989)
  ·
    refine ⟨19876113246193387006298999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 212011874626062794733855989 19876113246193387006298999)
    ·
      refine ⟨29814169869290080509448499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19876113246193387006298999 29814169869290080509448499)
      ·
        refine ⟨44721254803935120764172749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29814169869290080509448499 44721254803935120764172749)
        ·
          refine ⟨16770470551475670286564781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44721254803935120764172749 16770470551475670286564781)
          ·
            refine ⟨6288926456803376357461793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16770470551475670286564781 6288926456803376357461793)
            ·
              refine ⟨4716694842602532268096345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288926456803376357461793 4716694842602532268096345)
              ·
                refine ⟨3537521131951899201072259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4716694842602532268096345 3537521131951899201072259)
                ·
                  refine ⟨5306281697927848801608389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537521131951899201072259 5306281697927848801608389)
                  ·
                    refine ⟨994927818361471650301573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306281697927848801608389 994927818361471650301573)
                    ·
                      rfl

theorem cell23_5812845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_5812845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812845 prefixEnd_5812845 := by exact prefixLift 5812845
  have htrace : WordTrace (prefixWord ++ tailWord_5812845) baseStart_5812845 baseEnd_5812845 := by
    simpa [prefixWord, tailWord_5812845, baseEnd_5812845] using wordTrace_append hprefix tailTrace_5812845
  have hstable : (prefixWord ++ tailWord_5812845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812845).length < 2 ^ (prefixWord ++ tailWord_5812845).sum := by decide
  have hdescent : baseEnd_5812845 < baseStart_5812845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812867 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 1, 6]
def baseStart_5812867 : Nat := 118140960795 + 5812867 * 2 ^ 59
def prefixEnd_5812867 : Nat := 4983230072969 + 3 ^ 40 * 5812867 * 2
def baseEnd_5812867 : Nat := 994931583886271288276539

theorem tailTrace_5812867 : CollatzResearch.WordTrace tailWord_5812867 prefixEnd_5812867 994931583886271288276539 := by
  unfold tailWord_5812867
  simp only [CollatzResearch.WordTrace]
  refine ⟨212012677031983092491156855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141341784687988728327437903 212012677031983092491156855)
  ·
    refine ⟨318019015547974638736735283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212012677031983092491156855 318019015547974638736735283)
    ·
      refine ⟨477028523321961958105102925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318019015547974638736735283 477028523321961958105102925)
      ·
        refine ⟨178885696245735734289413597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 477028523321961958105102925 178885696245735734289413597)
        ·
          refine ⟨67082136092150900358530099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178885696245735734289413597 67082136092150900358530099)
          ·
            refine ⟨100623204138226350537795149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67082136092150900358530099 100623204138226350537795149)
            ·
              refine ⟨37733701551834881451673181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100623204138226350537795149 37733701551834881451673181)
              ·
                refine ⟨14150138081938080544377443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37733701551834881451673181 14150138081938080544377443)
                ·
                  refine ⟨21225207122907120816566165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14150138081938080544377443 21225207122907120816566165)
                  ·
                    refine ⟨994931583886271288276539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21225207122907120816566165 994931583886271288276539)
                    ·
                      rfl

theorem cell23_5812867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_5812867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812867 prefixEnd_5812867 := by exact prefixLift 5812867
  have htrace : WordTrace (prefixWord ++ tailWord_5812867) baseStart_5812867 baseEnd_5812867 := by
    simpa [prefixWord, tailWord_5812867, baseEnd_5812867] using wordTrace_append hprefix tailTrace_5812867
  have hstable : (prefixWord ++ tailWord_5812867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812867).length < 2 ^ (prefixWord ++ tailWord_5812867).sum := by decide
  have hdescent : baseEnd_5812867 < baseStart_5812867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812942 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2]
def baseStart_5812942 : Nat := 118140960795 + 5812942 * 2 ^ 59
def prefixEnd_5812942 : Nat := 4983230072969 + 3 ^ 40 * 5812942 * 2
def baseEnd_5812942 : Nat := 2984833262707901071391773

theorem tailTrace_5812942 : CollatzResearch.WordTrace tailWord_5812942 prefixEnd_5812942 2984833262707901071391773 := by
  unfold tailWord_5812942
  simp only [CollatzResearch.WordTrace]
  refine ⟨26501926563338922537517135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141343608337807586866758053 26501926563338922537517135)
  ·
    refine ⟨39752889845008383806275703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26501926563338922537517135 39752889845008383806275703)
    ·
      refine ⟨59629334767512575709413555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39752889845008383806275703 59629334767512575709413555)
      ·
        refine ⟨89444002151268863564120333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59629334767512575709413555 89444002151268863564120333)
        ·
          refine ⟨33541500806725823836545125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89444002151268863564120333 33541500806725823836545125)
          ·
            refine ⟨6289031401261091969352211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33541500806725823836545125 6289031401261091969352211)
            ·
              refine ⟨9433547101891637954028317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289031401261091969352211 9433547101891637954028317)
              ·
                refine ⟨3537580163209364232760619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9433547101891637954028317 3537580163209364232760619)
                ·
                  refine ⟨5306370244814046349140929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3537580163209364232760619 5306370244814046349140929)
                  ·
                    refine ⟨3979777683610534761855697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5306370244814046349140929 3979777683610534761855697)
                    ·
                      refine ⟨2984833262707901071391773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979777683610534761855697 2984833262707901071391773)
                      ·
                        rfl

theorem cell23_5812942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_5812942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812942 prefixEnd_5812942 := by exact prefixLift 5812942
  have htrace : WordTrace (prefixWord ++ tailWord_5812942) baseStart_5812942 baseEnd_5812942 := by
    simpa [prefixWord, tailWord_5812942, baseEnd_5812942] using wordTrace_append hprefix tailTrace_5812942
  have hstable : (prefixWord ++ tailWord_5812942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812942).length < 2 ^ (prefixWord ++ tailWord_5812942).sum := by decide
  have hdescent : baseEnd_5812942 < baseStart_5812942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5812975 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 2, 1, 3]
def baseStart_5812975 : Nat := 118140960795 + 5812975 * 2 ^ 59
def prefixEnd_5812975 : Nat := 4983230072969 + 3 ^ 40 * 5812975 * 2
def baseEnd_5812975 : Nat := 2984850207569499442279121

theorem tailTrace_5812975 : CollatzResearch.WordTrace tailWord_5812975 prefixEnd_5812975 2984850207569499442279121 := by
  unfold tailWord_5812975
  simp only [CollatzResearch.WordTrace]
  refine ⟨212016616115591826936088379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141344410743727884624058919 212016616115591826936088379)
  ·
    refine ⟨318024924173387740404132569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212016616115591826936088379 318024924173387740404132569)
    ·
      refine ⟨238518693130040805303099427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 318024924173387740404132569 238518693130040805303099427)
      ·
        refine ⟨357778039695061207954649141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238518693130040805303099427 357778039695061207954649141)
        ·
          refine ⟨33541691221411988245748357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 357778039695061207954649141 33541691221411988245748357)
          ·
            refine ⟨6289067104014747796077817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33541691221411988245748357 6289067104014747796077817)
            ·
              refine ⟨4716800328011060847058363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6289067104014747796077817 4716800328011060847058363)
              ·
                refine ⟨7075200492016591270587545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4716800328011060847058363 7075200492016591270587545)
                ·
                  refine ⟨5306400369012443452940659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7075200492016591270587545 5306400369012443452940659)
                  ·
                    refine ⟨7959600553518665179410989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5306400369012443452940659 7959600553518665179410989)
                    ·
                      refine ⟨2984850207569499442279121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7959600553518665179410989 2984850207569499442279121)
                      ·
                        rfl

theorem cell23_5812975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 2, 1, 3].length) (baseStart_5812975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5812975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5812975 prefixEnd_5812975 := by exact prefixLift 5812975
  have htrace : WordTrace (prefixWord ++ tailWord_5812975) baseStart_5812975 baseEnd_5812975 := by
    simpa [prefixWord, tailWord_5812975, baseEnd_5812975] using wordTrace_append hprefix tailTrace_5812975
  have hstable : (prefixWord ++ tailWord_5812975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5812975).length < 2 ^ (prefixWord ++ tailWord_5812975).sum := by decide
  have hdescent : baseEnd_5812975 < baseStart_5812975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5812975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813041 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_5813041 : Nat := 118140960795 + 5813041 * 2 ^ 59
def prefixEnd_5813041 : Nat := 4983230072969 + 3 ^ 40 * 5813041 * 2
def baseEnd_5813041 : Nat := 2984884097292696184053817

theorem tailTrace_5813041 : CollatzResearch.WordTrace tailWord_5813041 prefixEnd_5813041 2984884097292696184053817 := by
  unfold tailWord_5813041
  simp only [CollatzResearch.WordTrace]
  refine ⟨212019023333352720207990977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141346015555568480138660651 212019023333352720207990977)
  ·
    refine ⟨159014267500014540155993233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212019023333352720207990977 159014267500014540155993233)
    ·
      refine ⟨119260700625010905116994925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159014267500014540155993233 119260700625010905116994925)
      ·
        refine ⟨44722762734379089418873097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119260700625010905116994925 44722762734379089418873097)
        ·
          refine ⟨33542072050784317064154823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44722762734379089418873097 33542072050784317064154823)
          ·
            refine ⟨50313108076176475596232235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33542072050784317064154823 50313108076176475596232235)
            ·
              refine ⟨75469662114264713394348353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50313108076176475596232235 75469662114264713394348353)
              ·
                refine ⟨56602246585698535045761265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75469662114264713394348353 56602246585698535045761265)
                ·
                  refine ⟨42451684939273901284320949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56602246585698535045761265 42451684939273901284320949)
                  ·
                    refine ⟨3979845463056928245405089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42451684939273901284320949 3979845463056928245405089)
                    ·
                      refine ⟨2984884097292696184053817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3979845463056928245405089 2984884097292696184053817)
                      ·
                        rfl

theorem cell23_5813041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_5813041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813041 prefixEnd_5813041 := by exact prefixLift 5813041
  have htrace : WordTrace (prefixWord ++ tailWord_5813041) baseStart_5813041 baseEnd_5813041 := by
    simpa [prefixWord, tailWord_5813041, baseEnd_5813041] using wordTrace_append hprefix tailTrace_5813041
  have hstable : (prefixWord ++ tailWord_5813041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813041).length < 2 ^ (prefixWord ++ tailWord_5813041).sum := by decide
  have hdescent : baseEnd_5813041 < baseStart_5813041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813081 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_5813081 : Nat := 118140960795 + 5813081 * 2 ^ 59
def prefixEnd_5813081 : Nat := 4983230072969 + 3 ^ 40 * 5813081 * 2
def baseEnd_5813081 : Nat := 994968212172958675851211

theorem tailTrace_5813081 : CollatzResearch.WordTrace tailWord_5813081 prefixEnd_5813081 994968212172958675851211 := by
  unfold tailWord_5813081
  simp only [CollatzResearch.WordTrace]
  refine ⟨212020482253207807039447097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141346988168805204692964731 212020482253207807039447097)
  ·
    refine ⟨159015361689905855279585323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212020482253207807039447097 159015361689905855279585323)
    ·
      refine ⟨238523042534858782919377985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159015361689905855279585323 238523042534858782919377985)
      ·
        refine ⟨178892281901144087189533489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238523042534858782919377985 178892281901144087189533489)
        ·
          refine ⟨134169211425858065392150117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178892281901144087189533489 134169211425858065392150117)
          ·
            refine ⟨25156727142348387261028147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134169211425858065392150117 25156727142348387261028147)
            ·
              refine ⟨37735090713522580891542221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25156727142348387261028147 37735090713522580891542221)
              ·
                refine ⟨14150659017570967834328333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37735090713522580891542221 14150659017570967834328333)
                ·
                  refine ⟨5306497131589112937873125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14150659017570967834328333 5306497131589112937873125)
                  ·
                    refine ⟨994968212172958675851211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306497131589112937873125 994968212172958675851211)
                    ·
                      rfl

theorem cell23_5813081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_5813081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813081 prefixEnd_5813081 := by exact prefixLift 5813081
  have htrace : WordTrace (prefixWord ++ tailWord_5813081) baseStart_5813081 baseEnd_5813081 := by
    simpa [prefixWord, tailWord_5813081, baseEnd_5813081] using wordTrace_append hprefix tailTrace_5813081
  have hstable : (prefixWord ++ tailWord_5813081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813081).length < 2 ^ (prefixWord ++ tailWord_5813081).sum := by decide
  have hdescent : baseEnd_5813081 < baseStart_5813081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813091 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5813091 : Nat := 118140960795 + 5813091 * 2 ^ 59
def prefixEnd_5813091 : Nat := 4983230072969 + 3 ^ 40 * 5813091 * 2
def baseEnd_5813091 : Nat := 2984909771325420988428587

theorem tailTrace_5813091 : CollatzResearch.WordTrace tailWord_5813091 prefixEnd_5813091 2984909771325420988428587 := by
  unfold tailWord_5813091
  simp only [CollatzResearch.WordTrace]
  refine ⟨212020846983171578747311127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141347231322114385831540751 212020846983171578747311127)
  ·
    refine ⟨318031270474757368120966691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212020846983171578747311127 318031270474757368120966691)
    ·
      refine ⟨477046905712136052181450037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318031270474757368120966691 477046905712136052181450037)
      ·
        refine ⟨44723147410512754892010941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 477046905712136052181450037 44723147410512754892010941)
        ·
          refine ⟨16771180278942283084504103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44723147410512754892010941 16771180278942283084504103)
          ·
            refine ⟨25156770418413424626756155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771180278942283084504103 25156770418413424626756155)
            ·
              refine ⟨37735155627620136940134233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25156770418413424626756155 37735155627620136940134233)
              ·
                refine ⟨28301366720715102705100675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37735155627620136940134233 28301366720715102705100675)
                ·
                  refine ⟨42452050081072654057651013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28301366720715102705100675 42452050081072654057651013)
                  ·
                    refine ⟨7959759390201122635809565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42452050081072654057651013 7959759390201122635809565)
                    ·
                      refine ⟨2984909771325420988428587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7959759390201122635809565 2984909771325420988428587)
                      ·
                        rfl

theorem cell23_5813091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5813091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813091 prefixEnd_5813091 := by exact prefixLift 5813091
  have htrace : WordTrace (prefixWord ++ tailWord_5813091) baseStart_5813091 baseEnd_5813091 := by
    simpa [prefixWord, tailWord_5813091, baseEnd_5813091] using wordTrace_append hprefix tailTrace_5813091
  have hstable : (prefixWord ++ tailWord_5813091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813091).length < 2 ^ (prefixWord ++ tailWord_5813091).sum := by decide
  have hdescent : baseEnd_5813091 < baseStart_5813091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813122 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5813122 : Nat := 118140960795 + 5813122 * 2 ^ 59
def prefixEnd_5813122 : Nat := 4983230072969 + 3 ^ 40 * 5813122 * 2
def baseEnd_5813122 : Nat := 2984925689225710367140945

theorem tailTrace_5813122 : CollatzResearch.WordTrace tailWord_5813122 prefixEnd_5813122 2984925689225710367140945 := by
  unfold tailWord_5813122
  simp only [CollatzResearch.WordTrace]
  refine ⟨53005494411514817760422405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 141347985097372847361126413 53005494411514817760422405)
  ·
    refine ⟨9938530202159028330079201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53005494411514817760422405 9938530202159028330079201)
    ·
      refine ⟨7453897651619271247559401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9938530202159028330079201 7453897651619271247559401)
      ·
        refine ⟨5590423238714453435669551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7453897651619271247559401 5590423238714453435669551)
        ·
          refine ⟨8385634858071680153504327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5590423238714453435669551 8385634858071680153504327)
          ·
            refine ⟨12578452287107520230256491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8385634858071680153504327 12578452287107520230256491)
            ·
              refine ⟨18867678430661280345384737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12578452287107520230256491 18867678430661280345384737)
              ·
                refine ⟨14150758822995960259038553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18867678430661280345384737 14150758822995960259038553)
                ·
                  refine ⟨10613069117246970194278915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14150758822995960259038553 10613069117246970194278915)
                  ·
                    refine ⟨15919603675870455291418373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10613069117246970194278915 15919603675870455291418373)
                    ·
                      refine ⟨2984925689225710367140945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15919603675870455291418373 2984925689225710367140945)
                      ·
                        rfl

theorem cell23_5813122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5813122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813122 prefixEnd_5813122 := by exact prefixLift 5813122
  have htrace : WordTrace (prefixWord ++ tailWord_5813122) baseStart_5813122 baseEnd_5813122 := by
    simpa [prefixWord, tailWord_5813122, baseEnd_5813122] using wordTrace_append hprefix tailTrace_5813122
  have hstable : (prefixWord ++ tailWord_5813122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813122).length < 2 ^ (prefixWord ++ tailWord_5813122).sum := by decide
  have hdescent : baseEnd_5813122 < baseStart_5813122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813161 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_5813161 : Nat := 118140960795 + 5813161 * 2 ^ 59
def prefixEnd_5813161 : Nat := 4983230072969 + 3 ^ 40 * 5813161 * 2
def baseEnd_5813161 : Nat := 2984945714971235714553265

theorem tailTrace_5813161 : CollatzResearch.WordTrace tailWord_5813161 prefixEnd_5813161 2984945714971235714553265 := by
  unfold tailWord_5813161
  simp only [CollatzResearch.WordTrace]
  refine ⟨212023400092917980702359337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141348933395278653801572891 212023400092917980702359337)
  ·
    refine ⟨159017550069688485526769503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 212023400092917980702359337 159017550069688485526769503)
    ·
      refine ⟨238526325104532728290154255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159017550069688485526769503 238526325104532728290154255)
      ·
        refine ⟨357789487656799092435231383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238526325104532728290154255 357789487656799092435231383)
        ·
          refine ⟨536684231485198638652847075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357789487656799092435231383 536684231485198638652847075)
          ·
            refine ⟨805026347227797957979270613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536684231485198638652847075 805026347227797957979270613)
            ·
              refine ⟨18867805013151514640139155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 805026347227797957979270613 18867805013151514640139155)
              ·
                refine ⟨28301707519727271960208733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18867805013151514640139155 28301707519727271960208733)
                ·
                  refine ⟨10613140319897726985078275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28301707519727271960208733 10613140319897726985078275)
                  ·
                    refine ⟨15919710479846590477617413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10613140319897726985078275 15919710479846590477617413)
                    ·
                      refine ⟨2984945714971235714553265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15919710479846590477617413 2984945714971235714553265)
                      ·
                        rfl

theorem cell23_5813161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_5813161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813161 prefixEnd_5813161 := by exact prefixLift 5813161
  have htrace : WordTrace (prefixWord ++ tailWord_5813161) baseStart_5813161 baseEnd_5813161 := by
    simpa [prefixWord, tailWord_5813161, baseEnd_5813161] using wordTrace_append hprefix tailTrace_5813161
  have hstable : (prefixWord ++ tailWord_5813161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813161).length < 2 ^ (prefixWord ++ tailWord_5813161).sum := by decide
  have hdescent : baseEnd_5813161 < baseStart_5813161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813171 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 4, 4]
def baseStart_5813171 : Nat := 118140960795 + 5813171 * 2 ^ 59
def prefixEnd_5813171 : Nat := 4983230072969 + 3 ^ 40 * 5813171 * 2
def baseEnd_5813171 : Nat := 994983616592593558476073

theorem tailTrace_5813171 : CollatzResearch.WordTrace tailWord_5813171 prefixEnd_5813171 994983616592593558476073 := by
  unfold tailWord_5813171
  simp only [CollatzResearch.WordTrace]
  refine ⟨212023764822881752410223367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 141349176548587834940148911 212023764822881752410223367)
  ·
    refine ⟨318035647234322628615335051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212023764822881752410223367 318035647234322628615335051)
    ·
      refine ⟨477053470851483942923002577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318035647234322628615335051 477053470851483942923002577)
      ·
        refine ⟨357790103138612957192251933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477053470851483942923002577 357790103138612957192251933)
        ·
          refine ⟨134171288676979858947094475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 357790103138612957192251933 134171288676979858947094475)
          ·
            refine ⟨201256933015469788420641713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134171288676979858947094475 201256933015469788420641713)
            ·
              refine ⟨150942699761602341315481285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201256933015469788420641713 150942699761602341315481285)
              ·
                refine ⟨28301756205300438996652741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150942699761602341315481285 28301756205300438996652741)
                ·
                  refine ⟨5306579288493832311872389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28301756205300438996652741 5306579288493832311872389)
                  ·
                    refine ⟨994983616592593558476073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5306579288493832311872389 994983616592593558476073)
                    ·
                      rfl

theorem cell23_5813171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 4].length) (baseStart_5813171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813171 prefixEnd_5813171 := by exact prefixLift 5813171
  have htrace : WordTrace (prefixWord ++ tailWord_5813171) baseStart_5813171 baseEnd_5813171 := by
    simpa [prefixWord, tailWord_5813171, baseEnd_5813171] using wordTrace_append hprefix tailTrace_5813171
  have hstable : (prefixWord ++ tailWord_5813171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813171).length < 2 ^ (prefixWord ++ tailWord_5813171).sum := by decide
  have hdescent : baseEnd_5813171 < baseStart_5813171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813184 : List Nat := [2, 1, 1, 2, 3, 14]
def baseStart_5813184 : Nat := 118140960795 + 5813184 * 2 ^ 59
def prefixEnd_5813184 : Nat := 4983230072969 + 3 ^ 40 * 5813184 * 2
def baseEnd_5813184 : Nat := 12283775823153453187513

theorem tailTrace_5813184 : CollatzResearch.WordTrace tailWord_5813184 prefixEnd_5813184 12283775823153453187513 := by
  unfold tailWord_5813184
  simp only [CollatzResearch.WordTrace]
  refine ⟨106012119485917327815223303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141349492647889770420297737 106012119485917327815223303)
  ·
    refine ⟨159018179228875991722834955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106012119485917327815223303 159018179228875991722834955)
    ·
      refine ⟨238527268843313987584252433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159018179228875991722834955 238527268843313987584252433)
      ·
        refine ⟨178895451632485490688189325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238527268843313987584252433 178895451632485490688189325)
        ·
          refine ⟨67085794362182059008070997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 178895451632485490688189325 67085794362182059008070997)
          ·
            refine ⟨12283775823153453187513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 67085794362182059008070997 12283775823153453187513)
            ·
              rfl

theorem cell23_5813184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 14].length) (baseStart_5813184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813184 prefixEnd_5813184 := by exact prefixLift 5813184
  have htrace : WordTrace (prefixWord ++ tailWord_5813184) baseStart_5813184 baseEnd_5813184 := by
    simpa [prefixWord, tailWord_5813184, baseEnd_5813184] using wordTrace_append hprefix tailTrace_5813184
  have hstable : (prefixWord ++ tailWord_5813184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813184).length < 2 ^ (prefixWord ++ tailWord_5813184).sum := by decide
  have hdescent : baseEnd_5813184 < baseStart_5813184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813198 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_5813198 : Nat := 118140960795 + 5813198 * 2 ^ 59
def prefixEnd_5813198 : Nat := 4983230072969 + 3 ^ 40 * 5813198 * 2
def baseEnd_5813198 : Nat := 2984964713755452069790595

theorem tailTrace_5813198 : CollatzResearch.WordTrace tailWord_5813198 prefixEnd_5813198 2984964713755452069790595 := by
  unfold tailWord_5813198
  simp only [CollatzResearch.WordTrace]
  refine ⟨26503093699222992002682031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 141349833062522624014304165 26503093699222992002682031)
  ·
    refine ⟨39754640548834488004023047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26503093699222992002682031 39754640548834488004023047)
    ·
      refine ⟨59631960823251732006034571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39754640548834488004023047 59631960823251732006034571)
      ·
        refine ⟨89447941234877598009051857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59631960823251732006034571 89447941234877598009051857)
        ·
          refine ⟨67085955926158198506788893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89447941234877598009051857 67085955926158198506788893)
          ·
            refine ⟨25157233472309324440045835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67085955926158198506788893 25157233472309324440045835)
            ·
              refine ⟨37735850208463986660068753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25157233472309324440045835 37735850208463986660068753)
              ·
                refine ⟨28301887656347989995051565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37735850208463986660068753 28301887656347989995051565)
                ·
                  refine ⟨10613207871130496248144337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28301887656347989995051565 10613207871130496248144337)
                  ·
                    refine ⟨7959905903347872186108253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10613207871130496248144337 7959905903347872186108253)
                    ·
                      refine ⟨2984964713755452069790595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7959905903347872186108253 2984964713755452069790595)
                      ·
                        rfl

theorem cell23_5813198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_5813198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813198 prefixEnd_5813198 := by exact prefixLift 5813198
  have htrace : WordTrace (prefixWord ++ tailWord_5813198) baseStart_5813198 baseEnd_5813198 := by
    simpa [prefixWord, tailWord_5813198, baseEnd_5813198] using wordTrace_append hprefix tailTrace_5813198
  have hstable : (prefixWord ++ tailWord_5813198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813198).length < 2 ^ (prefixWord ++ tailWord_5813198).sum := by decide
  have hdescent : baseEnd_5813198 < baseStart_5813198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5813208 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_5813208 : Nat := 118140960795 + 5813208 * 2 ^ 59
def prefixEnd_5813208 : Nat := 4983230072969 + 3 ^ 40 * 5813208 * 2
def baseEnd_5813208 : Nat := 2984969848561997030665549

theorem tailTrace_5813208 : CollatzResearch.WordTrace tailWord_5813208 prefixEnd_5813208 2984969848561997030665549 := by
  unfold tailWord_5813208
  simp only [CollatzResearch.WordTrace]
  refine ⟨106012557161873853864660139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 141350076215831805152880185 106012557161873853864660139)
  ·
    refine ⟨159018835742810780796990209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106012557161873853864660139 159018835742810780796990209)
    ·
      refine ⟨119264126807108085597742657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159018835742810780796990209 119264126807108085597742657)
      ·
        refine ⟨89448095105331064198306993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119264126807108085597742657 89448095105331064198306993)
        ·
          refine ⟨67086071328998298148730245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89448095105331064198306993 67086071328998298148730245)
          ·
            refine ⟨12578638374187180902886921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67086071328998298148730245 12578638374187180902886921)
            ·
              refine ⟨9433978780640385677165191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12578638374187180902886921 9433978780640385677165191)
              ·
                refine ⟨14150968170960578515747787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9433978780640385677165191 14150968170960578515747787)
                ·
                  refine ⟨21226452256440867773621681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14150968170960578515747787 21226452256440867773621681)
                  ·
                    refine ⟨15919839192330650830216261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21226452256440867773621681 15919839192330650830216261)
                    ·
                      refine ⟨2984969848561997030665549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15919839192330650830216261 2984969848561997030665549)
                      ·
                        rfl

theorem cell23_5813208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_5813208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5813208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5813208 prefixEnd_5813208 := by exact prefixLift 5813208
  have htrace : WordTrace (prefixWord ++ tailWord_5813208) baseStart_5813208 baseEnd_5813208 := by
    simpa [prefixWord, tailWord_5813208, baseEnd_5813208] using wordTrace_append hprefix tailTrace_5813208
  have hstable : (prefixWord ++ tailWord_5813208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5813208).length < 2 ^ (prefixWord ++ tailWord_5813208).sum := by decide
  have hdescent : baseEnd_5813208 < baseStart_5813208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5813208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
