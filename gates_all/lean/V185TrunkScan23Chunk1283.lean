import V185TrunkScan23Chunk1282

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7601067 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 3, 5, 2]
def baseStart_7601067 : Nat := 118140960795 + 7601067 * 2 ^ 59
def prefixEnd_7601067 : Nat := 4983230072969 + 3 ^ 40 * 7601067 * 2
def baseEnd_7601067 : Nat := 3903000858028717524105835

theorem tailTrace_7601067 : CollatzResearch.WordTrace tailWord_7601067 prefixEnd_7601067 3903000858028717524105835 := by
  unfold tailWord_7601067
  simp only [CollatzResearch.WordTrace]
  refine ⟨277233689153639892737001455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184822459435759928491334303 277233689153639892737001455)
  ·
    refine ⟨415850533730459839105502183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277233689153639892737001455 415850533730459839105502183)
    ·
      refine ⟨623775800595689758658253275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415850533730459839105502183 623775800595689758658253275)
      ·
        refine ⟨935663700893534637987379913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623775800595689758658253275 935663700893534637987379913)
        ·
          refine ⟨701747775670150978490534935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 935663700893534637987379913 701747775670150978490534935)
          ·
            refine ⟨1052621663505226467735802403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701747775670150978490534935 1052621663505226467735802403)
            ·
              refine ⟨1578932495257839701603703605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052621663505226467735802403 1578932495257839701603703605)
              ·
                refine ⟨148024921430422472025347213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1578932495257839701603703605 148024921430422472025347213)
                ·
                  refine ⟨55509345536408427009505205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148024921430422472025347213 55509345536408427009505205)
                  ·
                    refine ⟨5204001144038290032141113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55509345536408427009505205 5204001144038290032141113)
                    ·
                      refine ⟨3903000858028717524105835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204001144038290032141113 3903000858028717524105835)
                      ·
                        rfl

theorem cell23_7601067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 5, 2].length) (baseStart_7601067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601067 prefixEnd_7601067 := by exact prefixLift 7601067
  have htrace : WordTrace (prefixWord ++ tailWord_7601067) baseStart_7601067 baseEnd_7601067 := by
    simpa [prefixWord, tailWord_7601067, baseEnd_7601067] using wordTrace_append hprefix tailTrace_7601067
  have hstable : (prefixWord ++ tailWord_7601067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601067).length < 2 ^ (prefixWord ++ tailWord_7601067).sum := by decide
  have hdescent : baseEnd_7601067 < baseStart_7601067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601077 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7601077 : Nat := 118140960795 + 7601077 * 2 ^ 59
def prefixEnd_7601077 : Nat := 4983230072969 + 3 ^ 40 * 7601077 * 2
def baseEnd_7601077 : Nat := 1301001997611754161660263

theorem tailTrace_7601077 : CollatzResearch.WordTrace tailWord_7601077 prefixEnd_7601077 1301001997611754161660263 := by
  unfold tailWord_7601077
  simp only [CollatzResearch.WordTrace]
  refine ⟨277234053883603664444865485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184822702589069109629910323 277234053883603664444865485)
  ·
    refine ⟨103962770206351374166824557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277234053883603664444865485 103962770206351374166824557)
    ·
      refine ⟨38986038827381765312559209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103962770206351374166824557 38986038827381765312559209)
      ·
        refine ⟨29239529120536323984419407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38986038827381765312559209 29239529120536323984419407)
        ·
          refine ⟨43859293680804485976629111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29239529120536323984419407 43859293680804485976629111)
          ·
            refine ⟨65788940521206728964943667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43859293680804485976629111 65788940521206728964943667)
            ·
              refine ⟨98683410781810093447415501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65788940521206728964943667 98683410781810093447415501)
              ·
                refine ⟨37006279043178785042780813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98683410781810093447415501 37006279043178785042780813)
                ·
                  refine ⟨13877354641192044391042805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37006279043178785042780813 13877354641192044391042805)
                  ·
                    refine ⟨1301001997611754161660263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13877354641192044391042805 1301001997611754161660263)
                    ·
                      rfl

theorem cell23_7601077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7601077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601077 prefixEnd_7601077 := by exact prefixLift 7601077
  have htrace : WordTrace (prefixWord ++ tailWord_7601077) baseStart_7601077 baseEnd_7601077 := by
    simpa [prefixWord, tailWord_7601077, baseEnd_7601077] using wordTrace_append hprefix tailTrace_7601077
  have hstable : (prefixWord ++ tailWord_7601077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601077).length < 2 ^ (prefixWord ++ tailWord_7601077).sum := by decide
  have hdescent : baseEnd_7601077 < baseStart_7601077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601108 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_7601108 : Nat := 118140960795 + 7601108 * 2 ^ 59
def prefixEnd_7601108 : Nat := 4983230072969 + 3 ^ 40 * 7601108 * 2
def baseEnd_7601108 : Nat := 3903021910735551863693147

theorem tailTrace_7601108 : CollatzResearch.WordTrace tailWord_7601108 prefixEnd_7601108 3903021910735551863693147 := by
  unfold tailWord_7601108
  simp only [CollatzResearch.WordTrace]
  refine ⟨138617592273245678369621989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184823456364327571159495985 138617592273245678369621989)
  ·
    refine ⟨25990798551233564694304123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138617592273245678369621989 25990798551233564694304123)
    ·
      refine ⟨38986197826850347041456185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25990798551233564694304123 38986197826850347041456185)
      ·
        refine ⟨29239648370137760281092139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38986197826850347041456185 29239648370137760281092139)
        ·
          refine ⟨43859472555206640421638209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29239648370137760281092139 43859472555206640421638209)
          ·
            refine ⟨32894604416404980316228657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43859472555206640421638209 32894604416404980316228657)
            ·
              refine ⟨24670953312303735237171493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32894604416404980316228657 24670953312303735237171493)
              ·
                refine ⟨4625803746056950356969655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24670953312303735237171493 4625803746056950356969655)
                ·
                  refine ⟨6938705619085425535454483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625803746056950356969655 6938705619085425535454483)
                  ·
                    refine ⟨10408058428628138303181725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938705619085425535454483 10408058428628138303181725)
                    ·
                      refine ⟨3903021910735551863693147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408058428628138303181725 3903021910735551863693147)
                      ·
                        rfl

theorem cell23_7601108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_7601108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601108 prefixEnd_7601108 := by exact prefixLift 7601108
  have htrace : WordTrace (prefixWord ++ tailWord_7601108) baseStart_7601108 baseEnd_7601108 := by
    simpa [prefixWord, tailWord_7601108, baseEnd_7601108] using wordTrace_append hprefix tailTrace_7601108
  have hstable : (prefixWord ++ tailWord_7601108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601108).length < 2 ^ (prefixWord ++ tailWord_7601108).sum := by decide
  have hdescent : baseEnd_7601108 < baseStart_7601108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601137 : List Nat := [1, 2, 2, 2, 4, 2, 1, 9]
def baseStart_7601137 : Nat := 118140960795 + 7601137 * 2 ^ 59
def prefixEnd_7601137 : Nat := 4983230072969 + 3 ^ 40 * 7601137 * 2
def baseEnd_7601137 : Nat := 144556918580538231490019

theorem tailTrace_7601137 : CollatzResearch.WordTrace tailWord_7601137 prefixEnd_7601137 144556918580538231490019 := by
  unfold tailWord_7601137
  simp only [CollatzResearch.WordTrace]
  refine ⟨277236242263386294692049665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184824161508924196461366443 277236242263386294692049665)
  ·
    refine ⟨207927181697539721019037249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277236242263386294692049665 207927181697539721019037249)
    ·
      refine ⟨155945386273154790764277937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207927181697539721019037249 155945386273154790764277937)
      ·
        refine ⟨116959039704866093073208453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155945386273154790764277937 116959039704866093073208453)
        ·
          refine ⟨21929819944662392451226585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116959039704866093073208453 21929819944662392451226585)
          ·
            refine ⟨16447364958496794338419939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21929819944662392451226585 16447364958496794338419939)
            ·
              refine ⟨24671047437745191507629909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447364958496794338419939 24671047437745191507629909)
              ·
                refine ⟨144556918580538231490019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24671047437745191507629909 144556918580538231490019)
                ·
                  rfl

theorem cell23_7601137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 9].length) (baseStart_7601137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601137 prefixEnd_7601137 := by exact prefixLift 7601137
  have htrace : WordTrace (prefixWord ++ tailWord_7601137) baseStart_7601137 baseEnd_7601137 := by
    simpa [prefixWord, tailWord_7601137, baseEnd_7601137] using wordTrace_append hprefix tailTrace_7601137
  have hstable : (prefixWord ++ tailWord_7601137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601137).length < 2 ^ (prefixWord ++ tailWord_7601137).sum := by decide
  have hdescent : baseEnd_7601137 < baseStart_7601137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601147 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3]
def baseStart_7601147 : Nat := 118140960795 + 7601147 * 2 ^ 59
def prefixEnd_7601147 : Nat := 4983230072969 + 3 ^ 40 * 7601147 * 2
def baseEnd_7601147 : Nat := 3903041936481077211105467

theorem tailTrace_7601147 : CollatzResearch.WordTrace tailWord_7601147 prefixEnd_7601147 3903041936481077211105467 := by
  unfold tailWord_7601147
  simp only [CollatzResearch.WordTrace]
  refine ⟨277236606993350066399913695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184824404662233377599942463 277236606993350066399913695)
  ·
    refine ⟨415854910490025099599870543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277236606993350066399913695 415854910490025099599870543)
    ·
      refine ⟨623782365735037649399805815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415854910490025099599870543 623782365735037649399805815)
      ·
        refine ⟨935673548602556474099708723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623782365735037649399805815 935673548602556474099708723)
        ·
          refine ⟨1403510322903834711149563085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935673548602556474099708723 1403510322903834711149563085)
          ·
            refine ⟨526316371088938016681086157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1403510322903834711149563085 526316371088938016681086157)
            ·
              refine ⟨197368639158351756255407309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526316371088938016681086157 197368639158351756255407309)
              ·
                refine ⟨74013239684381908595777741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197368639158351756255407309 74013239684381908595777741)
                ·
                  refine ⟨27754964881643215723416653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74013239684381908595777741 27754964881643215723416653)
                  ·
                    refine ⟨10408111830616205896281245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27754964881643215723416653 10408111830616205896281245)
                    ·
                      refine ⟨3903041936481077211105467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408111830616205896281245 3903041936481077211105467)
                      ·
                        rfl

theorem cell23_7601147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].length) (baseStart_7601147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601147 prefixEnd_7601147 := by exact prefixLift 7601147
  have htrace : WordTrace (prefixWord ++ tailWord_7601147) baseStart_7601147 baseEnd_7601147 := by
    simpa [prefixWord, tailWord_7601147, baseEnd_7601147] using wordTrace_append hprefix tailTrace_7601147
  have hstable : (prefixWord ++ tailWord_7601147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601147).length < 2 ^ (prefixWord ++ tailWord_7601147).sum := by decide
  have hdescent : baseEnd_7601147 < baseStart_7601147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601221 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_7601221 : Nat := 118140960795 + 7601221 * 2 ^ 59
def prefixEnd_7601221 : Nat := 4983230072969 + 3 ^ 40 * 7601221 * 2
def baseEnd_7601221 : Nat := 3903079934049509921580127

theorem tailTrace_7601221 : CollatzResearch.WordTrace tailWord_7601221 prefixEnd_7601221 3903079934049509921580127 := by
  unfold tailWord_7601221
  simp only [CollatzResearch.WordTrace]
  refine ⟨277239305995081977038107517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184826203996721318025405011 277239305995081977038107517)
  ·
    refine ⟨103964739748155741389290319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277239305995081977038107517 103964739748155741389290319)
    ·
      refine ⟨155947109622233612083935479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103964739748155741389290319 155947109622233612083935479)
      ·
        refine ⟨233920664433350418125903219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155947109622233612083935479 233920664433350418125903219)
        ·
          refine ⟨350880996650025627188854829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233920664433350418125903219 350880996650025627188854829)
          ·
            refine ⟨131580373743759610195820561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350880996650025627188854829 131580373743759610195820561)
            ·
              refine ⟨98685280307819707646865421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131580373743759610195820561 98685280307819707646865421)
              ·
                refine ⟨37006980115432390367574533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98685280307819707646865421 37006980115432390367574533)
                ·
                  refine ⟨6938808771643573193920225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37006980115432390367574533 6938808771643573193920225)
                  ·
                    refine ⟨5204106578732679895440169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6938808771643573193920225 5204106578732679895440169)
                    ·
                      refine ⟨3903079934049509921580127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204106578732679895440169 3903079934049509921580127)
                      ·
                        rfl

theorem cell23_7601221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_7601221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601221 prefixEnd_7601221 := by exact prefixLift 7601221
  have htrace : WordTrace (prefixWord ++ tailWord_7601221) baseStart_7601221 baseEnd_7601221 := by
    simpa [prefixWord, tailWord_7601221, baseEnd_7601221] using wordTrace_append hprefix tailTrace_7601221
  have hstable : (prefixWord ++ tailWord_7601221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601221).length < 2 ^ (prefixWord ++ tailWord_7601221).sum := by decide
  have hdescent : baseEnd_7601221 < baseStart_7601221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601234 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_7601234 : Nat := 118140960795 + 7601234 * 2 ^ 59
def prefixEnd_7601234 : Nat := 4983230072969 + 3 ^ 40 * 7601234 * 2
def baseEnd_7601234 : Nat := 3903086609298018370717567

theorem tailTrace_7601234 : CollatzResearch.WordTrace tailWord_7601234 prefixEnd_7601234 3903086609298018370717567 := by
  unfold tailWord_7601234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69309945036008720064582689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184826520096023253505553837 69309945036008720064582689)
  ·
    refine ⟨51982458777006540048437017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69309945036008720064582689 51982458777006540048437017)
    ·
      refine ⟨38986844082754905036327763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51982458777006540048437017 38986844082754905036327763)
      ·
        refine ⟨58480266124132357554491645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38986844082754905036327763 58480266124132357554491645)
        ·
          refine ⟨21930099796549634082934367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58480266124132357554491645 21930099796549634082934367)
          ·
            refine ⟨32895149694824451124401551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21930099796549634082934367 32895149694824451124401551)
            ·
              refine ⟨49342724542236676686602327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32895149694824451124401551 49342724542236676686602327)
              ·
                refine ⟨74014086813355015029903491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49342724542236676686602327 74014086813355015029903491)
                ·
                  refine ⟨111021130220032522544855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74014086813355015029903491 111021130220032522544855237)
                  ·
                    refine ⟨20816461916256097977160357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111021130220032522544855237 20816461916256097977160357)
                    ·
                      refine ⟨3903086609298018370717567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20816461916256097977160357 3903086609298018370717567)
                      ·
                        rfl

theorem cell23_7601234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_7601234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601234 prefixEnd_7601234 := by exact prefixLift 7601234
  have htrace : WordTrace (prefixWord ++ tailWord_7601234) baseStart_7601234 baseEnd_7601234 := by
    simpa [prefixWord, tailWord_7601234, baseEnd_7601234] using wordTrace_append hprefix tailTrace_7601234
  have hstable : (prefixWord ++ tailWord_7601234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601234).length < 2 ^ (prefixWord ++ tailWord_7601234).sum := by decide
  have hdescent : baseEnd_7601234 < baseStart_7601234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601244 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 7]
def baseStart_7601244 : Nat := 118140960795 + 7601244 * 2 ^ 59
def prefixEnd_7601244 : Nat := 4983230072969 + 3 ^ 40 * 7601244 * 2
def baseEnd_7601244 : Nat := 433676860456062592399169

theorem tailTrace_7601244 : CollatzResearch.WordTrace tailWord_7601244 prefixEnd_7601244 433676860456062592399169 := by
  unfold tailWord_7601244
  simp only [CollatzResearch.WordTrace]
  refine ⟨138620072436999325983097393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184826763249332434644129857 138620072436999325983097393)
  ·
    refine ⟨103965054327749494487323045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138620072436999325983097393 103965054327749494487323045)
    ·
      refine ⟨19493447686453030216373071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103965054327749494487323045 19493447686453030216373071)
      ·
        refine ⟨29240171529679545324559607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19493447686453030216373071 29240171529679545324559607)
        ·
          refine ⟨43860257294519317986839411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29240171529679545324559607 43860257294519317986839411)
          ·
            refine ⟨65790385941778976980259117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43860257294519317986839411 65790385941778976980259117)
            ·
              refine ⟨24671394728167116367597169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65790385941778976980259117 24671394728167116367597169)
              ·
                refine ⟨18503546046125337275697877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24671394728167116367597169 18503546046125337275697877)
                ·
                  refine ⟨433676860456062592399169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18503546046125337275697877 433676860456062592399169)
                  ·
                    rfl

theorem cell23_7601244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_7601244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601244 prefixEnd_7601244 := by exact prefixLift 7601244
  have htrace : WordTrace (prefixWord ++ tailWord_7601244) baseStart_7601244 baseEnd_7601244 := by
    simpa [prefixWord, tailWord_7601244, baseEnd_7601244] using wordTrace_append hprefix tailTrace_7601244
  have hstable : (prefixWord ++ tailWord_7601244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601244).length < 2 ^ (prefixWord ++ tailWord_7601244).sum := by decide
  have hdescent : baseEnd_7601244 < baseStart_7601244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601261 : List Nat := [1, 5, 1, 1, 2, 2, 1, 5, 5]
def baseStart_7601261 : Nat := 118140960795 + 7601261 * 2 ^ 59
def prefixEnd_7601261 : Nat := 4983230072969 + 3 ^ 40 * 7601261 * 2
def baseEnd_7601261 : Nat := 433677830363965529453327

theorem tailTrace_7601261 : CollatzResearch.WordTrace tailWord_7601261 prefixEnd_7601261 433677830363965529453327 := by
  unfold tailWord_7601261
  simp only [CollatzResearch.WordTrace]
  refine ⟨277240764914937063869563637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184827176609958042579709091 277240764914937063869563637)
  ·
    refine ⟨25991321710775349737771591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277240764914937063869563637 25991321710775349737771591)
    ·
      refine ⟨38986982566163024606657387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25991321710775349737771591 38986982566163024606657387)
      ·
        refine ⟨58480473849244536909986081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38986982566163024606657387 58480473849244536909986081)
        ·
          refine ⟨43860355386933402682489561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58480473849244536909986081 43860355386933402682489561)
          ·
            refine ⟨32895266540200052011867171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43860355386933402682489561 32895266540200052011867171)
            ·
              refine ⟨49342899810300078017800757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32895266540200052011867171 49342899810300078017800757)
              ·
                refine ⟨4625896857215632314168821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49342899810300078017800757 4625896857215632314168821)
                ·
                  refine ⟨433677830363965529453327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4625896857215632314168821 433677830363965529453327)
                  ·
                    rfl

theorem cell23_7601261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_7601261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601261 prefixEnd_7601261 := by exact prefixLift 7601261
  have htrace : WordTrace (prefixWord ++ tailWord_7601261) baseStart_7601261 baseEnd_7601261 := by
    simpa [prefixWord, tailWord_7601261, baseEnd_7601261] using wordTrace_append hprefix tailTrace_7601261
  have hstable : (prefixWord ++ tailWord_7601261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601261).length < 2 ^ (prefixWord ++ tailWord_7601261).sum := by decide
  have hdescent : baseEnd_7601261 < baseStart_7601261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_7601307 : Nat := 118140960795 + 7601307 * 2 ^ 59
def prefixEnd_7601307 : Nat := 4983230072969 + 3 ^ 40 * 7601307 * 2
def baseEnd_7601307 : Nat := 3903124093385796585104731

theorem tailTrace_7601307 : CollatzResearch.WordTrace tailWord_7601307 prefixEnd_7601307 3903124093385796585104731 := by
  unfold tailWord_7601307
  simp only [CollatzResearch.WordTrace]
  refine ⟨277242442672770413725738175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184828295115180275817158783 277242442672770413725738175)
  ·
    refine ⟨415863664009155620588607263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277242442672770413725738175 415863664009155620588607263)
    ·
      refine ⟨623795496013733430882910895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415863664009155620588607263 623795496013733430882910895)
      ·
        refine ⟨935693244020600146324366343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623795496013733430882910895 935693244020600146324366343)
        ·
          refine ⟨1403539866030900219486549515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935693244020600146324366343 1403539866030900219486549515)
          ·
            refine ⟨2105309799046350329229824273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403539866030900219486549515 2105309799046350329229824273)
            ·
              refine ⟨1578982349284762746922368205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2105309799046350329229824273 1578982349284762746922368205)
              ·
                refine ⟨592118380981786030095888077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1578982349284762746922368205 592118380981786030095888077)
                ·
                  refine ⟨222044392868169761285958029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592118380981786030095888077 222044392868169761285958029)
                  ·
                    refine ⟨83266647325563660482234261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222044392868169761285958029 83266647325563660482234261)
                    ·
                      refine ⟨3903124093385796585104731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83266647325563660482234261 3903124093385796585104731)
                      ·
                        rfl

theorem cell23_7601307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_7601307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601307 prefixEnd_7601307 := by exact prefixLift 7601307
  have htrace : WordTrace (prefixWord ++ tailWord_7601307) baseStart_7601307 baseEnd_7601307 := by
    simpa [prefixWord, tailWord_7601307, baseEnd_7601307] using wordTrace_append hprefix tailTrace_7601307
  have hstable : (prefixWord ++ tailWord_7601307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601307).length < 2 ^ (prefixWord ++ tailWord_7601307).sum := by decide
  have hdescent : baseEnd_7601307 < baseStart_7601307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601361 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_7601361 : Nat := 118140960795 + 7601361 * 2 ^ 59
def prefixEnd_7601361 : Nat := 4983230072969 + 3 ^ 40 * 7601361 * 2
def baseEnd_7601361 : Nat := 3903151821341139373829483

theorem tailTrace_7601361 : CollatzResearch.WordTrace tailWord_7601361 prefixEnd_7601361 3903151821341139373829483 := by
  unfold tailWord_7601361
  simp only [CollatzResearch.WordTrace]
  refine ⟨277244412214574780948203937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184829608143049853965469291 277244412214574780948203937)
  ·
    refine ⟨207933309160931085711152953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277244412214574780948203937 207933309160931085711152953)
    ·
      refine ⟨155949981870698314283364715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207933309160931085711152953 155949981870698314283364715)
      ·
        refine ⟨233924972806047471425047073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155949981870698314283364715 233924972806047471425047073)
        ·
          refine ⟨175443729604535603568785305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233924972806047471425047073 175443729604535603568785305)
          ·
            refine ⟨131582797203401702676588979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175443729604535603568785305 131582797203401702676588979)
            ·
              refine ⟨197374195805102554014883469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131582797203401702676588979 197374195805102554014883469)
              ·
                refine ⟨74015323426913457755581301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197374195805102554014883469 74015323426913457755581301)
                ·
                  refine ⟨6938936571273136664585747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74015323426913457755581301 6938936571273136664585747)
                  ·
                    refine ⟨10408404856909704996878621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938936571273136664585747 10408404856909704996878621)
                    ·
                      refine ⟨3903151821341139373829483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408404856909704996878621 3903151821341139373829483)
                      ·
                        rfl

theorem cell23_7601361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_7601361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601361 prefixEnd_7601361 := by exact prefixLift 7601361
  have htrace : WordTrace (prefixWord ++ tailWord_7601361) baseStart_7601361 baseEnd_7601361 := by
    simpa [prefixWord, tailWord_7601361, baseEnd_7601361] using wordTrace_append hprefix tailTrace_7601361
  have hstable : (prefixWord ++ tailWord_7601361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601361).length < 2 ^ (prefixWord ++ tailWord_7601361).sum := by decide
  have hdescent : baseEnd_7601361 < baseStart_7601361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601388 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 2, 3, 2]
def baseStart_7601388 : Nat := 118140960795 + 7601388 * 2 ^ 59
def prefixEnd_7601388 : Nat := 4983230072969 + 3 ^ 40 * 7601388 * 2
def baseEnd_7601388 : Nat := 3903165685318810768191859

theorem tailTrace_7601388 : CollatzResearch.WordTrace tailWord_7601388 prefixEnd_7601388 3903165685318810768191859 := by
  unfold tailWord_7601388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138622698492738482279718409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184830264656984643039624545 138622698492738482279718409)
  ·
    refine ⟨103967023869553861709788807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138622698492738482279718409 103967023869553861709788807)
    ·
      refine ⟨155950535804330792564683211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103967023869553861709788807 155950535804330792564683211)
      ·
        refine ⟨233925803706496188847024817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155950535804330792564683211 233925803706496188847024817)
        ·
          refine ⟨175444352779872141635268613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233925803706496188847024817 175444352779872141635268613)
          ·
            refine ⟨32895816146226026556612865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175444352779872141635268613 32895816146226026556612865)
            ·
              refine ⟨24671862109669519917459649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32895816146226026556612865 24671862109669519917459649)
              ·
                refine ⟨18503896582252139938094737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24671862109669519917459649 18503896582252139938094737)
                ·
                  refine ⟨13877922436689104953571053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18503896582252139938094737 13877922436689104953571053)
                  ·
                    refine ⟨5204220913758414357589145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13877922436689104953571053 5204220913758414357589145)
                    ·
                      refine ⟨3903165685318810768191859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204220913758414357589145 3903165685318810768191859)
                      ·
                        rfl

theorem cell23_7601388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 3, 2].length) (baseStart_7601388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601388 prefixEnd_7601388 := by exact prefixLift 7601388
  have htrace : WordTrace (prefixWord ++ tailWord_7601388) baseStart_7601388 baseEnd_7601388 := by
    simpa [prefixWord, tailWord_7601388, baseEnd_7601388] using wordTrace_append hprefix tailTrace_7601388
  have hstable : (prefixWord ++ tailWord_7601388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601388).length < 2 ^ (prefixWord ++ tailWord_7601388).sum := by decide
  have hdescent : baseEnd_7601388 < baseStart_7601388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601395 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 1, 1, 3]
def baseStart_7601395 : Nat := 118140960795 + 7601395 * 2 ^ 59
def prefixEnd_7601395 : Nat := 4983230072969 + 3 ^ 40 * 7601395 * 2
def baseEnd_7601395 : Nat := 3903169279683392240804327

theorem tailTrace_7601395 : CollatzResearch.WordTrace tailWord_7601395 prefixEnd_7601395 3903169279683392240804327 := by
  unfold tailWord_7601395
  simp only [CollatzResearch.WordTrace]
  refine ⟨277245652296451604754941639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184830434864301069836627759 277245652296451604754941639)
  ·
    refine ⟨415868478444677407132412459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277245652296451604754941639 415868478444677407132412459)
    ·
      refine ⟨623802717667016110698618689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415868478444677407132412459 623802717667016110698618689)
      ·
        refine ⟨467852038250262083023964017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623802717667016110698618689 467852038250262083023964017)
        ·
          refine ⟨350889028687696562267973013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467852038250262083023964017 350889028687696562267973013)
          ·
            refine ⟨16447923219735776356311235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 350889028687696562267973013 16447923219735776356311235)
            ·
              refine ⟨24671884829603664534466853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16447923219735776356311235 24671884829603664534466853)
              ·
                refine ⟨4625978405550687100212535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24671884829603664534466853 4625978405550687100212535)
                ·
                  refine ⟨6938967608326030650318803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4625978405550687100212535 6938967608326030650318803)
                  ·
                    refine ⟨10408451412489045975478205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6938967608326030650318803 10408451412489045975478205)
                    ·
                      refine ⟨3903169279683392240804327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408451412489045975478205 3903169279683392240804327)
                      ·
                        rfl

theorem cell23_7601395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 1, 1, 3].length) (baseStart_7601395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601395 prefixEnd_7601395 := by exact prefixLift 7601395
  have htrace : WordTrace (prefixWord ++ tailWord_7601395) baseStart_7601395 baseEnd_7601395 := by
    simpa [prefixWord, tailWord_7601395, baseEnd_7601395] using wordTrace_append hprefix tailTrace_7601395
  have hstable : (prefixWord ++ tailWord_7601395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601395).length < 2 ^ (prefixWord ++ tailWord_7601395).sum := by decide
  have hdescent : baseEnd_7601395 < baseStart_7601395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601411 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 1, 6]
def baseStart_7601411 : Nat := 118140960795 + 7601411 * 2 ^ 59
def prefixEnd_7601411 : Nat := 4983230072969 + 3 ^ 40 * 7601411 * 2
def baseEnd_7601411 : Nat := 1301059165124621392734751

theorem tailTrace_7601411 : CollatzResearch.WordTrace tailWord_7601411 prefixEnd_7601411 1301059165124621392734751 := by
  unfold tailWord_7601411
  simp only [CollatzResearch.WordTrace]
  refine ⟨277246235864393639487524087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184830823909595759658349391 277246235864393639487524087)
  ·
    refine ⟨415869353796590459231286131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277246235864393639487524087 415869353796590459231286131)
    ·
      refine ⟨623804030694885688846929197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415869353796590459231286131 623804030694885688846929197)
      ·
        refine ⟨233926511510582133317598449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623804030694885688846929197 233926511510582133317598449)
        ·
          refine ⟨175444883632936599988198837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233926511510582133317598449 175444883632936599988198837)
          ·
            refine ⟨16447957840587806248893641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 175444883632936599988198837 16447957840587806248893641)
            ·
              refine ⟨12335968380440854686670231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16447957840587806248893641 12335968380440854686670231)
              ·
                refine ⟨18503952570661282030005347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12335968380440854686670231 18503952570661282030005347)
                ·
                  refine ⟨27755928855991923045008021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18503952570661282030005347 27755928855991923045008021)
                  ·
                    refine ⟨1301059165124621392734751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27755928855991923045008021 1301059165124621392734751)
                    ·
                      rfl

theorem cell23_7601411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].length) (baseStart_7601411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601411 prefixEnd_7601411 := by exact prefixLift 7601411
  have htrace : WordTrace (prefixWord ++ tailWord_7601411) baseStart_7601411 baseEnd_7601411 := by
    simpa [prefixWord, tailWord_7601411, baseEnd_7601411] using wordTrace_append hprefix tailTrace_7601411
  have hstable : (prefixWord ++ tailWord_7601411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601411).length < 2 ^ (prefixWord ++ tailWord_7601411).sum := by decide
  have hdescent : baseEnd_7601411 < baseStart_7601411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601431 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_7601431 : Nat := 118140960795 + 7601431 * 2 ^ 59
def prefixEnd_7601431 : Nat := 4983230072969 + 3 ^ 40 * 7601431 * 2
def baseEnd_7601431 : Nat := 3903187764986954099954161

theorem tailTrace_7601431 : CollatzResearch.WordTrace tailWord_7601431 prefixEnd_7601431 3903187764986954099954161 := by
  unfold tailWord_7601431
  simp only [CollatzResearch.WordTrace]
  refine ⟨277246965324321182903252147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184831310216214121935501431 277246965324321182903252147)
  ·
    refine ⟨415870447986481774354878221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277246965324321182903252147 415870447986481774354878221)
    ·
      refine ⟨155951417994930665383079333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415870447986481774354878221 155951417994930665383079333)
      ·
        refine ⟨29240890874049499759327375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155951417994930665383079333 29240890874049499759327375)
        ·
          refine ⟨43861336311074249638991063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29240890874049499759327375 43861336311074249638991063)
          ·
            refine ⟨65792004466611374458486595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43861336311074249638991063 65792004466611374458486595)
            ·
              refine ⟨98688006699917061687729893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65792004466611374458486595 98688006699917061687729893)
              ·
                refine ⟨18504001256234449066449355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98688006699917061687729893 18504001256234449066449355)
                ·
                  refine ⟨27756001884351673599674033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504001256234449066449355 27756001884351673599674033)
                  ·
                    refine ⟨20817001413263755199755525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27756001884351673599674033 20817001413263755199755525)
                    ·
                      refine ⟨3903187764986954099954161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20817001413263755199755525 3903187764986954099954161)
                      ·
                        rfl

theorem cell23_7601431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_7601431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601431 prefixEnd_7601431 := by exact prefixLift 7601431
  have htrace : WordTrace (prefixWord ++ tailWord_7601431) baseStart_7601431 baseEnd_7601431 := by
    simpa [prefixWord, tailWord_7601431, baseEnd_7601431] using wordTrace_append hprefix tailTrace_7601431
  have hstable : (prefixWord ++ tailWord_7601431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601431).length < 2 ^ (prefixWord ++ tailWord_7601431).sum := by decide
  have hdescent : baseEnd_7601431 < baseStart_7601431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601445 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_7601445 : Nat := 118140960795 + 7601445 * 2 ^ 59
def prefixEnd_7601445 : Nat := 4983230072969 + 3 ^ 40 * 7601445 * 2
def baseEnd_7601445 : Nat := 1301064984572039015059699

theorem tailTrace_7601445 : CollatzResearch.WordTrace tailWord_7601445 prefixEnd_7601445 1301064984572039015059699 := by
  unfold tailWord_7601445
  simp only [CollatzResearch.WordTrace]
  refine ⟨277247475946270463294261789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184831650630846975529507859 277247475946270463294261789)
  ·
    refine ⟨103967803479851423735348171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277247475946270463294261789 103967803479851423735348171)
    ·
      refine ⟨155951705219777135603022257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103967803479851423735348171 155951705219777135603022257)
      ·
        refine ⟨116963778914832851702266693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155951705219777135603022257 116963778914832851702266693)
        ·
          refine ⟨21930708546531159694175005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116963778914832851702266693 21930708546531159694175005)
          ·
            refine ⟨8224015704949184885315627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21930708546531159694175005 8224015704949184885315627)
            ·
              refine ⟨12336023557423777327973441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224015704949184885315627 12336023557423777327973441)
              ·
                refine ⟨9252017668067832995980081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12336023557423777327973441 9252017668067832995980081)
                ·
                  refine ⟨6939013251050874746985061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9252017668067832995980081 6939013251050874746985061)
                  ·
                    refine ⟨1301064984572039015059699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939013251050874746985061 1301064984572039015059699)
                    ·
                      rfl

theorem cell23_7601445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_7601445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601445 prefixEnd_7601445 := by exact prefixLift 7601445
  have htrace : WordTrace (prefixWord ++ tailWord_7601445) baseStart_7601445 baseEnd_7601445 := by
    simpa [prefixWord, tailWord_7601445, baseEnd_7601445] using wordTrace_append hprefix tailTrace_7601445
  have hstable : (prefixWord ++ tailWord_7601445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601445).length < 2 ^ (prefixWord ++ tailWord_7601445).sum := by decide
  have hdescent : baseEnd_7601445 < baseStart_7601445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601462 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7601462 : Nat := 118140960795 + 7601462 * 2 ^ 59
def prefixEnd_7601462 : Nat := 4983230072969 + 3 ^ 40 * 7601462 * 2
def baseEnd_7601462 : Nat := 1301067894295747826222173

theorem tailTrace_7601462 : CollatzResearch.WordTrace tailWord_7601462 prefixEnd_7601462 1301067894295747826222173 := by
  unfold tailWord_7601462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17328005999200554699851915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184832063991472583465087093 17328005999200554699851915)
  ·
    refine ⟨25992008998800832049777873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17328005999200554699851915 25992008998800832049777873)
    ·
      refine ⟨19494006749100624037333405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25992008998800832049777873 19494006749100624037333405)
      ·
        refine ⟨7310252530912734014000027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19494006749100624037333405 7310252530912734014000027)
        ·
          refine ⟨10965378796369101021000041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310252530912734014000027 10965378796369101021000041)
          ·
            refine ⟨8224034097276825765750031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10965378796369101021000041 8224034097276825765750031)
            ·
              refine ⟨12336051145915238648625047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224034097276825765750031 12336051145915238648625047)
              ·
                refine ⟨18504076718872857972937571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336051145915238648625047 18504076718872857972937571)
                ·
                  refine ⟨27756115078309286959406357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504076718872857972937571 27756115078309286959406357)
                  ·
                    refine ⟨1301067894295747826222173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27756115078309286959406357 1301067894295747826222173)
                    ·
                      rfl

theorem cell23_7601462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7601462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601462 prefixEnd_7601462 := by exact prefixLift 7601462
  have htrace : WordTrace (prefixWord ++ tailWord_7601462) baseStart_7601462 baseEnd_7601462 := by
    simpa [prefixWord, tailWord_7601462, baseEnd_7601462] using wordTrace_append hprefix tailTrace_7601462
  have hstable : (prefixWord ++ tailWord_7601462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601462).length < 2 ^ (prefixWord ++ tailWord_7601462).sum := by decide
  have hdescent : baseEnd_7601462 < baseStart_7601462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601465 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7601465 : Nat := 118140960795 + 7601465 * 2 ^ 59
def prefixEnd_7601465 : Nat := 4983230072969 + 3 ^ 40 * 7601465 * 2
def baseEnd_7601465 : Nat := 3903205223329206966929005

theorem tailTrace_7601465 : CollatzResearch.WordTrace tailWord_7601465 prefixEnd_7601465 3903205223329206966929005 := by
  unfold tailWord_7601465
  simp only [CollatzResearch.WordTrace]
  refine ⟨277248205406198006709989849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184832136937465337806659899 277248205406198006709989849)
  ·
    refine ⟨207936154054648505032492387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277248205406198006709989849 207936154054648505032492387)
    ·
      refine ⟨311904231081972757548738581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207936154054648505032492387 311904231081972757548738581)
      ·
        refine ⟨14620510831967473010097121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 311904231081972757548738581 14620510831967473010097121)
        ·
          refine ⟨10965383123975604757572841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14620510831967473010097121 10965383123975604757572841)
          ·
            refine ⟨8224037342981703568179631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10965383123975604757572841 8224037342981703568179631)
            ·
              refine ⟨12336056014472555352269447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224037342981703568179631 12336056014472555352269447)
              ·
                refine ⟨18504084021708833028404171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336056014472555352269447 18504084021708833028404171)
                ·
                  refine ⟨27756126032563249542606257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504084021708833028404171 27756126032563249542606257)
                  ·
                    refine ⟨20817094524422437156954693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27756126032563249542606257 20817094524422437156954693)
                    ·
                      refine ⟨3903205223329206966929005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20817094524422437156954693 3903205223329206966929005)
                      ·
                        rfl

theorem cell23_7601465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7601465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601465 prefixEnd_7601465 := by exact prefixLift 7601465
  have htrace : WordTrace (prefixWord ++ tailWord_7601465) baseStart_7601465 baseEnd_7601465 := by
    simpa [prefixWord, tailWord_7601465, baseEnd_7601465] using wordTrace_append hprefix tailTrace_7601465
  have hstable : (prefixWord ++ tailWord_7601465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601465).length < 2 ^ (prefixWord ++ tailWord_7601465).sum := by decide
  have hdescent : baseEnd_7601465 < baseStart_7601465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601468 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_7601468 : Nat := 118140960795 + 7601468 * 2 ^ 59
def prefixEnd_7601468 : Nat := 4983230072969 + 3 ^ 40 * 7601468 * 2
def baseEnd_7601468 : Nat := 3903206763771170455191491

theorem tailTrace_7601468 : CollatzResearch.WordTrace tailWord_7601468 prefixEnd_7601468 3903206763771170455191491 := by
  unfold tailWord_7601468
  simp only [CollatzResearch.WordTrace]
  refine ⟨138624157412593569111174529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184832209883458092148232705 138624157412593569111174529)
  ·
    refine ⟨103968118059445176833380897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138624157412593569111174529 103968118059445176833380897)
    ·
      refine ⟨77976088544583882625035673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103968118059445176833380897 77976088544583882625035673)
      ·
        refine ⟨58482066408437911968776755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77976088544583882625035673 58482066408437911968776755)
        ·
          refine ⟨87723099612656867953165133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58482066408437911968776755 87723099612656867953165133)
          ·
            refine ⟨32896162354746325482436925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87723099612656867953165133 32896162354746325482436925)
            ·
              refine ⟨12336060883029872055913847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32896162354746325482436925 12336060883029872055913847)
              ·
                refine ⟨18504091324544808083870771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336060883029872055913847 18504091324544808083870771)
                ·
                  refine ⟨27756136986817212125806157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18504091324544808083870771 27756136986817212125806157)
                  ·
                    refine ⟨10408551370056454547177309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27756136986817212125806157 10408551370056454547177309)
                    ·
                      refine ⟨3903206763771170455191491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408551370056454547177309 3903206763771170455191491)
                      ·
                        rfl

theorem cell23_7601468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_7601468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601468 prefixEnd_7601468 := by exact prefixLift 7601468
  have htrace : WordTrace (prefixWord ++ tailWord_7601468) baseStart_7601468 baseEnd_7601468 := by
    simpa [prefixWord, tailWord_7601468, baseEnd_7601468] using wordTrace_append hprefix tailTrace_7601468
  have hstable : (prefixWord ++ tailWord_7601468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601468).length < 2 ^ (prefixWord ++ tailWord_7601468).sum := by decide
  have hdescent : baseEnd_7601468 < baseStart_7601468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601495 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 1, 3, 2]
def baseStart_7601495 : Nat := 118140960795 + 7601495 * 2 ^ 59
def prefixEnd_7601495 : Nat := 4983230072969 + 3 ^ 40 * 7601495 * 2
def baseEnd_7601495 : Nat := 3903220627748841849553867

theorem tailTrace_7601495 : CollatzResearch.WordTrace tailWord_7601495 prefixEnd_7601495 3903220627748841849553867 := by
  unfold tailWord_7601495
  simp only [CollatzResearch.WordTrace]
  refine ⟨277249299596089321833581939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184832866397392881222387959 277249299596089321833581939)
  ·
    refine ⟨415873949394133982750372909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277249299596089321833581939 415873949394133982750372909)
    ·
      refine ⟨155952731022800243531389841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415873949394133982750372909 155952731022800243531389841)
      ·
        refine ⟨116964548267100182648542381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155952731022800243531389841 116964548267100182648542381)
        ·
          refine ⟨43861705600162568493203393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116964548267100182648542381 43861705600162568493203393)
          ·
            refine ⟨32896279200121926369902545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43861705600162568493203393 32896279200121926369902545)
            ·
              refine ⟨24672209400091444777426909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32896279200121926369902545 24672209400091444777426909)
              ·
                refine ⟨9252078525034291791535091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24672209400091444777426909 9252078525034291791535091)
                ·
                  refine ⟨13878117787551437687302637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9252078525034291791535091 13878117787551437687302637)
                  ·
                    refine ⟨5204294170331789132738489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13878117787551437687302637 5204294170331789132738489)
                    ·
                      refine ⟨3903220627748841849553867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204294170331789132738489 3903220627748841849553867)
                      ·
                        rfl

theorem cell23_7601495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_7601495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601495 prefixEnd_7601495 := by exact prefixLift 7601495
  have htrace : WordTrace (prefixWord ++ tailWord_7601495) baseStart_7601495 baseEnd_7601495 := by
    simpa [prefixWord, tailWord_7601495, baseEnd_7601495] using wordTrace_append hprefix tailTrace_7601495
  have hstable : (prefixWord ++ tailWord_7601495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601495).length < 2 ^ (prefixWord ++ tailWord_7601495).sum := by decide
  have hdescent : baseEnd_7601495 < baseStart_7601495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601521 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_7601521 : Nat := 118140960795 + 7601521 * 2 ^ 59
def prefixEnd_7601521 : Nat := 4983230072969 + 3 ^ 40 * 7601521 * 2
def baseEnd_7601521 : Nat := 3903233978245858747828747

theorem tailTrace_7601521 : CollatzResearch.WordTrace tailWord_7601521 prefixEnd_7601521 3903233978245858747828747 := by
  unfold tailWord_7601521
  simp only [CollatzResearch.WordTrace]
  refine ⟨277250247893995128274028417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184833498595996752182685611 277250247893995128274028417)
  ·
    refine ⟨207937685920496346205521313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277250247893995128274028417 207937685920496346205521313)
    ·
      refine ⟨155953264440372259654140985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207937685920496346205521313 155953264440372259654140985)
      ·
        refine ⟨116964948330279194740605739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155953264440372259654140985 116964948330279194740605739)
        ·
          refine ⟨175447422495418792110908609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116964948330279194740605739 175447422495418792110908609)
          ·
            refine ⟨131585566871564094083181457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175447422495418792110908609 131585566871564094083181457)
            ·
              refine ⟨98689175153673070562386093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131585566871564094083181457 98689175153673070562386093)
              ·
                refine ⟨37008440682627401460894785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98689175153673070562386093 37008440682627401460894785)
                ·
                  refine ⟨27756330511970551095671089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37008440682627401460894785 27756330511970551095671089)
                  ·
                    refine ⟨20817247883977913321753317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27756330511970551095671089 20817247883977913321753317)
                    ·
                      refine ⟨3903233978245858747828747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20817247883977913321753317 3903233978245858747828747)
                      ·
                        rfl

theorem cell23_7601521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_7601521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601521 prefixEnd_7601521 := by exact prefixLift 7601521
  have htrace : WordTrace (prefixWord ++ tailWord_7601521) baseStart_7601521 baseEnd_7601521 := by
    simpa [prefixWord, tailWord_7601521, baseEnd_7601521] using wordTrace_append hprefix tailTrace_7601521
  have hstable : (prefixWord ++ tailWord_7601521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601521).length < 2 ^ (prefixWord ++ tailWord_7601521).sum := by decide
  have hdescent : baseEnd_7601521 < baseStart_7601521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601548 : List Nat := [2, 2, 1, 2, 1, 3, 2, 5, 5]
def baseStart_7601548 : Nat := 118140960795 + 7601548 * 2 ^ 59
def prefixEnd_7601548 : Nat := 4983230072969 + 3 ^ 40 * 7601548 * 2
def baseEnd_7601548 : Nat := 433694204691503349132347

theorem tailTrace_7601548 : CollatzResearch.WordTrace tailWord_7601548 prefixEnd_7601548 433694204691503349132347 := by
  unfold tailWord_7601548
  simp only [CollatzResearch.WordTrace]
  refine ⟨138625616332448655942630649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184834155109931541256840865 138625616332448655942630649)
  ·
    refine ⟨103969212249336491956972987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138625616332448655942630649 103969212249336491956972987)
    ·
      refine ⟨155953818374004737935459481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103969212249336491956972987 155953818374004737935459481)
      ·
        refine ⟨116965363780503553451594611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155953818374004737935459481 116965363780503553451594611)
        ·
          refine ⟨175448045670755330177391917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116965363780503553451594611 175448045670755330177391917)
          ·
            refine ⟨65793017126533248816521969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175448045670755330177391917 65793017126533248816521969)
            ·
              refine ⟨49344762844899936612391477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65793017126533248816521969 49344762844899936612391477)
              ·
                refine ⟨4626071516709369057411701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49344762844899936612391477 4626071516709369057411701)
                ·
                  refine ⟨433694204691503349132347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4626071516709369057411701 433694204691503349132347)
                  ·
                    rfl

theorem cell23_7601548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_7601548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601548 prefixEnd_7601548 := by exact prefixLift 7601548
  have htrace : WordTrace (prefixWord ++ tailWord_7601548) baseStart_7601548 baseEnd_7601548 := by
    simpa [prefixWord, tailWord_7601548, baseEnd_7601548] using wordTrace_append hprefix tailTrace_7601548
  have hstable : (prefixWord ++ tailWord_7601548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601548).length < 2 ^ (prefixWord ++ tailWord_7601548).sum := by decide
  have hdescent : baseEnd_7601548 < baseStart_7601548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601565 : List Nat := [1, 4, 2, 1, 3, 2, 1, 4, 5]
def baseStart_7601565 : Nat := 118140960795 + 7601565 * 2 ^ 59
def prefixEnd_7601565 : Nat := 4983230072969 + 3 ^ 40 * 7601565 * 2
def baseEnd_7601565 : Nat := 433695174599406286186505

theorem tailTrace_7601565 : CollatzResearch.WordTrace tailWord_7601565 prefixEnd_7601565 433695174599406286186505 := by
  unfold tailWord_7601565
  simp only [CollatzResearch.WordTrace]
  refine ⟨277251852705835723788630149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184834568470557149192420099 277251852705835723788630149)
  ·
    refine ⟨51984722382344198210368153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277251852705835723788630149 51984722382344198210368153)
    ·
      refine ⟨38988541786758148657776115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51984722382344198210368153 38988541786758148657776115)
      ·
        refine ⟨58482812680137222986664173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38988541786758148657776115 58482812680137222986664173)
        ·
          refine ⟨21931054755051458619999065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58482812680137222986664173 21931054755051458619999065)
          ·
            refine ⟨16448291066288593964999299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21931054755051458619999065 16448291066288593964999299)
            ·
              refine ⟨24672436599432890947498949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16448291066288593964999299 24672436599432890947498949)
              ·
                refine ⟨4626081862393667052656053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24672436599432890947498949 4626081862393667052656053)
                ·
                  refine ⟨433695174599406286186505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4626081862393667052656053 433695174599406286186505)
                  ·
                    rfl

theorem cell23_7601565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_7601565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601565 prefixEnd_7601565 := by exact prefixLift 7601565
  have htrace : WordTrace (prefixWord ++ tailWord_7601565) baseStart_7601565 baseEnd_7601565 := by
    simpa [prefixWord, tailWord_7601565, baseEnd_7601565] using wordTrace_append hprefix tailTrace_7601565
  have hstable : (prefixWord ++ tailWord_7601565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601565).length < 2 ^ (prefixWord ++ tailWord_7601565).sum := by decide
  have hdescent : baseEnd_7601565 < baseStart_7601565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601568 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2]
def baseStart_7601568 : Nat := 118140960795 + 7601568 * 2 ^ 59
def prefixEnd_7601568 : Nat := 4983230072969 + 3 ^ 40 * 7601568 * 2
def baseEnd_7601568 : Nat := 3903258111836620063941031

theorem tailTrace_7601568 : CollatzResearch.WordTrace tailWord_7601568 prefixEnd_7601568 3903258111836620063941031 := by
  unfold tailWord_7601568
  simp only [CollatzResearch.WordTrace]
  refine ⟨138625981062412427650494679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184834641416549903533992905 138625981062412427650494679)
  ·
    refine ⟨207938971593618641475742019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138625981062412427650494679 207938971593618641475742019)
    ·
      refine ⟨311908457390427962213613029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207938971593618641475742019 311908457390427962213613029)
      ·
        refine ⟨58482835760705242915052443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311908457390427962213613029 58482835760705242915052443)
        ·
          refine ⟨87724253641057864372578665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58482835760705242915052443 87724253641057864372578665)
          ·
            refine ⟨65793190230793398279433999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87724253641057864372578665 65793190230793398279433999)
            ·
              refine ⟨98689785346190097419150999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65793190230793398279433999 98689785346190097419150999)
              ·
                refine ⟨148034678019285146128726499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98689785346190097419150999 148034678019285146128726499)
                ·
                  refine ⟨222052017028927719193089749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148034678019285146128726499 222052017028927719193089749)
                  ·
                    refine ⟨5204344149115493418588041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 222052017028927719193089749 5204344149115493418588041)
                    ·
                      refine ⟨3903258111836620063941031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204344149115493418588041 3903258111836620063941031)
                      ·
                        rfl

theorem cell23_7601568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_7601568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601568 prefixEnd_7601568 := by exact prefixLift 7601568
  have htrace : WordTrace (prefixWord ++ tailWord_7601568) baseStart_7601568 baseEnd_7601568 := by
    simpa [prefixWord, tailWord_7601568, baseEnd_7601568] using wordTrace_append hprefix tailTrace_7601568
  have hstable : (prefixWord ++ tailWord_7601568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601568).length < 2 ^ (prefixWord ++ tailWord_7601568).sum := by decide
  have hdescent : baseEnd_7601568 < baseStart_7601568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601571 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_7601571 : Nat := 118140960795 + 7601571 * 2 ^ 59
def prefixEnd_7601571 : Nat := 4983230072969 + 3 ^ 40 * 7601571 * 2
def baseEnd_7601571 : Nat := 3903259652278583552203517

theorem tailTrace_7601571 : CollatzResearch.WordTrace tailWord_7601571 prefixEnd_7601571 3903259652278583552203517 := by
  unfold tailWord_7601571
  simp only [CollatzResearch.WordTrace]
  refine ⟨277252071543813986813348567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184834714362542657875565711 277252071543813986813348567)
  ·
    refine ⟨415878107315720980220022851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277252071543813986813348567 415878107315720980220022851)
    ·
      refine ⟨623817160973581470330034277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415878107315720980220022851 623817160973581470330034277)
      ·
        refine ⟨116965717682546525686881427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623817160973581470330034277 116965717682546525686881427)
        ·
          refine ⟨175448576523819788530322141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116965717682546525686881427 175448576523819788530322141)
          ·
            refine ⟨65793216196432420698870803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175448576523819788530322141 65793216196432420698870803)
            ·
              refine ⟨98689824294648631048306205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65793216196432420698870803 98689824294648631048306205)
              ·
                refine ⟨37008684110493236643114827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98689824294648631048306205 37008684110493236643114827)
                ·
                  refine ⟨55513026165739854964672241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37008684110493236643114827 55513026165739854964672241)
                  ·
                    refine ⟨41634769624304891223504181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55513026165739854964672241 41634769624304891223504181)
                    ·
                      refine ⟨3903259652278583552203517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41634769624304891223504181 3903259652278583552203517)
                      ·
                        rfl

theorem cell23_7601571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_7601571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601571 prefixEnd_7601571 := by exact prefixLift 7601571
  have htrace : WordTrace (prefixWord ++ tailWord_7601571) baseStart_7601571 baseEnd_7601571 := by
    simpa [prefixWord, tailWord_7601571, baseEnd_7601571] using wordTrace_append hprefix tailTrace_7601571
  have hstable : (prefixWord ++ tailWord_7601571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601571).length < 2 ^ (prefixWord ++ tailWord_7601571).sum := by decide
  have hdescent : baseEnd_7601571 < baseStart_7601571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601608 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_7601608 : Nat := 118140960795 + 7601608 * 2 ^ 59
def prefixEnd_7601608 : Nat := 4983230072969 + 3 ^ 40 * 7601608 * 2
def baseEnd_7601608 : Nat := 1301092883687599969146949

theorem tailTrace_7601608 : CollatzResearch.WordTrace tailWord_7601608 prefixEnd_7601608 1301092883687599969146949 := by
  unfold tailWord_7601608
  simp only [CollatzResearch.WordTrace]
  refine ⟨138626710522339971066222739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184835614029786628088296985 138626710522339971066222739)
  ·
    refine ⟨207940065783509956599334109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138626710522339971066222739 207940065783509956599334109)
    ·
      refine ⟨77977524668816233724750291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207940065783509956599334109 77977524668816233724750291)
      ·
        refine ⟨116966287003224350587125437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77977524668816233724750291 116966287003224350587125437)
        ·
          refine ⟨43862357626209131470172039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116966287003224350587125437 43862357626209131470172039)
          ·
            refine ⟨65793536439313697205258059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43862357626209131470172039 65793536439313697205258059)
            ·
              refine ⟨98690304658970545807887089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65793536439313697205258059 98690304658970545807887089)
              ·
                refine ⟨74017728494227909355915317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98690304658970545807887089 74017728494227909355915317)
                ·
                  refine ⟨6939162046333866502117061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74017728494227909355915317 6939162046333866502117061)
                  ·
                    refine ⟨1301092883687599969146949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939162046333866502117061 1301092883687599969146949)
                    ·
                      rfl

theorem cell23_7601608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_7601608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601608 prefixEnd_7601608 := by exact prefixLift 7601608
  have htrace : WordTrace (prefixWord ++ tailWord_7601608) baseStart_7601608 baseEnd_7601608 := by
    simpa [prefixWord, tailWord_7601608, baseEnd_7601608] using wordTrace_append hprefix tailTrace_7601608
  have hstable : (prefixWord ++ tailWord_7601608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601608).length < 2 ^ (prefixWord ++ tailWord_7601608).sum := by decide
  have hdescent : baseEnd_7601608 < baseStart_7601608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601611 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_7601611 : Nat := 118140960795 + 7601611 * 2 ^ 59
def prefixEnd_7601611 : Nat := 4983230072969 + 3 ^ 40 * 7601611 * 2
def baseEnd_7601611 : Nat := 3903280191504763395703333

theorem tailTrace_7601611 : CollatzResearch.WordTrace tailWord_7601611 prefixEnd_7601611 3903280191504763395703333 := by
  unfold tailWord_7601611
  simp only [CollatzResearch.WordTrace]
  refine ⟨277253530463669073644804687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184835686975779382429869791 277253530463669073644804687)
  ·
    refine ⟨415880295695503610467207031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277253530463669073644804687 415880295695503610467207031)
    ·
      refine ⟨623820443543255415700810547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415880295695503610467207031 623820443543255415700810547)
      ·
        refine ⟨935730665314883123551215821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623820443543255415700810547 935730665314883123551215821)
        ·
          refine ⟨350898999493081171331705933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935730665314883123551215821 350898999493081171331705933)
          ·
            refine ⟨131587124809905439249389725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350898999493081171331705933 131587124809905439249389725)
            ·
              refine ⟨49345171803714539718521147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131587124809905439249389725 49345171803714539718521147)
              ·
                refine ⟨74017757705571809577781721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49345171803714539718521147 74017757705571809577781721)
                ·
                  refine ⟨55513318279178857183336291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74017757705571809577781721 55513318279178857183336291)
                  ·
                    refine ⟨83269977418768285775004437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55513318279178857183336291 83269977418768285775004437)
                    ·
                      refine ⟨3903280191504763395703333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83269977418768285775004437 3903280191504763395703333)
                      ·
                        rfl

theorem cell23_7601611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_7601611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601611 prefixEnd_7601611 := by exact prefixLift 7601611
  have htrace : WordTrace (prefixWord ++ tailWord_7601611) baseStart_7601611 baseEnd_7601611 := by
    simpa [prefixWord, tailWord_7601611, baseEnd_7601611] using wordTrace_append hprefix tailTrace_7601611
  have hstable : (prefixWord ++ tailWord_7601611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601611).length < 2 ^ (prefixWord ++ tailWord_7601611).sum := by decide
  have hdescent : baseEnd_7601611 < baseStart_7601611 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601625 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_7601625 : Nat := 118140960795 + 7601625 * 2 ^ 59
def prefixEnd_7601625 : Nat := 4983230072969 + 3 ^ 40 * 7601625 * 2
def baseEnd_7601625 : Nat := 1301095793411308780309423

theorem tailTrace_7601625 : CollatzResearch.WordTrace tailWord_7601625 prefixEnd_7601625 1301095793411308780309423 := by
  unfold tailWord_7601625
  simp only [CollatzResearch.WordTrace]
  refine ⟨277254041085618354035814329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184836027390412236023876219 277254041085618354035814329)
  ·
    refine ⟨207940530814213765526860747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277254041085618354035814329 207940530814213765526860747)
    ·
      refine ⟨311910796221320648290291121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207940530814213765526860747 311910796221320648290291121)
      ·
        refine ⟨233933097165990486217718341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311910796221320648290291121 233933097165990486217718341)
        ·
          refine ⟨43862455718623216165822189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233933097165990486217718341 43862455718623216165822189)
          ·
            refine ⟨16448420894483706062183321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43862455718623216165822189 16448420894483706062183321)
            ·
              refine ⟨12336315670862779546637491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16448420894483706062183321 12336315670862779546637491)
              ·
                refine ⟨18504473506294169319956237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336315670862779546637491 18504473506294169319956237)
                ·
                  refine ⟨6939177564860313494983589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18504473506294169319956237 6939177564860313494983589)
                  ·
                    refine ⟨1301095793411308780309423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939177564860313494983589 1301095793411308780309423)
                    ·
                      rfl

theorem cell23_7601625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_7601625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601625 prefixEnd_7601625 := by exact prefixLift 7601625
  have htrace : WordTrace (prefixWord ++ tailWord_7601625) baseStart_7601625 baseEnd_7601625 := by
    simpa [prefixWord, tailWord_7601625, baseEnd_7601625] using wordTrace_append hprefix tailTrace_7601625
  have hstable : (prefixWord ++ tailWord_7601625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601625).length < 2 ^ (prefixWord ++ tailWord_7601625).sum := by decide
  have hdescent : baseEnd_7601625 < baseStart_7601625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601722 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4]
def baseStart_7601722 : Nat := 118140960795 + 7601722 * 2 ^ 59
def prefixEnd_7601722 : Nat := 4983230072969 + 3 ^ 40 * 7601722 * 2
def baseEnd_7601722 : Nat := 3903337187857412461415323

theorem tailTrace_7601722 : CollatzResearch.WordTrace tailWord_7601722 prefixEnd_7601722 3903337187857412461415323 := by
  unfold tailWord_7601722
  simp only [CollatzResearch.WordTrace]
  refine ⟨69314394741566734900523855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184838385977511293068063613 69314394741566734900523855)
  ·
    refine ⟨103971592112350102350785783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69314394741566734900523855 103971592112350102350785783)
    ·
      refine ⟨155957388168525153526178675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103971592112350102350785783 155957388168525153526178675)
      ·
        refine ⟨233936082252787730289268013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155957388168525153526178675 233936082252787730289268013)
        ·
          refine ⟨87726030844795398858475505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233936082252787730289268013 87726030844795398858475505)
          ·
            refine ⟨65794523133596549143856629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87726030844795398858475505 65794523133596549143856629)
            ·
              refine ⟨6168236543774676482236559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65794523133596549143856629 6168236543774676482236559)
              ·
                refine ⟨9252354815662014723354839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6168236543774676482236559 9252354815662014723354839)
                ·
                  refine ⟨13878532223493022085032259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9252354815662014723354839 13878532223493022085032259)
                  ·
                    refine ⟨20817798335239533127548389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13878532223493022085032259 20817798335239533127548389)
                    ·
                      refine ⟨3903337187857412461415323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20817798335239533127548389 3903337187857412461415323)
                      ·
                        rfl

theorem cell23_7601722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_7601722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601722 prefixEnd_7601722 := by exact prefixLift 7601722
  have htrace : WordTrace (prefixWord ++ tailWord_7601722) baseStart_7601722 baseEnd_7601722 := by
    simpa [prefixWord, tailWord_7601722, baseEnd_7601722] using wordTrace_append hprefix tailTrace_7601722
  have hstable : (prefixWord ++ tailWord_7601722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601722).length < 2 ^ (prefixWord ++ tailWord_7601722).sum := by decide
  have hdescent : baseEnd_7601722 < baseStart_7601722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601773 : List Nat := [1, 5, 1, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_7601773 : Nat := 118140960795 + 7601773 * 2 ^ 59
def prefixEnd_7601773 : Nat := 4983230072969 + 3 ^ 40 * 7601773 * 2
def baseEnd_7601773 : Nat := 3903363375370791761877589

theorem tailTrace_7601773 : CollatzResearch.WordTrace tailWord_7601773 prefixEnd_7601773 3903363375370791761877589 := by
  unfold tailWord_7601773
  simp only [CollatzResearch.WordTrace]
  refine ⟨277259439089082175312201973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184839626059388116874801315 277259439089082175312201973)
  ·
    refine ⟨25993072414601453935518935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277259439089082175312201973 25993072414601453935518935)
    ·
      refine ⟨38989608621902180903278403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25993072414601453935518935 38989608621902180903278403)
      ·
        refine ⟨58484412932853271354917605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38989608621902180903278403 58484412932853271354917605)
        ·
          refine ⟨10965827424909988379047051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58484412932853271354917605 10965827424909988379047051)
          ·
            refine ⟨16448741137364982568570577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10965827424909988379047051 16448741137364982568570577)
            ·
              refine ⟨12336555853023736926427933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16448741137364982568570577 12336555853023736926427933)
              ·
                refine ⟨4626208444883901347410475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12336555853023736926427933 4626208444883901347410475)
                ·
                  refine ⟨6939312667325852021115713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626208444883901347410475 6939312667325852021115713)
                  ·
                    refine ⟨5204484500494389015836785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939312667325852021115713 5204484500494389015836785)
                    ·
                      refine ⟨3903363375370791761877589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204484500494389015836785 3903363375370791761877589)
                      ·
                        rfl

theorem cell23_7601773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_7601773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601773 prefixEnd_7601773 := by exact prefixLift 7601773
  have htrace : WordTrace (prefixWord ++ tailWord_7601773) baseStart_7601773 baseEnd_7601773 := by
    simpa [prefixWord, tailWord_7601773, baseEnd_7601773] using wordTrace_append hprefix tailTrace_7601773
  have hstable : (prefixWord ++ tailWord_7601773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601773).length < 2 ^ (prefixWord ++ tailWord_7601773).sum := by decide
  have hdescent : baseEnd_7601773 < baseStart_7601773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601789 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_7601789 : Nat := 118140960795 + 7601789 * 2 ^ 59
def prefixEnd_7601789 : Nat := 4983230072969 + 3 ^ 40 * 7601789 * 2
def baseEnd_7601789 : Nat := 3903371591061263699277515

theorem tailTrace_7601789 : CollatzResearch.WordTrace tailWord_7601789 prefixEnd_7601789 3903371591061263699277515 := by
  unfold tailWord_7601789
  simp only [CollatzResearch.WordTrace]
  refine ⟨277260022657024210044784421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184840015104682806696522947 277260022657024210044784421)
  ·
    refine ⟨51986254248192039383397079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277260022657024210044784421 51986254248192039383397079)
    ·
      refine ⟨77979381372288059075095619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51986254248192039383397079 77979381372288059075095619)
      ·
        refine ⟨116969072058432088612643429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77979381372288059075095619 116969072058432088612643429)
        ·
          refine ⟨21931701010956016614870643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116969072058432088612643429 21931701010956016614870643)
          ·
            refine ⟨32897551516434024922305965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21931701010956016614870643 32897551516434024922305965)
            ·
              refine ⟨12336581818662759345864737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32897551516434024922305965 12336581818662759345864737)
              ·
                refine ⟨9252436363997069509398553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12336581818662759345864737 9252436363997069509398553)
                ·
                  refine ⟨6939327272997802132048915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9252436363997069509398553 6939327272997802132048915)
                  ·
                    refine ⟨10408990909496703198073373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939327272997802132048915 10408990909496703198073373)
                    ·
                      refine ⟨3903371591061263699277515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10408990909496703198073373 3903371591061263699277515)
                      ·
                        rfl

theorem cell23_7601789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_7601789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601789 prefixEnd_7601789 := by exact prefixLift 7601789
  have htrace : WordTrace (prefixWord ++ tailWord_7601789) baseStart_7601789 baseEnd_7601789 := by
    simpa [prefixWord, tailWord_7601789, baseEnd_7601789] using wordTrace_append hprefix tailTrace_7601789
  have hstable : (prefixWord ++ tailWord_7601789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601789).length < 2 ^ (prefixWord ++ tailWord_7601789).sum := by decide
  have hdescent : baseEnd_7601789 < baseStart_7601789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601806 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_7601806 : Nat := 118140960795 + 7601806 * 2 ^ 59
def prefixEnd_7601806 : Nat := 4983230072969 + 3 ^ 40 * 7601806 * 2
def baseEnd_7601806 : Nat := 3903380320232390132764937

theorem tailTrace_7601806 : CollatzResearch.WordTrace tailWord_7601806 prefixEnd_7601806 3903380320232390132764937 := by
  unfold tailWord_7601806
  simp only [CollatzResearch.WordTrace]
  refine ⟨34657580337245327743519159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184840428465308414632102181 34657580337245327743519159)
  ·
    refine ⟨51986370505867991615278739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34657580337245327743519159 51986370505867991615278739)
    ·
      refine ⟨77979555758801987422918109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51986370505867991615278739 77979555758801987422918109)
      ·
        refine ⟨29242333409550745283594291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77979555758801987422918109 29242333409550745283594291)
        ·
          refine ⟨43863500114326117925391437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29242333409550745283594291 43863500114326117925391437)
          ·
            refine ⟨16448812542872294222021789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43863500114326117925391437 16448812542872294222021789)
            ·
              refine ⟨6168304703577110333258171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16448812542872294222021789 6168304703577110333258171)
              ·
                refine ⟨9252457055365665499887257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6168304703577110333258171 9252457055365665499887257)
                ·
                  refine ⟨6939342791524249124915443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9252457055365665499887257 6939342791524249124915443)
                  ·
                    refine ⟨10409014187286373687373165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939342791524249124915443 10409014187286373687373165)
                    ·
                      refine ⟨3903380320232390132764937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409014187286373687373165 3903380320232390132764937)
                      ·
                        rfl

theorem cell23_7601806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_7601806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601806 prefixEnd_7601806 := by exact prefixLift 7601806
  have htrace : WordTrace (prefixWord ++ tailWord_7601806) baseStart_7601806 baseEnd_7601806 := by
    simpa [prefixWord, tailWord_7601806, baseEnd_7601806] using wordTrace_append hprefix tailTrace_7601806
  have hstable : (prefixWord ++ tailWord_7601806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601806).length < 2 ^ (prefixWord ++ tailWord_7601806).sum := by decide
  have hdescent : baseEnd_7601806 < baseStart_7601806 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601852 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 7]
def baseStart_7601852 : Nat := 118140960795 + 7601852 * 2 ^ 59
def prefixEnd_7601852 : Nat := 4983230072969 + 3 ^ 40 * 7601852 * 2
def baseEnd_7601852 : Nat := 433711548926944105865525

theorem tailTrace_7601852 : CollatzResearch.WordTrace tailWord_7601852 prefixEnd_7601852 433711548926944105865525 := by
  unfold tailWord_7601852
  simp only [CollatzResearch.WordTrace]
  refine ⟨138631160227897985902163905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184841546970530647869551873 138631160227897985902163905)
  ·
    refine ⟨103973370170923489426622929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138631160227897985902163905 103973370170923489426622929)
    ·
      refine ⟨77980027628192617069967197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103973370170923489426622929 77980027628192617069967197)
      ·
        refine ⟨29242510360572231401237699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77980027628192617069967197 29242510360572231401237699)
        ·
          refine ⟨43863765540858347101856549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29242510360572231401237699 43863765540858347101856549)
          ·
            refine ⟨8224456038910940081598103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43863765540858347101856549 8224456038910940081598103)
            ·
              refine ⟨12336684058366410122397155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8224456038910940081598103 12336684058366410122397155)
              ·
                refine ⟨18505026087549615183595733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336684058366410122397155 18505026087549615183595733)
                ·
                  refine ⟨433711548926944105865525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18505026087549615183595733 433711548926944105865525)
                  ·
                    rfl

theorem cell23_7601852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_7601852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601852 prefixEnd_7601852 := by exact prefixLift 7601852
  have htrace : WordTrace (prefixWord ++ tailWord_7601852) baseStart_7601852 baseEnd_7601852 := by
    simpa [prefixWord, tailWord_7601852, baseEnd_7601852] using wordTrace_append hprefix tailTrace_7601852
  have hstable : (prefixWord ++ tailWord_7601852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601852).length < 2 ^ (prefixWord ++ tailWord_7601852).sum := by decide
  have hdescent : baseEnd_7601852 < baseStart_7601852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601882 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_7601882 : Nat := 118140960795 + 7601882 * 2 ^ 59
def prefixEnd_7601882 : Nat := 4983230072969 + 3 ^ 40 * 7601882 * 2
def baseEnd_7601882 : Nat := 1301139781587377278471529

theorem tailTrace_7601882 : CollatzResearch.WordTrace tailWord_7601882 prefixEnd_7601882 1301139781587377278471529 := by
  unfold tailWord_7601882
  simp only [CollatzResearch.WordTrace]
  refine ⟨69315853661421821731979975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184842276430458191285279933 69315853661421821731979975)
  ·
    refine ⟨103973780492132732597969963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69315853661421821731979975 103973780492132732597969963)
    ·
      refine ⟨155960670738199098896954945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103973780492132732597969963 155960670738199098896954945)
      ·
        refine ⟨116970503053649324172716209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155960670738199098896954945 116970503053649324172716209)
        ·
          refine ⟨87727877290236993129537157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116970503053649324172716209 87727877290236993129537157)
          ·
            refine ⟨16448976991919436211788217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87727877290236993129537157 16448976991919436211788217)
            ·
              refine ⟨12336732743939577158841163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16448976991919436211788217 12336732743939577158841163)
              ·
                refine ⟨18505099115909365738261745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12336732743939577158841163 18505099115909365738261745)
                ·
                  refine ⟨13878824336932024303696309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18505099115909365738261745 13878824336932024303696309)
                  ·
                    refine ⟨1301139781587377278471529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13878824336932024303696309 1301139781587377278471529)
                    ·
                      rfl

theorem cell23_7601882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_7601882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601882 prefixEnd_7601882 := by exact prefixLift 7601882
  have htrace : WordTrace (prefixWord ++ tailWord_7601882) baseStart_7601882 baseEnd_7601882 := by
    simpa [prefixWord, tailWord_7601882, baseEnd_7601882] using wordTrace_append hprefix tailTrace_7601882
  have hstable : (prefixWord ++ tailWord_7601882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601882).length < 2 ^ (prefixWord ++ tailWord_7601882).sum := by decide
  have hdescent : baseEnd_7601882 < baseStart_7601882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601902 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_7601902 : Nat := 118140960795 + 7601902 * 2 ^ 59
def prefixEnd_7601902 : Nat := 4983230072969 + 3 ^ 40 * 7601902 * 2
def baseEnd_7601902 : Nat := 3903429614375221757164495

theorem tailTrace_7601902 : CollatzResearch.WordTrace tailWord_7601902 prefixEnd_7601902 3903429614375221757164495 := by
  unfold tailWord_7601902
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658018013201853792955995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184842762737076553562431973 34658018013201853792955995)
  ·
    refine ⟨51987027019802780689433993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34658018013201853792955995 51987027019802780689433993)
    ·
      refine ⟨38990270264852085517075495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51987027019802780689433993 38990270264852085517075495)
      ·
        refine ⟨58485405397278128275613243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38990270264852085517075495 58485405397278128275613243)
        ·
          refine ⟨87728108095917192413419865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58485405397278128275613243 87728108095917192413419865)
          ·
            refine ⟨65796081071937894310064899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87728108095917192413419865 65796081071937894310064899)
            ·
              refine ⟨98694121607906841465097349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65796081071937894310064899 98694121607906841465097349)
              ·
                refine ⟨18505147801482532774705753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98694121607906841465097349 18505147801482532774705753)
                ·
                  refine ⟨13878860851111899581029315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18505147801482532774705753 13878860851111899581029315)
                  ·
                    refine ⟨20818291276667849371543973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13878860851111899581029315 20818291276667849371543973)
                    ·
                      refine ⟨3903429614375221757164495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20818291276667849371543973 3903429614375221757164495)
                      ·
                        rfl

theorem cell23_7601902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_7601902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601902 prefixEnd_7601902 := by exact prefixLift 7601902
  have htrace : WordTrace (prefixWord ++ tailWord_7601902) baseStart_7601902 baseEnd_7601902 := by
    simpa [prefixWord, tailWord_7601902, baseEnd_7601902] using wordTrace_append hprefix tailTrace_7601902
  have hstable : (prefixWord ++ tailWord_7601902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601902).length < 2 ^ (prefixWord ++ tailWord_7601902).sum := by decide
  have hdescent : baseEnd_7601902 < baseStart_7601902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601933 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_7601933 : Nat := 118140960795 + 7601933 * 2 ^ 59
def prefixEnd_7601933 : Nat := 4983230072969 + 3 ^ 40 * 7601933 * 2
def baseEnd_7601933 : Nat := 1301148510758503711958951

theorem tailTrace_7601933 : CollatzResearch.WordTrace tailWord_7601933 prefixEnd_7601933 1301148510758503711958951 := by
  unfold tailWord_7601933
  simp only [CollatzResearch.WordTrace]
  refine ⟨277265274768502522638026453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184843516512335015092017635 277265274768502522638026453)
  ·
    refine ⟨6498404877386777874328745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277265274768502522638026453 6498404877386777874328745)
    ·
      refine ⟨4873803658040083405746559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6498404877386777874328745 4873803658040083405746559)
      ·
        refine ⟨7310705487060125108619839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4873803658040083405746559 7310705487060125108619839)
        ·
          refine ⟨10966058230590187662929759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310705487060125108619839 10966058230590187662929759)
          ·
            refine ⟨16449087345885281494394639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966058230590187662929759 16449087345885281494394639)
            ·
              refine ⟨24673631018827922241591959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16449087345885281494394639 24673631018827922241591959)
              ·
                refine ⟨37010446528241883362387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24673631018827922241591959 37010446528241883362387939)
                ·
                  refine ⟨55515669792362825043581909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37010446528241883362387939 55515669792362825043581909)
                  ·
                    refine ⟨1301148510758503711958951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55515669792362825043581909 1301148510758503711958951)
                    ·
                      rfl

theorem cell23_7601933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_7601933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601933 prefixEnd_7601933 := by exact prefixLift 7601933
  have htrace : WordTrace (prefixWord ++ tailWord_7601933) baseStart_7601933 baseEnd_7601933 := by
    simpa [prefixWord, tailWord_7601933, baseEnd_7601933] using wordTrace_append hprefix tailTrace_7601933
  have hstable : (prefixWord ++ tailWord_7601933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601933).length < 2 ^ (prefixWord ++ tailWord_7601933).sum := by decide
  have hdescent : baseEnd_7601933 < baseStart_7601933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601935 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_7601935 : Nat := 118140960795 + 7601935 * 2 ^ 59
def prefixEnd_7601935 : Nat := 4983230072969 + 3 ^ 40 * 7601935 * 2
def baseEnd_7601935 : Nat := 3903446559236820128051843

theorem tailTrace_7601935 : CollatzResearch.WordTrace tailWord_7601935 prefixEnd_7601935 3903446559236820128051843 := by
  unfold tailWord_7601935
  simp only [CollatzResearch.WordTrace]
  refine ⟨277265347714495276979599259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184843565142996851319732839 277265347714495276979599259)
  ·
    refine ⟨415898021571742915469398889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277265347714495276979599259 415898021571742915469398889)
    ·
      refine ⟨311923516178807186602049167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415898021571742915469398889 311923516178807186602049167)
      ·
        refine ⟨467885274268210779903073751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311923516178807186602049167 467885274268210779903073751)
        ·
          refine ⟨701827911402316169854610627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467885274268210779903073751 701827911402316169854610627)
          ·
            refine ⟨1052741867103474254781915941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701827911402316169854610627 1052741867103474254781915941)
            ·
              refine ⟨197389100081901422771609239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1052741867103474254781915941 197389100081901422771609239)
              ·
                refine ⟨296083650122852134157413859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197389100081901422771609239 296083650122852134157413859)
                ·
                  refine ⟨444125475184278201236120789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296083650122852134157413859 444125475184278201236120789)
                  ·
                    refine ⟨10409190824631520341471581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 444125475184278201236120789 10409190824631520341471581)
                    ·
                      refine ⟨3903446559236820128051843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409190824631520341471581 3903446559236820128051843)
                      ·
                        rfl

theorem cell23_7601935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_7601935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601935 prefixEnd_7601935 := by exact prefixLift 7601935
  have htrace : WordTrace (prefixWord ++ tailWord_7601935) baseStart_7601935 baseEnd_7601935 := by
    simpa [prefixWord, tailWord_7601935, baseEnd_7601935] using wordTrace_append hprefix tailTrace_7601935
  have hstable : (prefixWord ++ tailWord_7601935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601935).length < 2 ^ (prefixWord ++ tailWord_7601935).sum := by decide
  have hdescent : baseEnd_7601935 < baseStart_7601935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601946 : List Nat := [3, 1, 1, 3, 2, 3, 2, 3, 1, 4]
def baseStart_7601946 : Nat := 118140960795 + 7601946 * 2 ^ 59
def prefixEnd_7601946 : Nat := 4983230072969 + 3 ^ 40 * 7601946 * 2
def baseEnd_7601946 : Nat := 1301150735841339861671431

theorem tailTrace_7601946 : CollatzResearch.WordTrace tailWord_7601946 prefixEnd_7601946 1301150735841339861671431 := by
  unfold tailWord_7601946
  simp only [CollatzResearch.WordTrace]
  refine ⟨69316437229363856464562423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184843832611636950572166461 69316437229363856464562423)
  ·
    refine ⟨103974655844045784696843635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69316437229363856464562423 103974655844045784696843635)
    ·
      refine ⟨155961983766068677045265453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103974655844045784696843635 155961983766068677045265453)
      ·
        refine ⟨58485743912275753891974545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155961983766068677045265453 58485743912275753891974545)
        ·
          refine ⟨43864307934206815418980909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58485743912275753891974545 43864307934206815418980909)
          ·
            refine ⟨16449115475327555782117841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43864307934206815418980909 16449115475327555782117841)
            ·
              refine ⟨12336836606495666836588381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16449115475327555782117841 12336836606495666836588381)
              ·
                refine ⟨4626313727435875063720643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12336836606495666836588381 4626313727435875063720643)
                ·
                  refine ⟨6939470591153812595580965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626313727435875063720643 6939470591153812595580965)
                  ·
                    refine ⟨1301150735841339861671431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939470591153812595580965 1301150735841339861671431)
                    ·
                      rfl

theorem cell23_7601946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_7601946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601946 prefixEnd_7601946 := by exact prefixLift 7601946
  have htrace : WordTrace (prefixWord ++ tailWord_7601946) baseStart_7601946 baseEnd_7601946 := by
    simpa [prefixWord, tailWord_7601946, baseEnd_7601946] using wordTrace_append hprefix tailTrace_7601946
  have hstable : (prefixWord ++ tailWord_7601946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601946).length < 2 ^ (prefixWord ++ tailWord_7601946).sum := by decide
  have hdescent : baseEnd_7601946 < baseStart_7601946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601969 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_7601969 : Nat := 118140960795 + 7601969 * 2 ^ 59
def prefixEnd_7601969 : Nat := 4983230072969 + 3 ^ 40 * 7601969 * 2
def baseEnd_7601969 : Nat := 3903464017579072995026687

theorem tailTrace_7601969 : CollatzResearch.WordTrace tailWord_7601969 prefixEnd_7601969 3903464017579072995026687 := by
  unfold tailWord_7601969
  simp only [CollatzResearch.WordTrace]
  refine ⟨277266587796372100786336961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184844391864248067190891307 277266587796372100786336961)
  ·
    refine ⟨207949940847279075589752721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277266587796372100786336961 207949940847279075589752721)
    ·
      refine ⟨155962455635459306692314541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207949940847279075589752721 155962455635459306692314541)
      ·
        refine ⟨58485920863297240009617953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155962455635459306692314541 58485920863297240009617953)
        ·
          refine ⟨43864440647472930007213465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58485920863297240009617953 43864440647472930007213465)
          ·
            refine ⟨32898330485604697505410099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43864440647472930007213465 32898330485604697505410099)
            ·
              refine ⟨49347495728407046258115149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32898330485604697505410099 49347495728407046258115149)
              ·
                refine ⟨18505310898152642346793181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49347495728407046258115149 18505310898152642346793181)
                ·
                  refine ⟨6939491586807240880047443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18505310898152642346793181 6939491586807240880047443)
                  ·
                    refine ⟨10409237380210861320071165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939491586807240880047443 10409237380210861320071165)
                    ·
                      refine ⟨3903464017579072995026687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409237380210861320071165 3903464017579072995026687)
                      ·
                        rfl

theorem cell23_7601969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_7601969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601969 prefixEnd_7601969 := by exact prefixLift 7601969
  have htrace : WordTrace (prefixWord ++ tailWord_7601969) baseStart_7601969 baseEnd_7601969 := by
    simpa [prefixWord, tailWord_7601969, baseEnd_7601969] using wordTrace_append hprefix tailTrace_7601969
  have hstable : (prefixWord ++ tailWord_7601969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601969).length < 2 ^ (prefixWord ++ tailWord_7601969).sum := by decide
  have hdescent : baseEnd_7601969 < baseStart_7601969 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7601975 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_7601975 : Nat := 118140960795 + 7601975 * 2 ^ 59
def prefixEnd_7601975 : Nat := 4983230072969 + 3 ^ 40 * 7601975 * 2
def baseEnd_7601975 : Nat := 3903467098462999971551659

theorem tailTrace_7601975 : CollatzResearch.WordTrace tailWord_7601975 prefixEnd_7601975 3903467098462999971551659 := by
  unfold tailWord_7601975
  simp only [CollatzResearch.WordTrace]
  refine ⟨277266806634350363811055379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184844537756233575874036919 277266806634350363811055379)
  ·
    refine ⟨415900209951525545716583069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277266806634350363811055379 415900209951525545716583069)
    ·
      refine ⟨155962578731822079643718651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415900209951525545716583069 155962578731822079643718651)
      ·
        refine ⟨233943868097733119465577977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155962578731822079643718651 233943868097733119465577977)
        ·
          refine ⟨175457901073299839599183483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233943868097733119465577977 175457901073299839599183483)
          ·
            refine ⟨263186851609949759398775225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175457901073299839599183483 263186851609949759398775225)
            ·
              refine ⟨197390138707462319549081419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263186851609949759398775225 197390138707462319549081419)
              ·
                refine ⟨296085208061193479323622129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197390138707462319549081419 296085208061193479323622129)
                ·
                  refine ⟨222063906045895109492716597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296085208061193479323622129 222063906045895109492716597)
                  ·
                    refine ⟨20818491191802666514942181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222063906045895109492716597 20818491191802666514942181)
                    ·
                      refine ⟨3903467098462999971551659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20818491191802666514942181 3903467098462999971551659)
                      ·
                        rfl

theorem cell23_7601975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_7601975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7601975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7601975 prefixEnd_7601975 := by exact prefixLift 7601975
  have htrace : WordTrace (prefixWord ++ tailWord_7601975) baseStart_7601975 baseEnd_7601975 := by
    simpa [prefixWord, tailWord_7601975, baseEnd_7601975] using wordTrace_append hprefix tailTrace_7601975
  have hstable : (prefixWord ++ tailWord_7601975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7601975).length < 2 ^ (prefixWord ++ tailWord_7601975).sum := by decide
  have hdescent : baseEnd_7601975 < baseStart_7601975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7601975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602015 : List Nat := [1, 1, 2, 3, 1, 4, 11]
def baseStart_7602015 : Nat := 118140960795 + 7602015 * 2 ^ 59
def prefixEnd_7602015 : Nat := 4983230072969 + 3 ^ 40 * 7602015 * 2
def baseEnd_7602015 : Nat := 48191205403570121173475

theorem tailTrace_7602015 : CollatzResearch.WordTrace tailWord_7602015 prefixEnd_7602015 48191205403570121173475 := by
  unfold tailWord_7602015
  simp only [CollatzResearch.WordTrace]
  refine ⟨277268265554205450642511499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184845510369470300428340999 277268265554205450642511499)
  ·
    refine ⟨415902398331308175963767249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277268265554205450642511499 415902398331308175963767249)
    ·
      refine ⟨311926798748481131972825437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415902398331308175963767249 311926798748481131972825437)
      ·
        refine ⟨116972549530680424489809539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 311926798748481131972825437 116972549530680424489809539)
        ·
          refine ⟨175458824296020636734714309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116972549530680424489809539 175458824296020636734714309)
          ·
            refine ⟨32898529555503869387758933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175458824296020636734714309 32898529555503869387758933)
            ·
              refine ⟨48191205403570121173475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32898529555503869387758933 48191205403570121173475)
              ·
                rfl

theorem cell23_7602015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 11].length) (baseStart_7602015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602015 prefixEnd_7602015 := by exact prefixLift 7602015
  have htrace : WordTrace (prefixWord ++ tailWord_7602015) baseStart_7602015 baseEnd_7602015 := by
    simpa [prefixWord, tailWord_7602015, baseEnd_7602015] using wordTrace_append hprefix tailTrace_7602015
  have hstable : (prefixWord ++ tailWord_7602015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602015).length < 2 ^ (prefixWord ++ tailWord_7602015).sum := by decide
  have hdescent : baseEnd_7602015 < baseStart_7602015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602020 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_7602020 : Nat := 118140960795 + 7602020 * 2 ^ 59
def prefixEnd_7602020 : Nat := 4983230072969 + 3 ^ 40 * 7602020 * 2
def baseEnd_7602020 : Nat := 3903490205092452295488953

theorem tailTrace_7602020 : CollatzResearch.WordTrace tailWord_7602020 prefixEnd_7602020 3903490205092452295488953 := by
  unfold tailWord_7602020
  simp only [CollatzResearch.WordTrace]
  refine ⟨138634223959593668248221757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184845631946124890997629009 138634223959593668248221757)
  ·
    refine ⟨51987833984847625593083159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138634223959593668248221757 51987833984847625593083159)
    ·
      refine ⟨77981750977271438389624739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51987833984847625593083159 77981750977271438389624739)
      ·
        refine ⟨116972626465907157584437109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77981750977271438389624739 116972626465907157584437109)
        ·
          refine ⟨10966183731178796023540979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116972626465907157584437109 10966183731178796023540979)
          ·
            refine ⟨16449275596768194035311469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966183731178796023540979 16449275596768194035311469)
            ·
              refine ⟨6168478348788072763241801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16449275596768194035311469 6168478348788072763241801)
              ·
                refine ⟨4626358761591054572431351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168478348788072763241801 4626358761591054572431351)
                ·
                  refine ⟨6939538142386581858647027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626358761591054572431351 6939538142386581858647027)
                  ·
                    refine ⟨10409307213579872787970541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939538142386581858647027 10409307213579872787970541)
                    ·
                      refine ⟨3903490205092452295488953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409307213579872787970541 3903490205092452295488953)
                      ·
                        rfl

theorem cell23_7602020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_7602020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602020 prefixEnd_7602020 := by exact prefixLift 7602020
  have htrace : WordTrace (prefixWord ++ tailWord_7602020) baseStart_7602020 baseEnd_7602020 := by
    simpa [prefixWord, tailWord_7602020, baseEnd_7602020] using wordTrace_append hprefix tailTrace_7602020
  have hstable : (prefixWord ++ tailWord_7602020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602020).length < 2 ^ (prefixWord ++ tailWord_7602020).sum := by decide
  have hdescent : baseEnd_7602020 < baseStart_7602020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602035 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_7602035 : Nat := 118140960795 + 7602035 * 2 ^ 59
def prefixEnd_7602035 : Nat := 4983230072969 + 3 ^ 40 * 7602035 * 2
def baseEnd_7602035 : Nat := 3903497907302269736801383

theorem tailTrace_7602035 : CollatzResearch.WordTrace tailWord_7602035 prefixEnd_7602035 3903497907302269736801383 := by
  unfold tailWord_7602035
  simp only [CollatzResearch.WordTrace]
  refine ⟨277268995014132994058239559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184845996676088662705493039 277268995014132994058239559)
  ·
    refine ⟨415903492521199491087359339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277268995014132994058239559 415903492521199491087359339)
    ·
      refine ⟨623855238781799236631039009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415903492521199491087359339 623855238781799236631039009)
      ·
        refine ⟨467891429086349427473279257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623855238781799236631039009 467891429086349427473279257)
        ·
          refine ⟨350918571814762070604959443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467891429086349427473279257 350918571814762070604959443)
          ·
            refine ⟨526377857722143105907439165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350918571814762070604959443 526377857722143105907439165)
            ·
              refine ⟨197391696645803664715289687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526377857722143105907439165 197391696645803664715289687)
              ·
                refine ⟨296087544968705497072934531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197391696645803664715289687 296087544968705497072934531)
                ·
                  refine ⟨444131317453058245609401797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296087544968705497072934531 444131317453058245609401797)
                  ·
                    refine ⟨83274622022448421051762837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 444131317453058245609401797 83274622022448421051762837)
                    ·
                      refine ⟨3903497907302269736801383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83274622022448421051762837 3903497907302269736801383)
                      ·
                        rfl

theorem cell23_7602035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_7602035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602035 prefixEnd_7602035 := by exact prefixLift 7602035
  have htrace : WordTrace (prefixWord ++ tailWord_7602035) baseStart_7602035 baseEnd_7602035 := by
    simpa [prefixWord, tailWord_7602035, baseEnd_7602035] using wordTrace_append hprefix tailTrace_7602035
  have hstable : (prefixWord ++ tailWord_7602035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602035).length < 2 ^ (prefixWord ++ tailWord_7602035).sum := by decide
  have hdescent : baseEnd_7602035 < baseStart_7602035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602077 : List Nat := [1, 4, 2, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_7602077 : Nat := 118140960795 + 7602077 * 2 ^ 59
def prefixEnd_7602077 : Nat := 4983230072969 + 3 ^ 40 * 7602077 * 2
def baseEnd_7602077 : Nat := 3903519473489758572476191

theorem tailTrace_7602077 : CollatzResearch.WordTrace tailWord_7602077 prefixEnd_7602077 3903519473489758572476191 := by
  unfold tailWord_7602077
  simp only [CollatzResearch.WordTrace]
  refine ⟨277270526879980835231268485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184847017919987223487512323 277270526879980835231268485)
  ·
    refine ⟨51988223789996406605862841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277270526879980835231268485 51988223789996406605862841)
    ·
      refine ⟨38991167842497304954397131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51988223789996406605862841 38991167842497304954397131)
      ·
        refine ⟨58486751763745957431595697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38991167842497304954397131 58486751763745957431595697)
        ·
          refine ⟨43865063822809468073696773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58486751763745957431595697 43865063822809468073696773)
          ·
            refine ⟨8224699466776775263818145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43865063822809468073696773 8224699466776775263818145)
            ·
              refine ⟨6168524600082581447863609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224699466776775263818145 6168524600082581447863609)
              ·
                refine ⟨4626393450061936085897707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168524600082581447863609 4626393450061936085897707)
                ·
                  refine ⟨6939590175092904128846561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626393450061936085897707 6939590175092904128846561)
                  ·
                    refine ⟨5204692631319678096634921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939590175092904128846561 5204692631319678096634921)
                    ·
                      refine ⟨3903519473489758572476191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204692631319678096634921 3903519473489758572476191)
                      ·
                        rfl

theorem cell23_7602077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_7602077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602077 prefixEnd_7602077 := by exact prefixLift 7602077
  have htrace : WordTrace (prefixWord ++ tailWord_7602077) baseStart_7602077 baseEnd_7602077 := by
    simpa [prefixWord, tailWord_7602077, baseEnd_7602077] using wordTrace_append hprefix tailTrace_7602077
  have hstable : (prefixWord ++ tailWord_7602077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602077).length < 2 ^ (prefixWord ++ tailWord_7602077).sum := by decide
  have hdescent : baseEnd_7602077 < baseStart_7602077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602112 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_7602112 : Nat := 118140960795 + 7602112 * 2 ^ 59
def prefixEnd_7602112 : Nat := 4983230072969 + 3 ^ 40 * 7602112 * 2
def baseEnd_7602112 : Nat := 3903537445312665935538529

theorem tailTrace_7602112 : CollatzResearch.WordTrace tailWord_7602112 prefixEnd_7602112 3903537445312665935538529 := by
  unfold tailWord_7602112
  simp only [CollatzResearch.WordTrace]
  refine ⟨138635901717427018104396295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184847868956569357472528393 138635901717427018104396295)
  ·
    refine ⟨207953852576140527156594443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138635901717427018104396295 207953852576140527156594443)
    ·
      refine ⟨311930778864210790734891665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207953852576140527156594443 311930778864210790734891665)
      ·
        refine ⟨233948084148158093051168749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311930778864210790734891665 233948084148158093051168749)
        ·
          refine ⟨87730531555559284894188281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233948084148158093051168749 87730531555559284894188281)
          ·
            refine ⟨65797898666669463670641211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87730531555559284894188281 65797898666669463670641211)
            ·
              refine ⟨98696848000004195505961817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65797898666669463670641211 98696848000004195505961817)
              ·
                refine ⟨74022636000003146629471363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98696848000004195505961817 74022636000003146629471363)
                ·
                  refine ⟨111033954000004719944207045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74022636000003146629471363 111033954000004719944207045)
                  ·
                    refine ⟨20818866375000884989538821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 111033954000004719944207045 20818866375000884989538821)
                    ·
                      refine ⟨3903537445312665935538529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20818866375000884989538821 3903537445312665935538529)
                      ·
                        rfl

theorem cell23_7602112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_7602112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602112 prefixEnd_7602112 := by exact prefixLift 7602112
  have htrace : WordTrace (prefixWord ++ tailWord_7602112) baseStart_7602112 baseEnd_7602112 := by
    simpa [prefixWord, tailWord_7602112, baseEnd_7602112] using wordTrace_append hprefix tailTrace_7602112
  have hstable : (prefixWord ++ tailWord_7602112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602112).length < 2 ^ (prefixWord ++ tailWord_7602112).sum := by decide
  have hdescent : baseEnd_7602112 < baseStart_7602112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602120 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_7602120 : Nat := 118140960795 + 7602120 * 2 ^ 59
def prefixEnd_7602120 : Nat := 4983230072969 + 3 ^ 40 * 7602120 * 2
def baseEnd_7602120 : Nat := 3903541553157901904238493

theorem tailTrace_7602120 : CollatzResearch.WordTrace tailWord_7602120 prefixEnd_7602120 3903541553157901904238493 := by
  unfold tailWord_7602120
  simp only [CollatzResearch.WordTrace]
  refine ⟨138636047609412526787541907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184848063479216702383389209 138636047609412526787541907)
  ·
    refine ⟨207954071414118790181312861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138636047609412526787541907 207954071414118790181312861)
    ·
      refine ⟨77982776780294546317992323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207954071414118790181312861 77982776780294546317992323)
      ·
        refine ⟨116974165170441819476988485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77982776780294546317992323 116974165170441819476988485)
        ·
          refine ⟨21932655969457841151935341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116974165170441819476988485 21932655969457841151935341)
          ·
            refine ⟨8224745988546690431975753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21932655969457841151935341 8224745988546690431975753)
            ·
              refine ⟨6168559491410017823981815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224745988546690431975753 6168559491410017823981815)
              ·
                refine ⟨9252839237115026735972723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6168559491410017823981815 9252839237115026735972723)
                ·
                  refine ⟨13879258855672540103959085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9252839237115026735972723 13879258855672540103959085)
                  ·
                    refine ⟨5204722070877202538984657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13879258855672540103959085 5204722070877202538984657)
                    ·
                      refine ⟨3903541553157901904238493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204722070877202538984657 3903541553157901904238493)
                      ·
                        rfl

theorem cell23_7602120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_7602120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602120 prefixEnd_7602120 := by exact prefixLift 7602120
  have htrace : WordTrace (prefixWord ++ tailWord_7602120) baseStart_7602120 baseEnd_7602120 := by
    simpa [prefixWord, tailWord_7602120, baseEnd_7602120] using wordTrace_append hprefix tailTrace_7602120
  have hstable : (prefixWord ++ tailWord_7602120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602120).length < 2 ^ (prefixWord ++ tailWord_7602120).sum := by decide
  have hdescent : baseEnd_7602120 < baseStart_7602120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602133 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_7602133 : Nat := 118140960795 + 7602133 * 2 ^ 59
def prefixEnd_7602133 : Nat := 4983230072969 + 3 ^ 40 * 7602133 * 2
def baseEnd_7602133 : Nat := 3903548228406410353375933

theorem tailTrace_7602133 : CollatzResearch.WordTrace tailWord_7602133 prefixEnd_7602133 3903548228406410353375933 := by
  unfold tailWord_7602133
  simp only [CollatzResearch.WordTrace]
  refine ⟨277272569367777956795307053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184848379578518637863538035 277272569367777956795307053)
  ·
    refine ⟨103977213512916733798240145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277272569367777956795307053 103977213512916733798240145)
    ·
      refine ⟨77982910134687550348680109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103977213512916733798240145 77982910134687550348680109)
      ·
        refine ⟨29243591300507831380755041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77982910134687550348680109 29243591300507831380755041)
        ·
          refine ⟨21932693475380873535566281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29243591300507831380755041 21932693475380873535566281)
          ·
            refine ⟨16449520106535655151674711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21932693475380873535566281 16449520106535655151674711)
            ·
              refine ⟨24674280159803482727512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16449520106535655151674711 24674280159803482727512067)
              ·
                refine ⟨37011420239705224091268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24674280159803482727512067 37011420239705224091268101)
                ·
                  refine ⟨6939641294944729517112769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37011420239705224091268101 6939641294944729517112769)
                  ·
                    refine ⟨5204730971208547137834577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939641294944729517112769 5204730971208547137834577)
                    ·
                      refine ⟨3903548228406410353375933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204730971208547137834577 3903548228406410353375933)
                      ·
                        rfl

theorem cell23_7602133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_7602133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602133 prefixEnd_7602133 := by exact prefixLift 7602133
  have htrace : WordTrace (prefixWord ++ tailWord_7602133) baseStart_7602133 baseEnd_7602133 := by
    simpa [prefixWord, tailWord_7602133, baseEnd_7602133] using wordTrace_append hprefix tailTrace_7602133
  have hstable : (prefixWord ++ tailWord_7602133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602133).length < 2 ^ (prefixWord ++ tailWord_7602133).sum := by decide
  have hdescent : baseEnd_7602133 < baseStart_7602133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602186 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 2, 5]
def baseStart_7602186 : Nat := 118140960795 + 7602186 * 2 ^ 59
def prefixEnd_7602186 : Nat := 4983230072969 + 3 ^ 40 * 7602186 * 2
def baseEnd_7602186 : Nat := 1301191814293699548671063

theorem tailTrace_7602186 : CollatzResearch.WordTrace tailWord_7602186 prefixEnd_7602186 1301191814293699548671063 := by
  unfold tailWord_7602186
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318625609146486711746603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184849668291057297897990941 69318625609146486711746603)
  ·
    refine ⟨103977938413719730067619905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69318625609146486711746603 103977938413719730067619905)
    ·
      refine ⟨77983453810289797550714929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103977938413719730067619905 77983453810289797550714929)
      ·
        refine ⟨58487590357717348163036197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77983453810289797550714929 58487590357717348163036197)
        ·
          refine ⟨10966423192072002780569287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58487590357717348163036197 10966423192072002780569287)
          ·
            refine ⟨16449634788108004170853931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966423192072002780569287 16449634788108004170853931)
            ·
              refine ⟨24674452182162006256280897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16449634788108004170853931 24674452182162006256280897)
              ·
                refine ⟨18505839136621504692210673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24674452182162006256280897 18505839136621504692210673)
                ·
                  refine ⟨13879379352466128519158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18505839136621504692210673 13879379352466128519158005)
                  ·
                    refine ⟨1301191814293699548671063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13879379352466128519158005 1301191814293699548671063)
                    ·
                      rfl

theorem cell23_7602186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_7602186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602186 prefixEnd_7602186 := by exact prefixLift 7602186
  have htrace : WordTrace (prefixWord ++ tailWord_7602186) baseStart_7602186 baseEnd_7602186 := by
    simpa [prefixWord, tailWord_7602186, baseEnd_7602186] using wordTrace_append hprefix tailTrace_7602186
  have hstable : (prefixWord ++ tailWord_7602186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602186).length < 2 ^ (prefixWord ++ tailWord_7602186).sum := by decide
  have hdescent : baseEnd_7602186 < baseStart_7602186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602192 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_7602192 : Nat := 118140960795 + 7602192 * 2 ^ 59
def prefixEnd_7602192 : Nat := 4983230072969 + 3 ^ 40 * 7602192 * 2
def baseEnd_7602192 : Nat := 3903578523765025622538161

theorem tailTrace_7602192 : CollatzResearch.WordTrace tailWord_7602192 prefixEnd_7602192 3903578523765025622538161 := by
  unfold tailWord_7602192
  simp only [CollatzResearch.WordTrace]
  refine ⟨138637360637282104935852415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184849814183042806581136553 138637360637282104935852415)
  ·
    refine ⟨207956040955923157403778623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138637360637282104935852415 207956040955923157403778623)
    ·
      refine ⟨311934061433884736105667935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207956040955923157403778623 311934061433884736105667935)
      ·
        refine ⟨467901092150827104158501903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311934061433884736105667935 467901092150827104158501903)
        ·
          refine ⟨701851638226240656237752855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467901092150827104158501903 701851638226240656237752855)
          ·
            refine ⟨1052777457339360984356629283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701851638226240656237752855 1052777457339360984356629283)
            ·
              refine ⟨1579166186009041476534943925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052777457339360984356629283 1579166186009041476534943925)
              ·
                refine ⟨148046829938347638425150993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1579166186009041476534943925 148046829938347638425150993)
                ·
                  refine ⟨111035122453760728818863245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148046829938347638425150993 111035122453760728818863245)
                  ·
                    refine ⟨41638170920160273307073717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111035122453760728818863245 41638170920160273307073717)
                    ·
                      refine ⟨3903578523765025622538161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41638170920160273307073717 3903578523765025622538161)
                      ·
                        rfl

theorem cell23_7602192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_7602192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602192 prefixEnd_7602192 := by exact prefixLift 7602192
  have htrace : WordTrace (prefixWord ++ tailWord_7602192) baseStart_7602192 baseEnd_7602192 := by
    simpa [prefixWord, tailWord_7602192, baseEnd_7602192] using wordTrace_append hprefix tailTrace_7602192
  have hstable : (prefixWord ++ tailWord_7602192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602192).length < 2 ^ (prefixWord ++ tailWord_7602192).sum := by decide
  have hdescent : baseEnd_7602192 < baseStart_7602192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602226 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3]
def baseStart_7602226 : Nat := 118140960795 + 7602226 * 2 ^ 59
def prefixEnd_7602226 : Nat := 4983230072969 + 3 ^ 40 * 7602226 * 2
def baseEnd_7602226 : Nat := 3903595982107278489513005

theorem tailTrace_7602226 : CollatzResearch.WordTrace tailWord_7602226 prefixEnd_7602226 3903595982107278489513005 := by
  unfold tailWord_7602226
  simp only [CollatzResearch.WordTrace]
  refine ⟨69318990339110258419610633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184850640904294022452295021 69318990339110258419610633)
  ·
    refine ⟨51989242754332693814707975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69318990339110258419610633 51989242754332693814707975)
    ·
      refine ⟨77983864131499040722061963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51989242754332693814707975 77983864131499040722061963)
      ·
        refine ⟨116975796197248561083092945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77983864131499040722061963 116975796197248561083092945)
        ·
          refine ⟨87731847147936420812319709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116975796197248561083092945 87731847147936420812319709)
          ·
            refine ⟨32899442680476157804619891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87731847147936420812319709 32899442680476157804619891)
            ·
              refine ⟨49349164020714236706929837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32899442680476157804619891 49349164020714236706929837)
              ·
                refine ⟨18505936507767838765098689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49349164020714236706929837 18505936507767838765098689)
                ·
                  refine ⟨13879452380825879073824017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18505936507767838765098689 13879452380825879073824017)
                  ·
                    refine ⟨10409589285619409305368013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13879452380825879073824017 10409589285619409305368013)
                    ·
                      refine ⟨3903595982107278489513005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409589285619409305368013 3903595982107278489513005)
                      ·
                        rfl

theorem cell23_7602226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_7602226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602226 prefixEnd_7602226 := by exact prefixLift 7602226
  have htrace : WordTrace (prefixWord ++ tailWord_7602226) baseStart_7602226 baseEnd_7602226 := by
    simpa [prefixWord, tailWord_7602226, baseEnd_7602226] using wordTrace_append hprefix tailTrace_7602226
  have hstable : (prefixWord ++ tailWord_7602226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602226).length < 2 ^ (prefixWord ++ tailWord_7602226).sum := by decide
  have hdescent : baseEnd_7602226 < baseStart_7602226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602266 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2]
def baseStart_7602266 : Nat := 118140960795 + 7602266 * 2 ^ 59
def prefixEnd_7602266 : Nat := 4983230072969 + 3 ^ 40 * 7602266 * 2
def baseEnd_7602266 : Nat := 3903616521333458333012821

theorem tailTrace_7602266 : CollatzResearch.WordTrace tailWord_7602266 prefixEnd_7602266 3903616521333458333012821 := by
  unfold tailWord_7602266
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319355069074030127474663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184851613517530747006599101 69319355069074030127474663)
  ·
    refine ⟨103979032603611045191211995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69319355069074030127474663 103979032603611045191211995)
    ·
      refine ⟨155968548905416567786817993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103979032603611045191211995 155968548905416567786817993)
      ·
        refine ⟨116976411679062425840113495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155968548905416567786817993 116976411679062425840113495)
        ·
          refine ⟨175464617518593638760170243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116976411679062425840113495 175464617518593638760170243)
          ·
            refine ⟨263196926277890458140255365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175464617518593638760170243 263196926277890458140255365)
            ·
              refine ⟨49349423677104460901297881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263196926277890458140255365 49349423677104460901297881)
              ·
                refine ⟨37012067757828345675973411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49349423677104460901297881 37012067757828345675973411)
                ·
                  refine ⟨55518101636742518513960117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37012067757828345675973411 55518101636742518513960117)
                  ·
                    refine ⟨5204822028444611110683761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55518101636742518513960117 5204822028444611110683761)
                    ·
                      refine ⟨3903616521333458333012821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204822028444611110683761 3903616521333458333012821)
                      ·
                        rfl

theorem cell23_7602266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_7602266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602266 prefixEnd_7602266 := by exact prefixLift 7602266
  have htrace : WordTrace (prefixWord ++ tailWord_7602266) baseStart_7602266 baseEnd_7602266 := by
    simpa [prefixWord, tailWord_7602266, baseEnd_7602266] using wordTrace_append hprefix tailTrace_7602266
  have hstable : (prefixWord ++ tailWord_7602266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602266).length < 2 ^ (prefixWord ++ tailWord_7602266).sum := by decide
  have hdescent : baseEnd_7602266 < baseStart_7602266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602289 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_7602289 : Nat := 118140960795 + 7602289 * 2 ^ 59
def prefixEnd_7602289 : Nat := 4983230072969 + 3 ^ 40 * 7602289 * 2
def baseEnd_7602289 : Nat := 1301209443796170581008405

theorem tailTrace_7602289 : CollatzResearch.WordTrace tailWord_7602289 prefixEnd_7602289 1301209443796170581008405 := by
  unfold tailWord_7602289
  simp only [CollatzResearch.WordTrace]
  refine ⟨277278259155212795437985921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184852172770141863625323947 277278259155212795437985921)
  ·
    refine ⟨207958694366409596578489441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277278259155212795437985921 207958694366409596578489441)
    ·
      refine ⟨155969020774807197433867081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207958694366409596578489441 155969020774807197433867081)
      ·
        refine ⟨116976765581105398075400311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155969020774807197433867081 116976765581105398075400311)
        ·
          refine ⟨175465148371658097113100467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116976765581105398075400311 175465148371658097113100467)
          ·
            refine ⟨263197722557487145669650701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175465148371658097113100467 263197722557487145669650701)
            ·
              refine ⟨98699145959057679626119013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263197722557487145669650701 98699145959057679626119013)
              ·
                refine ⟨18506089867323314929897315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98699145959057679626119013 18506089867323314929897315)
                ·
                  refine ⟨27759134800984972394845973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18506089867323314929897315 27759134800984972394845973)
                  ·
                    refine ⟨1301209443796170581008405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27759134800984972394845973 1301209443796170581008405)
                    ·
                      rfl

theorem cell23_7602289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_7602289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602289 prefixEnd_7602289 := by exact prefixLift 7602289
  have htrace : WordTrace (prefixWord ++ tailWord_7602289) baseStart_7602289 baseEnd_7602289 := by
    simpa [prefixWord, tailWord_7602289, baseEnd_7602289] using wordTrace_append hprefix tailTrace_7602289
  have hstable : (prefixWord ++ tailWord_7602289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602289).length < 2 ^ (prefixWord ++ tailWord_7602289).sum := by decide
  have hdescent : baseEnd_7602289 < baseStart_7602289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602290 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 1, 1, 3]
def baseStart_7602290 : Nat := 118140960795 + 7602290 * 2 ^ 59
def prefixEnd_7602290 : Nat := 4983230072969 + 3 ^ 40 * 7602290 * 2
def baseEnd_7602290 : Nat := 3903628844869166239112711

theorem tailTrace_7602290 : CollatzResearch.WordTrace tailWord_7602290 prefixEnd_7602290 3903628844869166239112711 := by
  unfold tailWord_7602290
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319573907052293152193081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184852197085472781739181549 69319573907052293152193081)
  ·
    refine ⟨51989680430289219864144811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69319573907052293152193081 51989680430289219864144811)
    ·
      refine ⟨77984520645433829796217217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51989680430289219864144811 77984520645433829796217217)
      ·
        refine ⟨58488390484075372347162913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77984520645433829796217217 58488390484075372347162913)
        ·
          refine ⟨43866292863056529260372185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58488390484075372347162913 43866292863056529260372185)
          ·
            refine ⟨32899719647292396945279139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43866292863056529260372185 32899719647292396945279139)
            ·
              refine ⟨49349579470938595417918709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32899719647292396945279139 49349579470938595417918709)
              ·
                refine ⟨4626523075400493320429879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49349579470938595417918709 4626523075400493320429879)
                ·
                  refine ⟨6939784613100739980644819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626523075400493320429879 6939784613100739980644819)
                  ·
                    refine ⟨10409676919651109970967229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939784613100739980644819 10409676919651109970967229)
                    ·
                      refine ⟨3903628844869166239112711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409676919651109970967229 3903628844869166239112711)
                      ·
                        rfl

theorem cell23_7602290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_7602290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602290 prefixEnd_7602290 := by exact prefixLift 7602290
  have htrace : WordTrace (prefixWord ++ tailWord_7602290) baseStart_7602290 baseEnd_7602290 := by
    simpa [prefixWord, tailWord_7602290, baseEnd_7602290] using wordTrace_append hprefix tailTrace_7602290
  have hstable : (prefixWord ++ tailWord_7602290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602290).length < 2 ^ (prefixWord ++ tailWord_7602290).sum := by decide
  have hdescent : baseEnd_7602290 < baseStart_7602290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602330 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4]
def baseStart_7602330 : Nat := 118140960795 + 7602330 * 2 ^ 59
def prefixEnd_7602330 : Nat := 4983230072969 + 3 ^ 40 * 7602330 * 2
def baseEnd_7602330 : Nat := 3903649384095346082612527

theorem tailTrace_7602330 : CollatzResearch.WordTrace tailWord_7602330 prefixEnd_7602330 3903649384095346082612527 := by
  unfold tailWord_7602330
  simp only [CollatzResearch.WordTrace]
  refine ⟨69319938637016064860057111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184853169698709506293485629 69319938637016064860057111)
  ·
    refine ⟨103979907955524097290085667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69319938637016064860057111 103979907955524097290085667)
    ·
      refine ⟨155969861933286145935128501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103979907955524097290085667 155969861933286145935128501)
      ·
        refine ⟨14622174556245576181418297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155969861933286145935128501 14622174556245576181418297)
        ·
          refine ⟨10966630917184182136063723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14622174556245576181418297 10966630917184182136063723)
          ·
            refine ⟨16449946375776273204095585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966630917184182136063723 16449946375776273204095585)
            ·
              refine ⟨12337459781832204903071689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16449946375776273204095585 12337459781832204903071689)
              ·
                refine ⟨9253094836374153677303767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12337459781832204903071689 9253094836374153677303767)
                ·
                  refine ⟨13879642254561230515955651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253094836374153677303767 13879642254561230515955651)
                  ·
                    refine ⟨20819463381841845773933477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13879642254561230515955651 20819463381841845773933477)
                    ·
                      refine ⟨3903649384095346082612527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20819463381841845773933477 3903649384095346082612527)
                      ·
                        rfl

theorem cell23_7602330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_7602330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602330 prefixEnd_7602330 := by exact prefixLift 7602330
  have htrace : WordTrace (prefixWord ++ tailWord_7602330) baseStart_7602330 baseEnd_7602330 := by
    simpa [prefixWord, tailWord_7602330, baseEnd_7602330] using wordTrace_append hprefix tailTrace_7602330
  have hstable : (prefixWord ++ tailWord_7602330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602330).length < 2 ^ (prefixWord ++ tailWord_7602330).sum := by decide
  have hdescent : baseEnd_7602330 < baseStart_7602330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602333 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_7602333 : Nat := 118140960795 + 7602333 * 2 ^ 59
def prefixEnd_7602333 : Nat := 4983230072969 + 3 ^ 40 * 7602333 * 2
def baseEnd_7602333 : Nat := 3903650924537309570875013

theorem tailTrace_7602333 : CollatzResearch.WordTrace tailWord_7602333 prefixEnd_7602333 3903650924537309570875013 := by
  unfold tailWord_7602333
  simp only [CollatzResearch.WordTrace]
  refine ⟨277279863967053390952587653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184853242644702260635058435 277279863967053390952587653)
  ·
    refine ⟨51989974493822510803610185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277279863967053390952587653 51989974493822510803610185)
    ·
      refine ⟨38992480870366883102707639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51989974493822510803610185 38992480870366883102707639)
      ·
        refine ⟨58488721305550324654061459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38992480870366883102707639 58488721305550324654061459)
        ·
          refine ⟨87733081958325486981092189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58488721305550324654061459 87733081958325486981092189)
          ·
            refine ⟨32899905734372057617909571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87733081958325486981092189 32899905734372057617909571)
            ·
              refine ⟨49349858601558086426864357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32899905734372057617909571 49349858601558086426864357)
              ·
                refine ⟨9253098487792141205037067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49349858601558086426864357 9253098487792141205037067)
                ·
                  refine ⟨13879647731688211807555601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253098487792141205037067 13879647731688211807555601)
                  ·
                    refine ⟨10409735798766158855666701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13879647731688211807555601 10409735798766158855666701)
                    ·
                      refine ⟨3903650924537309570875013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409735798766158855666701 3903650924537309570875013)
                      ·
                        rfl

theorem cell23_7602333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_7602333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602333 prefixEnd_7602333 := by exact prefixLift 7602333
  have htrace : WordTrace (prefixWord ++ tailWord_7602333) baseStart_7602333 baseEnd_7602333 := by
    simpa [prefixWord, tailWord_7602333, baseEnd_7602333] using wordTrace_append hprefix tailTrace_7602333
  have hstable : (prefixWord ++ tailWord_7602333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602333).length < 2 ^ (prefixWord ++ tailWord_7602333).sum := by decide
  have hdescent : baseEnd_7602333 < baseStart_7602333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602336 : List Nat := [2, 1, 1, 4, 2, 2, 4, 7]
def baseStart_7602336 : Nat := 118140960795 + 7602336 * 2 ^ 59
def prefixEnd_7602336 : Nat := 4983230072969 + 3 ^ 40 * 7602336 * 2
def baseEnd_7602336 : Nat := 144579720925158261449537

theorem tailTrace_7602336 : CollatzResearch.WordTrace tailWord_7602336 prefixEnd_7602336 144579720925158261449537 := by
  unfold tailWord_7602336
  simp only [CollatzResearch.WordTrace]
  refine ⟨138639986693021261232473431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184853315590695014976631241 138639986693021261232473431)
  ·
    refine ⟨207959980039531891848710147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138639986693021261232473431 207959980039531891848710147)
    ·
      refine ⟨311939970059297837773065221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207959980039531891848710147 311939970059297837773065221)
      ·
        refine ⟨58488744386118344582449729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311939970059297837773065221 58488744386118344582449729)
        ·
          refine ⟨43866558289588758436837297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58488744386118344582449729 43866558289588758436837297)
          ·
            refine ⟨32899918717191568827627973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43866558289588758436837297 32899918717191568827627973)
            ·
              refine ⟨6168734759473419155180245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32899918717191568827627973 6168734759473419155180245)
              ·
                refine ⟨144579720925158261449537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6168734759473419155180245 144579720925158261449537)
                ·
                  rfl

theorem cell23_7602336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 7].length) (baseStart_7602336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602336 prefixEnd_7602336 := by exact prefixLift 7602336
  have htrace : WordTrace (prefixWord ++ tailWord_7602336) baseStart_7602336 baseEnd_7602336 := by
    simpa [prefixWord, tailWord_7602336, baseEnd_7602336] using wordTrace_append hprefix tailTrace_7602336
  have hstable : (prefixWord ++ tailWord_7602336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602336).length < 2 ^ (prefixWord ++ tailWord_7602336).sum := by decide
  have hdescent : baseEnd_7602336 < baseStart_7602336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602353 : List Nat := [1, 2, 2, 5, 3, 1, 9]
def baseStart_7602353 : Nat := 118140960795 + 7602353 * 2 ^ 59
def prefixEnd_7602353 : Nat := 4983230072969 + 3 ^ 40 * 7602353 * 2
def baseEnd_7602353 : Nat := 48193348075930857933641

theorem tailTrace_7602353 : CollatzResearch.WordTrace tailWord_7602353 prefixEnd_7602353 48193348075930857933641 := by
  unfold tailWord_7602353
  simp only [CollatzResearch.WordTrace]
  refine ⟨277280593426980934368315713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184853728951320622912210475 277280593426980934368315713)
  ·
    refine ⟨207960445070235700776236785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277280593426980934368315713 207960445070235700776236785)
    ·
      refine ⟨155970333802676775582177589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207960445070235700776236785 155970333802676775582177589)
      ·
        refine ⟨14622218794000947710829149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155970333802676775582177589 14622218794000947710829149)
        ·
          refine ⟨5483332047750355391560931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14622218794000947710829149 5483332047750355391560931)
          ·
            refine ⟨8224998071625533087341397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483332047750355391560931 8224998071625533087341397)
            ·
              refine ⟨48193348075930857933641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8224998071625533087341397 48193348075930857933641)
              ·
                rfl

theorem cell23_7602353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 9].length) (baseStart_7602353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602353 prefixEnd_7602353 := by exact prefixLift 7602353
  have htrace : WordTrace (prefixWord ++ tailWord_7602353) baseStart_7602353 baseEnd_7602353 := by
    simpa [prefixWord, tailWord_7602353, baseEnd_7602353] using wordTrace_append hprefix tailTrace_7602353
  have hstable : (prefixWord ++ tailWord_7602353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602353).length < 2 ^ (prefixWord ++ tailWord_7602353).sum := by decide
  have hdescent : baseEnd_7602353 < baseStart_7602353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602363 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 3]
def baseStart_7602363 : Nat := 118140960795 + 7602363 * 2 ^ 59
def prefixEnd_7602363 : Nat := 4983230072969 + 3 ^ 40 * 7602363 * 2
def baseEnd_7602363 : Nat := 3903666328956944453499875

theorem tailTrace_7602363 : CollatzResearch.WordTrace tailWord_7602363 prefixEnd_7602363 3903666328956944453499875 := by
  unfold tailWord_7602363
  simp only [CollatzResearch.WordTrace]
  refine ⟨277280958156944706076179743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184853972104629804050786495 277280958156944706076179743)
  ·
    refine ⟨415921437235417059114269615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277280958156944706076179743 415921437235417059114269615)
    ·
      refine ⟨623882155853125588671404423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415921437235417059114269615 623882155853125588671404423)
      ·
        refine ⟨935823233779688383007106635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623882155853125588671404423 935823233779688383007106635)
        ·
          refine ⟨1403734850669532574510659953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935823233779688383007106635 1403734850669532574510659953)
          ·
            refine ⟨1052801138002149430882994965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1403734850669532574510659953 1052801138002149430882994965)
            ·
              refine ⟨49350053343850754572640389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1052801138002149430882994965 49350053343850754572640389)
              ·
                refine ⟨9253135001972016482370073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49350053343850754572640389 9253135001972016482370073)
                ·
                  refine ⟨6939851251479012361777555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253135001972016482370073 6939851251479012361777555)
                  ·
                    refine ⟨10409776877218518542666333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6939851251479012361777555 10409776877218518542666333)
                    ·
                      refine ⟨3903666328956944453499875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409776877218518542666333 3903666328956944453499875)
                      ·
                        rfl

theorem cell23_7602363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 1, 3].length) (baseStart_7602363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602363 prefixEnd_7602363 := by exact prefixLift 7602363
  have htrace : WordTrace (prefixWord ++ tailWord_7602363) baseStart_7602363 baseEnd_7602363 := by
    simpa [prefixWord, tailWord_7602363, baseEnd_7602363] using wordTrace_append hprefix tailTrace_7602363
  have hstable : (prefixWord ++ tailWord_7602363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602363).length < 2 ^ (prefixWord ++ tailWord_7602363).sum := by decide
  have hdescent : baseEnd_7602363 < baseStart_7602363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602364 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_7602364 : Nat := 118140960795 + 7602364 * 2 ^ 59
def prefixEnd_7602364 : Nat := 4983230072969 + 3 ^ 40 * 7602364 * 2
def baseEnd_7602364 : Nat := 3903666842437598949587371

theorem tailTrace_7602364 : CollatzResearch.WordTrace tailWord_7602364 prefixEnd_7602364 3903666842437598949587371 := by
  unfold tailWord_7602364
  simp only [CollatzResearch.WordTrace]
  refine ⟨138640497314970541623483073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184853996419960722164644097 138640497314970541623483073)
  ·
    refine ⟨103980372986227906217612305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138640497314970541623483073 103980372986227906217612305)
    ·
      refine ⟨77985279739670929663209229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103980372986227906217612305 77985279739670929663209229)
      ·
        refine ⟨29244479902376598623703461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77985279739670929663209229 29244479902376598623703461)
        ·
          refine ⟨5483339981695612241944399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29244479902376598623703461 5483339981695612241944399)
          ·
            refine ⟨8225009972543418362916599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483339981695612241944399 8225009972543418362916599)
            ·
              refine ⟨12337514958815127544374899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225009972543418362916599 12337514958815127544374899)
              ·
                refine ⟨18506272438222691316562349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12337514958815127544374899 18506272438222691316562349)
                ·
                  refine ⟨6939852164333509243710881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18506272438222691316562349 6939852164333509243710881)
                  ·
                    refine ⟨5204889123250131932783161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939852164333509243710881 5204889123250131932783161)
                    ·
                      refine ⟨3903666842437598949587371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204889123250131932783161 3903666842437598949587371)
                      ·
                        rfl

theorem cell23_7602364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_7602364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602364 prefixEnd_7602364 := by exact prefixLift 7602364
  have htrace : WordTrace (prefixWord ++ tailWord_7602364) baseStart_7602364 baseEnd_7602364 := by
    simpa [prefixWord, tailWord_7602364, baseEnd_7602364] using wordTrace_append hprefix tailTrace_7602364
  have hstable : (prefixWord ++ tailWord_7602364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602364).length < 2 ^ (prefixWord ++ tailWord_7602364).sum := by decide
  have hdescent : baseEnd_7602364 < baseStart_7602364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602370 : List Nat := [3, 5, 1, 1, 1, 2, 2, 8]
def baseStart_7602370 : Nat := 118140960795 + 7602370 * 2 ^ 59
def prefixEnd_7602370 : Nat := 4983230072969 + 3 ^ 40 * 7602370 * 2
def baseEnd_7602370 : Nat := 144580367530426886152309

theorem tailTrace_7602370 : CollatzResearch.WordTrace tailWord_7602370 prefixEnd_7602370 144580367530426886152309 := by
  unfold tailWord_7602370
  simp only [CollatzResearch.WordTrace]
  refine ⟨69320303366979836567921141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184854142311946230847789709 69320303366979836567921141)
  ·
    refine ⟨6498778440654359678242607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69320303366979836567921141 6498778440654359678242607)
    ·
      refine ⟨9748167660981539517363911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498778440654359678242607 9748167660981539517363911)
      ·
        refine ⟨14622251491472309276045867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748167660981539517363911 14622251491472309276045867)
        ·
          refine ⟨21933377237208463914068801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622251491472309276045867 21933377237208463914068801)
          ·
            refine ⟨16450032927906347935551601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21933377237208463914068801 16450032927906347935551601)
            ·
              refine ⟨12337524695929760951663701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16450032927906347935551601 12337524695929760951663701)
              ·
                refine ⟨144580367530426886152309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12337524695929760951663701 144580367530426886152309)
                ·
                  rfl

theorem cell23_7602370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_7602370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602370 prefixEnd_7602370 := by exact prefixLift 7602370
  have htrace : WordTrace (prefixWord ++ tailWord_7602370) baseStart_7602370 baseEnd_7602370 := by
    simpa [prefixWord, tailWord_7602370, baseEnd_7602370] using wordTrace_append hprefix tailTrace_7602370
  have hstable : (prefixWord ++ tailWord_7602370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602370).length < 2 ^ (prefixWord ++ tailWord_7602370).sum := by decide
  have hdescent : baseEnd_7602370 < baseStart_7602370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602379 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 8]
def baseStart_7602379 : Nat := 118140960795 + 7602379 * 2 ^ 59
def prefixEnd_7602379 : Nat := 4983230072969 + 3 ^ 40 * 7602379 * 2
def baseEnd_7602379 : Nat := 1301224848215805463633267

theorem tailTrace_7602379 : CollatzResearch.WordTrace tailWord_7602379 prefixEnd_7602379 1301224848215805463633267 := by
  unfold tailWord_7602379
  simp only [CollatzResearch.WordTrace]
  refine ⟨277281541724886740808762191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184854361149924493872508127 277281541724886740808762191)
  ·
    refine ⟨415922312587330111213143287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277281541724886740808762191 415922312587330111213143287)
    ·
      refine ⟨623883468880995166819714931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415922312587330111213143287 623883468880995166819714931)
      ·
        refine ⟨935825203321492750229572397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623883468880995166819714931 935825203321492750229572397)
        ·
          refine ⟨350934451245559781336089649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935825203321492750229572397 350934451245559781336089649)
          ·
            refine ⟨263200838434169836002067237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350934451245559781336089649 263200838434169836002067237)
            ·
              refine ⟨49350157206406844250387607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 263200838434169836002067237 49350157206406844250387607)
              ·
                refine ⟨74025235809610266375581411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49350157206406844250387607 74025235809610266375581411)
                ·
                  refine ⟨111037853714415399563372117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74025235809610266375581411 111037853714415399563372117)
                  ·
                    refine ⟨1301224848215805463633267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111037853714415399563372117 1301224848215805463633267)
                    ·
                      rfl

theorem cell23_7602379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_7602379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602379 prefixEnd_7602379 := by exact prefixLift 7602379
  have htrace : WordTrace (prefixWord ++ tailWord_7602379) baseStart_7602379 baseEnd_7602379 := by
    simpa [prefixWord, tailWord_7602379, baseEnd_7602379] using wordTrace_append hprefix tailTrace_7602379
  have hstable : (prefixWord ++ tailWord_7602379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602379).length < 2 ^ (prefixWord ++ tailWord_7602379).sum := by decide
  have hdescent : baseEnd_7602379 < baseStart_7602379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602409 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 9]
def baseStart_7602409 : Nat := 118140960795 + 7602409 * 2 ^ 59
def prefixEnd_7602409 : Nat := 4983230072969 + 3 ^ 40 * 7602409 * 2
def baseEnd_7602409 : Nat := 433743327674116808169407

theorem tailTrace_7602409 : CollatzResearch.WordTrace tailWord_7602409 prefixEnd_7602409 433743327674116808169407 := by
  unfold tailWord_7602409
  simp only [CollatzResearch.WordTrace]
  refine ⟨277282635914778055932354281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184855090609852037288236187 277282635914778055932354281)
  ·
    refine ⟨207961976936083541949265711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277282635914778055932354281 207961976936083541949265711)
    ·
      refine ⟨311942965404125312923898567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207961976936083541949265711 311942965404125312923898567)
      ·
        refine ⟨467914448106187969385847851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311942965404125312923898567 467914448106187969385847851)
        ·
          refine ⟨701871672159281954078771777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467914448106187969385847851 701871672159281954078771777)
          ·
            refine ⟨526403754119461465559078833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 701871672159281954078771777 526403754119461465559078833)
            ·
              refine ⟨394802815589596099169309125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 526403754119461465559078833 394802815589596099169309125)
              ·
                refine ⟨74025527923049268594245461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394802815589596099169309125 74025527923049268594245461)
                ·
                  refine ⟨433743327674116808169407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74025527923049268594245461 433743327674116808169407)
                  ·
                    rfl

theorem cell23_7602409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_7602409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602409 prefixEnd_7602409 := by exact prefixLift 7602409
  have htrace : WordTrace (prefixWord ++ tailWord_7602409) baseStart_7602409 baseEnd_7602409 := by
    simpa [prefixWord, tailWord_7602409, baseEnd_7602409] using wordTrace_append hprefix tailTrace_7602409
  have hstable : (prefixWord ++ tailWord_7602409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602409).length < 2 ^ (prefixWord ++ tailWord_7602409).sum := by decide
  have hdescent : baseEnd_7602409 < baseStart_7602409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602456 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_7602456 : Nat := 118140960795 + 7602456 * 2 ^ 59
def prefixEnd_7602456 : Nat := 4983230072969 + 3 ^ 40 * 7602456 * 2
def baseEnd_7602456 : Nat := 1301238027552604196545649

theorem tailTrace_7602456 : CollatzResearch.WordTrace tailWord_7602456 prefixEnd_7602456 1301238027552604196545649 := by
  unfold tailWord_7602456
  simp only [CollatzResearch.WordTrace]
  refine ⟨138642175072803891479657611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184856233430405188639543481 138642175072803891479657611)
  ·
    refine ⟨207963262609205837219486417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138642175072803891479657611 207963262609205837219486417)
    ·
      refine ⟨155972446956904377914614813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207963262609205837219486417 155972446956904377914614813)
      ·
        refine ⟨58489667608839141717980555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155972446956904377914614813 58489667608839141717980555)
        ·
          refine ⟨87734501413258712576970833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58489667608839141717980555 87734501413258712576970833)
          ·
            refine ⟨65800876059944034432728125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87734501413258712576970833 65800876059944034432728125)
            ·
              refine ⟨24675328522479012912273047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65800876059944034432728125 24675328522479012912273047)
              ·
                refine ⟨37012992783718519368409571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24675328522479012912273047 37012992783718519368409571)
                ·
                  refine ⟨55519489175577779052614357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37012992783718519368409571 55519489175577779052614357)
                  ·
                    refine ⟨1301238027552604196545649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55519489175577779052614357 1301238027552604196545649)
                    ·
                      rfl

theorem cell23_7602456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_7602456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602456 prefixEnd_7602456 := by exact prefixLift 7602456
  have htrace : WordTrace (prefixWord ++ tailWord_7602456) baseStart_7602456 baseEnd_7602456 := by
    simpa [prefixWord, tailWord_7602456, baseEnd_7602456] using wordTrace_append hprefix tailTrace_7602456
  have hstable : (prefixWord ++ tailWord_7602456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602456).length < 2 ^ (prefixWord ++ tailWord_7602456).sum := by decide
  have hdescent : baseEnd_7602456 < baseStart_7602456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602471 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7602471 : Nat := 118140960795 + 7602471 * 2 ^ 59
def prefixEnd_7602471 : Nat := 4983230072969 + 3 ^ 40 * 7602471 * 2
def baseEnd_7602471 : Nat := 3903721784867630030949379

theorem tailTrace_7602471 : CollatzResearch.WordTrace tailWord_7602471 prefixEnd_7602471 3903721784867630030949379 := by
  unfold tailWord_7602471
  simp only [CollatzResearch.WordTrace]
  refine ⟨277284897240553440521111267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184856598160368960347407511 277284897240553440521111267)
  ·
    refine ⟨415927345860830160781666901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277284897240553440521111267 415927345860830160781666901)
    ·
      refine ⟨4874148584306603446660159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 415927345860830160781666901 4874148584306603446660159)
      ·
        refine ⟨7311222876459905169990239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4874148584306603446660159 7311222876459905169990239)
        ·
          refine ⟨10966834314689857754985359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7311222876459905169990239 10966834314689857754985359)
          ·
            refine ⟨16450251472034786632478039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10966834314689857754985359 16450251472034786632478039)
            ·
              refine ⟨24675377208052179948717059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16450251472034786632478039 24675377208052179948717059)
              ·
                refine ⟨37013065812078269923075589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24675377208052179948717059 37013065812078269923075589)
                ·
                  refine ⟨6939949839764675610576673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37013065812078269923075589 6939949839764675610576673)
                  ·
                    refine ⟨5204962379823506707932505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6939949839764675610576673 5204962379823506707932505)
                    ·
                      refine ⟨3903721784867630030949379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5204962379823506707932505 3903721784867630030949379)
                      ·
                        rfl

theorem cell23_7602471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7602471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602471 prefixEnd_7602471 := by exact prefixLift 7602471
  have htrace : WordTrace (prefixWord ++ tailWord_7602471) baseStart_7602471 baseEnd_7602471 := by
    simpa [prefixWord, tailWord_7602471, baseEnd_7602471] using wordTrace_append hprefix tailTrace_7602471
  have hstable : (prefixWord ++ tailWord_7602471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602471).length < 2 ^ (prefixWord ++ tailWord_7602471).sum := by decide
  have hdescent : baseEnd_7602471 < baseStart_7602471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602503 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 3, 4]
def baseStart_7602503 : Nat := 118140960795 + 7602503 * 2 ^ 59
def prefixEnd_7602503 : Nat := 4983230072969 + 3 ^ 40 * 7602503 * 2
def baseEnd_7602503 : Nat := 1301246072082857968583077

theorem tailTrace_7602503 : CollatzResearch.WordTrace tailWord_7602503 prefixEnd_7602503 1301246072082857968583077 := by
  unfold tailWord_7602503
  simp only [CollatzResearch.WordTrace]
  refine ⟨277286064376437509986276163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184857376250958339990850775 277286064376437509986276163)
  ·
    refine ⟨415929096564656264979414245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277286064376437509986276163 415929096564656264979414245)
    ·
      refine ⟨77986705605873049683640171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415929096564656264979414245 77986705605873049683640171)
      ·
        refine ⟨116980058408809574525460257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77986705605873049683640171 116980058408809574525460257)
        ·
          refine ⟨87735043806607180894095193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116980058408809574525460257 87735043806607180894095193)
          ·
            refine ⟨65801282854955385670571395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87735043806607180894095193 65801282854955385670571395)
            ·
              refine ⟨98701924282433078505857093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65801282854955385670571395 98701924282433078505857093)
              ·
                refine ⟨18506610802956202219848205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98701924282433078505857093 18506610802956202219848205)
                ·
                  refine ⟨6939979051108575832443077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18506610802956202219848205 6939979051108575832443077)
                  ·
                    refine ⟨1301246072082857968583077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939979051108575832443077 1301246072082857968583077)
                    ·
                      rfl

theorem cell23_7602503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_7602503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602503 prefixEnd_7602503 := by exact prefixLift 7602503
  have htrace : WordTrace (prefixWord ++ tailWord_7602503) baseStart_7602503 baseEnd_7602503 := by
    simpa [prefixWord, tailWord_7602503, baseEnd_7602503] using wordTrace_append hprefix tailTrace_7602503
  have hstable : (prefixWord ++ tailWord_7602503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602503).length < 2 ^ (prefixWord ++ tailWord_7602503).sum := by decide
  have hdescent : baseEnd_7602503 < baseStart_7602503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602513 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_7602513 : Nat := 118140960795 + 7602513 * 2 ^ 59
def prefixEnd_7602513 : Nat := 4983230072969 + 3 ^ 40 * 7602513 * 2
def baseEnd_7602513 : Nat := 3903743351055118866624185

theorem tailTrace_7602513 : CollatzResearch.WordTrace tailWord_7602513 prefixEnd_7602513 3903743351055118866624185 := by
  unfold tailWord_7602513
  simp only [CollatzResearch.WordTrace]
  refine ⟨277286429106401281694140193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184857619404267521129426795 277286429106401281694140193)
  ·
    refine ⟨207964821829800961270605145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277286429106401281694140193 207964821829800961270605145)
    ·
      refine ⟨155973616372350720952953859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207964821829800961270605145 155973616372350720952953859)
      ·
        refine ⟨233960424558526081429430789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155973616372350720952953859 233960424558526081429430789)
        ·
          refine ⟨43867579604723640268018273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233960424558526081429430789 43867579604723640268018273)
          ·
            refine ⟨32900684703542730201013705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43867579604723640268018273 32900684703542730201013705)
            ·
              refine ⟨24675513527657047650760279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32900684703542730201013705 24675513527657047650760279)
              ·
                refine ⟨37013270291485571476140419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24675513527657047650760279 37013270291485571476140419)
                ·
                  refine ⟨55519905437228357214210629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37013270291485571476140419 55519905437228357214210629)
                  ·
                    refine ⟨10409982269480316977664493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55519905437228357214210629 10409982269480316977664493)
                    ·
                      refine ⟨3903743351055118866624185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10409982269480316977664493 3903743351055118866624185)
                      ·
                        rfl

theorem cell23_7602513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_7602513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602513 prefixEnd_7602513 := by exact prefixLift 7602513
  have htrace : WordTrace (prefixWord ++ tailWord_7602513) baseStart_7602513 baseEnd_7602513 := by
    simpa [prefixWord, tailWord_7602513, baseEnd_7602513] using wordTrace_append hprefix tailTrace_7602513
  have hstable : (prefixWord ++ tailWord_7602513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602513).length < 2 ^ (prefixWord ++ tailWord_7602513).sum := by decide
  have hdescent : baseEnd_7602513 < baseStart_7602513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602520 : List Nat := [2, 1, 2, 2, 1, 1, 2, 7, 1, 4]
def baseStart_7602520 : Nat := 118140960795 + 7602520 * 2 ^ 59
def prefixEnd_7602520 : Nat := 4983230072969 + 3 ^ 40 * 7602520 * 2
def baseEnd_7602520 : Nat := 1301248981806566779745551

theorem tailTrace_7602520 : CollatzResearch.WordTrace tailWord_7602520 prefixEnd_7602520 1301248981806566779745551 := by
  unfold tailWord_7602520
  simp only [CollatzResearch.WordTrace]
  refine ⟨138643342208687960944822507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184857789611583947926430009 138643342208687960944822507)
  ·
    refine ⟨207965013313031941417233761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138643342208687960944822507 207965013313031941417233761)
    ·
      refine ⟨155973759984773956062925321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207965013313031941417233761 155973759984773956062925321)
      ·
        refine ⟨116980319988580467047193991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155973759984773956062925321 116980319988580467047193991)
        ·
          refine ⟨175470479982870700570790987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116980319988580467047193991 175470479982870700570790987)
          ·
            refine ⟨263205719974306050856186481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175470479982870700570790987 263205719974306050856186481)
            ·
              refine ⟨197404289980729538142139861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263205719974306050856186481 197404289980729538142139861)
              ·
                refine ⟨4626663046423348550206403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 197404289980729538142139861 4626663046423348550206403)
                ·
                  refine ⟨6939994569635022825309605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626663046423348550206403 6939994569635022825309605)
                  ·
                    refine ⟨1301248981806566779745551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6939994569635022825309605 1301248981806566779745551)
                    ·
                      rfl

theorem cell23_7602520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_7602520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602520 prefixEnd_7602520 := by exact prefixLift 7602520
  have htrace : WordTrace (prefixWord ++ tailWord_7602520) baseStart_7602520 baseEnd_7602520 := by
    simpa [prefixWord, tailWord_7602520, baseEnd_7602520] using wordTrace_append hprefix tailTrace_7602520
  have hstable : (prefixWord ++ tailWord_7602520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602520).length < 2 ^ (prefixWord ++ tailWord_7602520).sum := by decide
  have hdescent : baseEnd_7602520 < baseStart_7602520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602530 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_7602530 : Nat := 118140960795 + 7602530 * 2 ^ 59
def prefixEnd_7602530 : Nat := 4983230072969 + 3 ^ 40 * 7602530 * 2
def baseEnd_7602530 : Nat := 3903752080226245300111607

theorem tailTrace_7602530 : CollatzResearch.WordTrace tailWord_7602530 prefixEnd_7602530 3903752080226245300111607 := by
  unfold tailWord_7602530
  simp only [CollatzResearch.WordTrace]
  refine ⟨69321762286834923399377261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184858032764893129065006029 69321762286834923399377261)
  ·
    refine ⟨25995660857563096274766473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69321762286834923399377261 25995660857563096274766473)
    ·
      refine ⟨19496745643172322206074855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25995660857563096274766473 19496745643172322206074855)
      ·
        refine ⟨29245118464758483309112283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19496745643172322206074855 29245118464758483309112283)
        ·
          refine ⟨43867677697137724963668425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29245118464758483309112283 43867677697137724963668425)
          ·
            refine ⟨32900758272853293722751319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43867677697137724963668425 32900758272853293722751319)
            ·
              refine ⟨49351137409279940584126979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32900758272853293722751319 49351137409279940584126979)
              ·
                refine ⟨74026706113919910876190469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49351137409279940584126979 74026706113919910876190469)
                ·
                  refine ⟨13880007396359983289285713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74026706113919910876190469 13880007396359983289285713)
                  ·
                    refine ⟨10410005547269987466964285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13880007396359983289285713 10410005547269987466964285)
                    ·
                      refine ⟨3903752080226245300111607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410005547269987466964285 3903752080226245300111607)
                      ·
                        rfl

theorem cell23_7602530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_7602530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602530 prefixEnd_7602530 := by exact prefixLift 7602530
  have htrace : WordTrace (prefixWord ++ tailWord_7602530) baseStart_7602530 baseEnd_7602530 := by
    simpa [prefixWord, tailWord_7602530, baseEnd_7602530] using wordTrace_append hprefix tailTrace_7602530
  have hstable : (prefixWord ++ tailWord_7602530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602530).length < 2 ^ (prefixWord ++ tailWord_7602530).sum := by decide
  have hdescent : baseEnd_7602530 < baseStart_7602530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602537 : List Nat := [1, 2, 1, 1, 1, 3, 7, 2, 1, 4]
def baseStart_7602537 : Nat := 118140960795 + 7602537 * 2 ^ 59
def prefixEnd_7602537 : Nat := 4983230072969 + 3 ^ 40 * 7602537 * 2
def baseEnd_7602537 : Nat := 1301251891530275590908025

theorem tailTrace_7602537 : CollatzResearch.WordTrace tailWord_7602537 prefixEnd_7602537 1301251891530275590908025 := by
  unfold tailWord_7602537
  simp only [CollatzResearch.WordTrace]
  refine ⟨277287304458314333793013865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184858202972209555862009243 277287304458314333793013865)
  ·
    refine ⟨207965478343735750344760399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277287304458314333793013865 207965478343735750344760399)
    ·
      refine ⟨311948217515603625517140599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207965478343735750344760399 311948217515603625517140599)
      ·
        refine ⟨467922326273405438275710899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311948217515603625517140599 467922326273405438275710899)
        ·
          refine ⟨701883489410108157413566349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467922326273405438275710899 701883489410108157413566349)
          ·
            refine ⟨263206308528790559030087381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 701883489410108157413566349 263206308528790559030087381)
            ·
              refine ⟨6168897856143528727267673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263206308528790559030087381 6168897856143528727267673)
              ·
                refine ⟨4626673392107646545450755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168897856143528727267673 4626673392107646545450755)
                ·
                  refine ⟨6940010088161469818176133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626673392107646545450755 6940010088161469818176133)
                  ·
                    refine ⟨1301251891530275590908025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940010088161469818176133 1301251891530275590908025)
                    ·
                      rfl

theorem cell23_7602537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 2, 1, 4].length) (baseStart_7602537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602537 prefixEnd_7602537 := by exact prefixLift 7602537
  have htrace : WordTrace (prefixWord ++ tailWord_7602537) baseStart_7602537 baseEnd_7602537 := by
    simpa [prefixWord, tailWord_7602537, baseEnd_7602537] using wordTrace_append hprefix tailTrace_7602537
  have hstable : (prefixWord ++ tailWord_7602537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602537).length < 2 ^ (prefixWord ++ tailWord_7602537).sum := by decide
  have hdescent : baseEnd_7602537 < baseStart_7602537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602556 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7602556 : Nat := 118140960795 + 7602556 * 2 ^ 59
def prefixEnd_7602556 : Nat := 4983230072969 + 3 ^ 40 * 7602556 * 2
def baseEnd_7602556 : Nat := 3903765430723262198386487

theorem tailTrace_7602556 : CollatzResearch.WordTrace tailWord_7602556 prefixEnd_7602556 3903765430723262198386487 := by
  unfold tailWord_7602556
  simp only [CollatzResearch.WordTrace]
  refine ⟨138643998722622750018977761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184858664963497000025303681 138643998722622750018977761)
  ·
    refine ⟨103982999041967062514233321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138643998722622750018977761 103982999041967062514233321)
    ·
      refine ⟨77987249281475296885674991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103982999041967062514233321 77987249281475296885674991)
      ·
        refine ⟨116980873922212945328512487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77987249281475296885674991 116980873922212945328512487)
        ·
          refine ⟨175471310883319417992768731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116980873922212945328512487 175471310883319417992768731)
          ·
            refine ⟨263206966324979126989153097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175471310883319417992768731 263206966324979126989153097)
            ·
              refine ⟨197405224743734345241864823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263206966324979126989153097 197405224743734345241864823)
              ·
                refine ⟨296107837115601517862797235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197405224743734345241864823 296107837115601517862797235)
                ·
                  refine ⟨444161755673402276794195853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 296107837115601517862797235 444161755673402276794195853)
                  ·
                    refine ⟨166560658377525853797823445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 444161755673402276794195853 166560658377525853797823445)
                    ·
                      refine ⟨3903765430723262198386487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166560658377525853797823445 3903765430723262198386487)
                      ·
                        rfl

theorem cell23_7602556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7602556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602556 prefixEnd_7602556 := by exact prefixLift 7602556
  have htrace : WordTrace (prefixWord ++ tailWord_7602556) baseStart_7602556 baseEnd_7602556 := by
    simpa [prefixWord, tailWord_7602556, baseEnd_7602556] using wordTrace_append hprefix tailTrace_7602556
  have hstable : (prefixWord ++ tailWord_7602556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602556).length < 2 ^ (prefixWord ++ tailWord_7602556).sum := by decide
  have hdescent : baseEnd_7602556 < baseStart_7602556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602594 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 1, 1, 3]
def baseStart_7602594 : Nat := 118140960795 + 7602594 * 2 ^ 59
def prefixEnd_7602594 : Nat := 4983230072969 + 3 ^ 40 * 7602594 * 2
def baseEnd_7602594 : Nat := 3903784942988133049711313

theorem tailTrace_7602594 : CollatzResearch.WordTrace tailWord_7602594 prefixEnd_7602594 3903784942988133049711313 := by
  unfold tailWord_7602594
  simp only [CollatzResearch.WordTrace]
  refine ⟨69322345854776958131959709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184859588946071888351892557 69322345854776958131959709)
  ·
    refine ⟨25995879695541359299484891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69322345854776958131959709 25995879695541359299484891)
    ·
      refine ⟨38993819543312038949227337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25995879695541359299484891 38993819543312038949227337)
      ·
        refine ⟨29245364657484029211920503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38993819543312038949227337 29245364657484029211920503)
        ·
          refine ⟨43868046986226043817880755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29245364657484029211920503 43868046986226043817880755)
          ·
            refine ⟨65802070479339065726821133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43868046986226043817880755 65802070479339065726821133)
            ·
              refine ⟨24675776429752149647557925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65802070479339065726821133 24675776429752149647557925)
              ·
                refine ⟨4626708080578528058917111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24675776429752149647557925 4626708080578528058917111)
                ·
                  refine ⟨6940062120867792088375667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626708080578528058917111 6940062120867792088375667)
                  ·
                    refine ⟨10410093181301688132563501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6940062120867792088375667 10410093181301688132563501)
                    ·
                      refine ⟨3903784942988133049711313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410093181301688132563501 3903784942988133049711313)
                      ·
                        rfl

theorem cell23_7602594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_7602594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602594 prefixEnd_7602594 := by exact prefixLift 7602594
  have htrace : WordTrace (prefixWord ++ tailWord_7602594) baseStart_7602594 baseEnd_7602594 := by
    simpa [prefixWord, tailWord_7602594, baseEnd_7602594] using wordTrace_append hprefix tailTrace_7602594
  have hstable : (prefixWord ++ tailWord_7602594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602594).length < 2 ^ (prefixWord ++ tailWord_7602594).sum := by decide
  have hdescent : baseEnd_7602594 < baseStart_7602594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602610 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_7602610 : Nat := 118140960795 + 7602610 * 2 ^ 59
def prefixEnd_7602610 : Nat := 4983230072969 + 3 ^ 40 * 7602610 * 2
def baseEnd_7602610 : Nat := 1301264386226201662370413

theorem tailTrace_7602610 : CollatzResearch.WordTrace tailWord_7602610 prefixEnd_7602610 1301264386226201662370413 := by
  unfold tailWord_7602610
  simp only [CollatzResearch.WordTrace]
  refine ⟨69322491746762466815105321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184859977991366578173614189 69322491746762466815105321)
  ·
    refine ⟨51991868810071850111328991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69322491746762466815105321 51991868810071850111328991)
    ·
      refine ⟨77987803215107775166993487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51991868810071850111328991 77987803215107775166993487)
      ·
        refine ⟨116981704822661662750490231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77987803215107775166993487 116981704822661662750490231)
        ·
          refine ⟨175472557233992494125735347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116981704822661662750490231 175472557233992494125735347)
          ·
            refine ⟨263208835850988741188603021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175472557233992494125735347 263208835850988741188603021)
            ·
              refine ⟨98703313444120777945726133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263208835850988741188603021 98703313444120777945726133)
              ·
                refine ⟨9253435635386322932411825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98703313444120777945726133 9253435635386322932411825)
                ·
                  refine ⟨6940076726539742199308869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253435635386322932411825 6940076726539742199308869)
                  ·
                    refine ⟨1301264386226201662370413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940076726539742199308869 1301264386226201662370413)
                    ·
                      rfl

theorem cell23_7602610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_7602610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602610 prefixEnd_7602610 := by exact prefixLift 7602610
  have htrace : WordTrace (prefixWord ++ tailWord_7602610) baseStart_7602610 baseEnd_7602610 := by
    simpa [prefixWord, tailWord_7602610, baseEnd_7602610] using wordTrace_append hprefix tailTrace_7602610
  have hstable : (prefixWord ++ tailWord_7602610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602610).length < 2 ^ (prefixWord ++ tailWord_7602610).sum := by decide
  have hdescent : baseEnd_7602610 < baseStart_7602610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602617 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 5, 2, 2]
def baseStart_7602617 : Nat := 118140960795 + 7602617 * 2 ^ 59
def prefixEnd_7602617 : Nat := 4983230072969 + 3 ^ 40 * 7602617 * 2
def baseEnd_7602617 : Nat := 3903796753043186459723707

theorem tailTrace_7602617 : CollatzResearch.WordTrace tailWord_7602617 prefixEnd_7602617 3903796753043186459723707 := by
  unfold tailWord_7602617
  simp only [CollatzResearch.WordTrace]
  refine ⟨277290222298024507455926105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184860148198683004970617403 277290222298024507455926105)
  ·
    refine ⟨207967666723518380591944579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277290222298024507455926105 207967666723518380591944579)
    ·
      refine ⟨311951500085277570887916869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207967666723518380591944579 311951500085277570887916869)
      ·
        refine ⟨58490906265989544541484413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 311951500085277570887916869 58490906265989544541484413)
        ·
          refine ⟨21934089849746079203056655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58490906265989544541484413 21934089849746079203056655)
          ·
            refine ⟨32901134774619118804584983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21934089849746079203056655 32901134774619118804584983)
            ·
              refine ⟨49351702161928678206877475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32901134774619118804584983 49351702161928678206877475)
              ·
                refine ⟨74027553242893017310316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49351702161928678206877475 74027553242893017310316213)
                ·
                  refine ⟨6940083116521220372842145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74027553242893017310316213 6940083116521220372842145)
                  ·
                    refine ⟨5205062337390915279631609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940083116521220372842145 5205062337390915279631609)
                    ·
                      refine ⟨3903796753043186459723707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205062337390915279631609 3903796753043186459723707)
                      ·
                        rfl

theorem cell23_7602617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_7602617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602617 prefixEnd_7602617 := by exact prefixLift 7602617
  have htrace : WordTrace (prefixWord ++ tailWord_7602617) baseStart_7602617 baseEnd_7602617 := by
    simpa [prefixWord, tailWord_7602617, baseEnd_7602617] using wordTrace_append hprefix tailTrace_7602617
  have hstable : (prefixWord ++ tailWord_7602617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602617).length < 2 ^ (prefixWord ++ tailWord_7602617).sum := by decide
  have hdescent : baseEnd_7602617 < baseStart_7602617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602644 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_7602644 : Nat := 118140960795 + 7602644 * 2 ^ 59
def prefixEnd_7602644 : Nat := 4983230072969 + 3 ^ 40 * 7602644 * 2
def baseEnd_7602644 : Nat := 1301270205673619284695361

theorem tailTrace_7602644 : CollatzResearch.WordTrace tailWord_7602644 prefixEnd_7602644 1301270205673619284695361 := by
  unfold tailWord_7602644
  simp only [CollatzResearch.WordTrace]
  refine ⟨138645603534463345533579493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184860804712617794044772657 138645603534463345533579493)
  ·
    refine ⟨25996050662711877287546155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138645603534463345533579493 25996050662711877287546155)
    ·
      refine ⟨38994075994067815931319233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25996050662711877287546155 38994075994067815931319233)
      ·
        refine ⟨29245556995550861948489425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38994075994067815931319233 29245556995550861948489425)
        ·
          refine ⟨21934167746663146461367069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29245556995550861948489425 21934167746663146461367069)
          ·
            refine ⟨8225312904998679923012651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21934167746663146461367069 8225312904998679923012651)
            ·
              refine ⟨12337969357498019884518977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225312904998679923012651 12337969357498019884518977)
              ·
                refine ⟨9253477018123514913389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12337969357498019884518977 9253477018123514913389233)
                ·
                  refine ⟨6940107763592636185041925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253477018123514913389233 6940107763592636185041925)
                  ·
                    refine ⟨1301270205673619284695361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940107763592636185041925 1301270205673619284695361)
                    ·
                      rfl

theorem cell23_7602644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_7602644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602644 prefixEnd_7602644 := by exact prefixLift 7602644
  have htrace : WordTrace (prefixWord ++ tailWord_7602644) baseStart_7602644 baseEnd_7602644 := by
    simpa [prefixWord, tailWord_7602644, baseEnd_7602644] using wordTrace_append hprefix tailTrace_7602644
  have hstable : (prefixWord ++ tailWord_7602644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602644).length < 2 ^ (prefixWord ++ tailWord_7602644).sum := by decide
  have hdescent : baseEnd_7602644 < baseStart_7602644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602674 : List Nat := [3, 2, 1, 4, 3, 1, 2, 7]
def baseStart_7602674 : Nat := 118140960795 + 7602674 * 2 ^ 59
def prefixEnd_7602674 : Nat := 4983230072969 + 3 ^ 40 * 7602674 * 2
def baseEnd_7602674 : Nat := 144586148942240471730035

theorem tailTrace_7602674 : CollatzResearch.WordTrace tailWord_7602674 prefixEnd_7602674 144586148942240471730035 := by
  unfold tailWord_7602674
  simp only [CollatzResearch.WordTrace]
  refine ⟨69323075314704501547687769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184861534172545337460500717 69323075314704501547687769)
  ·
    refine ⟨51992306486028376160765827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69323075314704501547687769 51992306486028376160765827)
    ·
      refine ⟨77988459729042564241148741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51992306486028376160765827 77988459729042564241148741)
      ·
        refine ⟨14622836199195480795215389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77988459729042564241148741 14622836199195480795215389)
        ·
          refine ⟨5483563574698305298205771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14622836199195480795215389 5483563574698305298205771)
          ·
            refine ⟨8225345362047457947308657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483563574698305298205771 8225345362047457947308657)
            ·
              refine ⟨6169009021535593460481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225345362047457947308657 6169009021535593460481493)
              ·
                refine ⟨144586148942240471730035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6169009021535593460481493 144586148942240471730035)
                ·
                  rfl

theorem cell23_7602674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_7602674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602674 prefixEnd_7602674 := by exact prefixLift 7602674
  have htrace : WordTrace (prefixWord ++ tailWord_7602674) baseStart_7602674 baseEnd_7602674 := by
    simpa [prefixWord, tailWord_7602674, baseEnd_7602674] using wordTrace_append hprefix tailTrace_7602674
  have hstable : (prefixWord ++ tailWord_7602674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602674).length < 2 ^ (prefixWord ++ tailWord_7602674).sum := by decide
  have hdescent : baseEnd_7602674 < baseStart_7602674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602693 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7602693 : Nat := 118140960795 + 7602693 * 2 ^ 59
def prefixEnd_7602693 : Nat := 4983230072969 + 3 ^ 40 * 7602693 * 2
def baseEnd_7602693 : Nat := 3903835777572928162373357

theorem tailTrace_7602693 : CollatzResearch.WordTrace tailWord_7602693 prefixEnd_7602693 3903835777572928162373357 := by
  unfold tailWord_7602693
  simp only [CollatzResearch.WordTrace]
  refine ⟨277292994245749172435692733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184861996163832781623795155 277292994245749172435692733)
  ·
    refine ⟨103984872842155939663384775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277292994245749172435692733 103984872842155939663384775)
    ·
      refine ⟨155977309263233909495077163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103984872842155939663384775 155977309263233909495077163)
      ·
        refine ⟨233965963894850864242615745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155977309263233909495077163 233965963894850864242615745)
        ·
          refine ⟨175474472921138148181961809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233965963894850864242615745 175474472921138148181961809)
          ·
            refine ⟨131605854690853611136471357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175474472921138148181961809 131605854690853611136471357)
            ·
              refine ⟨49352195509070104176176759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131605854690853611136471357 49352195509070104176176759)
              ·
                refine ⟨74028293263605156264265139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49352195509070104176176759 74028293263605156264265139)
                ·
                  refine ⟨111042439895407734396397709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74028293263605156264265139 111042439895407734396397709)
                  ·
                    refine ⟨41640914960777900398649141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 111042439895407734396397709 41640914960777900398649141)
                    ·
                      refine ⟨3903835777572928162373357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41640914960777900398649141 3903835777572928162373357)
                      ·
                        rfl

theorem cell23_7602693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7602693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602693 prefixEnd_7602693 := by exact prefixLift 7602693
  have htrace : WordTrace (prefixWord ++ tailWord_7602693) baseStart_7602693 baseEnd_7602693 := by
    simpa [prefixWord, tailWord_7602693, baseEnd_7602693] using wordTrace_append hprefix tailTrace_7602693
  have hstable : (prefixWord ++ tailWord_7602693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602693).length < 2 ^ (prefixWord ++ tailWord_7602693).sum := by decide
  have hdescent : baseEnd_7602693 < baseStart_7602693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602701 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_7602701 : Nat := 118140960795 + 7602701 * 2 ^ 59
def prefixEnd_7602701 : Nat := 4983230072969 + 3 ^ 40 * 7602701 * 2
def baseEnd_7602701 : Nat := 3903839885418164131073321

theorem tailTrace_7602701 : CollatzResearch.WordTrace tailWord_7602701 prefixEnd_7602701 3903839885418164131073321 := by
  unfold tailWord_7602701
  simp only [CollatzResearch.WordTrace]
  refine ⟨277293286029720189801983957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184862190686480126534655971 277293286029720189801983957)
  ·
    refine ⟨6499061391321566948483999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 277293286029720189801983957 6499061391321566948483999)
    ·
      refine ⟨9748592086982350422725999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499061391321566948483999 9748592086982350422725999)
      ·
        refine ⟨14622888130473525634088999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748592086982350422725999 14622888130473525634088999)
        ·
          refine ⟨21934332195710288451133499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14622888130473525634088999 21934332195710288451133499)
          ·
            refine ⟨32901498293565432676700249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21934332195710288451133499 32901498293565432676700249)
            ·
              refine ⟨24676123720174074507525187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32901498293565432676700249 24676123720174074507525187)
              ·
                refine ⟨37014185580261111761287781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24676123720174074507525187 37014185580261111761287781)
                ·
                  refine ⟨6940159796298958455241459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37014185580261111761287781 6940159796298958455241459)
                  ·
                    refine ⟨10410239694448437682862189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6940159796298958455241459 10410239694448437682862189)
                    ·
                      refine ⟨3903839885418164131073321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410239694448437682862189 3903839885418164131073321)
                      ·
                        rfl

theorem cell23_7602701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_7602701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602701 prefixEnd_7602701 := by exact prefixLift 7602701
  have htrace : WordTrace (prefixWord ++ tailWord_7602701) baseStart_7602701 baseEnd_7602701 := by
    simpa [prefixWord, tailWord_7602701, baseEnd_7602701] using wordTrace_append hprefix tailTrace_7602701
  have hstable : (prefixWord ++ tailWord_7602701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602701).length < 2 ^ (prefixWord ++ tailWord_7602701).sum := by decide
  have hdescent : baseEnd_7602701 < baseStart_7602701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602707 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 4, 2, 2]
def baseStart_7602707 : Nat := 118140960795 + 7602707 * 2 ^ 59
def prefixEnd_7602707 : Nat := 4983230072969 + 3 ^ 40 * 7602707 * 2
def baseEnd_7602707 : Nat := 3903842966302091107598293

theorem tailTrace_7602707 : CollatzResearch.WordTrace tailWord_7602707 prefixEnd_7602707 3903842966302091107598293 := by
  unfold tailWord_7602707
  simp only [CollatzResearch.WordTrace]
  refine ⟨277293504867698452826702375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184862336578465635217801583 277293504867698452826702375)
  ·
    refine ⟨415940257301547679240053563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277293504867698452826702375 415940257301547679240053563)
    ·
      refine ⟨623910385952321518860080345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415940257301547679240053563 623910385952321518860080345)
      ·
        refine ⟨467932789464241139145060259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623910385952321518860080345 467932789464241139145060259)
        ·
          refine ⟨701899184196361708717590389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467932789464241139145060259 701899184196361708717590389)
          ·
            refine ⟨65803048518408910192274099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 701899184196361708717590389 65803048518408910192274099)
            ·
              refine ⟨98704572777613365288411149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65803048518408910192274099 98704572777613365288411149)
              ·
                refine ⟨37014214791605011983154181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98704572777613365288411149 37014214791605011983154181)
                ·
                  refine ⟨6940165273425939746841409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37014214791605011983154181 6940165273425939746841409)
                  ·
                    refine ⟨5205123955069454810131057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940165273425939746841409 5205123955069454810131057)
                    ·
                      refine ⟨3903842966302091107598293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205123955069454810131057 3903842966302091107598293)
                      ·
                        rfl

theorem cell23_7602707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 2, 2].length) (baseStart_7602707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602707 prefixEnd_7602707 := by exact prefixLift 7602707
  have htrace : WordTrace (prefixWord ++ tailWord_7602707) baseStart_7602707 baseEnd_7602707 := by
    simpa [prefixWord, tailWord_7602707, baseEnd_7602707] using wordTrace_append hprefix tailTrace_7602707
  have hstable : (prefixWord ++ tailWord_7602707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602707).length < 2 ^ (prefixWord ++ tailWord_7602707).sum := by decide
  have hdescent : baseEnd_7602707 < baseStart_7602707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602758 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7602758 : Nat := 118140960795 + 7602758 * 2 ^ 59
def prefixEnd_7602758 : Nat := 4983230072969 + 3 ^ 40 * 7602758 * 2
def baseEnd_7602758 : Nat := 3903869153815470408060559

theorem tailTrace_7602758 : CollatzResearch.WordTrace tailWord_7602758 prefixEnd_7602758 3903869153815470408060559 := by
  unfold tailWord_7602758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665480155953552766775279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184863576660342459024539285 8665480155953552766775279)
  ·
    refine ⟨12998220233930329150162919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8665480155953552766775279 12998220233930329150162919)
    ·
      refine ⟨19497330350895493725244379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12998220233930329150162919 19497330350895493725244379)
      ·
        refine ⟨29245995526343240587866569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19497330350895493725244379 29245995526343240587866569)
        ·
          refine ⟨21934496644757430440899927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29245995526343240587866569 21934496644757430440899927)
          ·
            refine ⟨32901744967136145661349891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21934496644757430440899927 32901744967136145661349891)
            ·
              refine ⟨49352617450704218492024837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32901744967136145661349891 49352617450704218492024837)
              ·
                refine ⟨9253615772007040967254657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49352617450704218492024837 9253615772007040967254657)
                ·
                  refine ⟨6940211829005280725440993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253615772007040967254657 6940211829005280725440993)
                  ·
                    refine ⟨5205158871753960544080745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940211829005280725440993 5205158871753960544080745)
                    ·
                      refine ⟨3903869153815470408060559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205158871753960544080745 3903869153815470408060559)
                      ·
                        rfl

theorem cell23_7602758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7602758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602758 prefixEnd_7602758 := by exact prefixLift 7602758
  have htrace : WordTrace (prefixWord ++ tailWord_7602758) baseStart_7602758 baseEnd_7602758 := by
    simpa [prefixWord, tailWord_7602758, baseEnd_7602758] using wordTrace_append hprefix tailTrace_7602758
  have hstable : (prefixWord ++ tailWord_7602758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602758).length < 2 ^ (prefixWord ++ tailWord_7602758).sum := by decide
  have hdescent : baseEnd_7602758 < baseStart_7602758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602770 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_7602770 : Nat := 118140960795 + 7602770 * 2 ^ 59
def prefixEnd_7602770 : Nat := 4983230072969 + 3 ^ 40 * 7602770 * 2
def baseEnd_7602770 : Nat := 3903875315583324361110503

theorem tailTrace_7602770 : CollatzResearch.WordTrace tailWord_7602770 prefixEnd_7602770 3903875315583324361110503 := by
  unfold tailWord_7602770
  simp only [CollatzResearch.WordTrace]
  refine ⟨69323950666617553646561441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184863868444313476390830509 69323950666617553646561441)
  ·
    refine ⟨51992962999963165234921081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69323950666617553646561441 51992962999963165234921081)
    ·
      refine ⟨38994722249972373926190811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51992962999963165234921081 38994722249972373926190811)
      ·
        refine ⟨58492083374958560889286217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38994722249972373926190811 58492083374958560889286217)
        ·
          refine ⟨43869062531218920666964663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58492083374958560889286217 43869062531218920666964663)
          ·
            refine ⟨65803593796828381000446995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43869062531218920666964663 65803593796828381000446995)
            ·
              refine ⟨98705390695242571500670493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65803593796828381000446995 98705390695242571500670493)
              ·
                refine ⟨37014521510715964312751435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98705390695242571500670493 37014521510715964312751435)
                ·
                  refine ⟨55521782266073946469127153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37014521510715964312751435 55521782266073946469127153)
                  ·
                    refine ⟨41641336699555459851845365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55521782266073946469127153 41641336699555459851845365)
                    ·
                      refine ⟨3903875315583324361110503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41641336699555459851845365 3903875315583324361110503)
                      ·
                        rfl

theorem cell23_7602770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_7602770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602770 prefixEnd_7602770 := by exact prefixLift 7602770
  have htrace : WordTrace (prefixWord ++ tailWord_7602770) baseStart_7602770 baseEnd_7602770 := by
    simpa [prefixWord, tailWord_7602770, baseEnd_7602770] using wordTrace_append hprefix tailTrace_7602770
  have hstable : (prefixWord ++ tailWord_7602770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602770).length < 2 ^ (prefixWord ++ tailWord_7602770).sum := by decide
  have hdescent : baseEnd_7602770 < baseStart_7602770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602797 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_7602797 : Nat := 118140960795 + 7602797 * 2 ^ 59
def prefixEnd_7602797 : Nat := 4983230072969 + 3 ^ 40 * 7602797 * 2
def baseEnd_7602797 : Nat := 3903889179560995755472879

theorem tailTrace_7602797 : CollatzResearch.WordTrace tailWord_7602797 prefixEnd_7602797 3903889179560995755472879 := by
  unfold tailWord_7602797
  simp only [CollatzResearch.WordTrace]
  refine ⟨277296787437372398197478645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184864524958248265464985763 277296787437372398197478645)
  ·
    refine ⟨25996573822253662331013623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277296787437372398197478645 25996573822253662331013623)
    ·
      refine ⟨38994860733380493496520435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25996573822253662331013623 38994860733380493496520435)
      ·
        refine ⟨58492291100070740244780653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38994860733380493496520435 58492291100070740244780653)
        ·
          refine ⟨21934609162526527591792745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58492291100070740244780653 21934609162526527591792745)
          ·
            refine ⟨16450956871894895693844559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21934609162526527591792745 16450956871894895693844559)
            ·
              refine ⟨24676435307842343540766839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16450956871894895693844559 24676435307842343540766839)
              ·
                refine ⟨37014652961763515311150259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24676435307842343540766839 37014652961763515311150259)
                ·
                  refine ⟨55521979442645272966725389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37014652961763515311150259 55521979442645272966725389)
                  ·
                    refine ⟨20820742290991977362522021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55521979442645272966725389 20820742290991977362522021)
                    ·
                      refine ⟨3903889179560995755472879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20820742290991977362522021 3903889179560995755472879)
                      ·
                        rfl

theorem cell23_7602797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_7602797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602797 prefixEnd_7602797 := by exact prefixLift 7602797
  have htrace : WordTrace (prefixWord ++ tailWord_7602797) baseStart_7602797 baseEnd_7602797 := by
    simpa [prefixWord, tailWord_7602797, baseEnd_7602797] using wordTrace_append hprefix tailTrace_7602797
  have hstable : (prefixWord ++ tailWord_7602797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602797).length < 2 ^ (prefixWord ++ tailWord_7602797).sum := by decide
  have hdescent : baseEnd_7602797 < baseStart_7602797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602817 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_7602817 : Nat := 118140960795 + 7602817 * 2 ^ 59
def prefixEnd_7602817 : Nat := 4983230072969 + 3 ^ 40 * 7602817 * 2
def baseEnd_7602817 : Nat := 3903899449174085677222787

theorem tailTrace_7602817 : CollatzResearch.WordTrace tailWord_7602817 prefixEnd_7602817 3903899449174085677222787 := by
  unfold tailWord_7602817
  simp only [CollatzResearch.WordTrace]
  refine ⟨277297516897299941613206705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184865011264866627742137803 277297516897299941613206705)
  ·
    refine ⟨207973137672974956209905029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277297516897299941613206705 207973137672974956209905029)
    ·
      refine ⟨38994963313682804289357193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207973137672974956209905029 38994963313682804289357193)
      ·
        refine ⟨29246222485262103217017895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38994963313682804289357193 29246222485262103217017895)
        ·
          refine ⟨43869333727893154825526843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29246222485262103217017895 43869333727893154825526843)
          ·
            refine ⟨65804000591839732238290265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43869333727893154825526843 65804000591839732238290265)
            ·
              refine ⟨49353000443879799178717699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65804000591839732238290265 49353000443879799178717699)
              ·
                refine ⟨74029500665819698768076549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49353000443879799178717699 74029500665819698768076549)
                ·
                  refine ⟨13880531374841193519014353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74029500665819698768076549 13880531374841193519014353)
                  ·
                    refine ⟨10410398531130895139260765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13880531374841193519014353 10410398531130895139260765)
                    ·
                      refine ⟨3903899449174085677222787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410398531130895139260765 3903899449174085677222787)
                      ·
                        rfl

theorem cell23_7602817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_7602817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602817 prefixEnd_7602817 := by exact prefixLift 7602817
  have htrace : WordTrace (prefixWord ++ tailWord_7602817) baseStart_7602817 baseEnd_7602817 := by
    simpa [prefixWord, tailWord_7602817, baseEnd_7602817] using wordTrace_append hprefix tailTrace_7602817
  have hstable : (prefixWord ++ tailWord_7602817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602817).length < 2 ^ (prefixWord ++ tailWord_7602817).sum := by decide
  have hdescent : baseEnd_7602817 < baseStart_7602817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602840 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_7602840 : Nat := 118140960795 + 7602840 * 2 ^ 59
def prefixEnd_7602840 : Nat := 4983230072969 + 3 ^ 40 * 7602840 * 2
def baseEnd_7602840 : Nat := 3903911259229139087235181

theorem tailTrace_7602840 : CollatzResearch.WordTrace tailWord_7602840 prefixEnd_7602840 3903911259229139087235181 := by
  unfold tailWord_7602840
  simp only [CollatzResearch.WordTrace]
  refine ⟨138649177888108308270646987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184865570517477744360862649 138649177888108308270646987)
  ·
    refine ⟨207973766832162462405970481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138649177888108308270646987 207973766832162462405970481)
    ·
      refine ⟨155980325124121846804477861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207973766832162462405970481 155980325124121846804477861)
      ·
        refine ⟨29246310960772846275839599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155980325124121846804477861 29246310960772846275839599)
        ·
          refine ⟨43869466441159269413759399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29246310960772846275839599 43869466441159269413759399)
          ·
            refine ⟨65804199661738904120639099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43869466441159269413759399 65804199661738904120639099)
            ·
              refine ⟨98706299492608356180958649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65804199661738904120639099 98706299492608356180958649)
              ·
                refine ⟨74029724619456267135718987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98706299492608356180958649 74029724619456267135718987)
                ·
                  refine ⟨111044586929184400703578481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74029724619456267135718987 111044586929184400703578481)
                  ·
                    refine ⟨83283440196888300527683861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 111044586929184400703578481 83283440196888300527683861)
                    ·
                      refine ⟨3903911259229139087235181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83283440196888300527683861 3903911259229139087235181)
                      ·
                        rfl

theorem cell23_7602840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_7602840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602840 prefixEnd_7602840 := by exact prefixLift 7602840
  have htrace : WordTrace (prefixWord ++ tailWord_7602840) baseStart_7602840 baseEnd_7602840 := by
    simpa [prefixWord, tailWord_7602840, baseEnd_7602840] using wordTrace_append hprefix tailTrace_7602840
  have hstable : (prefixWord ++ tailWord_7602840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602840).length < 2 ^ (prefixWord ++ tailWord_7602840).sum := by decide
  have hdescent : baseEnd_7602840 < baseStart_7602840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602867 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 1, 5]
def baseStart_7602867 : Nat := 118140960795 + 7602867 * 2 ^ 59
def prefixEnd_7602867 : Nat := 4983230072969 + 3 ^ 40 * 7602867 * 2
def baseEnd_7602867 : Nat := 1301308374402270160532519

theorem tailTrace_7602867 : CollatzResearch.WordTrace tailWord_7602867 prefixEnd_7602867 1301308374402270160532519 := by
  unfold tailWord_7602867
  simp only [CollatzResearch.WordTrace]
  refine ⟨277299340547118800152526855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184866227031412533435017903 277299340547118800152526855)
  ·
    refine ⟨415949010820678200228790283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277299340547118800152526855 415949010820678200228790283)
    ·
      refine ⟨623923516231017300343185425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415949010820678200228790283 623923516231017300343185425)
      ·
        refine ⟨467942637173262975257389069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623923516231017300343185425 467942637173262975257389069)
        ·
          refine ⟨175478488939973615721520901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467942637173262975257389069 175478488939973615721520901)
          ·
            refine ⟨32902216676245052947785169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175478488939973615721520901 32902216676245052947785169)
            ·
              refine ⟨24676662507183789710838877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32902216676245052947785169 24676662507183789710838877)
              ·
                refine ⟨9253748440193921141564579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24676662507183789710838877 9253748440193921141564579)
                ·
                  refine ⟨13880622660290881712346869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253748440193921141564579 13880622660290881712346869)
                  ·
                    refine ⟨1301308374402270160532519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13880622660290881712346869 1301308374402270160532519)
                    ·
                      rfl

theorem cell23_7602867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 5].length) (baseStart_7602867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602867 prefixEnd_7602867 := by exact prefixLift 7602867
  have htrace : WordTrace (prefixWord ++ tailWord_7602867) baseStart_7602867 baseEnd_7602867 := by
    simpa [prefixWord, tailWord_7602867, baseEnd_7602867] using wordTrace_append hprefix tailTrace_7602867
  have hstable : (prefixWord ++ tailWord_7602867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602867).length < 2 ^ (prefixWord ++ tailWord_7602867).sum := by decide
  have hdescent : baseEnd_7602867 < baseStart_7602867 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602874 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2]
def baseStart_7602874 : Nat := 118140960795 + 7602874 * 2 ^ 59
def prefixEnd_7602874 : Nat := 4983230072969 + 3 ^ 40 * 7602874 * 2
def baseEnd_7602874 : Nat := 3903928717571391954210025

theorem tailTrace_7602874 : CollatzResearch.WordTrace tailWord_7602874 prefixEnd_7602874 3903928717571391954210025 := by
  unfold tailWord_7602874
  simp only [CollatzResearch.WordTrace]
  refine ⟨69324898964523360087007919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184866397238728960232021117 69324898964523360087007919)
  ·
    refine ⟨103987348446785040130511879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69324898964523360087007919 103987348446785040130511879)
    ·
      refine ⟨155981022670177560195767819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103987348446785040130511879 155981022670177560195767819)
      ·
        refine ⟨233971534005266340293651729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155981022670177560195767819 233971534005266340293651729)
        ·
          refine ⟨175478650503949755220238797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233971534005266340293651729 175478650503949755220238797)
          ·
            refine ⟨65804493938981158207589549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175478650503949755220238797 65804493938981158207589549)
            ·
              refine ⟨24676685227117934327846081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65804493938981158207589549 24676685227117934327846081)
              ·
                refine ⟨18507513920338450745884561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24676685227117934327846081 18507513920338450745884561)
                ·
                  refine ⟨13880635440253838059413421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18507513920338450745884561 13880635440253838059413421)
                  ·
                    refine ⟨5205238290095189272280033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13880635440253838059413421 5205238290095189272280033)
                    ·
                      refine ⟨3903928717571391954210025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205238290095189272280033 3903928717571391954210025)
                      ·
                        rfl

theorem cell23_7602874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_7602874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602874 prefixEnd_7602874 := by exact prefixLift 7602874
  have htrace : WordTrace (prefixWord ++ tailWord_7602874) baseStart_7602874 baseEnd_7602874 := by
    simpa [prefixWord, tailWord_7602874, baseEnd_7602874] using wordTrace_append hprefix tailTrace_7602874
  have hstable : (prefixWord ++ tailWord_7602874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602874).length < 2 ^ (prefixWord ++ tailWord_7602874).sum := by decide
  have hdescent : baseEnd_7602874 < baseStart_7602874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602887 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_7602887 : Nat := 118140960795 + 7602887 * 2 ^ 59
def prefixEnd_7602887 : Nat := 4983230072969 + 3 ^ 40 * 7602887 * 2
def baseEnd_7602887 : Nat := 3903935392819900403347465

theorem tailTrace_7602887 : CollatzResearch.WordTrace tailWord_7602887 prefixEnd_7602887 3903935392819900403347465 := by
  unfold tailWord_7602887
  simp only [CollatzResearch.WordTrace]
  refine ⟨277300070007046343568254915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184866713338030895712169943 277300070007046343568254915)
  ·
    refine ⟨415950105010569515352382373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277300070007046343568254915 415950105010569515352382373)
    ·
      refine ⟨77990644689481784128571695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 415950105010569515352382373 77990644689481784128571695)
      ·
        refine ⟨116985967034222676192857543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77990644689481784128571695 116985967034222676192857543)
        ·
          refine ⟨175478950551334014289286315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116985967034222676192857543 175478950551334014289286315)
          ·
            refine ⟨263218425827001021433929473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175478950551334014289286315 263218425827001021433929473)
            ·
              refine ⟨197413819370250766075447105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263218425827001021433929473 197413819370250766075447105)
              ·
                refine ⟨148060364527688074556585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197413819370250766075447105 148060364527688074556585329)
                ·
                  refine ⟨111045273395766055917438997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148060364527688074556585329 111045273395766055917438997)
                  ·
                    refine ⟨5205247190426533871129953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111045273395766055917438997 5205247190426533871129953)
                    ·
                      refine ⟨3903935392819900403347465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205247190426533871129953 3903935392819900403347465)
                      ·
                        rfl

theorem cell23_7602887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_7602887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602887 prefixEnd_7602887 := by exact prefixLift 7602887
  have htrace : WordTrace (prefixWord ++ tailWord_7602887) baseStart_7602887 baseEnd_7602887 := by
    simpa [prefixWord, tailWord_7602887, baseEnd_7602887] using wordTrace_append hprefix tailTrace_7602887
  have hstable : (prefixWord ++ tailWord_7602887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602887).length < 2 ^ (prefixWord ++ tailWord_7602887).sum := by decide
  have hdescent : baseEnd_7602887 < baseStart_7602887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602904 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_7602904 : Nat := 118140960795 + 7602904 * 2 ^ 59
def prefixEnd_7602904 : Nat := 4983230072969 + 3 ^ 40 * 7602904 * 2
def baseEnd_7602904 : Nat := 3903944121991026836834887

theorem tailTrace_7602904 : CollatzResearch.WordTrace tailWord_7602904 prefixEnd_7602904 3903944121991026836834887 := by
  unfold tailWord_7602904
  simp only [CollatzResearch.WordTrace]
  refine ⟨138650345023992377735811883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184867126698656503647749177 138650345023992377735811883)
  ·
    refine ⟨207975517535988566603717825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138650345023992377735811883 207975517535988566603717825)
    ·
      refine ⟨155981638151991424952788369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207975517535988566603717825 155981638151991424952788369)
      ·
        refine ⟨116986228613993568714591277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155981638151991424952788369 116986228613993568714591277)
        ·
          refine ⟨43869835730247588267971729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116986228613993568714591277 43869835730247588267971729)
          ·
            refine ⟨32902376797685691200978797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43869835730247588267971729 32902376797685691200978797)
            ·
              refine ⟨12338391299132134200367049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32902376797685691200978797 12338391299132134200367049)
              ·
                refine ⟨9253793474349100650275287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12338391299132134200367049 9253793474349100650275287)
                ·
                  refine ⟨13880690211523650975412931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253793474349100650275287 13880690211523650975412931)
                  ·
                    refine ⟨20821035317285476463119397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13880690211523650975412931 20821035317285476463119397)
                    ·
                      refine ⟨3903944121991026836834887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20821035317285476463119397 3903944121991026836834887)
                      ·
                        rfl

theorem cell23_7602904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_7602904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602904 prefixEnd_7602904 := by exact prefixLift 7602904
  have htrace : WordTrace (prefixWord ++ tailWord_7602904) baseStart_7602904 baseEnd_7602904 := by
    simpa [prefixWord, tailWord_7602904, baseEnd_7602904] using wordTrace_append hprefix tailTrace_7602904
  have hstable : (prefixWord ++ tailWord_7602904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602904).length < 2 ^ (prefixWord ++ tailWord_7602904).sum := by decide
  have hdescent : baseEnd_7602904 < baseStart_7602904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602908 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_7602908 : Nat := 118140960795 + 7602908 * 2 ^ 59
def prefixEnd_7602908 : Nat := 4983230072969 + 3 ^ 40 * 7602908 * 2
def baseEnd_7602908 : Nat := 3903946175913644821184869

theorem tailTrace_7602908 : CollatzResearch.WordTrace tailWord_7602908 prefixEnd_7602908 3903946175913644821184869 := by
  unfold tailWord_7602908
  simp only [CollatzResearch.WordTrace]
  refine ⟨138650417969985132077384689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184867223959980176103179585 138650417969985132077384689)
  ·
    refine ⟨103987813477488849058038517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138650417969985132077384689 103987813477488849058038517)
    ·
      refine ⟨9748857513514579599191111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103987813477488849058038517 9748857513514579599191111)
      ·
        refine ⟨14623286270271869398786667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748857513514579599191111 14623286270271869398786667)
        ·
          refine ⟨21934929405407804098180001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623286270271869398786667 21934929405407804098180001)
          ·
            refine ⟨16451197054055853073635001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21934929405407804098180001 16451197054055853073635001)
            ·
              refine ⟨12338397790541889805226251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16451197054055853073635001 12338397790541889805226251)
              ·
                refine ⟨18507596685812834707839377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338397790541889805226251 18507596685812834707839377)
                ·
                  refine ⟨13880697514359626030879533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18507596685812834707839377 13880697514359626030879533)
                  ·
                    refine ⟨5205261567884859761579825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13880697514359626030879533 5205261567884859761579825)
                    ·
                      refine ⟨3903946175913644821184869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205261567884859761579825 3903946175913644821184869)
                      ·
                        rfl

theorem cell23_7602908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_7602908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602908 prefixEnd_7602908 := by exact prefixLift 7602908
  have htrace : WordTrace (prefixWord ++ tailWord_7602908) baseStart_7602908 baseEnd_7602908 := by
    simpa [prefixWord, tailWord_7602908, baseEnd_7602908] using wordTrace_append hprefix tailTrace_7602908
  have hstable : (prefixWord ++ tailWord_7602908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602908).length < 2 ^ (prefixWord ++ tailWord_7602908).sum := by decide
  have hdescent : baseEnd_7602908 < baseStart_7602908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602917 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7602917 : Nat := 118140960795 + 7602917 * 2 ^ 59
def prefixEnd_7602917 : Nat := 4983230072969 + 3 ^ 40 * 7602917 * 2
def baseEnd_7602917 : Nat := 3903950797239535285972327

theorem tailTrace_7602917 : CollatzResearch.WordTrace tailWord_7602917 prefixEnd_7602917 3903950797239535285972327 := by
  unfold tailWord_7602917
  simp only [CollatzResearch.WordTrace]
  refine ⟨277301164196937658691847005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184867442797958439127898003 277301164196937658691847005)
  ·
    refine ⟨103987936573851622009442627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277301164196937658691847005 103987936573851622009442627)
    ·
      refine ⟨155981904860777433014163941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103987936573851622009442627 155981904860777433014163941)
      ·
        refine ⟨29246607161395768690155739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155981904860777433014163941 29246607161395768690155739)
        ·
          refine ⟨43869910742093653035233609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29246607161395768690155739 43869910742093653035233609)
          ·
            refine ⟨32902433056570239776425207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43869910742093653035233609 32902433056570239776425207)
            ·
              refine ⟨49353649584855359664637811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32902433056570239776425207 49353649584855359664637811)
              ·
                refine ⟨74030474377283039496956717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49353649584855359664637811 74030474377283039496956717)
                ·
                  refine ⟨27761427891481139811358769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74030474377283039496956717 27761427891481139811358769)
                  ·
                    refine ⟨20821070918610854858519077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27761427891481139811358769 20821070918610854858519077)
                    ·
                      refine ⟨3903950797239535285972327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20821070918610854858519077 3903950797239535285972327)
                      ·
                        rfl

theorem cell23_7602917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7602917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602917 prefixEnd_7602917 := by exact prefixLift 7602917
  have htrace : WordTrace (prefixWord ++ tailWord_7602917) baseStart_7602917 baseEnd_7602917 := by
    simpa [prefixWord, tailWord_7602917, baseEnd_7602917] using wordTrace_append hprefix tailTrace_7602917
  have hstable : (prefixWord ++ tailWord_7602917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602917).length < 2 ^ (prefixWord ++ tailWord_7602917).sum := by decide
  have hdescent : baseEnd_7602917 < baseStart_7602917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602932 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_7602932 : Nat := 118140960795 + 7602932 * 2 ^ 59
def prefixEnd_7602932 : Nat := 4983230072969 + 3 ^ 40 * 7602932 * 2
def baseEnd_7602932 : Nat := 3903958499449352727284759

theorem tailTrace_7602932 : CollatzResearch.WordTrace tailWord_7602932 prefixEnd_7602932 3903958499449352727284759 := by
  unfold tailWord_7602932
  simp only [CollatzResearch.WordTrace]
  refine ⟨138650855645941658126821525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184867807527922210835762033 138650855645941658126821525)
  ·
    refine ⟨6499258858403515224694759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 138650855645941658126821525 6499258858403515224694759)
    ·
      refine ⟨9748888287605272837042139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499258858403515224694759 9748888287605272837042139)
      ·
        refine ⟨14623332431407909255563209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9748888287605272837042139 14623332431407909255563209)
        ·
          refine ⟨10967499323555931941672407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14623332431407909255563209 10967499323555931941672407)
          ·
            refine ⟨16451248985333897912508611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10967499323555931941672407 16451248985333897912508611)
            ·
              refine ⟨24676873478000846868762917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16451248985333897912508611 24676873478000846868762917)
              ·
                refine ⟨4626913777125158787893047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24676873478000846868762917 4626913777125158787893047)
                ·
                  refine ⟨6940370665687738181839571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626913777125158787893047 6940370665687738181839571)
                  ·
                    refine ⟨10410555998531607272759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6940370665687738181839571 10410555998531607272759357)
                    ·
                      refine ⟨3903958499449352727284759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410555998531607272759357 3903958499449352727284759)
                      ·
                        rfl

theorem cell23_7602932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_7602932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602932 prefixEnd_7602932 := by exact prefixLift 7602932
  have htrace : WordTrace (prefixWord ++ tailWord_7602932) baseStart_7602932 baseEnd_7602932 := by
    simpa [prefixWord, tailWord_7602932, baseEnd_7602932] using wordTrace_append hprefix tailTrace_7602932
  have hstable : (prefixWord ++ tailWord_7602932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602932).length < 2 ^ (prefixWord ++ tailWord_7602932).sum := by decide
  have hdescent : baseEnd_7602932 < baseStart_7602932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602954 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_7602954 : Nat := 118140960795 + 7602954 * 2 ^ 59
def prefixEnd_7602954 : Nat := 4983230072969 + 3 ^ 40 * 7602954 * 2
def baseEnd_7602954 : Nat := 3903969796023751641209657

theorem tailTrace_7602954 : CollatzResearch.WordTrace tailWord_7602954 prefixEnd_7602954 3903969796023751641209657 := by
  unfold tailWord_7602954
  simp only [CollatzResearch.WordTrace]
  refine ⟨69325628424450903502735979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184868342465202409340629277 69325628424450903502735979)
  ·
    refine ⟨103988442636676355254103969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69325628424450903502735979 103988442636676355254103969)
    ·
      refine ⟨77991331977507266440577977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103988442636676355254103969 77991331977507266440577977)
      ·
        refine ⟨58493498983130449830433483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77991331977507266440577977 58493498983130449830433483)
        ·
          refine ⟨87740248474695674745650225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58493498983130449830433483 87740248474695674745650225)
          ·
            refine ⟨65805186356021756059237669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87740248474695674745650225 65805186356021756059237669)
            ·
              refine ⟨12338472441754079261107063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65805186356021756059237669 12338472441754079261107063)
              ·
                refine ⟨18507708662631118891660595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338472441754079261107063 18507708662631118891660595)
                ·
                  refine ⟨27761562993946678337490893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18507708662631118891660595 27761562993946678337490893)
                  ·
                    refine ⟨10410586122730004376559085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27761562993946678337490893 10410586122730004376559085)
                    ·
                      refine ⟨3903969796023751641209657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410586122730004376559085 3903969796023751641209657)
                      ·
                        rfl

theorem cell23_7602954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_7602954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602954 prefixEnd_7602954 := by exact prefixLift 7602954
  have htrace : WordTrace (prefixWord ++ tailWord_7602954) baseStart_7602954 baseEnd_7602954 := by
    simpa [prefixWord, tailWord_7602954, baseEnd_7602954] using wordTrace_append hprefix tailTrace_7602954
  have hstable : (prefixWord ++ tailWord_7602954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602954).length < 2 ^ (prefixWord ++ tailWord_7602954).sum := by decide
  have hdescent : baseEnd_7602954 < baseStart_7602954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7602981 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 1, 3, 2]
def baseStart_7602981 : Nat := 118140960795 + 7602981 * 2 ^ 59
def prefixEnd_7602981 : Nat := 4983230072969 + 3 ^ 40 * 7602981 * 2
def baseEnd_7602981 : Nat := 3903983660001423035572033

theorem tailTrace_7602981 : CollatzResearch.WordTrace tailWord_7602981 prefixEnd_7602981 3903983660001423035572033 := by
  unfold tailWord_7602981
  simp only [CollatzResearch.WordTrace]
  refine ⟨277303498468705797622176797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184868998979137198414784531 277303498468705797622176797)
  ·
    refine ⟨103988811925764674108316299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277303498468705797622176797 103988811925764674108316299)
    ·
      refine ⟨155983217888647011162474449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103988811925764674108316299 155983217888647011162474449)
      ·
        refine ⟨116987413416485258371855837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155983217888647011162474449 116987413416485258371855837)
        ·
          refine ⟨43870280031181971889445939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116987413416485258371855837 43870280031181971889445939)
          ·
            refine ⟨65805420046772957834168909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43870280031181971889445939 65805420046772957834168909)
            ·
              refine ⟨24677032517539859187813341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65805420046772957834168909 24677032517539859187813341)
              ·
                refine ⟨9253887194077447195430003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24677032517539859187813341 9253887194077447195430003)
                ·
                  refine ⟨13880830791116170793145005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9253887194077447195430003 13880830791116170793145005)
                  ·
                    refine ⟨5205311546668564047429377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13880830791116170793145005 5205311546668564047429377)
                    ·
                      refine ⟨3903983660001423035572033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205311546668564047429377 3903983660001423035572033)
                      ·
                        rfl

theorem cell23_7602981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_7602981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7602981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7602981 prefixEnd_7602981 := by exact prefixLift 7602981
  have htrace : WordTrace (prefixWord ++ tailWord_7602981) baseStart_7602981 baseEnd_7602981 := by
    simpa [prefixWord, tailWord_7602981, baseEnd_7602981] using wordTrace_append hprefix tailTrace_7602981
  have hstable : (prefixWord ++ tailWord_7602981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7602981).length < 2 ^ (prefixWord ++ tailWord_7602981).sum := by decide
  have hdescent : baseEnd_7602981 < baseStart_7602981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7602981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603005 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_7603005 : Nat := 118140960795 + 7603005 * 2 ^ 59
def prefixEnd_7603005 : Nat := 4983230072969 + 3 ^ 40 * 7603005 * 2
def baseEnd_7603005 : Nat := 3903995983537130941671923

theorem tailTrace_7603005 : CollatzResearch.WordTrace tailWord_7603005 prefixEnd_7603005 3903995983537130941671923 := by
  unfold tailWord_7603005
  simp only [CollatzResearch.WordTrace]
  refine ⟨277304373820618849721050469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184869582547079233147366979 277304373820618849721050469)
  ·
    refine ⟨51994570091366034322696963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277304373820618849721050469 51994570091366034322696963)
    ·
      refine ⟨77991855137049051484045445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51994570091366034322696963 77991855137049051484045445)
      ·
        refine ⟨14623472838196697153258521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77991855137049051484045445 14623472838196697153258521)
        ·
          refine ⟨10967604628647522864943891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14623472838196697153258521 10967604628647522864943891)
          ·
            refine ⟨16451406942971284297415837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10967604628647522864943891 16451406942971284297415837)
            ·
              refine ⟨6169277603614231611530939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16451406942971284297415837 6169277603614231611530939)
              ·
                refine ⟨9253916405421347417296409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169277603614231611530939 9253916405421347417296409)
                ·
                  refine ⟨6940437304066010562972307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253916405421347417296409 6940437304066010562972307)
                  ·
                    refine ⟨10410655956099015844458461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6940437304066010562972307 10410655956099015844458461)
                    ·
                      refine ⟨3903995983537130941671923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410655956099015844458461 3903995983537130941671923)
                      ·
                        rfl

theorem cell23_7603005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_7603005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603005 prefixEnd_7603005 := by exact prefixLift 7603005
  have htrace : WordTrace (prefixWord ++ tailWord_7603005) baseStart_7603005 baseEnd_7603005 := by
    simpa [prefixWord, tailWord_7603005, baseEnd_7603005] using wordTrace_append hprefix tailTrace_7603005
  have hstable : (prefixWord ++ tailWord_7603005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603005).length < 2 ^ (prefixWord ++ tailWord_7603005).sum := by decide
  have hdescent : baseEnd_7603005 < baseStart_7603005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603017 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 7]
def baseStart_7603017 : Nat := 118140960795 + 7603017 * 2 ^ 59
def prefixEnd_7603017 : Nat := 4983230072969 + 3 ^ 40 * 7603017 * 2
def baseEnd_7603017 : Nat := 433778016144998321635763

theorem tailTrace_7603017 : CollatzResearch.WordTrace tailWord_7603017 prefixEnd_7603017 433778016144998321635763 := by
  unfold tailWord_7603017
  simp only [CollatzResearch.WordTrace]
  refine ⟨277304811496575375770487305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184869874331050250513658203 277304811496575375770487305)
  ·
    refine ⟨207978608622431531827865479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277304811496575375770487305 207978608622431531827865479)
    ·
      refine ⟨311967912933647297741798219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207978608622431531827865479 311967912933647297741798219)
      ·
        refine ⟨467951869400470946612697329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311967912933647297741798219 467951869400470946612697329)
        ·
          refine ⟨350963902050353209959522997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 467951869400470946612697329 350963902050353209959522997)
          ·
            refine ⟨32902865817220613433705281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 350963902050353209959522997 32902865817220613433705281)
            ·
              refine ⟨24677149362915460075278961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32902865817220613433705281 24677149362915460075278961)
              ·
                refine ⟨18507862022186595056459221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24677149362915460075278961 18507862022186595056459221)
                ·
                  refine ⟨433778016144998321635763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18507862022186595056459221 433778016144998321635763)
                  ·
                    rfl

theorem cell23_7603017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 7].length) (baseStart_7603017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603017 prefixEnd_7603017 := by exact prefixLift 7603017
  have htrace : WordTrace (prefixWord ++ tailWord_7603017) baseStart_7603017 baseEnd_7603017 := by
    simpa [prefixWord, tailWord_7603017, baseEnd_7603017] using wordTrace_append hprefix tailTrace_7603017
  have hstable : (prefixWord ++ tailWord_7603017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603017).length < 2 ^ (prefixWord ++ tailWord_7603017).sum := by decide
  have hdescent : baseEnd_7603017 < baseStart_7603017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3]
def baseStart_7603027 : Nat := 118140960795 + 7603027 * 2 ^ 59
def prefixEnd_7603027 : Nat := 4983230072969 + 3 ^ 40 * 7603027 * 2
def baseEnd_7603027 : Nat := 3904007280111529855596821

theorem tailTrace_7603027 : CollatzResearch.WordTrace tailWord_7603027 prefixEnd_7603027 3904007280111529855596821 := by
  unfold tailWord_7603027
  simp only [CollatzResearch.WordTrace]
  refine ⟨277305176226539147478351335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184870117484359431652234223 277305176226539147478351335)
  ·
    refine ⟨415957764339808721217527003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277305176226539147478351335 415957764339808721217527003)
    ·
      refine ⟨623936646509713081826290505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415957764339808721217527003 623936646509713081826290505)
      ·
        refine ⟨467952484882284811369717879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623936646509713081826290505 467952484882284811369717879)
        ·
          refine ⟨701928727323427217054576819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467952484882284811369717879 701928727323427217054576819)
          ·
            refine ⟨1052893090985140825581865229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701928727323427217054576819 1052893090985140825581865229)
            ·
              refine ⟨394834909119427809593199461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1052893090985140825581865229 394834909119427809593199461)
              ·
                refine ⟨74031545459892714298724899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394834909119427809593199461 74031545459892714298724899)
                ·
                  refine ⟨111047318189839071448087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74031545459892714298724899 111047318189839071448087349)
                  ·
                    refine ⟨10410686080297412948258189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111047318189839071448087349 10410686080297412948258189)
                    ·
                      refine ⟨3904007280111529855596821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410686080297412948258189 3904007280111529855596821)
                      ·
                        rfl

theorem cell23_7603027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_7603027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603027 prefixEnd_7603027 := by exact prefixLift 7603027
  have htrace : WordTrace (prefixWord ++ tailWord_7603027) baseStart_7603027 baseEnd_7603027 := by
    simpa [prefixWord, tailWord_7603027, baseEnd_7603027] using wordTrace_append hprefix tailTrace_7603027
  have hstable : (prefixWord ++ tailWord_7603027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603027).length < 2 ^ (prefixWord ++ tailWord_7603027).sum := by decide
  have hdescent : baseEnd_7603027 < baseStart_7603027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603057 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_7603057 : Nat := 118140960795 + 7603057 * 2 ^ 59
def prefixEnd_7603057 : Nat := 4983230072969 + 3 ^ 40 * 7603057 * 2
def baseEnd_7603057 : Nat := 3904022684531164738221683

theorem tailTrace_7603057 : CollatzResearch.WordTrace tailWord_7603057 prefixEnd_7603057 3904022684531164738221683 := by
  unfold tailWord_7603057
  simp only [CollatzResearch.WordTrace]
  refine ⟨277306270416430462601943425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184870846944286975067962283 277306270416430462601943425)
  ·
    refine ⟨207979702812322846951457569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277306270416430462601943425 207979702812322846951457569)
    ·
      refine ⟨155984777109242135213593177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207979702812322846951457569 155984777109242135213593177)
      ·
        refine ⟨116988582831931601410194883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155984777109242135213593177 116988582831931601410194883)
        ·
          refine ⟨175482874247897402115292325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116988582831931601410194883 175482874247897402115292325)
          ·
            refine ⟨32903038921480762896617311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175482874247897402115292325 32903038921480762896617311)
            ·
              refine ⟨49354558382221144344925967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32903038921480762896617311 49354558382221144344925967)
              ·
                refine ⟨74031837573331716517388951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49354558382221144344925967 74031837573331716517388951)
                ·
                  refine ⟨111047756359997574776083427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74031837573331716517388951 111047756359997574776083427)
                  ·
                    refine ⟨166571634539996362164125141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111047756359997574776083427 166571634539996362164125141)
                    ·
                      refine ⟨3904022684531164738221683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166571634539996362164125141 3904022684531164738221683)
                      ·
                        rfl

theorem cell23_7603057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_7603057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603057 prefixEnd_7603057 := by exact prefixLift 7603057
  have htrace : WordTrace (prefixWord ++ tailWord_7603057) baseStart_7603057 baseEnd_7603057 := by
    simpa [prefixWord, tailWord_7603057, baseEnd_7603057] using wordTrace_append hprefix tailTrace_7603057
  have hstable : (prefixWord ++ tailWord_7603057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603057).length < 2 ^ (prefixWord ++ tailWord_7603057).sum := by decide
  have hdescent : baseEnd_7603057 < baseStart_7603057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603062 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_7603062 : Nat := 118140960795 + 7603062 * 2 ^ 59
def prefixEnd_7603062 : Nat := 4983230072969 + 3 ^ 40 * 7603062 * 2
def baseEnd_7603062 : Nat := 3904025251934437218659161

theorem tailTrace_7603062 : CollatzResearch.WordTrace tailWord_7603062 prefixEnd_7603062 3904025251934437218659161 := by
  unfold tailWord_7603062
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331653298838271778492215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184870968520941565637250293 17331653298838271778492215)
  ·
    refine ⟨25997479948257407667738323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17331653298838271778492215 25997479948257407667738323)
    ·
      refine ⟨38996219922386111501607485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25997479948257407667738323 38996219922386111501607485)
      ·
        refine ⟨14623582470894791813102807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38996219922386111501607485 14623582470894791813102807)
        ·
          refine ⟨21935373706342187719654211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623582470894791813102807 21935373706342187719654211)
          ·
            refine ⟨32903060559513281579481317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21935373706342187719654211 32903060559513281579481317)
            ·
              refine ⟨6169323854908740296152747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32903060559513281579481317 6169323854908740296152747)
              ·
                refine ⟨9253985782363110444229121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169323854908740296152747 9253985782363110444229121)
                ·
                  refine ⟨6940489336772332833171841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9253985782363110444229121 6940489336772332833171841)
                  ·
                    refine ⟨5205367002579249624878881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940489336772332833171841 5205367002579249624878881)
                    ·
                      refine ⟨3904025251934437218659161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205367002579249624878881 3904025251934437218659161)
                      ·
                        rfl

theorem cell23_7603062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_7603062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603062 prefixEnd_7603062 := by exact prefixLift 7603062
  have htrace : WordTrace (prefixWord ++ tailWord_7603062) baseStart_7603062 baseEnd_7603062 := by
    simpa [prefixWord, tailWord_7603062, baseEnd_7603062] using wordTrace_append hprefix tailTrace_7603062
  have hstable : (prefixWord ++ tailWord_7603062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603062).length < 2 ^ (prefixWord ++ tailWord_7603062).sum := by decide
  have hdescent : baseEnd_7603062 < baseStart_7603062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603067 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_7603067 : Nat := 118140960795 + 7603067 * 2 ^ 59
def prefixEnd_7603067 : Nat := 4983230072969 + 3 ^ 40 * 7603067 * 2
def baseEnd_7603067 : Nat := 3904027819337709699096637

theorem tailTrace_7603067 : CollatzResearch.WordTrace tailWord_7603067 prefixEnd_7603067 3904027819337709699096637 := by
  unfold tailWord_7603067
  simp only [CollatzResearch.WordTrace]
  refine ⟨277306635146394234309807455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184871090097596156206538303 277306635146394234309807455)
  ·
    refine ⟨415959952719591351464711183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277306635146394234309807455 415959952719591351464711183)
    ·
      refine ⟨623939929079387027197066775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415959952719591351464711183 623939929079387027197066775)
      ·
        refine ⟨935909893619080540795600163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623939929079387027197066775 935909893619080540795600163)
        ·
          refine ⟨1403864840428620811193400245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935909893619080540795600163 1403864840428620811193400245)
          ·
            refine ⟨131612328790183201049381273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1403864840428620811193400245 131612328790183201049381273)
            ·
              refine ⟨98709246592637400787035955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131612328790183201049381273 98709246592637400787035955)
              ·
                refine ⟨148063869888956101180553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98709246592637400787035955 148063869888956101180553933)
                ·
                  refine ⟨55523951208358537942707725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148063869888956101180553933 55523951208358537942707725)
                  ·
                    refine ⟨20821481703134451728515397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55523951208358537942707725 20821481703134451728515397)
                    ·
                      refine ⟨3904027819337709699096637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20821481703134451728515397 3904027819337709699096637)
                      ·
                        rfl

theorem cell23_7603067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_7603067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603067 prefixEnd_7603067 := by exact prefixLift 7603067
  have htrace : WordTrace (prefixWord ++ tailWord_7603067) baseStart_7603067 baseEnd_7603067 := by
    simpa [prefixWord, tailWord_7603067, baseEnd_7603067] using wordTrace_append hprefix tailTrace_7603067
  have hstable : (prefixWord ++ tailWord_7603067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603067).length < 2 ^ (prefixWord ++ tailWord_7603067).sum := by decide
  have hdescent : baseEnd_7603067 < baseStart_7603067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603084 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7603084 : Nat := 118140960795 + 7603084 * 2 ^ 59
def prefixEnd_7603084 : Nat := 4983230072969 + 3 ^ 40 * 7603084 * 2
def baseEnd_7603084 : Nat := 3904036548508836132584059

theorem tailTrace_7603084 : CollatzResearch.WordTrace tailWord_7603084 prefixEnd_7603084 3904036548508836132584059 := by
  unfold tailWord_7603084
  simp only [CollatzResearch.WordTrace]
  refine ⟨138653627593666323106588153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184871503458221764142117537 138653627593666323106588153)
  ·
    refine ⟨103990220695249742329941115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138653627593666323106588153 103990220695249742329941115)
    ·
      refine ⟨155985331042874613494911673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103990220695249742329941115 155985331042874613494911673)
      ·
        refine ⟨116988998282155960121183755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155985331042874613494911673 116988998282155960121183755)
        ·
          refine ⟨175483497423233940181775633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116988998282155960121183755 175483497423233940181775633)
          ·
            refine ⟨131612623067425455136331725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175483497423233940181775633 131612623067425455136331725)
            ·
              refine ⟨49354733650284545676124397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131612623067425455136331725 49354733650284545676124397)
              ·
                refine ⟨18508025118856704628546649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49354733650284545676124397 18508025118856704628546649)
                ·
                  refine ⟨13881018839142528471409987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18508025118856704628546649 13881018839142528471409987)
                  ·
                    refine ⟨20821528258713792707114981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13881018839142528471409987 20821528258713792707114981)
                    ·
                      refine ⟨3904036548508836132584059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20821528258713792707114981 3904036548508836132584059)
                      ·
                        rfl

theorem cell23_7603084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7603084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603084 prefixEnd_7603084 := by exact prefixLift 7603084
  have htrace : WordTrace (prefixWord ++ tailWord_7603084) baseStart_7603084 baseEnd_7603084 := by
    simpa [prefixWord, tailWord_7603084, baseEnd_7603084] using wordTrace_append hprefix tailTrace_7603084
  have hstable : (prefixWord ++ tailWord_7603084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603084).length < 2 ^ (prefixWord ++ tailWord_7603084).sum := by decide
  have hdescent : baseEnd_7603084 < baseStart_7603084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603097 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_7603097 : Nat := 118140960795 + 7603097 * 2 ^ 59
def prefixEnd_7603097 : Nat := 4983230072969 + 3 ^ 40 * 7603097 * 2
def baseEnd_7603097 : Nat := 3904043223757344581721499

theorem tailTrace_7603097 : CollatzResearch.WordTrace tailWord_7603097 prefixEnd_7603097 3904043223757344581721499 := by
  unfold tailWord_7603097
  simp only [CollatzResearch.WordTrace]
  refine ⟨277307729336285549433399545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184871819557523699622266363 277307729336285549433399545)
  ·
    refine ⟨207980797002214162075049659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277307729336285549433399545 207980797002214162075049659)
    ·
      refine ⟨311971195503321243112574489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207980797002214162075049659 311971195503321243112574489)
      ·
        refine ⟨233978396627490932334430867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311971195503321243112574489 233978396627490932334430867)
        ·
          refine ⟨350967594941236398501646301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233978396627490932334430867 350967594941236398501646301)
          ·
            refine ⟨131612848102963649438117363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 350967594941236398501646301 131612848102963649438117363)
            ·
              refine ⟨197419272154445474157176045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131612848102963649438117363 197419272154445474157176045)
              ·
                refine ⟨74032227057917052808941017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197419272154445474157176045 74032227057917052808941017)
                ·
                  refine ⟨55524170293437789606705763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74032227057917052808941017 55524170293437789606705763)
                  ·
                    refine ⟨83286255440156684410058645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55524170293437789606705763 83286255440156684410058645)
                    ·
                      refine ⟨3904043223757344581721499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83286255440156684410058645 3904043223757344581721499)
                      ·
                        rfl

theorem cell23_7603097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_7603097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603097 prefixEnd_7603097 := by exact prefixLift 7603097
  have htrace : WordTrace (prefixWord ++ tailWord_7603097) baseStart_7603097 baseEnd_7603097 := by
    simpa [prefixWord, tailWord_7603097, baseEnd_7603097] using wordTrace_append hprefix tailTrace_7603097
  have hstable : (prefixWord ++ tailWord_7603097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603097).length < 2 ^ (prefixWord ++ tailWord_7603097).sum := by decide
  have hdescent : baseEnd_7603097 < baseStart_7603097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603101 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_7603101 : Nat := 118140960795 + 7603101 * 2 ^ 59
def prefixEnd_7603101 : Nat := 4983230072969 + 3 ^ 40 * 7603101 * 2
def baseEnd_7603101 : Nat := 3904045277679962566071481

theorem tailTrace_7603101 : CollatzResearch.WordTrace tailWord_7603101 prefixEnd_7603101 3904045277679962566071481 := by
  unfold tailWord_7603101
  simp only [CollatzResearch.WordTrace]
  refine ⟨277307875228271058116545157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184871916818847372077696771 277307875228271058116545157)
  ·
    refine ⟨51995226605300823396852217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277307875228271058116545157 51995226605300823396852217)
    ·
      refine ⟨38996419953975617547639163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51995226605300823396852217 38996419953975617547639163)
      ·
        refine ⟨58494629930963426321458745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38996419953975617547639163 58494629930963426321458745)
        ·
          refine ⟨43870972448222569741094059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58494629930963426321458745 43870972448222569741094059)
          ·
            refine ⟨65806458672333854611641089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43870972448222569741094059 65806458672333854611641089)
            ·
              refine ⟨49354844004250390958730817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65806458672333854611641089 49354844004250390958730817)
              ·
                refine ⟨37016133003187793219048113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49354844004250390958730817 37016133003187793219048113)
                ·
                  refine ⟨27762099752390844914286085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37016133003187793219048113 27762099752390844914286085)
                  ·
                    refine ⟨5205393703573283421428641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27762099752390844914286085 5205393703573283421428641)
                    ·
                      refine ⟨3904045277679962566071481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205393703573283421428641 3904045277679962566071481)
                      ·
                        rfl

theorem cell23_7603101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_7603101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603101 prefixEnd_7603101 := by exact prefixLift 7603101
  have htrace : WordTrace (prefixWord ++ tailWord_7603101) baseStart_7603101 baseEnd_7603101 := by
    simpa [prefixWord, tailWord_7603101, baseEnd_7603101] using wordTrace_append hprefix tailTrace_7603101
  have hstable : (prefixWord ++ tailWord_7603101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603101).length < 2 ^ (prefixWord ++ tailWord_7603101).sum := by decide
  have hdescent : baseEnd_7603101 < baseStart_7603101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603107 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 8]
def baseStart_7603107 : Nat := 118140960795 + 7603107 * 2 ^ 59
def prefixEnd_7603107 : Nat := 4983230072969 + 3 ^ 40 * 7603107 * 2
def baseEnd_7603107 : Nat := 433783150951543282510717

theorem tailTrace_7603107 : CollatzResearch.WordTrace tailWord_7603107 prefixEnd_7603107 433783150951543282510717 := by
  unfold tailWord_7603107
  simp only [CollatzResearch.WordTrace]
  refine ⟨277308094066249321141263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184872062710832880760842383 277308094066249321141263575)
  ·
    refine ⟨415962141099373981711895363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277308094066249321141263575 415962141099373981711895363)
    ·
      refine ⟨623943211649060972567843045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415962141099373981711895363 623943211649060972567843045)
      ·
        refine ⟨116989352184198932356470571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623943211649060972567843045 116989352184198932356470571)
        ·
          refine ⟨175484028276298398534705857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116989352184198932356470571 175484028276298398534705857)
          ·
            refine ⟨131613021207223798901029393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175484028276298398534705857 131613021207223798901029393)
            ·
              refine ⟨98709765905417849175772045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131613021207223798901029393 98709765905417849175772045)
              ·
                refine ⟨37016162214531693440914517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98709765905417849175772045 37016162214531693440914517)
                ·
                  refine ⟨433783150951543282510717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37016162214531693440914517 433783150951543282510717)
                  ·
                    rfl

theorem cell23_7603107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 8].length) (baseStart_7603107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603107 prefixEnd_7603107 := by exact prefixLift 7603107
  have htrace : WordTrace (prefixWord ++ tailWord_7603107) baseStart_7603107 baseEnd_7603107 := by
    simpa [prefixWord, tailWord_7603107, baseEnd_7603107] using wordTrace_append hprefix tailTrace_7603107
  have hstable : (prefixWord ++ tailWord_7603107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603107).length < 2 ^ (prefixWord ++ tailWord_7603107).sum := by decide
  have hdescent : baseEnd_7603107 < baseStart_7603107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603158 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_7603158 : Nat := 118140960795 + 7603158 * 2 ^ 59
def prefixEnd_7603158 : Nat := 4983230072969 + 3 ^ 40 * 7603158 * 2
def baseEnd_7603158 : Nat := 433786060675252093673191

theorem tailTrace_7603158 : CollatzResearch.WordTrace tailWord_7603158 prefixEnd_7603158 433786060675252093673191 := by
  unfold tailWord_7603158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331872136816534803210633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184873302792709704567580085 17331872136816534803210633)
  ·
    refine ⟨12998904102612401102407975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17331872136816534803210633 12998904102612401102407975)
    ·
      refine ⟨19498356153918601653611963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12998904102612401102407975 19498356153918601653611963)
      ·
        refine ⟨29247534230877902480417945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498356153918601653611963 29247534230877902480417945)
        ·
          refine ⟨21935650673158426860313459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29247534230877902480417945 21935650673158426860313459)
          ·
            refine ⟨32903476009737640290470189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21935650673158426860313459 32903476009737640290470189)
            ·
              refine ⟨12338803503651615108926321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32903476009737640290470189 12338803503651615108926321)
              ·
                refine ⟨9254102627738711331694741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12338803503651615108926321 9254102627738711331694741)
                ·
                  refine ⟨433786060675252093673191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9254102627738711331694741 433786060675252093673191)
                  ·
                    rfl

theorem cell23_7603158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_7603158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603158 prefixEnd_7603158 := by exact prefixLift 7603158
  have htrace : WordTrace (prefixWord ++ tailWord_7603158) baseStart_7603158 baseEnd_7603158 := by
    simpa [prefixWord, tailWord_7603158, baseEnd_7603158] using wordTrace_append hprefix tailTrace_7603158
  have hstable : (prefixWord ++ tailWord_7603158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603158).length < 2 ^ (prefixWord ++ tailWord_7603158).sum := by decide
  have hdescent : baseEnd_7603158 < baseStart_7603158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603194 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3]
def baseStart_7603194 : Nat := 118140960795 + 7603194 * 2 ^ 59
def prefixEnd_7603194 : Nat := 4983230072969 + 3 ^ 40 * 7603194 * 2
def baseEnd_7603194 : Nat := 3904093031380830702208553

theorem tailTrace_7603194 : CollatzResearch.WordTrace tailWord_7603194 prefixEnd_7603194 3904093031380830702208553 := by
  unfold tailWord_7603194
  simp only [CollatzResearch.WordTrace]
  refine ⟨69327816804233533749920159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184874178144622756666453757 69327816804233533749920159)
  ·
    refine ⟨103991725206350300624880239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69327816804233533749920159 103991725206350300624880239)
    ·
      refine ⟨155987587809525450937320359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103991725206350300624880239 155987587809525450937320359)
      ·
        refine ⟨233981381714288176405980539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155987587809525450937320359 233981381714288176405980539)
        ·
          refine ⟨350972072571432264608970809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233981381714288176405980539 350972072571432264608970809)
          ·
            refine ⟨263229054428574198456728107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350972072571432264608970809 263229054428574198456728107)
            ·
              refine ⟨394843581642861297685092161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263229054428574198456728107 394843581642861297685092161)
              ·
                refine ⟨296132686232145973263819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394843581642861297685092161 296132686232145973263819121)
                ·
                  refine ⟨222099514674109479947864341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296132686232145973263819121 222099514674109479947864341)
                  ·
                    refine ⟨10410914750348881872556141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222099514674109479947864341 10410914750348881872556141)
                    ·
                      refine ⟨3904093031380830702208553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10410914750348881872556141 3904093031380830702208553)
                      ·
                        rfl

theorem cell23_7603194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_7603194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603194 prefixEnd_7603194 := by exact prefixLift 7603194
  have htrace : WordTrace (prefixWord ++ tailWord_7603194) baseStart_7603194 baseEnd_7603194 := by
    simpa [prefixWord, tailWord_7603194, baseEnd_7603194] using wordTrace_append hprefix tailTrace_7603194
  have hstable : (prefixWord ++ tailWord_7603194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603194).length < 2 ^ (prefixWord ++ tailWord_7603194).sum := by decide
  have hdescent : baseEnd_7603194 < baseStart_7603194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603201 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7603201 : Nat := 118140960795 + 7603201 * 2 ^ 59
def prefixEnd_7603201 : Nat := 4983230072969 + 3 ^ 40 * 7603201 * 2
def baseEnd_7603201 : Nat := 1301365541915137391607007

theorem tailTrace_7603201 : CollatzResearch.WordTrace tailWord_7603201 prefixEnd_7603201 1301365541915137391607007 := by
  unfold tailWord_7603201
  simp only [CollatzResearch.WordTrace]
  refine ⟨277311522527908775195185457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184874348351939183463456971 277311522527908775195185457)
  ·
    refine ⟨207983641895931581396389093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277311522527908775195185457 207983641895931581396389093)
    ·
      refine ⟨38996932855487171511822955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 207983641895931581396389093 38996932855487171511822955)
      ·
        refine ⟨58495399283230757267734433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38996932855487171511822955 58495399283230757267734433)
        ·
          refine ⟨43871549462423067950800825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58495399283230757267734433 43871549462423067950800825)
          ·
            refine ⟨32903662096817300963100619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43871549462423067950800825 32903662096817300963100619)
            ·
              refine ⟨49355493145225951444650929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32903662096817300963100619 49355493145225951444650929)
              ·
                refine ⟨37016619858919463583488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49355493145225951444650929 37016619858919463583488197)
                ·
                  refine ⟨6940616223547399421904037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37016619858919463583488197 6940616223547399421904037)
                  ·
                    refine ⟨1301365541915137391607007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940616223547399421904037 1301365541915137391607007)
                    ·
                      rfl

theorem cell23_7603201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7603201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603201 prefixEnd_7603201 := by exact prefixLift 7603201
  have htrace : WordTrace (prefixWord ++ tailWord_7603201) baseStart_7603201 baseEnd_7603201 := by
    simpa [prefixWord, tailWord_7603201, baseEnd_7603201] using wordTrace_append hprefix tailTrace_7603201
  have hstable : (prefixWord ++ tailWord_7603201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603201).length < 2 ^ (prefixWord ++ tailWord_7603201).sum := by decide
  have hdescent : baseEnd_7603201 < baseStart_7603201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603211 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5]
def baseStart_7603211 : Nat := 118140960795 + 7603211 * 2 ^ 59
def prefixEnd_7603211 : Nat := 4983230072969 + 3 ^ 40 * 7603211 * 2
def baseEnd_7603211 : Nat := 3904101760551957135695975

theorem tailTrace_7603211 : CollatzResearch.WordTrace tailWord_7603211 prefixEnd_7603211 3904101760551957135695975 := by
  unfold tailWord_7603211
  simp only [CollatzResearch.WordTrace]
  refine ⟨277311887257872546903049487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184874591505248364602032991 277311887257872546903049487)
  ·
    refine ⟨415967830886808820354574231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277311887257872546903049487 415967830886808820354574231)
    ·
      refine ⟨623951746330213230531861347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415967830886808820354574231 623951746330213230531861347)
      ·
        refine ⟨935927619495319845797792021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623951746330213230531861347 935927619495319845797792021)
        ·
          refine ⟨43871607163843117771771501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 935927619495319845797792021 43871607163843117771771501)
          ·
            refine ⟨16451852686441169164414313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43871607163843117771771501 16451852686441169164414313)
            ·
              refine ⟨12338889514830876873310735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16451852686441169164414313 12338889514830876873310735)
              ·
                refine ⟨18508334272246315309966103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12338889514830876873310735 18508334272246315309966103)
                ·
                  refine ⟨27762501408369472964949155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18508334272246315309966103 27762501408369472964949155)
                  ·
                    refine ⟨41643752112554209447423733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27762501408369472964949155 41643752112554209447423733)
                    ·
                      refine ⟨3904101760551957135695975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41643752112554209447423733 3904101760551957135695975)
                      ·
                        rfl

theorem cell23_7603211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].length) (baseStart_7603211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603211 prefixEnd_7603211 := by exact prefixLift 7603211
  have htrace : WordTrace (prefixWord ++ tailWord_7603211) baseStart_7603211 baseEnd_7603211 := by
    simpa [prefixWord, tailWord_7603211, baseEnd_7603211] using wordTrace_append hprefix tailTrace_7603211
  have hstable : (prefixWord ++ tailWord_7603211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603211).length < 2 ^ (prefixWord ++ tailWord_7603211).sum := by decide
  have hdescent : baseEnd_7603211 < baseStart_7603211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603214 : List Nat := [4, 1, 1, 2, 2, 2, 11]
def baseStart_7603214 : Nat := 118140960795 + 7603214 * 2 ^ 59
def prefixEnd_7603214 : Nat := 4983230072969 + 3 ^ 40 * 7603214 * 2
def baseEnd_7603214 : Nat := 48198806185110131159981

theorem tailTrace_7603214 : CollatzResearch.WordTrace tailWord_7603214 prefixEnd_7603214 48198806185110131159981 := by
  unfold tailWord_7603214
  simp only [CollatzResearch.WordTrace]
  refine ⟨34663999584607709801926087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184874664451241118943605797 34663999584607709801926087)
  ·
    refine ⟨51995999376911564702889131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34663999584607709801926087 51995999376911564702889131)
    ·
      refine ⟨77993999065367347054333697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51995999376911564702889131 77993999065367347054333697)
      ·
        refine ⟨58495499299025510290750273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77993999065367347054333697 58495499299025510290750273)
        ·
          refine ⟨43871624474269132718062705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58495499299025510290750273 43871624474269132718062705)
          ·
            refine ⟨32903718355701849538547029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43871624474269132718062705 32903718355701849538547029)
            ·
              refine ⟨48198806185110131159981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32903718355701849538547029 48198806185110131159981)
              ·
                rfl

theorem cell23_7603214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 11].length) (baseStart_7603214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603214 prefixEnd_7603214 := by exact prefixLift 7603214
  have htrace : WordTrace (prefixWord ++ tailWord_7603214) baseStart_7603214 baseEnd_7603214 := by
    simpa [prefixWord, tailWord_7603214, baseEnd_7603214] using wordTrace_append hprefix tailTrace_7603214
  have hstable : (prefixWord ++ tailWord_7603214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603214).length < 2 ^ (prefixWord ++ tailWord_7603214).sum := by decide
  have hdescent : baseEnd_7603214 < baseStart_7603214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603225 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 1, 2, 2]
def baseStart_7603225 : Nat := 118140960795 + 7603225 * 2 ^ 59
def prefixEnd_7603225 : Nat := 4983230072969 + 3 ^ 40 * 7603225 * 2
def baseEnd_7603225 : Nat := 3904108949281120080920911

theorem tailTrace_7603225 : CollatzResearch.WordTrace tailWord_7603225 prefixEnd_7603225 3904108949281120080920911 := by
  unfold tailWord_7603225
  simp only [CollatzResearch.WordTrace]
  refine ⟨277312397879821827294059129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184874931919881218196039419 277312397879821827294059129)
  ·
    refine ⟨207984298409866370470544347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277312397879821827294059129 207984298409866370470544347)
    ·
      refine ⟨311976447614799555705816521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207984298409866370470544347 311976447614799555705816521)
      ·
        refine ⟨233982335711099666779362391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311976447614799555705816521 233982335711099666779362391)
        ·
          refine ⟨350973503566649500169043587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233982335711099666779362391 350973503566649500169043587)
          ·
            refine ⟨526460255349974250253565381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350973503566649500169043587 526460255349974250253565381)
            ·
              refine ⟨98711297878120171922543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526460255349974250253565381 98711297878120171922543509)
              ·
                refine ⟨4627092088036883058869227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98711297878120171922543509 4627092088036883058869227)
                ·
                  refine ⟨6940638132055324588303841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627092088036883058869227 6940638132055324588303841)
                  ·
                    refine ⟨5205478599041493441227881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940638132055324588303841 5205478599041493441227881)
                    ·
                      refine ⟨3904108949281120080920911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205478599041493441227881 3904108949281120080920911)
                      ·
                        rfl

theorem cell23_7603225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 2, 2].length) (baseStart_7603225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603225 prefixEnd_7603225 := by exact prefixLift 7603225
  have htrace : WordTrace (prefixWord ++ tailWord_7603225) baseStart_7603225 baseEnd_7603225 := by
    simpa [prefixWord, tailWord_7603225, baseEnd_7603225] using wordTrace_append hprefix tailTrace_7603225
  have hstable : (prefixWord ++ tailWord_7603225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603225).length < 2 ^ (prefixWord ++ tailWord_7603225).sum := by decide
  have hdescent : baseEnd_7603225 < baseStart_7603225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603235 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 2, 4]
def baseStart_7603235 : Nat := 118140960795 + 7603235 * 2 ^ 59
def prefixEnd_7603235 : Nat := 4983230072969 + 3 ^ 40 * 7603235 * 2
def baseEnd_7603235 : Nat := 1301371361362555013931955

theorem tailTrace_7603235 : CollatzResearch.WordTrace tailWord_7603235 prefixEnd_7603235 1301371361362555013931955 := by
  unfold tailWord_7603235
  simp only [CollatzResearch.WordTrace]
  refine ⟨277312762609785599001923159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184875175073190399334615439 277312762609785599001923159)
  ·
    refine ⟨415969143914678398502884739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277312762609785599001923159 415969143914678398502884739)
    ·
      refine ⟨623953715872017597754327109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415969143914678398502884739 623953715872017597754327109)
      ·
        refine ⟨116991321726003299578936333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623953715872017597754327109 116991321726003299578936333)
        ·
          refine ⟨43871745647251237342101125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116991321726003299578936333 43871745647251237342101125)
          ·
            refine ⟨8225952308859607001643961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43871745647251237342101125 8225952308859607001643961)
            ·
              refine ⟨6169464231644705251232971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225952308859607001643961 6169464231644705251232971)
              ·
                refine ⟨9254196347467057876849457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169464231644705251232971 9254196347467057876849457)
                ·
                  refine ⟨6940647260600293407637093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9254196347467057876849457 6940647260600293407637093)
                  ·
                    refine ⟨1301371361362555013931955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940647260600293407637093 1301371361362555013931955)
                    ·
                      rfl

theorem cell23_7603235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 2, 4].length) (baseStart_7603235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603235 prefixEnd_7603235 := by exact prefixLift 7603235
  have htrace : WordTrace (prefixWord ++ tailWord_7603235) baseStart_7603235 baseEnd_7603235 := by
    simpa [prefixWord, tailWord_7603235, baseEnd_7603235] using wordTrace_append hprefix tailTrace_7603235
  have hstable : (prefixWord ++ tailWord_7603235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603235).length < 2 ^ (prefixWord ++ tailWord_7603235).sum := by decide
  have hdescent : baseEnd_7603235 < baseStart_7603235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603242 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_7603242 : Nat := 118140960795 + 7603242 * 2 ^ 59
def prefixEnd_7603242 : Nat := 4983230072969 + 3 ^ 40 * 7603242 * 2
def baseEnd_7603242 : Nat := 3904117678452246514408333

theorem tailTrace_7603242 : CollatzResearch.WordTrace tailWord_7603242 prefixEnd_7603242 3904117678452246514408333 := by
  unfold tailWord_7603242
  simp only [CollatzResearch.WordTrace]
  refine ⟨69328254480190059799356995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184875345280506826131618653 69328254480190059799356995)
  ·
    refine ⟨103992381720285089699035493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69328254480190059799356995 103992381720285089699035493)
    ·
      refine ⟨19498571572553454318569155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103992381720285089699035493 19498571572553454318569155)
      ·
        refine ⟨29247857358830181477853733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19498571572553454318569155 29247857358830181477853733)
        ·
          refine ⟨5483973254780659027097575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29247857358830181477853733 5483973254780659027097575)
          ·
            refine ⟨8225959882170988540646363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483973254780659027097575 8225959882170988540646363)
            ·
              refine ⟨12338939823256482810969545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8225959882170988540646363 12338939823256482810969545)
              ·
                refine ⟨9254204867442362108227159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12338939823256482810969545 9254204867442362108227159)
                ·
                  refine ⟨13881307301163543162340739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254204867442362108227159 13881307301163543162340739)
                  ·
                    refine ⟨20821960951745314743511109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13881307301163543162340739 20821960951745314743511109)
                    ·
                      refine ⟨3904117678452246514408333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20821960951745314743511109 3904117678452246514408333)
                      ·
                        rfl

theorem cell23_7603242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_7603242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603242 prefixEnd_7603242 := by exact prefixLift 7603242
  have htrace : WordTrace (prefixWord ++ tailWord_7603242) baseStart_7603242 baseEnd_7603242 := by
    simpa [prefixWord, tailWord_7603242, baseEnd_7603242] using wordTrace_append hprefix tailTrace_7603242
  have hstable : (prefixWord ++ tailWord_7603242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603242).length < 2 ^ (prefixWord ++ tailWord_7603242).sum := by decide
  have hdescent : baseEnd_7603242 < baseStart_7603242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603262 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3]
def baseStart_7603262 : Nat := 118140960795 + 7603262 * 2 ^ 59
def prefixEnd_7603262 : Nat := 4983230072969 + 3 ^ 40 * 7603262 * 2
def baseEnd_7603262 : Nat := 3904127948065336436158241

theorem tailTrace_7603262 : CollatzResearch.WordTrace tailWord_7603262 prefixEnd_7603262 3904127948065336436158241 := by
  unfold tailWord_7603262
  simp only [CollatzResearch.WordTrace]
  refine ⟨34664218422585972826644505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184875831587125188408770693 34664218422585972826644505)
  ·
    refine ⟨25998163816939479619983379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34664218422585972826644505 25998163816939479619983379)
    ·
      refine ⟨38997245725409219429975069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25998163816939479619983379 38997245725409219429975069)
      ·
        refine ⟨14623967147028457286240651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38997245725409219429975069 14623967147028457286240651)
        ·
          refine ⟨21935950720542685929360977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623967147028457286240651 21935950720542685929360977)
          ·
            refine ⟨16451963040407014447020733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21935950720542685929360977 16451963040407014447020733)
            ·
              refine ⟨6169486140152630417632775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16451963040407014447020733 6169486140152630417632775)
              ·
                refine ⟨9254229210228945626449163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6169486140152630417632775 9254229210228945626449163)
                ·
                  refine ⟨13881343815343418439673745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254229210228945626449163 13881343815343418439673745)
                  ·
                    refine ⟨10411007861507563829755309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13881343815343418439673745 10411007861507563829755309)
                    ·
                      refine ⟨3904127948065336436158241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411007861507563829755309 3904127948065336436158241)
                      ·
                        rfl

theorem cell23_7603262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_7603262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603262 prefixEnd_7603262 := by exact prefixLift 7603262
  have htrace : WordTrace (prefixWord ++ tailWord_7603262) baseStart_7603262 baseEnd_7603262 := by
    simpa [prefixWord, tailWord_7603262, baseEnd_7603262] using wordTrace_append hprefix tailTrace_7603262
  have hstable : (prefixWord ++ tailWord_7603262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603262).length < 2 ^ (prefixWord ++ tailWord_7603262).sum := by decide
  have hdescent : baseEnd_7603262 < baseStart_7603262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603301 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_7603301 : Nat := 118140960795 + 7603301 * 2 ^ 59
def prefixEnd_7603301 : Nat := 4983230072969 + 3 ^ 40 * 7603301 * 2
def baseEnd_7603301 : Nat := 3904147973810861783570561

theorem tailTrace_7603301 : CollatzResearch.WordTrace tailWord_7603301 prefixEnd_7603301 3904147973810861783570561 := by
  unfold tailWord_7603301
  simp only [CollatzResearch.WordTrace]
  refine ⟨277315169827546492273825757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184876779885030994849217171 277315169827546492273825757)
  ·
    refine ⟨103993188685329934602684659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277315169827546492273825757 103993188685329934602684659)
    ·
      refine ⟨155989783027994901904026989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103993188685329934602684659 155989783027994901904026989)
      ·
        refine ⟨58496168635498088214010121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155989783027994901904026989 58496168635498088214010121)
        ·
          refine ⟨43872126476623566160507591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58496168635498088214010121 43872126476623566160507591)
          ·
            refine ⟨65808189714935349240761387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43872126476623566160507591 65808189714935349240761387)
            ·
              refine ⟨98712284572403023861142081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65808189714935349240761387 98712284572403023861142081)
              ·
                refine ⟨74034213429302267895856561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98712284572403023861142081 74034213429302267895856561)
                ·
                  refine ⟨55525660071976700921892421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74034213429302267895856561 55525660071976700921892421)
                  ·
                    refine ⟨10411061263495631422854829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55525660071976700921892421 10411061263495631422854829)
                    ·
                      refine ⟨3904147973810861783570561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411061263495631422854829 3904147973810861783570561)
                      ·
                        rfl

theorem cell23_7603301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_7603301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603301 prefixEnd_7603301 := by exact prefixLift 7603301
  have htrace : WordTrace (prefixWord ++ tailWord_7603301) baseStart_7603301 baseEnd_7603301 := by
    simpa [prefixWord, tailWord_7603301, baseEnd_7603301] using wordTrace_append hprefix tailTrace_7603301
  have hstable : (prefixWord ++ tailWord_7603301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603301).length < 2 ^ (prefixWord ++ tailWord_7603301).sum := by decide
  have hdescent : baseEnd_7603301 < baseStart_7603301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603331 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3]
def baseStart_7603331 : Nat := 118140960795 + 7603331 * 2 ^ 59
def prefixEnd_7603331 : Nat := 4983230072969 + 3 ^ 40 * 7603331 * 2
def baseEnd_7603331 : Nat := 3904163378230496666195423

theorem tailTrace_7603331 : CollatzResearch.WordTrace tailWord_7603331 prefixEnd_7603331 3904163378230496666195423 := by
  unfold tailWord_7603331
  simp only [CollatzResearch.WordTrace]
  refine ⟨277316264017437807397417847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184877509344958538264945231 277316264017437807397417847)
  ·
    refine ⟨415974396026156711096126771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277316264017437807397417847 415974396026156711096126771)
    ·
      refine ⟨623961594039235066644190157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415974396026156711096126771 623961594039235066644190157)
      ·
        refine ⟨233985597764713149991571309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 623961594039235066644190157 233985597764713149991571309)
        ·
          refine ⟨87744599161767431246839241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233985597764713149991571309 87744599161767431246839241)
          ·
            refine ⟨65808449371325573435129431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87744599161767431246839241 65808449371325573435129431)
            ·
              refine ⟨98712674056988360152694147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65808449371325573435129431 98712674056988360152694147)
              ·
                refine ⟨148069011085482540229041221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98712674056988360152694147 148069011085482540229041221)
                ·
                  refine ⟨27762939578527976292945229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148069011085482540229041221 27762939578527976292945229)
                  ·
                    refine ⟨10411102341947991109854461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27762939578527976292945229 10411102341947991109854461)
                    ·
                      refine ⟨3904163378230496666195423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411102341947991109854461 3904163378230496666195423)
                      ·
                        rfl

theorem cell23_7603331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_7603331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603331 prefixEnd_7603331 := by exact prefixLift 7603331
  have htrace : WordTrace (prefixWord ++ tailWord_7603331) baseStart_7603331 baseEnd_7603331 := by
    simpa [prefixWord, tailWord_7603331, baseEnd_7603331] using wordTrace_append hprefix tailTrace_7603331
  have hstable : (prefixWord ++ tailWord_7603331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603331).length < 2 ^ (prefixWord ++ tailWord_7603331).sum := by decide
  have hdescent : baseEnd_7603331 < baseStart_7603331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603332 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_7603332 : Nat := 118140960795 + 7603332 * 2 ^ 59
def prefixEnd_7603332 : Nat := 4983230072969 + 3 ^ 40 * 7603332 * 2
def baseEnd_7603332 : Nat := 3904163891711151162282919

theorem tailTrace_7603332 : CollatzResearch.WordTrace tailWord_7603332 prefixEnd_7603332 3904163891711151162282919 := by
  unfold tailWord_7603332
  simp only [CollatzResearch.WordTrace]
  refine ⟨138658150245217092284102125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184877533660289456378802833 138658150245217092284102125)
  ·
    refine ⟨51996806341956409606538297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138658150245217092284102125 51996806341956409606538297)
    ·
      refine ⟨38997604756467307204903723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51996806341956409606538297 38997604756467307204903723)
      ·
        refine ⟨58496407134700960807355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38997604756467307204903723 58496407134700960807355585)
        ·
          refine ⟨43872305351025720605516689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58496407134700960807355585 43872305351025720605516689)
          ·
            refine ⟨32904229013269290454137517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43872305351025720605516689 32904229013269290454137517)
            ·
              refine ⟨12339085879975983920301569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32904229013269290454137517 12339085879975983920301569)
              ·
                refine ⟨9254314409981987940226177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12339085879975983920301569 9254314409981987940226177)
                ·
                  refine ⟨6940735807486490955169633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9254314409981987940226177 6940735807486490955169633)
                  ·
                    refine ⟨5205551855614868216377225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940735807486490955169633 5205551855614868216377225)
                    ·
                      refine ⟨3904163891711151162282919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205551855614868216377225 3904163891711151162282919)
                      ·
                        rfl

theorem cell23_7603332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_7603332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603332 prefixEnd_7603332 := by exact prefixLift 7603332
  have htrace : WordTrace (prefixWord ++ tailWord_7603332) baseStart_7603332 baseEnd_7603332 := by
    simpa [prefixWord, tailWord_7603332, baseEnd_7603332] using wordTrace_append hprefix tailTrace_7603332
  have hstable : (prefixWord ++ tailWord_7603332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603332).length < 2 ^ (prefixWord ++ tailWord_7603332).sum := by decide
  have hdescent : baseEnd_7603332 < baseStart_7603332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603338 : List Nat := [3, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_7603338 : Nat := 118140960795 + 7603338 * 2 ^ 59
def prefixEnd_7603338 : Nat := 4983230072969 + 3 ^ 40 * 7603338 * 2
def baseEnd_7603338 : Nat := 433796330288342015423099

theorem tailTrace_7603338 : CollatzResearch.WordTrace tailWord_7603338 prefixEnd_7603338 433796330288342015423099 := by
  unfold tailWord_7603338
  simp only [CollatzResearch.WordTrace]
  refine ⟨69329129832103111898230667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184877679552274965061948445 69329129832103111898230667)
  ·
    refine ⟨103993694748154667847346001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69329129832103111898230667 103993694748154667847346001)
    ·
      refine ⟨77995271061116000885509501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103993694748154667847346001 77995271061116000885509501)
      ·
        refine ⟨29248226647918500332066063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77995271061116000885509501 29248226647918500332066063)
        ·
          refine ⟨43872339971877750498099095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29248226647918500332066063 43872339971877750498099095)
          ·
            refine ⟨65808509957816625747148643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43872339971877750498099095 65808509957816625747148643)
            ·
              refine ⟨98712764936724938620722965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65808509957816625747148643 98712764936724938620722965)
              ·
                refine ⟨4627160856408981497846389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98712764936724938620722965 4627160856408981497846389)
                ·
                  refine ⟨433796330288342015423099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627160856408981497846389 433796330288342015423099)
                  ·
                    rfl

theorem cell23_7603338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_7603338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603338 prefixEnd_7603338 := by exact prefixLift 7603338
  have htrace : WordTrace (prefixWord ++ tailWord_7603338) baseStart_7603338 baseEnd_7603338 := by
    simpa [prefixWord, tailWord_7603338, baseEnd_7603338] using wordTrace_append hprefix tailTrace_7603338
  have hstable : (prefixWord ++ tailWord_7603338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603338).length < 2 ^ (prefixWord ++ tailWord_7603338).sum := by decide
  have hdescent : baseEnd_7603338 < baseStart_7603338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603351 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 1, 7]
def baseStart_7603351 : Nat := 118140960795 + 7603351 * 2 ^ 59
def prefixEnd_7603351 : Nat := 4983230072969 + 3 ^ 40 * 7603351 * 2
def baseEnd_7603351 : Nat := 1301391215947862195981777

theorem tailTrace_7603351 : CollatzResearch.WordTrace tailWord_7603351 prefixEnd_7603351 1301391215947862195981777 := by
  unfold tailWord_7603351
  simp only [CollatzResearch.WordTrace]
  refine ⟨277316993477365350813145907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184877995651576900542097271 277316993477365350813145907)
  ·
    refine ⟨415975490216048026219718861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277316993477365350813145907 415975490216048026219718861)
    ·
      refine ⟨155990808831018009832394573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415975490216048026219718861 155990808831018009832394573)
      ·
        refine ⟨58496553311631753687147965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155990808831018009832394573 58496553311631753687147965)
        ·
          refine ⟨21936207491861907632680487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58496553311631753687147965 21936207491861907632680487)
          ·
            refine ⟨32904311237792861449020731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21936207491861907632680487 32904311237792861449020731)
            ·
              refine ⟨49356466856689292173531097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32904311237792861449020731 49356466856689292173531097)
              ·
                refine ⟨37017350142516969130148323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49356466856689292173531097 37017350142516969130148323)
                ·
                  refine ⟨55526025213775453695222485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37017350142516969130148323 55526025213775453695222485)
                  ·
                    refine ⟨1301391215947862195981777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55526025213775453695222485 1301391215947862195981777)
                    ·
                      rfl

theorem cell23_7603351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_7603351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603351 prefixEnd_7603351 := by exact prefixLift 7603351
  have htrace : WordTrace (prefixWord ++ tailWord_7603351) baseStart_7603351 baseEnd_7603351 := by
    simpa [prefixWord, tailWord_7603351, baseEnd_7603351] using wordTrace_append hprefix tailTrace_7603351
  have hstable : (prefixWord ++ tailWord_7603351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603351).length < 2 ^ (prefixWord ++ tailWord_7603351).sum := by decide
  have hdescent : baseEnd_7603351 < baseStart_7603351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603388 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7603388 : Nat := 118140960795 + 7603388 * 2 ^ 59
def prefixEnd_7603388 : Nat := 4983230072969 + 3 ^ 40 * 7603388 * 2
def baseEnd_7603388 : Nat := 3904192646627802943182661

theorem tailTrace_7603388 : CollatzResearch.WordTrace tailWord_7603388 prefixEnd_7603388 3904192646627802943182661 := by
  unfold tailWord_7603388
  simp only [CollatzResearch.WordTrace]
  refine ⟨138659171489115653066121409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184878895318820870754828545 138659171489115653066121409)
  ·
    refine ⟨103994378616836739799591057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138659171489115653066121409 103994378616836739799591057)
    ·
      refine ⟨77995783962627554849693293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103994378616836739799591057 77995783962627554849693293)
      ·
        refine ⟨29248418985985333068634985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77995783962627554849693293 29248418985985333068634985)
        ·
          refine ⟨21936314239488999801476239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29248418985985333068634985 21936314239488999801476239)
          ·
            refine ⟨32904471359233499702214359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21936314239488999801476239 32904471359233499702214359)
            ·
              refine ⟨49356707038850249553321539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32904471359233499702214359 49356707038850249553321539)
              ·
                refine ⟨74035060558275374329982309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49356707038850249553321539 74035060558275374329982309)
                ·
                  refine ⟨13881573854676632686871683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74035060558275374329982309 13881573854676632686871683)
                  ·
                    refine ⟨20822360782014949030307525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13881573854676632686871683 20822360782014949030307525)
                    ·
                      refine ⟨3904192646627802943182661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20822360782014949030307525 3904192646627802943182661)
                      ·
                        rfl

theorem cell23_7603388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7603388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603388 prefixEnd_7603388 := by exact prefixLift 7603388
  have htrace : WordTrace (prefixWord ++ tailWord_7603388) baseStart_7603388 baseEnd_7603388 := by
    simpa [prefixWord, tailWord_7603388, baseEnd_7603388] using wordTrace_append hprefix tailTrace_7603388
  have hstable : (prefixWord ++ tailWord_7603388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603388).length < 2 ^ (prefixWord ++ tailWord_7603388).sum := by decide
  have hdescent : baseEnd_7603388 < baseStart_7603388 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603411 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 6]
def baseStart_7603411 : Nat := 118140960795 + 7603411 * 2 ^ 59
def prefixEnd_7603411 : Nat := 4983230072969 + 3 ^ 40 * 7603411 * 2
def baseEnd_7603411 : Nat := 433800495186984039243895

theorem tailTrace_7603411 : CollatzResearch.WordTrace tailWord_7603411 prefixEnd_7603411 433800495186984039243895 := by
  unfold tailWord_7603411
  simp only [CollatzResearch.WordTrace]
  refine ⟨277319181857147981060330087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184879454571431987373553391 277319181857147981060330087)
  ·
    refine ⟨415978772785721971590495131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277319181857147981060330087 415978772785721971590495131)
    ·
      refine ⟨623968159178582957385742697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415978772785721971590495131 623968159178582957385742697)
      ·
        refine ⟨467976119383937218039307023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 623968159178582957385742697 467976119383937218039307023)
        ·
          refine ⟨701964179075905827058960535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 467976119383937218039307023 701964179075905827058960535)
          ·
            refine ⟨1052946268613858740588440803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 701964179075905827058960535 1052946268613858740588440803)
            ·
              refine ⟨1579419402920788110882661205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1052946268613858740588440803 1579419402920788110882661205)
              ·
                refine ⟨9254410563988992837203093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1579419402920788110882661205 9254410563988992837203093)
                ·
                  refine ⟨433800495186984039243895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9254410563988992837203093 433800495186984039243895)
                  ·
                    rfl

theorem cell23_7603411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 6].length) (baseStart_7603411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603411 prefixEnd_7603411 := by exact prefixLift 7603411
  have htrace : WordTrace (prefixWord ++ tailWord_7603411) baseStart_7603411 baseEnd_7603411 := by
    simpa [prefixWord, tailWord_7603411, baseEnd_7603411] using wordTrace_append hprefix tailTrace_7603411
  have hstable : (prefixWord ++ tailWord_7603411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603411).length < 2 ^ (prefixWord ++ tailWord_7603411).sum := by decide
  have hdescent : baseEnd_7603411 < baseStart_7603411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603425 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_7603425 : Nat := 118140960795 + 7603425 * 2 ^ 59
def prefixEnd_7603425 : Nat := 4983230072969 + 3 ^ 40 * 7603425 * 2
def baseEnd_7603425 : Nat := 3904211645412019298419991

theorem tailTrace_7603425 : CollatzResearch.WordTrace tailWord_7603425 prefixEnd_7603425 3904211645412019298419991 := by
  unfold tailWord_7603425
  simp only [CollatzResearch.WordTrace]
  refine ⟨277319692479097261451339729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184879794986064840967559819 277319692479097261451339729)
  ·
    refine ⟨207989769359322946088504797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277319692479097261451339729 207989769359322946088504797)
    ·
      refine ⟨77996163509746104783189299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207989769359322946088504797 77996163509746104783189299)
      ·
        refine ⟨116994245264619157174783949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77996163509746104783189299 116994245264619157174783949)
        ·
          refine ⟨43872841974232183940543981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116994245264619157174783949 43872841974232183940543981)
          ·
            refine ⟨16452315740337068977703993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43872841974232183940543981 16452315740337068977703993)
            ·
              refine ⟨12339236805252801733277995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16452315740337068977703993 12339236805252801733277995)
              ·
                refine ⟨18508855207879202599916993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12339236805252801733277995 18508855207879202599916993)
                ·
                  refine ⟨13881641405909401949937745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18508855207879202599916993 13881641405909401949937745)
                  ·
                    refine ⟨10411231054432051462453309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13881641405909401949937745 10411231054432051462453309)
                    ·
                      refine ⟨3904211645412019298419991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411231054432051462453309 3904211645412019298419991)
                      ·
                        rfl

theorem cell23_7603425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_7603425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603425 prefixEnd_7603425 := by exact prefixLift 7603425
  have htrace : WordTrace (prefixWord ++ tailWord_7603425) baseStart_7603425 baseEnd_7603425 := by
    simpa [prefixWord, tailWord_7603425, baseEnd_7603425] using wordTrace_append hprefix tailTrace_7603425
  have hstable : (prefixWord ++ tailWord_7603425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603425).length < 2 ^ (prefixWord ++ tailWord_7603425).sum := by decide
  have hdescent : baseEnd_7603425 < baseStart_7603425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603448 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2]
def baseStart_7603448 : Nat := 118140960795 + 7603448 * 2 ^ 59
def prefixEnd_7603448 : Nat := 4983230072969 + 3 ^ 40 * 7603448 * 2
def baseEnd_7603448 : Nat := 3904223455467072708432385

theorem tailTrace_7603448 : CollatzResearch.WordTrace tailWord_7603448 prefixEnd_7603448 3904223455467072708432385 := by
  unfold tailWord_7603448
  simp only [CollatzResearch.WordTrace]
  refine ⟨138660265679006968189713499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184880354238675957586284665 138660265679006968189713499)
  ·
    refine ⟨207990398518510452284570249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138660265679006968189713499 207990398518510452284570249)
    ·
      refine ⟨155992798888882839213427687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207990398518510452284570249 155992798888882839213427687)
      ·
        refine ⟨233989198333324258820141531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155992798888882839213427687 233989198333324258820141531)
        ·
          refine ⟨350983797499986388230212297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233989198333324258820141531 350983797499986388230212297)
          ·
            refine ⟨263237848124989791172659223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350983797499986388230212297 263237848124989791172659223)
            ·
              refine ⟨394856772187484686758988835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263237848124989791172659223 394856772187484686758988835)
              ·
                refine ⟨592285158281227030138483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394856772187484686758988835 592285158281227030138483253)
                ·
                  refine ⟨55526733588865034075482805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 592285158281227030138483253 55526733588865034075482805)
                  ·
                    refine ⟨5205631273956096944576513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 55526733588865034075482805 5205631273956096944576513)
                    ·
                      refine ⟨3904223455467072708432385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205631273956096944576513 3904223455467072708432385)
                      ·
                        rfl

theorem cell23_7603448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 5, 2].length) (baseStart_7603448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603448 prefixEnd_7603448 := by exact prefixLift 7603448
  have htrace : WordTrace (prefixWord ++ tailWord_7603448) baseStart_7603448 baseEnd_7603448 := by
    simpa [prefixWord, tailWord_7603448, baseEnd_7603448] using wordTrace_append hprefix tailTrace_7603448
  have hstable : (prefixWord ++ tailWord_7603448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603448).length < 2 ^ (prefixWord ++ tailWord_7603448).sum := by decide
  have hdescent : baseEnd_7603448 < baseStart_7603448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603482 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2]
def baseStart_7603482 : Nat := 118140960795 + 7603482 * 2 ^ 59
def prefixEnd_7603482 : Nat := 4983230072969 + 3 ^ 40 * 7603482 * 2
def baseEnd_7603482 : Nat := 3904240913809325575407229

theorem tailTrace_7603482 : CollatzResearch.WordTrace tailWord_7603482 prefixEnd_7603482 3904240913809325575407229 := by
  unfold tailWord_7603482
  simp only [CollatzResearch.WordTrace]
  refine ⟨69330442859972690046541175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184881180959927173457443133 69330442859972690046541175)
  ·
    refine ⟨103995664289959035069811763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69330442859972690046541175 103995664289959035069811763)
    ·
      refine ⟨155993496434938552604717645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103995664289959035069811763 155993496434938552604717645)
      ·
        refine ⟨58497561163101957226769117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155993496434938552604717645 58497561163101957226769117)
        ·
          refine ⟨21936585436163233960038419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58497561163101957226769117 21936585436163233960038419)
          ·
            refine ⟨32904878154244850940057629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21936585436163233960038419 32904878154244850940057629)
            ·
              refine ⟨12339329307841819102521611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32904878154244850940057629 12339329307841819102521611)
              ·
                refine ⟨18508993961762728653782417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12339329307841819102521611 18508993961762728653782417)
                ·
                  refine ⟨13881745471322046490336813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18508993961762728653782417 13881745471322046490336813)
                  ·
                    refine ⟨5205654551745767433876305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13881745471322046490336813 5205654551745767433876305)
                    ·
                      refine ⟨3904240913809325575407229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205654551745767433876305 3904240913809325575407229)
                      ·
                        rfl

theorem cell23_7603482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_7603482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603482 prefixEnd_7603482 := by exact prefixLift 7603482
  have htrace : WordTrace (prefixWord ++ tailWord_7603482) baseStart_7603482 baseEnd_7603482 := by
    simpa [prefixWord, tailWord_7603482, baseEnd_7603482] using wordTrace_append hprefix tailTrace_7603482
  have hstable : (prefixWord ++ tailWord_7603482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603482).length < 2 ^ (prefixWord ++ tailWord_7603482).sum := by decide
  have hdescent : baseEnd_7603482 < baseStart_7603482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603505 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 4, 4]
def baseStart_7603505 : Nat := 118140960795 + 7603505 * 2 ^ 59
def prefixEnd_7603505 : Nat := 4983230072969 + 3 ^ 40 * 7603505 * 2
def baseEnd_7603505 : Nat := 1301417574621459661806541

theorem tailTrace_7603505 : CollatzResearch.WordTrace tailWord_7603505 prefixEnd_7603505 1301417574621459661806541 := by
  unfold tailWord_7603505
  simp only [CollatzResearch.WordTrace]
  refine ⟨277322610318807435114251969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184881740212538290076167979 277322610318807435114251969)
  ·
    refine ⟨207991957739105576335688977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277322610318807435114251969 207991957739105576335688977)
    ·
      refine ⟨155993968304329182251766733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207991957739105576335688977 155993968304329182251766733)
      ·
        refine ⟨58497738114123443344412525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155993968304329182251766733 58497738114123443344412525)
        ·
          refine ⟨21936651792796291254154697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58497738114123443344412525 21936651792796291254154697)
          ·
            refine ⟨16452488844597218440616023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21936651792796291254154697 16452488844597218440616023)
            ·
              refine ⟨24678733266895827660924035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16452488844597218440616023 24678733266895827660924035)
              ·
                refine ⟨37018099900343741491386053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24678733266895827660924035 37018099900343741491386053)
                ·
                  refine ⟨6940893731314451529634885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37018099900343741491386053 6940893731314451529634885)
                  ·
                    refine ⟨1301417574621459661806541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6940893731314451529634885 1301417574621459661806541)
                    ·
                      rfl

theorem cell23_7603505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_7603505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603505 prefixEnd_7603505 := by exact prefixLift 7603505
  have htrace : WordTrace (prefixWord ++ tailWord_7603505) baseStart_7603505 baseEnd_7603505 := by
    simpa [prefixWord, tailWord_7603505, baseEnd_7603505] using wordTrace_append hprefix tailTrace_7603505
  have hstable : (prefixWord ++ tailWord_7603505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603505).length < 2 ^ (prefixWord ++ tailWord_7603505).sum := by decide
  have hdescent : baseEnd_7603505 < baseStart_7603505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603511 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_7603511 : Nat := 118140960795 + 7603511 * 2 ^ 59
def prefixEnd_7603511 : Nat := 4983230072969 + 3 ^ 40 * 7603511 * 2
def baseEnd_7603511 : Nat := 3904255804748305961944595

theorem tailTrace_7603511 : CollatzResearch.WordTrace tailWord_7603511 prefixEnd_7603511 3904255804748305961944595 := by
  unfold tailWord_7603511
  simp only [CollatzResearch.WordTrace]
  refine ⟨277322829156785698138970387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184881886104523798759313591 277322829156785698138970387)
  ·
    refine ⟨415984243735178547208455581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277322829156785698138970387 415984243735178547208455581)
    ·
      refine ⟨155994091400691955203170843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 415984243735178547208455581 155994091400691955203170843)
      ·
        refine ⟨233991137101037932804756265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155994091400691955203170843 233991137101037932804756265)
        ·
          refine ⟨175493352825778449603567199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233991137101037932804756265 175493352825778449603567199)
          ·
            refine ⟨263240029238667674405350799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175493352825778449603567199 263240029238667674405350799)
            ·
              refine ⟨394860043858001511608026199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263240029238667674405350799 394860043858001511608026199)
              ·
                refine ⟨592290065787002267412039299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 394860043858001511608026199 592290065787002267412039299)
                ·
                  refine ⟨888435098680503401118058949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592290065787002267412039299 888435098680503401118058949)
                  ·
                    refine ⟨166581581002594387709636053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888435098680503401118058949 166581581002594387709636053)
                    ·
                      refine ⟨3904255804748305961944595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166581581002594387709636053 3904255804748305961944595)
                      ·
                        rfl

theorem cell23_7603511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_7603511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603511 prefixEnd_7603511 := by exact prefixLift 7603511
  have htrace : WordTrace (prefixWord ++ tailWord_7603511) baseStart_7603511 baseEnd_7603511 := by
    simpa [prefixWord, tailWord_7603511, baseEnd_7603511] using wordTrace_append hprefix tailTrace_7603511
  have hstable : (prefixWord ++ tailWord_7603511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603511).length < 2 ^ (prefixWord ++ tailWord_7603511).sum := by decide
  have hdescent : baseEnd_7603511 < baseStart_7603511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603518 : List Nat := [4, 2, 1, 2, 1, 1, 2, 10]
def baseStart_7603518 : Nat := 118140960795 + 7603518 * 2 ^ 59
def prefixEnd_7603518 : Nat := 4983230072969 + 3 ^ 40 * 7603518 * 2
def baseEnd_7603518 : Nat := 144602199967143979057669

theorem tailTrace_7603518 : CollatzResearch.WordTrace tailWord_7603518 prefixEnd_7603518 144602199967143979057669 := by
  unfold tailWord_7603518
  simp only [CollatzResearch.WordTrace]
  refine ⟨34665385558470042291809401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184882056311840225556316805 34665385558470042291809401)
  ·
    refine ⟨25999039168852531718857051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34665385558470042291809401 25999039168852531718857051)
    ·
      refine ⟨38998558753278797578285577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25999039168852531718857051 38998558753278797578285577)
      ·
        refine ⟨29248919064959098183714183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38998558753278797578285577 29248919064959098183714183)
        ·
          refine ⟨43873378597438647275571275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29248919064959098183714183 43873378597438647275571275)
          ·
            refine ⟨65810067896157970913356913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43873378597438647275571275 65810067896157970913356913)
            ·
              refine ⟨49357550922118478185017685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65810067896157970913356913 49357550922118478185017685)
              ·
                refine ⟨144602199967143979057669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49357550922118478185017685 144602199967143979057669)
                ·
                  rfl

theorem cell23_7603518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_7603518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603518 prefixEnd_7603518 := by exact prefixLift 7603518
  have htrace : WordTrace (prefixWord ++ tailWord_7603518) baseStart_7603518 baseEnd_7603518 := by
    simpa [prefixWord, tailWord_7603518, baseEnd_7603518] using wordTrace_append hprefix tailTrace_7603518
  have hstable : (prefixWord ++ tailWord_7603518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603518).length < 2 ^ (prefixWord ++ tailWord_7603518).sum := by decide
  have hdescent : baseEnd_7603518 < baseStart_7603518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603526 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_7603526 : Nat := 118140960795 + 7603526 * 2 ^ 59
def prefixEnd_7603526 : Nat := 4983230072969 + 3 ^ 40 * 7603526 * 2
def baseEnd_7603526 : Nat := 1301421168986041134419009

theorem tailTrace_7603526 : CollatzResearch.WordTrace tailWord_7603526 prefixEnd_7603526 1301421168986041134419009 := by
  unfold tailWord_7603526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666355507866604865648951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184882250834487570467177621 8666355507866604865648951)
  ·
    refine ⟨12999533261799907298473427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8666355507866604865648951 12999533261799907298473427)
    ·
      refine ⟨19499299892699860947710141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999533261799907298473427 19499299892699860947710141)
      ·
        refine ⟨7312237459762447855391303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19499299892699860947710141 7312237459762447855391303)
        ·
          refine ⟨10968356189643671783086955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312237459762447855391303 10968356189643671783086955)
          ·
            refine ⟨16452534284465507674630433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10968356189643671783086955 16452534284465507674630433)
            ·
              refine ⟨12339400713349130755972825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16452534284465507674630433 12339400713349130755972825)
              ·
                refine ⟨9254550535011848066979619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12339400713349130755972825 9254550535011848066979619)
                ·
                  refine ⟨13881825802517772100469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254550535011848066979619 13881825802517772100469429)
                  ·
                    refine ⟨1301421168986041134419009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13881825802517772100469429 1301421168986041134419009)
                    ·
                      rfl

theorem cell23_7603526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_7603526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603526 prefixEnd_7603526 := by exact prefixLift 7603526
  have htrace : WordTrace (prefixWord ++ tailWord_7603526) baseStart_7603526 baseEnd_7603526 := by
    simpa [prefixWord, tailWord_7603526, baseEnd_7603526] using wordTrace_append hprefix tailTrace_7603526
  have hstable : (prefixWord ++ tailWord_7603526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603526).length < 2 ^ (prefixWord ++ tailWord_7603526).sum := by decide
  have hdescent : baseEnd_7603526 < baseStart_7603526 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603531 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 9]
def baseStart_7603531 : Nat := 118140960795 + 7603531 * 2 ^ 59
def prefixEnd_7603531 : Nat := 4983230072969 + 3 ^ 40 * 7603531 * 2
def baseEnd_7603531 : Nat := 1301422024787131961231501

theorem tailTrace_7603531 : CollatzResearch.WordTrace tailWord_7603531 prefixEnd_7603531 1301422024787131961231501 := by
  unfold tailWord_7603531
  simp only [CollatzResearch.WordTrace]
  refine ⟨277323558616713241554698447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184882372411142161036465631 277323558616713241554698447)
  ·
    refine ⟨415985337925069862332047671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277323558616713241554698447 415985337925069862332047671)
    ·
      refine ⟨623978006887604793498071507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415985337925069862332047671 623978006887604793498071507)
      ·
        refine ⟨935967010331407190247107261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623978006887604793498071507 935967010331407190247107261)
        ·
          refine ⟨350987628874277696342665223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 935967010331407190247107261 350987628874277696342665223)
          ·
            refine ⟨526481443311416544513997835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350987628874277696342665223 526481443311416544513997835)
            ·
              refine ⟨789722164967124816770996753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 526481443311416544513997835 789722164967124816770996753)
              ·
                refine ⟨592291623725343612578247565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 789722164967124816770996753 592291623725343612578247565)
                ·
                  refine ⟨222109358897003854716842837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 592291623725343612578247565 222109358897003854716842837)
                  ·
                    refine ⟨1301422024787131961231501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 222109358897003854716842837 1301422024787131961231501)
                    ·
                      rfl

theorem cell23_7603531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_7603531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603531 prefixEnd_7603531 := by exact prefixLift 7603531
  have htrace : WordTrace (prefixWord ++ tailWord_7603531) baseStart_7603531 baseEnd_7603531 := by
    simpa [prefixWord, tailWord_7603531, baseEnd_7603531] using wordTrace_append hprefix tailTrace_7603531
  have hstable : (prefixWord ++ tailWord_7603531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603531).length < 2 ^ (prefixWord ++ tailWord_7603531).sum := by decide
  have hdescent : baseEnd_7603531 < baseStart_7603531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603532 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 1, 2, 3]
def baseStart_7603532 : Nat := 118140960795 + 7603532 * 2 ^ 59
def prefixEnd_7603532 : Nat := 4983230072969 + 3 ^ 40 * 7603532 * 2
def baseEnd_7603532 : Nat := 3904266587842050379781999

theorem tailTrace_7603532 : CollatzResearch.WordTrace tailWord_7603532 prefixEnd_7603532 3904266587842050379781999 := by
  unfold tailWord_7603532
  simp only [CollatzResearch.WordTrace]
  refine ⟨138661797544854809362742425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184882396726473079150323233 138661797544854809362742425)
  ·
    refine ⟨103996348158641107022056819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138661797544854809362742425 103996348158641107022056819)
    ·
      refine ⟨155994522237961660533085229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103996348158641107022056819 155994522237961660533085229)
      ·
        refine ⟨58497945839235622699906961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155994522237961660533085229 58497945839235622699906961)
        ·
          refine ⟨43873459379426717024930221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58497945839235622699906961 43873459379426717024930221)
          ·
            refine ⟨16452547267285018884348833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43873459379426717024930221 16452547267285018884348833)
            ·
              refine ⟨12339410450463764163261625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16452547267285018884348833 12339410450463764163261625)
              ·
                refine ⟨9254557837847823122446219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12339410450463764163261625 9254557837847823122446219)
                ·
                  refine ⟨13881836756771734683669329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254557837847823122446219 13881836756771734683669329)
                  ·
                    refine ⟨10411377567578801012751997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13881836756771734683669329 10411377567578801012751997)
                    ·
                      refine ⟨3904266587842050379781999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411377567578801012751997 3904266587842050379781999)
                      ·
                        rfl

theorem cell23_7603532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_7603532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603532 prefixEnd_7603532 := by exact prefixLift 7603532
  have htrace : WordTrace (prefixWord ++ tailWord_7603532) baseStart_7603532 baseEnd_7603532 := by
    simpa [prefixWord, tailWord_7603532, baseEnd_7603532] using wordTrace_append hprefix tailTrace_7603532
  have hstable : (prefixWord ++ tailWord_7603532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603532).length < 2 ^ (prefixWord ++ tailWord_7603532).sum := by decide
  have hdescent : baseEnd_7603532 < baseStart_7603532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603545 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 3]
def baseStart_7603545 : Nat := 118140960795 + 7603545 * 2 ^ 59
def prefixEnd_7603545 : Nat := 4983230072969 + 3 ^ 40 * 7603545 * 2
def baseEnd_7603545 : Nat := 3904273263090558828919439

theorem tailTrace_7603545 : CollatzResearch.WordTrace tailWord_7603545 prefixEnd_7603545 3904273263090558828919439 := by
  unfold tailWord_7603545
  simp only [CollatzResearch.WordTrace]
  refine ⟨277324069238662521945708089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184882712825775014630472059 277324069238662521945708089)
  ·
    refine ⟨207993051928996891459281067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277324069238662521945708089 207993051928996891459281067)
    ·
      refine ⟨311989577893495337188921601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207993051928996891459281067 311989577893495337188921601)
      ·
        refine ⟨233992183420121502891691201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311989577893495337188921601 233992183420121502891691201)
        ·
          refine ⟨175494137565091127168768401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233992183420121502891691201 175494137565091127168768401)
          ·
            refine ⟨131620603173818345376576301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175494137565091127168768401 131620603173818345376576301)
            ·
              refine ⟨49357726190181879516216113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131620603173818345376576301 49357726190181879516216113)
              ·
                refine ⟨37018294642636409637162085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49357726190181879516216113 37018294642636409637162085)
                ·
                  refine ⟨6940930245494326806967891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37018294642636409637162085 6940930245494326806967891)
                  ·
                    refine ⟨10411395368241490210451837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6940930245494326806967891 10411395368241490210451837)
                    ·
                      refine ⟨3904273263090558828919439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411395368241490210451837 3904273263090558828919439)
                      ·
                        rfl

theorem cell23_7603545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 1, 3].length) (baseStart_7603545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603545 prefixEnd_7603545 := by exact prefixLift 7603545
  have htrace : WordTrace (prefixWord ++ tailWord_7603545) baseStart_7603545 baseEnd_7603545 := by
    simpa [prefixWord, tailWord_7603545, baseEnd_7603545] using wordTrace_append hprefix tailTrace_7603545
  have hstable : (prefixWord ++ tailWord_7603545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603545).length < 2 ^ (prefixWord ++ tailWord_7603545).sum := by decide
  have hdescent : baseEnd_7603545 < baseStart_7603545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603568 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_7603568 : Nat := 118140960795 + 7603568 * 2 ^ 59
def prefixEnd_7603568 : Nat := 4983230072969 + 3 ^ 40 * 7603568 * 2
def baseEnd_7603568 : Nat := 3904285073145612238931833

theorem tailTrace_7603568 : CollatzResearch.WordTrace tailWord_7603568 prefixEnd_7603568 3904285073145612238931833 := by
  unfold tailWord_7603568
  simp only [CollatzResearch.WordTrace]
  refine ⟨138662454058789598436897679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184883272078386131249196905 138662454058789598436897679)
  ·
    refine ⟨207993681088184397655346519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138662454058789598436897679 207993681088184397655346519)
    ·
      refine ⟨311990521632276596483019779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207993681088184397655346519 311990521632276596483019779)
      ·
        refine ⟨467985782448414894724529669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311990521632276596483019779 467985782448414894724529669)
        ·
          refine ⟨87747334209077792760849313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467985782448414894724529669 87747334209077792760849313)
          ·
            refine ⟨65810500656808344570636985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87747334209077792760849313 65810500656808344570636985)
            ·
              refine ⟨49357875492606258427977739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65810500656808344570636985 49357875492606258427977739)
              ·
                refine ⟨74036813238909387641966609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49357875492606258427977739 74036813238909387641966609)
                ·
                  refine ⟨55527609929182040731474957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74036813238909387641966609 55527609929182040731474957)
                  ·
                    refine ⟨20822853723443265274303109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55527609929182040731474957 20822853723443265274303109)
                    ·
                      refine ⟨3904285073145612238931833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20822853723443265274303109 3904285073145612238931833)
                      ·
                        rfl

theorem cell23_7603568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_7603568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603568 prefixEnd_7603568 := by exact prefixLift 7603568
  have htrace : WordTrace (prefixWord ++ tailWord_7603568) baseStart_7603568 baseEnd_7603568 := by
    simpa [prefixWord, tailWord_7603568, baseEnd_7603568] using wordTrace_append hprefix tailTrace_7603568
  have hstable : (prefixWord ++ tailWord_7603568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603568).length < 2 ^ (prefixWord ++ tailWord_7603568).sum := by decide
  have hdescent : baseEnd_7603568 < baseStart_7603568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603619 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 2, 2, 2]
def baseStart_7603619 : Nat := 118140960795 + 7603619 * 2 ^ 59
def prefixEnd_7603619 : Nat := 4983230072969 + 3 ^ 40 * 7603619 * 2
def baseEnd_7603619 : Nat := 3904311260658991539394099

theorem tailTrace_7603619 : CollatzResearch.WordTrace tailWord_7603619 prefixEnd_7603619 3904311260658991539394099 := by
  unfold tailWord_7603619
  simp only [CollatzResearch.WordTrace]
  refine ⟨277326768240394432583901911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184884512160262955055934607 277326768240394432583901911)
  ·
    refine ⟨415990152360591648875852867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277326768240394432583901911 415990152360591648875852867)
    ·
      refine ⟨623985228540887473313779301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415990152360591648875852867 623985228540887473313779301)
      ·
        refine ⟨116997230351416401246333619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623985228540887473313779301 116997230351416401246333619)
        ·
          refine ⟨175495845527124601869500429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116997230351416401246333619 175495845527124601869500429)
          ·
            refine ⟨65810942072671725701062661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175495845527124601869500429 65810942072671725701062661)
            ·
              refine ⟨12339551638625948568949249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65810942072671725701062661 12339551638625948568949249)
              ·
                refine ⟨9254663728969461426711937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12339551638625948568949249 9254663728969461426711937)
                ·
                  refine ⟨6940997796727096070033953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9254663728969461426711937 6940997796727096070033953)
                  ·
                    refine ⟨5205748347545322052525465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6940997796727096070033953 5205748347545322052525465)
                    ·
                      refine ⟨3904311260658991539394099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205748347545322052525465 3904311260658991539394099)
                      ·
                        rfl

theorem cell23_7603619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_7603619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603619 prefixEnd_7603619 := by exact prefixLift 7603619
  have htrace : WordTrace (prefixWord ++ tailWord_7603619) baseStart_7603619 baseEnd_7603619 := by
    simpa [prefixWord, tailWord_7603619, baseEnd_7603619] using wordTrace_append hprefix tailTrace_7603619
  have hstable : (prefixWord ++ tailWord_7603619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603619).length < 2 ^ (prefixWord ++ tailWord_7603619).sum := by decide
  have hdescent : baseEnd_7603619 < baseStart_7603619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603648 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7]
def baseStart_7603648 : Nat := 118140960795 + 7603648 * 2 ^ 59
def prefixEnd_7603648 : Nat := 4983230072969 + 3 ^ 40 * 7603648 * 2
def baseEnd_7603648 : Nat := 3904326151597971925931465

theorem tailTrace_7603648 : CollatzResearch.WordTrace tailWord_7603648 prefixEnd_7603648 3904326151597971925931465 := by
  unfold tailWord_7603648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138663912978644685268353799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184885217304859580357805065 138663912978644685268353799)
  ·
    refine ⟨207995869467967027902530699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138663912978644685268353799 207995869467967027902530699)
    ·
      refine ⟨311993804201950541853796049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207995869467967027902530699 311993804201950541853796049)
      ·
        refine ⟨233995353151462906390347037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311993804201950541853796049 233995353151462906390347037)
        ·
          refine ⟨87748257431798589896380139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233995353151462906390347037 87748257431798589896380139)
          ·
            refine ⟨131622386147697884844570209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87748257431798589896380139 131622386147697884844570209)
            ·
              refine ⟨98716789610773413633427657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131622386147697884844570209 98716789610773413633427657)
              ·
                refine ⟨74037592208080060225070743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98716789610773413633427657 74037592208080060225070743)
                ·
                  refine ⟨111056388312120090337606115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74037592208080060225070743 111056388312120090337606115)
                  ·
                    refine ⟨166584582468180135506409173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111056388312120090337606115 166584582468180135506409173)
                    ·
                      refine ⟨3904326151597971925931465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166584582468180135506409173 3904326151597971925931465)
                      ·
                        rfl

theorem cell23_7603648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_7603648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603648 prefixEnd_7603648 := by exact prefixLift 7603648
  have htrace : WordTrace (prefixWord ++ tailWord_7603648) baseStart_7603648 baseEnd_7603648 := by
    simpa [prefixWord, tailWord_7603648, baseEnd_7603648] using wordTrace_append hprefix tailTrace_7603648
  have hstable : (prefixWord ++ tailWord_7603648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603648).length < 2 ^ (prefixWord ++ tailWord_7603648).sum := by decide
  have hdescent : baseEnd_7603648 < baseStart_7603648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603695 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_7603695 : Nat := 118140960795 + 7603695 * 2 ^ 59
def prefixEnd_7603695 : Nat := 4983230072969 + 3 ^ 40 * 7603695 * 2
def baseEnd_7603695 : Nat := 3904350285188733242043749

theorem tailTrace_7603695 : CollatzResearch.WordTrace tailWord_7603695 prefixEnd_7603695 3904350285188733242043749 := by
  unfold tailWord_7603695
  simp only [CollatzResearch.WordTrace]
  refine ⟨277329540188119097563668539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184886360125412731709112359 277329540188119097563668539)
  ·
    refine ⟨415994310282178646345502809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277329540188119097563668539 415994310282178646345502809)
    ·
      refine ⟨311995732711633984759127107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415994310282178646345502809 311995732711633984759127107)
      ·
        refine ⟨467993599067450977138690661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311995732711633984759127107 467993599067450977138690661)
        ·
          refine ⟨87748799825147058213504499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467993599067450977138690661 87748799825147058213504499)
          ·
            refine ⟨131623199737720587320256749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87748799825147058213504499 131623199737720587320256749)
            ·
              refine ⟨49358699901645220245096281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131623199737720587320256749 49358699901645220245096281)
              ·
                refine ⟨37019024926233915183822211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49358699901645220245096281 37019024926233915183822211)
                ·
                  refine ⟨55528537389350872775733317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37019024926233915183822211 55528537389350872775733317)
                  ·
                    refine ⟨10411600760503288645449997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55528537389350872775733317 10411600760503288645449997)
                    ·
                      refine ⟨3904350285188733242043749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411600760503288645449997 3904350285188733242043749)
                      ·
                        rfl

theorem cell23_7603695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_7603695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603695 prefixEnd_7603695 := by exact prefixLift 7603695
  have htrace : WordTrace (prefixWord ++ tailWord_7603695) baseStart_7603695 baseEnd_7603695 := by
    simpa [prefixWord, tailWord_7603695, baseEnd_7603695] using wordTrace_append hprefix tailTrace_7603695
  have hstable : (prefixWord ++ tailWord_7603695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603695).length < 2 ^ (prefixWord ++ tailWord_7603695).sum := by decide
  have hdescent : baseEnd_7603695 < baseStart_7603695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603736 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 3, 4]
def baseStart_7603736 : Nat := 118140960795 + 7603736 * 2 ^ 59
def prefixEnd_7603736 : Nat := 4983230072969 + 3 ^ 40 * 7603736 * 2
def baseEnd_7603736 : Nat := 1301457112631855860543687

theorem tailTrace_7603736 : CollatzResearch.WordTrace tailWord_7603736 prefixEnd_7603736 1301457112631855860543687 := by
  unfold tailWord_7603736
  simp only [CollatzResearch.WordTrace]
  refine ⟨138665517790485280782955531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184887357053980374377274041 138665517790485280782955531)
  ·
    refine ⟨207998276685727921174433297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138665517790485280782955531 207998276685727921174433297)
    ·
      refine ⟨155998707514295940880824973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207998276685727921174433297 155998707514295940880824973)
      ·
        refine ⟨58499515317860977830309365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155998707514295940880824973 58499515317860977830309365)
        ·
          refine ⟨5484329561049466671591503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58499515317860977830309365 5484329561049466671591503)
          ·
            refine ⟨8226494341574200007387255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484329561049466671591503 8226494341574200007387255)
            ·
              refine ⟨12339741512361300011080883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8226494341574200007387255 12339741512361300011080883)
              ·
                refine ⟨18509612268541950016621325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12339741512361300011080883 18509612268541950016621325)
                ·
                  refine ⟨6941104600703231256232997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18509612268541950016621325 6941104600703231256232997)
                  ·
                    refine ⟨1301457112631855860543687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941104600703231256232997 1301457112631855860543687)
                    ·
                      rfl

theorem cell23_7603736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 3, 4].length) (baseStart_7603736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603736 prefixEnd_7603736 := by exact prefixLift 7603736
  have htrace : WordTrace (prefixWord ++ tailWord_7603736) baseStart_7603736 baseEnd_7603736 := by
    simpa [prefixWord, tailWord_7603736, baseEnd_7603736] using wordTrace_append hprefix tailTrace_7603736
  have hstable : (prefixWord ++ tailWord_7603736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603736).length < 2 ^ (prefixWord ++ tailWord_7603736).sum := by decide
  have hdescent : baseEnd_7603736 < baseStart_7603736 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603769 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 2, 3, 2]
def baseStart_7603769 : Nat := 118140960795 + 7603769 * 2 ^ 59
def prefixEnd_7603769 : Nat := 4983230072969 + 3 ^ 40 * 7603769 * 2
def baseEnd_7603769 : Nat := 3904388282757165952518409

theorem tailTrace_7603769 : CollatzResearch.WordTrace tailWord_7603769 prefixEnd_7603769 3904388282757165952518409 := by
  unfold tailWord_7603769
  simp only [CollatzResearch.WordTrace]
  refine ⟨277332239189851008201862361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184888159459900672134574907 277332239189851008201862361)
  ·
    refine ⟨207999179392388256151396771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277332239189851008201862361 207999179392388256151396771)
    ·
      refine ⟨311998769088582384227095157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 207999179392388256151396771 311998769088582384227095157)
      ·
        refine ⟨29249884602054598521290171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 311998769088582384227095157 29249884602054598521290171)
        ·
          refine ⟨43874826903081897781935257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29249884602054598521290171 43874826903081897781935257)
          ·
            refine ⟨32906120177311423336451443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43874826903081897781935257 32906120177311423336451443)
            ·
              refine ⟨49359180265967135004677165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32906120177311423336451443 49359180265967135004677165)
              ·
                refine ⟨18509692599737675626753937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49359180265967135004677165 18509692599737675626753937)
                ·
                  refine ⟨13882269449803256720065453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18509692599737675626753937 13882269449803256720065453)
                  ·
                    refine ⟨5205851043676221270024545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13882269449803256720065453 5205851043676221270024545)
                    ·
                      refine ⟨3904388282757165952518409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205851043676221270024545 3904388282757165952518409)
                      ·
                        rfl

theorem cell23_7603769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_7603769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603769 prefixEnd_7603769 := by exact prefixLift 7603769
  have htrace : WordTrace (prefixWord ++ tailWord_7603769) baseStart_7603769 baseEnd_7603769 := by
    simpa [prefixWord, tailWord_7603769, baseEnd_7603769] using wordTrace_append hprefix tailTrace_7603769
  have hstable : (prefixWord ++ tailWord_7603769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603769).length < 2 ^ (prefixWord ++ tailWord_7603769).sum := by decide
  have hdescent : baseEnd_7603769 < baseStart_7603769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603775 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 3, 6]
def baseStart_7603775 : Nat := 118140960795 + 7603775 * 2 ^ 59
def prefixEnd_7603775 : Nat := 4983230072969 + 3 ^ 40 * 7603775 * 2
def baseEnd_7603775 : Nat := 1301463787880364309681127

theorem tailTrace_7603775 : CollatzResearch.WordTrace tailWord_7603775 prefixEnd_7603775 1301463787880364309681127 := by
  unfold tailWord_7603775
  simp only [CollatzResearch.WordTrace]
  refine ⟨277332458027829271226580779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184888305351886180817720519 277332458027829271226580779)
  ·
    refine ⟨415998687041743906839871169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277332458027829271226580779 415998687041743906839871169)
    ·
      refine ⟨311999015281307930129903377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 415998687041743906839871169 311999015281307930129903377)
      ·
        refine ⟨233999261460980947597427533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 311999015281307930129903377 233999261460980947597427533)
        ·
          refine ⟨87749723047867855349035325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233999261460980947597427533 87749723047867855349035325)
          ·
            refine ⟨32906146142950445755888247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87749723047867855349035325 32906146142950445755888247)
            ·
              refine ⟨49359219214425668633832371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32906146142950445755888247 49359219214425668633832371)
              ·
                refine ⟨74038828821638502950748557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49359219214425668633832371 74038828821638502950748557)
                ·
                  refine ⟨27764560808114438606530709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74038828821638502950748557 27764560808114438606530709)
                  ·
                    refine ⟨1301463787880364309681127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27764560808114438606530709 1301463787880364309681127)
                    ·
                      rfl

theorem cell23_7603775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_7603775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603775 prefixEnd_7603775 := by exact prefixLift 7603775
  have htrace : WordTrace (prefixWord ++ tailWord_7603775) baseStart_7603775 baseEnd_7603775 := by
    simpa [prefixWord, tailWord_7603775, baseEnd_7603775] using wordTrace_append hprefix tailTrace_7603775
  have hstable : (prefixWord ++ tailWord_7603775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603775).length < 2 ^ (prefixWord ++ tailWord_7603775).sum := by decide
  have hdescent : baseEnd_7603775 < baseStart_7603775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603812 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_7603812 : Nat := 118140960795 + 7603812 * 2 ^ 59
def prefixEnd_7603812 : Nat := 4983230072969 + 3 ^ 40 * 7603812 * 2
def baseEnd_7603812 : Nat := 3904410362425309284280711

theorem tailTrace_7603812 : CollatzResearch.WordTrace tailWord_7603812 prefixEnd_7603812 3904410362425309284280711 := by
  unfold tailWord_7603812
  simp only [CollatzResearch.WordTrace]
  refine ⟨138666903764347613272838845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184889205019130151030451793 138666903764347613272838845)
  ·
    refine ⟨52000088911630354977314567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138666903764347613272838845 52000088911630354977314567)
    ·
      refine ⟨78000133367445532465971851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52000088911630354977314567 78000133367445532465971851)
      ·
        refine ⟨117000200051168298698957777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78000133367445532465971851 117000200051168298698957777)
        ·
          refine ⟨87750150038376224024218333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117000200051168298698957777 87750150038376224024218333)
          ·
            refine ⟨32906306264391084009081875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87750150038376224024218333 32906306264391084009081875)
            ·
              refine ⟨49359459396586626013622813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32906306264391084009081875 49359459396586626013622813)
              ·
                refine ⟨18509797273719984755108555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49359459396586626013622813 18509797273719984755108555)
                ·
                  refine ⟨27764695910579977132662833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18509797273719984755108555 27764695910579977132662833)
                  ·
                    refine ⟨20823521932934982849497125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27764695910579977132662833 20823521932934982849497125)
                    ·
                      refine ⟨3904410362425309284280711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20823521932934982849497125 3904410362425309284280711)
                      ·
                        rfl

theorem cell23_7603812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_7603812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603812 prefixEnd_7603812 := by exact prefixLift 7603812
  have htrace : WordTrace (prefixWord ++ tailWord_7603812) baseStart_7603812 baseEnd_7603812 := by
    simpa [prefixWord, tailWord_7603812, baseEnd_7603812] using wordTrace_append hprefix tailTrace_7603812
  have hstable : (prefixWord ++ tailWord_7603812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603812).length < 2 ^ (prefixWord ++ tailWord_7603812).sum := by decide
  have hdescent : baseEnd_7603812 < baseStart_7603812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603816 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_7603816 : Nat := 118140960795 + 7603816 * 2 ^ 59
def prefixEnd_7603816 : Nat := 4983230072969 + 3 ^ 40 * 7603816 * 2
def baseEnd_7603816 : Nat := 3904412416347927268630693

theorem tailTrace_7603816 : CollatzResearch.WordTrace tailWord_7603816 prefixEnd_7603816 3904412416347927268630693 := by
  unfold tailWord_7603816
  simp only [CollatzResearch.WordTrace]
  refine ⟨138666976710340367614411651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184889302280453823485882201 138666976710340367614411651)
  ·
    refine ⟨208000465065510551421617477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138666976710340367614411651 208000465065510551421617477)
    ·
      refine ⟨39000087199783228391553277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208000465065510551421617477 39000087199783228391553277)
      ·
        refine ⟨14625032699918710646832479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39000087199783228391553277 14625032699918710646832479)
        ·
          refine ⟨21937549049878065970248719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625032699918710646832479 21937549049878065970248719)
          ·
            refine ⟨32906323574817098955373079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21937549049878065970248719 32906323574817098955373079)
            ·
              refine ⟨49359485362225648433059619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32906323574817098955373079 49359485362225648433059619)
              ·
                refine ⟨74039228043338472649589429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49359485362225648433059619 74039228043338472649589429)
                ·
                  refine ⟨6941177629062981810899009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74039228043338472649589429 6941177629062981810899009)
                  ·
                    refine ⟨5205883221797236358174257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6941177629062981810899009 5205883221797236358174257)
                    ·
                      refine ⟨3904412416347927268630693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205883221797236358174257 3904412416347927268630693)
                      ·
                        rfl

theorem cell23_7603816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_7603816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603816 prefixEnd_7603816 := by exact prefixLift 7603816
  have htrace : WordTrace (prefixWord ++ tailWord_7603816) baseStart_7603816 baseEnd_7603816 := by
    simpa [prefixWord, tailWord_7603816, baseEnd_7603816] using wordTrace_append hprefix tailTrace_7603816
  have hstable : (prefixWord ++ tailWord_7603816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603816).length < 2 ^ (prefixWord ++ tailWord_7603816).sum := by decide
  have hdescent : baseEnd_7603816 < baseStart_7603816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603829 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_7603829 : Nat := 118140960795 + 7603829 * 2 ^ 59
def prefixEnd_7603829 : Nat := 4983230072969 + 3 ^ 40 * 7603829 * 2
def baseEnd_7603829 : Nat := 3904419091596435717768133

theorem tailTrace_7603829 : CollatzResearch.WordTrace tailWord_7603829 prefixEnd_7603829 3904419091596435717768133 := by
  unfold tailWord_7603829
  simp only [CollatzResearch.WordTrace]
  refine ⟨277334427569633638449046541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184889618379755758966031027 277334427569633638449046541)
  ·
    refine ⟨104000410338612614418392453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277334427569633638449046541 104000410338612614418392453)
    ·
      refine ⟨19500076938489865203448585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104000410338612614418392453 19500076938489865203448585)
      ·
        refine ⟨14625057703867398902586439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19500076938489865203448585 14625057703867398902586439)
        ·
          refine ⟨21937586555801098353879659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625057703867398902586439 21937586555801098353879659)
          ·
            refine ⟨32906379833701647530819489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21937586555801098353879659 32906379833701647530819489)
            ·
              refine ⟨24679784875276235648114617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32906379833701647530819489 24679784875276235648114617)
              ·
                refine ⟨18509838656457176736085963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24679784875276235648114617 18509838656457176736085963)
                ·
                  refine ⟨27764757984685765104128945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18509838656457176736085963 27764757984685765104128945)
                  ·
                    refine ⟨20823568488514323828096709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27764757984685765104128945 20823568488514323828096709)
                    ·
                      refine ⟨3904419091596435717768133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20823568488514323828096709 3904419091596435717768133)
                      ·
                        rfl

theorem cell23_7603829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_7603829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603829 prefixEnd_7603829 := by exact prefixLift 7603829
  have htrace : WordTrace (prefixWord ++ tailWord_7603829) baseStart_7603829 baseEnd_7603829 := by
    simpa [prefixWord, tailWord_7603829, baseEnd_7603829] using wordTrace_append hprefix tailTrace_7603829
  have hstable : (prefixWord ++ tailWord_7603829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603829).length < 2 ^ (prefixWord ++ tailWord_7603829).sum := by decide
  have hdescent : baseEnd_7603829 < baseStart_7603829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603833 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 1, 2, 2]
def baseStart_7603833 : Nat := 118140960795 + 7603833 * 2 ^ 59
def prefixEnd_7603833 : Nat := 4983230072969 + 3 ^ 40 * 7603833 * 2
def baseEnd_7603833 : Nat := 3904421145519053702118115

theorem tailTrace_7603833 : CollatzResearch.WordTrace tailWord_7603833 prefixEnd_7603833 3904421145519053702118115 := by
  unfold tailWord_7603833
  simp only [CollatzResearch.WordTrace]
  refine ⟨277334573461619147132192153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184889715641079431421461435 277334573461619147132192153)
  ·
    refine ⟨208000930096214360349144115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277334573461619147132192153 208000930096214360349144115)
    ·
      refine ⟨312001395144321540523716173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208000930096214360349144115 312001395144321540523716173)
      ·
        refine ⟨117000523179120577696393565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312001395144321540523716173 117000523179120577696393565)
        ·
          refine ⟨43875196192170216636147587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117000523179120577696393565 43875196192170216636147587)
          ·
            refine ⟨65812794288255324954221381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43875196192170216636147587 65812794288255324954221381)
            ·
              refine ⟨12339898929047873428916509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65812794288255324954221381 12339898929047873428916509)
              ·
                refine ⟨4627462098392952535843691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12339898929047873428916509 4627462098392952535843691)
                ·
                  refine ⟨6941193147589428803765537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627462098392952535843691 6941193147589428803765537)
                  ·
                    refine ⟨5205894860692071602824153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6941193147589428803765537 5205894860692071602824153)
                    ·
                      refine ⟨3904421145519053702118115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205894860692071602824153 3904421145519053702118115)
                      ·
                        rfl

theorem cell23_7603833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_7603833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603833 prefixEnd_7603833 := by exact prefixLift 7603833
  have htrace : WordTrace (prefixWord ++ tailWord_7603833) baseStart_7603833 baseEnd_7603833 := by
    simpa [prefixWord, tailWord_7603833, baseEnd_7603833] using wordTrace_append hprefix tailTrace_7603833
  have hstable : (prefixWord ++ tailWord_7603833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603833).length < 2 ^ (prefixWord ++ tailWord_7603833).sum := by decide
  have hdescent : baseEnd_7603833 < baseStart_7603833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603865 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 8]
def baseStart_7603865 : Nat := 118140960795 + 7603865 * 2 ^ 59
def prefixEnd_7603865 : Nat := 4983230072969 + 3 ^ 40 * 7603865 * 2
def baseEnd_7603865 : Nat := 1301479192299999192305989

theorem tailTrace_7603865 : CollatzResearch.WordTrace tailWord_7603865 prefixEnd_7603865 1301479192299999192305989 := by
  unfold tailWord_7603865
  simp only [CollatzResearch.WordTrace]
  refine ⟨277335740597503216597357049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184890493731668811064904699 277335740597503216597357049)
  ·
    refine ⟨208001805448127412448017787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277335740597503216597357049 208001805448127412448017787)
    ·
      refine ⟨312002708172191118672026681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208001805448127412448017787 312002708172191118672026681)
      ·
        refine ⟨234002031129143339004020011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312002708172191118672026681 234002031129143339004020011)
        ·
          refine ⟨351003046693715008506030017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234002031129143339004020011 351003046693715008506030017)
          ·
            refine ⟨263252285020286256379522513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351003046693715008506030017 263252285020286256379522513)
            ·
              refine ⟨197439213765214692284641885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 263252285020286256379522513 197439213765214692284641885)
              ·
                refine ⟨74039705161955509606740707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197439213765214692284641885 74039705161955509606740707)
                ·
                  refine ⟨111059557742933264410111061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74039705161955509606740707 111059557742933264410111061)
                  ·
                    refine ⟨1301479192299999192305989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111059557742933264410111061 1301479192299999192305989)
                    ·
                      rfl

theorem cell23_7603865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 8].length) (baseStart_7603865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603865 prefixEnd_7603865 := by exact prefixLift 7603865
  have htrace : WordTrace (prefixWord ++ tailWord_7603865) baseStart_7603865 baseEnd_7603865 := by
    simpa [prefixWord, tailWord_7603865, baseEnd_7603865] using wordTrace_append hprefix tailTrace_7603865
  have hstable : (prefixWord ++ tailWord_7603865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603865).length < 2 ^ (prefixWord ++ tailWord_7603865).sum := by decide
  have hdescent : baseEnd_7603865 < baseStart_7603865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603876 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_7603876 : Nat := 118140960795 + 7603876 * 2 ^ 59
def prefixEnd_7603876 : Nat := 4983230072969 + 3 ^ 40 * 7603876 * 2
def baseEnd_7603876 : Nat := 3904443225187197033880417

theorem tailTrace_7603876 : CollatzResearch.WordTrace tailWord_7603876 prefixEnd_7603876 3904443225187197033880417 := by
  unfold tailWord_7603876
  simp only [CollatzResearch.WordTrace]
  refine ⟨138668070900231682738003741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184890761200308910317338321 138668070900231682738003741)
  ·
    refine ⟨52000526587586881026751403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138668070900231682738003741 52000526587586881026751403)
    ·
      refine ⟨78000789881380321540127105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52000526587586881026751403 78000789881380321540127105)
      ·
        refine ⟨58500592411035241155095329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78000789881380321540127105 58500592411035241155095329)
        ·
          refine ⟨43875444308276430866321497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58500592411035241155095329 43875444308276430866321497)
          ·
            refine ⟨32906583231207323149741123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43875444308276430866321497 32906583231207323149741123)
            ·
              refine ⟨49359874846810984724611685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32906583231207323149741123 49359874846810984724611685)
              ·
                refine ⟨9254976533777059635864691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49359874846810984724611685 9254976533777059635864691)
                ·
                  refine ⟨13882464800665589453797037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9254976533777059635864691 13882464800665589453797037)
                  ·
                    refine ⟨5205924300249596045173889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13882464800665589453797037 5205924300249596045173889)
                    ·
                      refine ⟨3904443225187197033880417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205924300249596045173889 3904443225187197033880417)
                      ·
                        rfl

theorem cell23_7603876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_7603876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603876 prefixEnd_7603876 := by exact prefixLift 7603876
  have htrace : WordTrace (prefixWord ++ tailWord_7603876) baseStart_7603876 baseEnd_7603876 := by
    simpa [prefixWord, tailWord_7603876, baseEnd_7603876] using wordTrace_append hprefix tailTrace_7603876
  have hstable : (prefixWord ++ tailWord_7603876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603876).length < 2 ^ (prefixWord ++ tailWord_7603876).sum := by decide
  have hdescent : baseEnd_7603876 < baseStart_7603876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603917 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_7603917 : Nat := 118140960795 + 7603917 * 2 ^ 59
def prefixEnd_7603917 : Nat := 4983230072969 + 3 ^ 40 * 7603917 * 2
def baseEnd_7603917 : Nat := 3904464277894031373467729

theorem tailTrace_7603917 : CollatzResearch.WordTrace tailWord_7603917 prefixEnd_7603917 3904464277894031373467729 := by
  unfold tailWord_7603917
  simp only [CollatzResearch.WordTrace]
  refine ⟨277337637193314829478250005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184891758128876552985500003 277337637193314829478250005)
  ·
    refine ⟨13000201743436632631792969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 277337637193314829478250005 13000201743436632631792969)
    ·
      refine ⟨9750151307577474473844727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13000201743436632631792969 9750151307577474473844727)
      ·
        refine ⟨14625226961366211710767091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750151307577474473844727 14625226961366211710767091)
        ·
          refine ⟨21937840442049317566150637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625226961366211710767091 21937840442049317566150637)
          ·
            refine ⟨8226690165768494087306489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21937840442049317566150637 8226690165768494087306489)
            ·
              refine ⟨6170017624326370565479867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8226690165768494087306489 6170017624326370565479867)
              ·
                refine ⟨9255026436489555848219801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170017624326370565479867 9255026436489555848219801)
                ·
                  refine ⟨6941269827367166886164851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255026436489555848219801 6941269827367166886164851)
                  ·
                    refine ⟨10411904741050750329247277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6941269827367166886164851 10411904741050750329247277)
                    ·
                      refine ⟨3904464277894031373467729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10411904741050750329247277 3904464277894031373467729)
                      ·
                        rfl

theorem cell23_7603917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_7603917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603917 prefixEnd_7603917 := by exact prefixLift 7603917
  have htrace : WordTrace (prefixWord ++ tailWord_7603917) baseStart_7603917 baseEnd_7603917 := by
    simpa [prefixWord, tailWord_7603917, baseEnd_7603917] using wordTrace_append hprefix tailTrace_7603917
  have hstable : (prefixWord ++ tailWord_7603917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603917).length < 2 ^ (prefixWord ++ tailWord_7603917).sum := by decide
  have hdescent : baseEnd_7603917 < baseStart_7603917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603962 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4]
def baseStart_7603962 : Nat := 118140960795 + 7603962 * 2 ^ 59
def prefixEnd_7603962 : Nat := 4983230072969 + 3 ^ 40 * 7603962 * 2
def baseEnd_7603962 : Nat := 3904487384523483697405021

theorem tailTrace_7603962 : CollatzResearch.WordTrace tailWord_7603962 prefixEnd_7603962 3904487384523483697405021 := by
  unfold tailWord_7603962
  simp only [CollatzResearch.WordTrace]
  refine ⟨69334819619537950540909535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184892852318767868109092093 69334819619537950540909535)
  ·
    refine ⟨104002229429306925811364303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69334819619537950540909535 104002229429306925811364303)
    ·
      refine ⟨156003344143960388717046455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104002229429306925811364303 156003344143960388717046455)
      ·
        refine ⟨234005016215940583075569683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156003344143960388717046455 234005016215940583075569683)
        ·
          refine ⟨351007524323910874613354525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234005016215940583075569683 351007524323910874613354525)
          ·
            refine ⟨131627821621466577980007947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 351007524323910874613354525 131627821621466577980007947)
            ·
              refine ⟨197441732432199866970011921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131627821621466577980007947 197441732432199866970011921)
              ·
                refine ⟨148081299324149900227508941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197441732432199866970011921 148081299324149900227508941)
                ·
                  refine ⟨55530487246556212585315853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 148081299324149900227508941 55530487246556212585315853)
                  ·
                    refine ⟨20823932717458579719493445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55530487246556212585315853 20823932717458579719493445)
                    ·
                      refine ⟨3904487384523483697405021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20823932717458579719493445 3904487384523483697405021)
                      ·
                        rfl

theorem cell23_7603962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_7603962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603962 prefixEnd_7603962 := by exact prefixLift 7603962
  have htrace : WordTrace (prefixWord ++ tailWord_7603962) baseStart_7603962 baseEnd_7603962 := by
    simpa [prefixWord, tailWord_7603962, baseEnd_7603962] using wordTrace_append hprefix tailTrace_7603962
  have hstable : (prefixWord ++ tailWord_7603962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603962).length < 2 ^ (prefixWord ++ tailWord_7603962).sum := by decide
  have hdescent : baseEnd_7603962 < baseStart_7603962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603979 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 6, 2]
def baseStart_7603979 : Nat := 118140960795 + 7603979 * 2 ^ 59
def prefixEnd_7603979 : Nat := 4983230072969 + 3 ^ 40 * 7603979 * 2
def baseEnd_7603979 : Nat := 3904496113694610130892443

theorem tailTrace_7603979 : CollatzResearch.WordTrace tailWord_7603979 prefixEnd_7603979 3904496113694610130892443 := by
  unfold tailWord_7603979
  simp only [CollatzResearch.WordTrace]
  refine ⟨277339898519090214067006991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184893265679393476044671327 277339898519090214067006991)
  ·
    refine ⟨416009847778635321100510487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277339898519090214067006991 416009847778635321100510487)
    ·
      refine ⟨624014771667952981650765731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416009847778635321100510487 624014771667952981650765731)
      ·
        refine ⟨936022157501929472476148597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624014771667952981650765731 936022157501929472476148597)
        ·
          refine ⟨87752077265805888044638931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 936022157501929472476148597 87752077265805888044638931)
          ·
            refine ⟨131628115898708832066958397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87752077265805888044638931 131628115898708832066958397)
            ·
              refine ⟨49360543462015812025109399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131628115898708832066958397 49360543462015812025109399)
              ·
                refine ⟨74040815193023718037664099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49360543462015812025109399 74040815193023718037664099)
                ·
                  refine ⟨111061222789535577056496149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74040815193023718037664099 111061222789535577056496149)
                  ·
                    refine ⟨5205994818259480174523257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111061222789535577056496149 5205994818259480174523257)
                    ·
                      refine ⟨3904496113694610130892443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5205994818259480174523257 3904496113694610130892443)
                      ·
                        rfl

theorem cell23_7603979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 6, 2].length) (baseStart_7603979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603979 prefixEnd_7603979 := by exact prefixLift 7603979
  have htrace : WordTrace (prefixWord ++ tailWord_7603979) baseStart_7603979 baseEnd_7603979 := by
    simpa [prefixWord, tailWord_7603979, baseEnd_7603979] using wordTrace_append hprefix tailTrace_7603979
  have hstable : (prefixWord ++ tailWord_7603979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603979).length < 2 ^ (prefixWord ++ tailWord_7603979).sum := by decide
  have hdescent : baseEnd_7603979 < baseStart_7603979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603989 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 5, 4]
def baseStart_7603989 : Nat := 118140960795 + 7603989 * 2 ^ 59
def prefixEnd_7603989 : Nat := 4983230072969 + 3 ^ 40 * 7603989 * 2
def baseEnd_7603989 : Nat := 1301500416167051697255799

theorem tailTrace_7603989 : CollatzResearch.WordTrace tailWord_7603989 prefixEnd_7603989 1301500416167051697255799 := by
  unfold tailWord_7603989
  simp only [CollatzResearch.WordTrace]
  refine ⟨277340263249053985774871021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184893508832702657183247347 277340263249053985774871021)
  ·
    refine ⟨104002598718395244665576633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277340263249053985774871021 104002598718395244665576633)
    ·
      refine ⟨78001949038796433499182475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104002598718395244665576633 78001949038796433499182475)
      ·
        refine ⟨117002923558194650248773713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78001949038796433499182475 117002923558194650248773713)
        ·
          refine ⟨87752192668645987686580285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117002923558194650248773713 87752192668645987686580285)
          ·
            refine ⟨32907072250742245382467607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87752192668645987686580285 32907072250742245382467607)
            ·
              refine ⟨49360608376113368073701411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32907072250742245382467607 49360608376113368073701411)
              ·
                refine ⟨74040912564170052110552117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49360608376113368073701411 74040912564170052110552117)
                ·
                  refine ⟨6941335552890942385364261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74040912564170052110552117 6941335552890942385364261)
                  ·
                    refine ⟨1301500416167051697255799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941335552890942385364261 1301500416167051697255799)
                    ·
                      rfl

theorem cell23_7603989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_7603989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603989 prefixEnd_7603989 := by exact prefixLift 7603989
  have htrace : WordTrace (prefixWord ++ tailWord_7603989) baseStart_7603989 baseEnd_7603989 := by
    simpa [prefixWord, tailWord_7603989, baseEnd_7603989] using wordTrace_append hprefix tailTrace_7603989
  have hstable : (prefixWord ++ tailWord_7603989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603989).length < 2 ^ (prefixWord ++ tailWord_7603989).sum := by decide
  have hdescent : baseEnd_7603989 < baseStart_7603989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7603999 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_7603999 : Nat := 118140960795 + 7603999 * 2 ^ 59
def prefixEnd_7603999 : Nat := 4983230072969 + 3 ^ 40 * 7603999 * 2
def baseEnd_7603999 : Nat := 3904506383307700052642351

theorem tailTrace_7603999 : CollatzResearch.WordTrace tailWord_7603999 prefixEnd_7603999 3904506383307700052642351 := by
  unfold tailWord_7603999
  simp only [CollatzResearch.WordTrace]
  refine ⟨277340627979017757482735051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184893751986011838321823367 277340627979017757482735051)
  ·
    refine ⟨416010941968526636224102577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277340627979017757482735051 416010941968526636224102577)
    ·
      refine ⟨312008206476394977168076933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416010941968526636224102577 312008206476394977168076933)
      ·
        refine ⟨58501538714324058219014425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312008206476394977168076933 58501538714324058219014425)
        ·
          refine ⟨43876154035743043664260819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58501538714324058219014425 43876154035743043664260819)
          ·
            refine ⟨65814231053614565496391229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43876154035743043664260819 65814231053614565496391229)
            ·
              refine ⟨24680336645105462061146711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65814231053614565496391229 24680336645105462061146711)
              ·
                refine ⟨37020504967658193091720067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24680336645105462061146711 37020504967658193091720067)
                ·
                  refine ⟨55530757451487289637580101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37020504967658193091720067 55530757451487289637580101)
                  ·
                    refine ⟨10412017022153866807046269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55530757451487289637580101 10412017022153866807046269)
                    ·
                      refine ⟨3904506383307700052642351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412017022153866807046269 3904506383307700052642351)
                      ·
                        rfl

theorem cell23_7603999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_7603999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7603999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7603999 prefixEnd_7603999 := by exact prefixLift 7603999
  have htrace : WordTrace (prefixWord ++ tailWord_7603999) baseStart_7603999 baseEnd_7603999 := by
    simpa [prefixWord, tailWord_7603999, baseEnd_7603999] using wordTrace_append hprefix tailTrace_7603999
  have hstable : (prefixWord ++ tailWord_7603999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7603999).length < 2 ^ (prefixWord ++ tailWord_7603999).sum := by decide
  have hdescent : baseEnd_7603999 < baseStart_7603999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7603999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604019 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 8]
def baseStart_7604019 : Nat := 118140960795 + 7604019 * 2 ^ 59
def prefixEnd_7604019 : Nat := 4983230072969 + 3 ^ 40 * 7604019 * 2
def baseEnd_7604019 : Nat := 433835183657865552710251

theorem tailTrace_7604019 : CollatzResearch.WordTrace tailWord_7604019 prefixEnd_7604019 433835183657865552710251 := by
  unfold tailWord_7604019
  simp only [CollatzResearch.WordTrace]
  refine ⟨277341357438945300898463111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184894238292630200598975407 277341357438945300898463111)
  ·
    refine ⟨416012036158417951347694667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277341357438945300898463111 416012036158417951347694667)
    ·
      refine ⟨624018054237626927021542001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416012036158417951347694667 624018054237626927021542001)
      ·
        refine ⟨468013540678220195266156501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624018054237626927021542001 468013540678220195266156501)
        ·
          refine ⟨10969067359645785826550543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 468013540678220195266156501 10969067359645785826550543)
          ·
            refine ⟨16453601039468678739825815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969067359645785826550543 16453601039468678739825815)
            ·
              refine ⟨24680401559203018109738723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16453601039468678739825815 24680401559203018109738723)
              ·
                refine ⟨37020602338804527164608085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24680401559203018109738723 37020602338804527164608085)
                ·
                  refine ⟨433835183657865552710251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37020602338804527164608085 433835183657865552710251)
                  ·
                    rfl

theorem cell23_7604019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 8].length) (baseStart_7604019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604019 prefixEnd_7604019 := by exact prefixLift 7604019
  have htrace : WordTrace (prefixWord ++ tailWord_7604019) baseStart_7604019 baseEnd_7604019 := by
    simpa [prefixWord, tailWord_7604019, baseEnd_7604019] using wordTrace_append hprefix tailTrace_7604019
  have hstable : (prefixWord ++ tailWord_7604019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604019).length < 2 ^ (prefixWord ++ tailWord_7604019).sum := by decide
  have hdescent : baseEnd_7604019 < baseStart_7604019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604069 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_7604069 : Nat := 118140960795 + 7604069 * 2 ^ 59
def prefixEnd_7604069 : Nat := 4983230072969 + 3 ^ 40 * 7604069 * 2
def baseEnd_7604069 : Nat := 3904542326953514778767029

theorem tailTrace_7604069 : CollatzResearch.WordTrace tailWord_7604069 prefixEnd_7604069 3904542326953514778767029 := by
  unfold tailWord_7604069
  simp only [CollatzResearch.WordTrace]
  refine ⟨277343181088764159437783261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184895454059176106291855507 277343181088764159437783261)
  ·
    refine ⟨104003692908286559789168723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277343181088764159437783261 104003692908286559789168723)
    ·
      refine ⟨156005539362429839683753085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104003692908286559789168723 156005539362429839683753085)
      ·
        refine ⟨58502077260911189881407407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156005539362429839683753085 58502077260911189881407407)
        ·
          refine ⟨87753115891366784822111111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58502077260911189881407407 87753115891366784822111111)
          ·
            refine ⟨131629673837050177233166667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87753115891366784822111111 131629673837050177233166667)
            ·
              refine ⟨197444510755575265849750001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131629673837050177233166667 197444510755575265849750001)
              ·
                refine ⟨148083383066681449387312501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197444510755575265849750001 148083383066681449387312501)
                ·
                  refine ⟨13882817162501385880060547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 148083383066681449387312501 13882817162501385880060547)
                  ·
                    refine ⟨20824225743752078820090821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13882817162501385880060547 20824225743752078820090821)
                    ·
                      refine ⟨3904542326953514778767029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20824225743752078820090821 3904542326953514778767029)
                      ·
                        rfl

theorem cell23_7604069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_7604069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604069 prefixEnd_7604069 := by exact prefixLift 7604069
  have htrace : WordTrace (prefixWord ++ tailWord_7604069) baseStart_7604069 baseEnd_7604069 := by
    simpa [prefixWord, tailWord_7604069, baseEnd_7604069] using wordTrace_append hprefix tailTrace_7604069
  have hstable : (prefixWord ++ tailWord_7604069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604069).length < 2 ^ (prefixWord ++ tailWord_7604069).sum := by decide
  have hdescent : baseEnd_7604069 < baseStart_7604069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604089 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 5]
def baseStart_7604089 : Nat := 118140960795 + 7604089 * 2 ^ 59
def prefixEnd_7604089 : Nat := 4983230072969 + 3 ^ 40 * 7604089 * 2
def baseEnd_7604089 : Nat := 3904552596566604700516937

theorem tailTrace_7604089 : CollatzResearch.WordTrace tailWord_7604089 prefixEnd_7604089 3904552596566604700516937 := by
  unfold tailWord_7604089
  simp only [CollatzResearch.WordTrace]
  refine ⟨277343910548691702853511321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184895940365794468569007547 277343910548691702853511321)
  ·
    refine ⟨208007932911518777140133491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277343910548691702853511321 208007932911518777140133491)
    ·
      refine ⟨312011899367278165710200237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208007932911518777140133491 312011899367278165710200237)
      ·
        refine ⟨117004462262729312141325089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312011899367278165710200237 117004462262729312141325089)
        ·
          refine ⟨87753346697046984105993817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117004462262729312141325089 87753346697046984105993817)
          ·
            refine ⟨65815010022785238079495363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87753346697046984105993817 65815010022785238079495363)
            ·
              refine ⟨98722515034177857119243045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65815010022785238079495363 98722515034177857119243045)
              ·
                refine ⟨18510471568908348209858071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98722515034177857119243045 18510471568908348209858071)
                ·
                  refine ⟨27765707353362522314787107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18510471568908348209858071 27765707353362522314787107)
                  ·
                    refine ⟨41648561030043783472180661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27765707353362522314787107 41648561030043783472180661)
                    ·
                      refine ⟨3904552596566604700516937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41648561030043783472180661 3904552596566604700516937)
                      ·
                        rfl

theorem cell23_7604089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_7604089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604089 prefixEnd_7604089 := by exact prefixLift 7604089
  have htrace : WordTrace (prefixWord ++ tailWord_7604089) baseStart_7604089 baseEnd_7604089 := by
    simpa [prefixWord, tailWord_7604089, baseEnd_7604089] using wordTrace_append hprefix tailTrace_7604089
  have hstable : (prefixWord ++ tailWord_7604089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604089).length < 2 ^ (prefixWord ++ tailWord_7604089).sum := by decide
  have hdescent : baseEnd_7604089 < baseStart_7604089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604096 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 2, 4]
def baseStart_7604096 : Nat := 118140960795 + 7604096 * 2 ^ 59
def prefixEnd_7604096 : Nat := 4983230072969 + 3 ^ 40 * 7604096 * 2
def baseEnd_7604096 : Nat := 1301518730310395391043135

theorem tailTrace_7604096 : CollatzResearch.WordTrace tailWord_7604096 prefixEnd_7604096 1301518730310395391043135 := by
  unfold tailWord_7604096
  simp only [CollatzResearch.WordTrace]
  refine ⟨138672082929833171524508071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184896110573110895366010761 138672082929833171524508071)
  ·
    refine ⟨208008124394749757286762107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138672082929833171524508071 208008124394749757286762107)
    ·
      refine ⟨312012186592124635930143161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208008124394749757286762107 312012186592124635930143161)
      ·
        refine ⟨234009139944093476947607371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312012186592124635930143161 234009139944093476947607371)
        ·
          refine ⟨351013709916140215421411057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234009139944093476947607371 351013709916140215421411057)
          ·
            refine ⟨263260282437105161566058293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351013709916140215421411057 263260282437105161566058293)
            ·
              refine ⟨24680651478478608896817965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263260282437105161566058293 24680651478478608896817965)
              ·
                refine ⟨9255244304429478336306737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24680651478478608896817965 9255244304429478336306737)
                ·
                  refine ⟨6941433228322108752230053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255244304429478336306737 6941433228322108752230053)
                  ·
                    refine ⟨1301518730310395391043135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941433228322108752230053 1301518730310395391043135)
                    ·
                      rfl

theorem cell23_7604096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 2, 4].length) (baseStart_7604096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604096 prefixEnd_7604096 := by exact prefixLift 7604096
  have htrace : WordTrace (prefixWord ++ tailWord_7604096) baseStart_7604096 baseEnd_7604096 := by
    simpa [prefixWord, tailWord_7604096, baseEnd_7604096] using wordTrace_append hprefix tailTrace_7604096
  have hstable : (prefixWord ++ tailWord_7604096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604096).length < 2 ^ (prefixWord ++ tailWord_7604096).sum := by decide
  have hdescent : baseEnd_7604096 < baseStart_7604096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604099 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_7604099 : Nat := 118140960795 + 7604099 * 2 ^ 59
def prefixEnd_7604099 : Nat := 4983230072969 + 3 ^ 40 * 7604099 * 2
def baseEnd_7604099 : Nat := 3904557731373149661391891

theorem tailTrace_7604099 : CollatzResearch.WordTrace tailWord_7604099 prefixEnd_7604099 3904557731373149661391891 := by
  unfold tailWord_7604099
  simp only [CollatzResearch.WordTrace]
  refine ⟨277344275278655474561375351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184896183519103649707583567 277344275278655474561375351)
  ·
    refine ⟨416016412917983211842063027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277344275278655474561375351 416016412917983211842063027)
    ·
      refine ⟨624024619376974817763094541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416016412917983211842063027 624024619376974817763094541)
      ·
        refine ⟨234009232266365556661160453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624024619376974817763094541 234009232266365556661160453)
        ·
          refine ⟨43876731049943541873967585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234009232266365556661160453 43876731049943541873967585)
          ·
            refine ⟨32907548287457656405475689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43876731049943541873967585 32907548287457656405475689)
            ·
              refine ⟨24680661215593242304106767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32907548287457656405475689 24680661215593242304106767)
              ·
                refine ⟨37020991823389863456160151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24680661215593242304106767 37020991823389863456160151)
                ·
                  refine ⟨55531487735084795184240227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37020991823389863456160151 55531487735084795184240227)
                  ·
                    refine ⟨83297231602627192776360341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55531487735084795184240227 83297231602627192776360341)
                    ·
                      refine ⟨3904557731373149661391891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83297231602627192776360341 3904557731373149661391891)
                      ·
                        rfl

theorem cell23_7604099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_7604099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604099 prefixEnd_7604099 := by exact prefixLift 7604099
  have htrace : WordTrace (prefixWord ++ tailWord_7604099) baseStart_7604099 baseEnd_7604099 := by
    simpa [prefixWord, tailWord_7604099, baseEnd_7604099] using wordTrace_append hprefix tailTrace_7604099
  have hstable : (prefixWord ++ tailWord_7604099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604099).length < 2 ^ (prefixWord ++ tailWord_7604099).sum := by decide
  have hdescent : baseEnd_7604099 < baseStart_7604099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604116 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7604116 : Nat := 118140960795 + 7604116 * 2 ^ 59
def prefixEnd_7604116 : Nat := 4983230072969 + 3 ^ 40 * 7604116 * 2
def baseEnd_7604116 : Nat := 3904566460544276094879313

theorem tailTrace_7604116 : CollatzResearch.WordTrace tailWord_7604116 prefixEnd_7604116 3904566460544276094879313 := by
  unfold tailWord_7604116
  simp only [CollatzResearch.WordTrace]
  refine ⟨138672447659796943232372101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184896596879729257643162801 138672447659796943232372101)
  ·
    refine ⟨26001083936211926856069769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138672447659796943232372101 26001083936211926856069769)
    ·
      refine ⟨19500812952158945142052327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26001083936211926856069769 19500812952158945142052327)
      ·
        refine ⟨29251219428238417713078491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19500812952158945142052327 29251219428238417713078491)
        ·
          refine ⟨43876829142357626569617737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29251219428238417713078491 43876829142357626569617737)
          ·
            refine ⟨32907621856768219927213303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43876829142357626569617737 32907621856768219927213303)
            ·
              refine ⟨49361432785152329890819955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32907621856768219927213303 49361432785152329890819955)
              ·
                refine ⟨74042149177728494836229933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49361432785152329890819955 74042149177728494836229933)
                ·
                  refine ⟨27765805941648185563586225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74042149177728494836229933 27765805941648185563586225)
                  ·
                    refine ⟨20824354456236139172689669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27765805941648185563586225 20824354456236139172689669)
                    ·
                      refine ⟨3904566460544276094879313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20824354456236139172689669 3904566460544276094879313)
                      ·
                        rfl

theorem cell23_7604116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7604116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604116 prefixEnd_7604116 := by exact prefixLift 7604116
  have htrace : WordTrace (prefixWord ++ tailWord_7604116) baseStart_7604116 baseEnd_7604116 := by
    simpa [prefixWord, tailWord_7604116, baseEnd_7604116] using wordTrace_append hprefix tailTrace_7604116
  have hstable : (prefixWord ++ tailWord_7604116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604116).length < 2 ^ (prefixWord ++ tailWord_7604116).sum := by decide
  have hdescent : baseEnd_7604116 < baseStart_7604116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604126 : List Nat := [4, 3, 1, 3, 12]
def baseStart_7604126 : Nat := 118140960795 + 7604126 * 2 ^ 59
def prefixEnd_7604126 : Nat := 4983230072969 + 3 ^ 40 * 7604126 * 2
def baseEnd_7604126 : Nat := 5356065288547079637523

theorem tailTrace_7604126 : CollatzResearch.WordTrace tailWord_7604126 prefixEnd_7604126 5356065288547079637523 := by
  unfold tailWord_7604126
  simp only [CollatzResearch.WordTrace]
  refine ⟨34668157506194707271576029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184896840033038438781738821 34668157506194707271576029)
  ·
    refine ⟨13000559064823015226841011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34668157506194707271576029 13000559064823015226841011)
    ·
      refine ⟨19500838597234522840261517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13000559064823015226841011 19500838597234522840261517)
      ·
        refine ⟨7312814473962946065098069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19500838597234522840261517 7312814473962946065098069)
        ·
          refine ⟨5356065288547079637523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7312814473962946065098069 5356065288547079637523)
          ·
            rfl

theorem cell23_7604126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 12].length) (baseStart_7604126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604126 prefixEnd_7604126 := by exact prefixLift 7604126
  have htrace : WordTrace (prefixWord ++ tailWord_7604126) baseStart_7604126 baseEnd_7604126 := by
    simpa [prefixWord, tailWord_7604126, baseEnd_7604126] using wordTrace_append hprefix tailTrace_7604126
  have hstable : (prefixWord ++ tailWord_7604126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604126).length < 2 ^ (prefixWord ++ tailWord_7604126).sum := by decide
  have hdescent : baseEnd_7604126 < baseStart_7604126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604130 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 2, 4]
def baseStart_7604130 : Nat := 118140960795 + 7604130 * 2 ^ 59
def prefixEnd_7604130 : Nat := 4983230072969 + 3 ^ 40 * 7604130 * 2
def baseEnd_7604130 : Nat := 1301524549757813013368083

theorem tailTrace_7604130 : CollatzResearch.WordTrace tailWord_7604130 prefixEnd_7604130 1301524549757813013368083 := by
  unfold tailWord_7604130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69336351485385791713938461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184896937294362111237169229 69336351485385791713938461)
  ·
    refine ⟨26001131807019671892726923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69336351485385791713938461 26001131807019671892726923)
    ·
      refine ⟨39001697710529507839090385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26001131807019671892726923 39001697710529507839090385)
      ·
        refine ⟨29251273282897130879317789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39001697710529507839090385 29251273282897130879317789)
        ·
          refine ⟨10969227481086424079744171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29251273282897130879317789 10969227481086424079744171)
          ·
            refine ⟨16453841221629636119616257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969227481086424079744171 16453841221629636119616257)
            ·
              refine ⟨12340380916222227089712193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16453841221629636119616257 12340380916222227089712193)
              ·
                refine ⟨9255285687166670317284145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12340380916222227089712193 9255285687166670317284145)
                ·
                  refine ⟨6941464265375002737963109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255285687166670317284145 6941464265375002737963109)
                  ·
                    refine ⟨1301524549757813013368083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941464265375002737963109 1301524549757813013368083)
                    ·
                      rfl

theorem cell23_7604130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_7604130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604130 prefixEnd_7604130 := by exact prefixLift 7604130
  have htrace : WordTrace (prefixWord ++ tailWord_7604130) baseStart_7604130 baseEnd_7604130 := by
    simpa [prefixWord, tailWord_7604130, baseEnd_7604130] using wordTrace_append hprefix tailTrace_7604130
  have hstable : (prefixWord ++ tailWord_7604130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604130).length < 2 ^ (prefixWord ++ tailWord_7604130).sum := by decide
  have hdescent : baseEnd_7604130 < baseStart_7604130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604153 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 3]
def baseStart_7604153 : Nat := 118140960795 + 7604153 * 2 ^ 59
def prefixEnd_7604153 : Nat := 4983230072969 + 3 ^ 40 * 7604153 * 2
def baseEnd_7604153 : Nat := 3904585459328492450116643

theorem tailTrace_7604153 : CollatzResearch.WordTrace tailWord_7604153 prefixEnd_7604153 3904585459328492450116643 := by
  unfold tailWord_7604153
  simp only [CollatzResearch.WordTrace]
  refine ⟨277346244820459841783841113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184897496546973227855894075 277346244820459841783841113)
  ·
    refine ⟨208009683615344881337880835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277346244820459841783841113 208009683615344881337880835)
    ·
      refine ⟨312014525423017322006821253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208009683615344881337880835 312014525423017322006821253)
      ·
        refine ⟨58502723516815747876278985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312014525423017322006821253 58502723516815747876278985)
        ·
          refine ⟨43877042637611810907209239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58502723516815747876278985 43877042637611810907209239)
          ·
            refine ⟨65815563956417716360813859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43877042637611810907209239 65815563956417716360813859)
            ·
              refine ⟨98723345934626574541220789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65815563956417716360813859 98723345934626574541220789)
              ·
                refine ⟨9255313681371241363239449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98723345934626574541220789 9255313681371241363239449)
                ·
                  refine ⟨6941485261028431022429587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255313681371241363239449 6941485261028431022429587)
                  ·
                    refine ⟨10412227891542646533644381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6941485261028431022429587 10412227891542646533644381)
                    ·
                      refine ⟨3904585459328492450116643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412227891542646533644381 3904585459328492450116643)
                      ·
                        rfl

theorem cell23_7604153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_7604153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604153 prefixEnd_7604153 := by exact prefixLift 7604153
  have htrace : WordTrace (prefixWord ++ tailWord_7604153) baseStart_7604153 baseEnd_7604153 := by
    simpa [prefixWord, tailWord_7604153, baseEnd_7604153] using wordTrace_append hprefix tailTrace_7604153
  have hstable : (prefixWord ++ tailWord_7604153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604153).length < 2 ^ (prefixWord ++ tailWord_7604153).sum := by decide
  have hdescent : baseEnd_7604153 < baseStart_7604153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604159 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_7604159 : Nat := 118140960795 + 7604159 * 2 ^ 59
def prefixEnd_7604159 : Nat := 4983230072969 + 3 ^ 40 * 7604159 * 2
def baseEnd_7604159 : Nat := 3904588540212419426641615

theorem tailTrace_7604159 : CollatzResearch.WordTrace tailWord_7604159 prefixEnd_7604159 3904588540212419426641615 := by
  unfold tailWord_7604159
  simp only [CollatzResearch.WordTrace]
  refine ⟨277346463658438104808559531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184897642438958736539039687 277346463658438104808559531)
  ·
    refine ⟨416019695487657157212839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277346463658438104808559531 416019695487657157212839297)
    ·
      refine ⟨312014771615742867909629473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416019695487657157212839297 312014771615742867909629473)
      ·
        refine ⟨234011078711807150932222105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312014771615742867909629473 234011078711807150932222105)
        ·
          refine ⟨175508309033855363199166579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234011078711807150932222105 175508309033855363199166579)
          ·
            refine ⟨263262463550783044798749869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175508309033855363199166579 263262463550783044798749869)
            ·
              refine ⟨98723423831543641799531201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263262463550783044798749869 98723423831543641799531201)
              ·
                refine ⟨74042567873657731349648401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98723423831543641799531201 74042567873657731349648401)
                ·
                  refine ⟨55531925905243298512236301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74042567873657731349648401 55531925905243298512236301)
                  ·
                    refine ⟨20824472214466236942088613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55531925905243298512236301 20824472214466236942088613)
                    ·
                      refine ⟨3904588540212419426641615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20824472214466236942088613 3904588540212419426641615)
                      ·
                        rfl

theorem cell23_7604159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_7604159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604159 prefixEnd_7604159 := by exact prefixLift 7604159
  have htrace : WordTrace (prefixWord ++ tailWord_7604159) baseStart_7604159 baseEnd_7604159 := by
    simpa [prefixWord, tailWord_7604159, baseEnd_7604159] using wordTrace_append hprefix tailTrace_7604159
  have hstable : (prefixWord ++ tailWord_7604159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604159).length < 2 ^ (prefixWord ++ tailWord_7604159).sum := by decide
  have hdescent : baseEnd_7604159 < baseStart_7604159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604180 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_7604180 : Nat := 118140960795 + 7604180 * 2 ^ 59
def prefixEnd_7604180 : Nat := 4983230072969 + 3 ^ 40 * 7604180 * 2
def baseEnd_7604180 : Nat := 3904599323306163844479019

theorem tailTrace_7604180 : CollatzResearch.WordTrace tailWord_7604180 prefixEnd_7604180 3904599323306163844479019 := by
  unfold tailWord_7604180
  simp only [CollatzResearch.WordTrace]
  refine ⟨138673614795681012697536997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184898153060908016930049329 138673614795681012697536997)
  ·
    refine ⟨26001302774190189880788187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138673614795681012697536997 26001302774190189880788187)
    ·
      refine ⟨39001954161285284821182281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26001302774190189880788187 39001954161285284821182281)
      ·
        refine ⟨29251465620963963615886711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39001954161285284821182281 29251465620963963615886711)
        ·
          refine ⟨43877198431445945423830067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29251465620963963615886711 43877198431445945423830067)
          ·
            refine ⟨65815797647168918135745101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43877198431445945423830067 65815797647168918135745101)
            ·
              refine ⟨24680924117688344300904413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65815797647168918135745101 24680924117688344300904413)
              ·
                refine ⟨9255346544133129112839155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24680924117688344300904413 9255346544133129112839155)
                ·
                  refine ⟨13883019816199693669258733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9255346544133129112839155 13883019816199693669258733)
                  ·
                    refine ⟨5206132431074885125972025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13883019816199693669258733 5206132431074885125972025)
                    ·
                      refine ⟨3904599323306163844479019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206132431074885125972025 3904599323306163844479019)
                      ·
                        rfl

theorem cell23_7604180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_7604180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604180 prefixEnd_7604180 := by exact prefixLift 7604180
  have htrace : WordTrace (prefixWord ++ tailWord_7604180) baseStart_7604180 baseEnd_7604180 := by
    simpa [prefixWord, tailWord_7604180, baseEnd_7604180] using wordTrace_append hprefix tailTrace_7604180
  have hstable : (prefixWord ++ tailWord_7604180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604180).length < 2 ^ (prefixWord ++ tailWord_7604180).sum := by decide
  have hdescent : baseEnd_7604180 < baseStart_7604180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604250 : List Nat := [3, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_7604250 : Nat := 118140960795 + 7604250 * 2 ^ 59
def prefixEnd_7604250 : Nat := 4983230072969 + 3 ^ 40 * 7604250 * 2
def baseEnd_7604250 : Nat := 433848362994664285622633

theorem tailTrace_7604250 : CollatzResearch.WordTrace tailWord_7604250 prefixEnd_7604250 433848362994664285622633 := by
  unfold tailWord_7604250
  simp only [CollatzResearch.WordTrace]
  refine ⟨69337445675277106837530551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184899855134072284900081469 69337445675277106837530551)
  ·
    refine ⟨104006168512915660256295827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69337445675277106837530551 104006168512915660256295827)
    ·
      refine ⟨156009252769373490384443741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104006168512915660256295827 156009252769373490384443741)
      ·
        refine ⟨58503469788515058894166403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156009252769373490384443741 58503469788515058894166403)
        ·
          refine ⟨87755204682772588341249605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58503469788515058894166403 87755204682772588341249605)
          ·
            refine ⟨16454100878019860313984301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87755204682772588341249605 16454100878019860313984301)
            ·
              refine ⟨6170287829257447617744113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16454100878019860313984301 6170287829257447617744113)
              ·
                refine ⟨4627715871943085713308085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170287829257447617744113 4627715871943085713308085)
                ·
                  refine ⟨433848362994664285622633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627715871943085713308085 433848362994664285622633)
                  ·
                    rfl

theorem cell23_7604250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_7604250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604250 prefixEnd_7604250 := by exact prefixLift 7604250
  have htrace : WordTrace (prefixWord ++ tailWord_7604250) baseStart_7604250 baseEnd_7604250 := by
    simpa [prefixWord, tailWord_7604250, baseEnd_7604250] using wordTrace_append hprefix tailTrace_7604250
  have hstable : (prefixWord ++ tailWord_7604250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604250).length < 2 ^ (prefixWord ++ tailWord_7604250).sum := by decide
  have hdescent : baseEnd_7604250 < baseStart_7604250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604317 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_7604317 : Nat := 118140960795 + 7604317 * 2 ^ 59
def prefixEnd_7604317 : Nat := 4983230072969 + 3 ^ 40 * 7604317 * 2
def baseEnd_7604317 : Nat := 3904669670155829808465889

theorem tailTrace_7604317 : CollatzResearch.WordTrace tailWord_7604317 prefixEnd_7604317 3904669670155829808465889 := by
  unfold tailWord_7604317
  simp only [CollatzResearch.WordTrace]
  refine ⟨277352226391865697792811205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184901484261243798528540803 277352226391865697792811205)
  ·
    refine ⟨52003542448474818336152101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277352226391865697792811205 52003542448474818336152101)
    ·
      refine ⟨9750664209089028438028519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52003542448474818336152101 9750664209089028438028519)
      ·
        refine ⟨14625996313633542657042779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750664209089028438028519 14625996313633542657042779)
        ·
          refine ⟨21938994470450313985564169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14625996313633542657042779 21938994470450313985564169)
          ·
            refine ⟨16454245852837735489173127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21938994470450313985564169 16454245852837735489173127)
            ·
              refine ⟨24681368779256603233759691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454245852837735489173127 24681368779256603233759691)
              ·
                refine ⟨37022053168884904850639537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24681368779256603233759691 37022053168884904850639537)
                ·
                  refine ⟨27766539876663678637979653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37022053168884904850639537 27766539876663678637979653)
                  ·
                    refine ⟨5206226226874439744621185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27766539876663678637979653 5206226226874439744621185)
                    ·
                      refine ⟨3904669670155829808465889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206226226874439744621185 3904669670155829808465889)
                      ·
                        rfl

theorem cell23_7604317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_7604317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604317 prefixEnd_7604317 := by exact prefixLift 7604317
  have htrace : WordTrace (prefixWord ++ tailWord_7604317) baseStart_7604317 baseEnd_7604317 := by
    simpa [prefixWord, tailWord_7604317, baseEnd_7604317] using wordTrace_append hprefix tailTrace_7604317
  have hstable : (prefixWord ++ tailWord_7604317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604317).length < 2 ^ (prefixWord ++ tailWord_7604317).sum := by decide
  have hdescent : baseEnd_7604317 < baseStart_7604317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604401 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 1, 1, 3]
def baseStart_7604401 : Nat := 118140960795 + 7604401 * 2 ^ 59
def prefixEnd_7604401 : Nat := 4983230072969 + 3 ^ 40 * 7604401 * 2
def baseEnd_7604401 : Nat := 3904712802530807479815503

theorem tailTrace_7604401 : CollatzResearch.WordTrace tailWord_7604401 prefixEnd_7604401 3904712802530807479815503 := by
  unfold tailWord_7604401
  simp only [CollatzResearch.WordTrace]
  refine ⟨277355290123561380138869057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184903526749040920092579371 277355290123561380138869057)
  ·
    refine ⟨208016467592671035104151793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277355290123561380138869057 208016467592671035104151793)
    ·
      refine ⟨156012350694503276328113845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208016467592671035104151793 156012350694503276328113845)
      ·
        refine ⟨14626157877609682155760673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156012350694503276328113845 14626157877609682155760673)
        ·
          refine ⟨10969618408207261616820505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14626157877609682155760673 10969618408207261616820505)
          ·
            refine ⟨8227213806155446212615379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10969618408207261616820505 8227213806155446212615379)
            ·
              refine ⟨12340820709233169318923069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227213806155446212615379 12340820709233169318923069)
              ·
                refine ⟨4627807765962438494596151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12340820709233169318923069 4627807765962438494596151)
                ·
                  refine ⟨6941711648943657741894227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627807765962438494596151 6941711648943657741894227)
                  ·
                    refine ⟨10412567473415486612841341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6941711648943657741894227 10412567473415486612841341)
                    ·
                      refine ⟨3904712802530807479815503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412567473415486612841341 3904712802530807479815503)
                      ·
                        rfl

theorem cell23_7604401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_7604401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604401 prefixEnd_7604401 := by exact prefixLift 7604401
  have htrace : WordTrace (prefixWord ++ tailWord_7604401) baseStart_7604401 baseEnd_7604401 := by
    simpa [prefixWord, tailWord_7604401, baseEnd_7604401] using wordTrace_append hprefix tailTrace_7604401
  have hstable : (prefixWord ++ tailWord_7604401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604401).length < 2 ^ (prefixWord ++ tailWord_7604401).sum := by decide
  have hdescent : baseEnd_7604401 < baseStart_7604401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604410 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3]
def baseStart_7604410 : Nat := 118140960795 + 7604410 * 2 ^ 59
def prefixEnd_7604410 : Nat := 4983230072969 + 3 ^ 40 * 7604410 * 2
def baseEnd_7604410 : Nat := 3904717423856697944602961

theorem tailTrace_7604410 : CollatzResearch.WordTrace tailWord_7604410 prefixEnd_7604410 3904717423856697944602961 := by
  unfold tailWord_7604410
  simp only [CollatzResearch.WordTrace]
  refine ⟨69338904595132193668986671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184903745587019183117297789 69338904595132193668986671)
  ·
    refine ⟨104008356892698290503480007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69338904595132193668986671 104008356892698290503480007)
    ·
      refine ⟨156012535339047435755220011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104008356892698290503480007 156012535339047435755220011)
      ·
        refine ⟨234018803008571153632830017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156012535339047435755220011 234018803008571153632830017)
        ·
          refine ⟨175514102256428365224622513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234018803008571153632830017 175514102256428365224622513)
          ·
            refine ⟨131635576692321273918466885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175514102256428365224622513 131635576692321273918466885)
            ·
              refine ⟨24681670629810238859712541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131635576692321273918466885 24681670629810238859712541)
              ·
                refine ⟨9255626486178839572392203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24681670629810238859712541 9255626486178839572392203)
                ·
                  refine ⟨13883439729268259358588305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9255626486178839572392203 13883439729268259358588305)
                  ·
                    refine ⟨10412579796951194518941229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13883439729268259358588305 10412579796951194518941229)
                    ·
                      refine ⟨3904717423856697944602961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412579796951194518941229 3904717423856697944602961)
                      ·
                        rfl

theorem cell23_7604410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_7604410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604410 prefixEnd_7604410 := by exact prefixLift 7604410
  have htrace : WordTrace (prefixWord ++ tailWord_7604410) baseStart_7604410 baseEnd_7604410 := by
    simpa [prefixWord, tailWord_7604410, baseEnd_7604410] using wordTrace_append hprefix tailTrace_7604410
  have hstable : (prefixWord ++ tailWord_7604410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604410).length < 2 ^ (prefixWord ++ tailWord_7604410).sum := by decide
  have hdescent : baseEnd_7604410 < baseStart_7604410 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604434 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7604434 : Nat := 118140960795 + 7604434 * 2 ^ 59
def prefixEnd_7604434 : Nat := 4983230072969 + 3 ^ 40 * 7604434 * 2
def baseEnd_7604434 : Nat := 1301576582464135283567617

theorem tailTrace_7604434 : CollatzResearch.WordTrace tailWord_7604434 prefixEnd_7604434 1301576582464135283567617 := by
  unfold tailWord_7604434
  simp only [CollatzResearch.WordTrace]
  refine ⟨69339123433110456693705089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184904329154961217849880237 69339123433110456693705089)
  ·
    refine ⟨52004342574832842520278817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69339123433110456693705089 52004342574832842520278817)
    ·
      refine ⟨39003256931124631890209113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52004342574832842520278817 39003256931124631890209113)
      ·
        refine ⟨29252442698343473917656835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39003256931124631890209113 29252442698343473917656835)
        ·
          refine ⟨43878664047515210876485253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29252442698343473917656835 43878664047515210876485253)
          ·
            refine ⟨8227249508909102039340985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43878664047515210876485253 8227249508909102039340985)
            ·
              refine ⟨6170437131681826529505739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8227249508909102039340985 6170437131681826529505739)
              ·
                refine ⟨9255655697522739794258609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170437131681826529505739 9255655697522739794258609)
                ·
                  refine ⟨6941741773142054845693957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9255655697522739794258609 6941741773142054845693957)
                  ·
                    refine ⟨1301576582464135283567617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941741773142054845693957 1301576582464135283567617)
                    ·
                      rfl

theorem cell23_7604434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7604434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604434 prefixEnd_7604434 := by exact prefixLift 7604434
  have htrace : WordTrace (prefixWord ++ tailWord_7604434) baseStart_7604434 baseEnd_7604434 := by
    simpa [prefixWord, tailWord_7604434, baseEnd_7604434] using wordTrace_append hprefix tailTrace_7604434
  have hstable : (prefixWord ++ tailWord_7604434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604434).length < 2 ^ (prefixWord ++ tailWord_7604434).sum := by decide
  have hdescent : baseEnd_7604434 < baseStart_7604434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604444 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_7604444 : Nat := 118140960795 + 7604444 * 2 ^ 59
def prefixEnd_7604444 : Nat := 4983230072969 + 3 ^ 40 * 7604444 * 2
def baseEnd_7604444 : Nat := 3904734882198950811577805

theorem tailTrace_7604444 : CollatzResearch.WordTrace tailWord_7604444 prefixEnd_7604444 3904734882198950811577805 := by
  unfold tailWord_7604444
  simp only [CollatzResearch.WordTrace]
  refine ⟨138678429231202799241342193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184904572308270398988456257 138678429231202799241342193)
  ·
    refine ⟨104008821923402099431006645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138678429231202799241342193 104008821923402099431006645)
    ·
      refine ⟨9750827055318946821656873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104008821923402099431006645 9750827055318946821656873)
      ·
        refine ⟨7313120291489210116242655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9750827055318946821656873 7313120291489210116242655)
        ·
          refine ⟨10969680437233815174363983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7313120291489210116242655 10969680437233815174363983)
          ·
            refine ⟨16454520655850722761545975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10969680437233815174363983 16454520655850722761545975)
            ·
              refine ⟨24681780983776084142318963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16454520655850722761545975 24681780983776084142318963)
              ·
                refine ⟨37022671475664126213478445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24681780983776084142318963 37022671475664126213478445)
                ·
                  refine ⟨13883501803374047330054417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37022671475664126213478445 13883501803374047330054417)
                  ·
                    refine ⟨10412626352530535497540813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13883501803374047330054417 10412626352530535497540813)
                    ·
                      refine ⟨3904734882198950811577805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412626352530535497540813 3904734882198950811577805)
                      ·
                        rfl

theorem cell23_7604444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_7604444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604444 prefixEnd_7604444 := by exact prefixLift 7604444
  have htrace : WordTrace (prefixWord ++ tailWord_7604444) baseStart_7604444 baseEnd_7604444 := by
    simpa [prefixWord, tailWord_7604444, baseEnd_7604444] using wordTrace_append hprefix tailTrace_7604444
  have hstable : (prefixWord ++ tailWord_7604444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604444).length < 2 ^ (prefixWord ++ tailWord_7604444).sum := by decide
  have hdescent : baseEnd_7604444 < baseStart_7604444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604483 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3]
def baseStart_7604483 : Nat := 118140960795 + 7604483 * 2 ^ 59
def prefixEnd_7604483 : Nat := 4983230072969 + 3 ^ 40 * 7604483 * 2
def baseEnd_7604483 : Nat := 3904754907944476158990125

theorem tailTrace_7604483 : CollatzResearch.WordTrace tailWord_7604483 prefixEnd_7604483 3904754907944476158990125 := by
  unfold tailWord_7604483
  simp only [CollatzResearch.WordTrace]
  refine ⟨277358280909264308143354103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184905520606176205428902735 277358280909264308143354103)
  ·
    refine ⟨416037421363896462215031155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277358280909264308143354103 416037421363896462215031155)
    ·
      refine ⟨624056132045844693322546733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416037421363896462215031155 624056132045844693322546733)
      ·
        refine ⟨234021049517191759995955025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624056132045844693322546733 234021049517191759995955025)
        ·
          refine ⟨175515787137893819996966269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234021049517191759995955025 175515787137893819996966269)
          ·
            refine ⟨65818420176710182498862351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175515787137893819996966269 65818420176710182498862351)
            ·
              refine ⟨98727630265065273748293527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65818420176710182498862351 98727630265065273748293527)
              ·
                refine ⟨148091445397597910622440291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98727630265065273748293527 148091445397597910622440291)
                ·
                  refine ⟨222137168096396865933660437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148091445397597910622440291 222137168096396865933660437)
                  ·
                    refine ⟨10412679754518603090640333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 222137168096396865933660437 10412679754518603090640333)
                    ·
                      refine ⟨3904754907944476158990125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10412679754518603090640333 3904754907944476158990125)
                      ·
                        rfl

theorem cell23_7604483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_7604483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604483 prefixEnd_7604483 := by exact prefixLift 7604483
  have htrace : WordTrace (prefixWord ++ tailWord_7604483) baseStart_7604483 baseEnd_7604483 := by
    simpa [prefixWord, tailWord_7604483, baseEnd_7604483] using wordTrace_append hprefix tailTrace_7604483
  have hstable : (prefixWord ++ tailWord_7604483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604483).length < 2 ^ (prefixWord ++ tailWord_7604483).sum := by decide
  have hdescent : baseEnd_7604483 < baseStart_7604483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604497 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 4, 2]
def baseStart_7604497 : Nat := 118140960795 + 7604497 * 2 ^ 59
def prefixEnd_7604497 : Nat := 4983230072969 + 3 ^ 40 * 7604497 * 2
def baseEnd_7604497 : Nat := 3904762096673639104215061

theorem tailTrace_7604497 : CollatzResearch.WordTrace tailWord_7604497 prefixEnd_7604497 3904762096673639104215061 := by
  unfold tailWord_7604497
  simp only [CollatzResearch.WordTrace]
  refine ⟨277358791531213588534363745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184905861020809059022909163 277358791531213588534363745)
  ·
    refine ⟨208019093648410191400772809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277358791531213588534363745 208019093648410191400772809)
    ·
      refine ⟨156014320236307643550579607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208019093648410191400772809 156014320236307643550579607)
      ·
        refine ⟨234021480354461465325869411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156014320236307643550579607 234021480354461465325869411)
        ·
          refine ⟨351032220531692197988804117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234021480354461465325869411 351032220531692197988804117)
          ·
            refine ⟨16454635337423071780725193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351032220531692197988804117 16454635337423071780725193)
            ·
              refine ⟨12340976503067303835543895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16454635337423071780725193 12340976503067303835543895)
              ·
                refine ⟨18511464754600955753315843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12340976503067303835543895 18511464754600955753315843)
                ·
                  refine ⟨27767197131901433629973765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18511464754600955753315843 27767197131901433629973765)
                  ·
                    refine ⟨5206349462231518805620081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27767197131901433629973765 5206349462231518805620081)
                    ·
                      refine ⟨3904762096673639104215061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206349462231518805620081 3904762096673639104215061)
                      ·
                        rfl

theorem cell23_7604497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4, 2].length) (baseStart_7604497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604497 prefixEnd_7604497 := by exact prefixLift 7604497
  have htrace : WordTrace (prefixWord ++ tailWord_7604497) baseStart_7604497 baseEnd_7604497 := by
    simpa [prefixWord, tailWord_7604497, baseEnd_7604497] using wordTrace_append hprefix tailTrace_7604497
  have hstable : (prefixWord ++ tailWord_7604497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604497).length < 2 ^ (prefixWord ++ tailWord_7604497).sum := by decide
  have hdescent : baseEnd_7604497 < baseStart_7604497 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604503 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 9]
def baseStart_7604503 : Nat := 118140960795 + 7604503 * 2 ^ 59
def prefixEnd_7604503 : Nat := 4983230072969 + 3 ^ 40 * 7604503 * 2
def baseEnd_7604503 : Nat := 433862797506396231193337

theorem tailTrace_7604503 : CollatzResearch.WordTrace tailWord_7604503 prefixEnd_7604503 433862797506396231193337 := by
  unfold tailWord_7604503
  simp only [CollatzResearch.WordTrace]
  refine ⟨277359010369191851559082163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184906006912794567706054775 277359010369191851559082163)
  ·
    refine ⟨416038515553787777338623245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277359010369191851559082163 416038515553787777338623245)
    ·
      refine ⟨156014443332670416501983717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416038515553787777338623245 156014443332670416501983717)
      ·
        refine ⟨29252708124875703094121947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156014443332670416501983717 29252708124875703094121947)
        ·
          refine ⟨43879062187313554641182921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29252708124875703094121947 43879062187313554641182921)
          ·
            refine ⟨32909296640485165980887191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43879062187313554641182921 32909296640485165980887191)
            ·
              refine ⟨49363944960727748971330787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32909296640485165980887191 49363944960727748971330787)
              ·
                refine ⟨74045917441091623456996181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49363944960727748971330787 74045917441091623456996181)
                ·
                  refine ⟨433862797506396231193337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74045917441091623456996181 433862797506396231193337)
                  ·
                    rfl

theorem cell23_7604503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 9].length) (baseStart_7604503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604503 prefixEnd_7604503 := by exact prefixLift 7604503
  have htrace : WordTrace (prefixWord ++ tailWord_7604503) baseStart_7604503 baseEnd_7604503 := by
    simpa [prefixWord, tailWord_7604503, baseEnd_7604503] using wordTrace_append hprefix tailTrace_7604503
  have hstable : (prefixWord ++ tailWord_7604503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604503).length < 2 ^ (prefixWord ++ tailWord_7604503).sum := by decide
  have hdescent : baseEnd_7604503 < baseStart_7604503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604537 : List Nat := [1, 2, 1, 6, 1, 1, 2, 4, 5]
def baseStart_7604537 : Nat := 118140960795 + 7604537 * 2 ^ 59
def prefixEnd_7604537 : Nat := 4983230072969 + 3 ^ 40 * 7604537 * 2
def baseEnd_7604537 : Nat := 433864737322202105301653

theorem tailTrace_7604537 : CollatzResearch.WordTrace tailWord_7604537 prefixEnd_7604537 433864737322202105301653 := by
  unfold tailWord_7604537
  simp only [CollatzResearch.WordTrace]
  refine ⟨277360250451068675365819865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184906833634045783577213243 277360250451068675365819865)
  ·
    refine ⟨208020187838301506524364899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277360250451068675365819865 208020187838301506524364899)
    ·
      refine ⟨312030281757452259786547349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208020187838301506524364899 312030281757452259786547349)
      ·
        refine ⟨14626419457380574677494407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 312030281757452259786547349 14626419457380574677494407)
        ·
          refine ⟨21939629186070862016241611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626419457380574677494407 21939629186070862016241611)
          ·
            refine ⟨32909443779106293024362417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939629186070862016241611 32909443779106293024362417)
            ·
              refine ⟨24682082834329719768271813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32909443779106293024362417 24682082834329719768271813)
              ·
                refine ⟨4627890531436822456550965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24682082834329719768271813 4627890531436822456550965)
                ·
                  refine ⟨433864737322202105301653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4627890531436822456550965 433864737322202105301653)
                  ·
                    rfl

theorem cell23_7604537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 4, 5].length) (baseStart_7604537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604537 prefixEnd_7604537 := by exact prefixLift 7604537
  have htrace : WordTrace (prefixWord ++ tailWord_7604537) baseStart_7604537 baseEnd_7604537 := by
    simpa [prefixWord, tailWord_7604537, baseEnd_7604537] using wordTrace_append hprefix tailTrace_7604537
  have hstable : (prefixWord ++ tailWord_7604537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604537).length < 2 ^ (prefixWord ++ tailWord_7604537).sum := by decide
  have hdescent : baseEnd_7604537 < baseStart_7604537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604543 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_7604543 : Nat := 118140960795 + 7604543 * 2 ^ 59
def prefixEnd_7604543 : Nat := 4983230072969 + 3 ^ 40 * 7604543 * 2
def baseEnd_7604543 : Nat := 3904785716783745924239849

theorem tailTrace_7604543 : CollatzResearch.WordTrace tailWord_7604543 prefixEnd_7604543 3904785716783745924239849 := by
  unfold tailWord_7604543
  simp only [CollatzResearch.WordTrace]
  refine ⟨277360469289046938390538283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184906979526031292260358855 277360469289046938390538283)
  ·
    refine ⟨416040703933570407585807425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277360469289046938390538283 416040703933570407585807425)
    ·
      refine ⟨312030527950177805689355569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416040703933570407585807425 312030527950177805689355569)
      ·
        refine ⟨234022895962633354267016677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312030527950177805689355569 234022895962633354267016677)
        ·
          refine ⟨43879292992993753925065627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234022895962633354267016677 43879292992993753925065627)
          ·
            refine ⟨65818939489490630887598441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43879292992993753925065627 65818939489490630887598441)
            ·
              refine ⟨49364204617117973165698831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65818939489490630887598441 49364204617117973165698831)
              ·
                refine ⟨74046306925676959748548247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49364204617117973165698831 74046306925676959748548247)
                ·
                  refine ⟨111069460388515439622822371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74046306925676959748548247 111069460388515439622822371)
                  ·
                    refine ⟨166604190582773159434233557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111069460388515439622822371 166604190582773159434233557)
                    ·
                      refine ⟨3904785716783745924239849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166604190582773159434233557 3904785716783745924239849)
                      ·
                        rfl

theorem cell23_7604543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_7604543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604543 prefixEnd_7604543 := by exact prefixLift 7604543
  have htrace : WordTrace (prefixWord ++ tailWord_7604543) baseStart_7604543 baseEnd_7604543 := by
    simpa [prefixWord, tailWord_7604543, baseEnd_7604543] using wordTrace_append hprefix tailTrace_7604543
  have hstable : (prefixWord ++ tailWord_7604543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604543).length < 2 ^ (prefixWord ++ tailWord_7604543).sum := by decide
  have hdescent : baseEnd_7604543 < baseStart_7604543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604548 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_7604548 : Nat := 118140960795 + 7604548 * 2 ^ 59
def prefixEnd_7604548 : Nat := 4983230072969 + 3 ^ 40 * 7604548 * 2
def baseEnd_7604548 : Nat := 3904788284187018404677327

theorem tailTrace_7604548 : CollatzResearch.WordTrace tailWord_7604548 prefixEnd_7604548 3904788284187018404677327 := by
  unfold tailWord_7604548
  simp only [CollatzResearch.WordTrace]
  refine ⟨138680325827014412122235149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184907101102685882829646865 138680325827014412122235149)
  ·
    refine ⟨52005122185130404545838181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138680325827014412122235149 52005122185130404545838181)
    ·
      refine ⟨9750960409711950852344659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52005122185130404545838181 9750960409711950852344659)
      ·
        refine ⟨14626440614567926278516989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9750960409711950852344659 14626440614567926278516989)
        ·
          refine ⟨5484915230462972354443871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14626440614567926278516989 5484915230462972354443871)
          ·
            refine ⟨8227372845694458531665807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5484915230462972354443871 8227372845694458531665807)
            ·
              refine ⟨12341059268541687797498711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227372845694458531665807 12341059268541687797498711)
              ·
                refine ⟨18511588902812531696248067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341059268541687797498711 18511588902812531696248067)
                ·
                  refine ⟨27767383354218797544372101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18511588902812531696248067 27767383354218797544372101)
                  ·
                    refine ⟨5206384378916024539569769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27767383354218797544372101 5206384378916024539569769)
                    ·
                      refine ⟨3904788284187018404677327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206384378916024539569769 3904788284187018404677327)
                      ·
                        rfl

theorem cell23_7604548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_7604548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604548 prefixEnd_7604548 := by exact prefixLift 7604548
  have htrace : WordTrace (prefixWord ++ tailWord_7604548) baseStart_7604548 baseEnd_7604548 := by
    simpa [prefixWord, tailWord_7604548, baseEnd_7604548] using wordTrace_append hprefix tailTrace_7604548
  have hstable : (prefixWord ++ tailWord_7604548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604548).length < 2 ^ (prefixWord ++ tailWord_7604548).sum := by decide
  have hdescent : baseEnd_7604548 < baseStart_7604548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604570 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4]
def baseStart_7604570 : Nat := 118140960795 + 7604570 * 2 ^ 59
def prefixEnd_7604570 : Nat := 4983230072969 + 3 ^ 40 * 7604570 * 2
def baseEnd_7604570 : Nat := 3904799580761417318602225

theorem tailTrace_7604570 : CollatzResearch.WordTrace tailWord_7604570 prefixEnd_7604570 3904799580761417318602225 := by
  unfold tailWord_7604570
  simp only [CollatzResearch.WordTrace]
  refine ⟨69340363514987280500442791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184907636039966081334514109 69340363514987280500442791)
  ·
    refine ⟨104010545272480920750664187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69340363514987280500442791 104010545272480920750664187)
    ·
      refine ⟨156015817908721381125996281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104010545272480920750664187 156015817908721381125996281)
      ·
        refine ⟨117011863431541035844497211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156015817908721381125996281 117011863431541035844497211)
        ·
          refine ⟨175517795147311553766745817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117011863431541035844497211 175517795147311553766745817)
          ·
            refine ⟨131638346360483665325059363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175517795147311553766745817 131638346360483665325059363)
            ·
              refine ⟨197457519540725497987589045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131638346360483665325059363 197457519540725497987589045)
              ·
                refine ⟨18511642456943015436336473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197457519540725497987589045 18511642456943015436336473)
                ·
                  refine ⟨13883731842707261577252355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18511642456943015436336473 13883731842707261577252355)
                  ·
                    refine ⟨20825597764060892365878533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13883731842707261577252355 20825597764060892365878533)
                    ·
                      refine ⟨3904799580761417318602225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20825597764060892365878533 3904799580761417318602225)
                      ·
                        rfl

theorem cell23_7604570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_7604570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604570 prefixEnd_7604570 := by exact prefixLift 7604570
  have htrace : WordTrace (prefixWord ++ tailWord_7604570) baseStart_7604570 baseEnd_7604570 := by
    simpa [prefixWord, tailWord_7604570, baseEnd_7604570] using wordTrace_append hprefix tailTrace_7604570
  have hstable : (prefixWord ++ tailWord_7604570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604570).length < 2 ^ (prefixWord ++ tailWord_7604570).sum := by decide
  have hdescent : baseEnd_7604570 < baseStart_7604570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604648 : List Nat := [2, 1, 6, 1, 1, 1, 4, 2, 1, 4]
def baseStart_7604648 : Nat := 118140960795 + 7604648 * 2 ^ 59
def prefixEnd_7604648 : Nat := 4983230072969 + 3 ^ 40 * 7604648 * 2
def baseEnd_7604648 : Nat := 1301613210750822671142289

theorem tailTrace_7604648 : CollatzResearch.WordTrace tailWord_7604648 prefixEnd_7604648 1301613210750822671142289 := by
  unfold tailWord_7604648
  simp only [CollatzResearch.WordTrace]
  refine ⟨138682149476833270661555299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184909532635777694215407065 138682149476833270661555299)
  ·
    refine ⟨208023224215249905992332949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138682149476833270661555299 208023224215249905992332949)
    ·
      refine ⟨9751088635089839343390607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208023224215249905992332949 9751088635089839343390607)
      ·
        refine ⟨14626632952634759015085911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751088635089839343390607 14626632952634759015085911)
        ·
          refine ⟨21939949428952138522628867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14626632952634759015085911 21939949428952138522628867)
          ·
            refine ⟨32909924143428207783943301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21939949428952138522628867 32909924143428207783943301)
            ·
              refine ⟨6170610776892788959489369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32909924143428207783943301 6170610776892788959489369)
              ·
                refine ⟨4627958082669591719617027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6170610776892788959489369 4627958082669591719617027)
                ·
                  refine ⟨6941937124004387579425541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4627958082669591719617027 6941937124004387579425541)
                  ·
                    refine ⟨1301613210750822671142289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6941937124004387579425541 1301613210750822671142289)
                    ·
                      rfl

theorem cell23_7604648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_7604648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604648 prefixEnd_7604648 := by exact prefixLift 7604648
  have htrace : WordTrace (prefixWord ++ tailWord_7604648) baseStart_7604648 baseEnd_7604648 := by
    simpa [prefixWord, tailWord_7604648, baseEnd_7604648] using wordTrace_append hprefix tailTrace_7604648
  have hstable : (prefixWord ++ tailWord_7604648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604648).length < 2 ^ (prefixWord ++ tailWord_7604648).sum := by decide
  have hdescent : baseEnd_7604648 < baseStart_7604648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604711 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_7604711 : Nat := 118140960795 + 7604711 * 2 ^ 59
def prefixEnd_7604711 : Nat := 4983230072969 + 3 ^ 40 * 7604711 * 2
def baseEnd_7604711 : Nat := 3904871981533701266939077

theorem tailTrace_7604711 : CollatzResearch.WordTrace tailWord_7604711 prefixEnd_7604711 3904871981533701266939077 := by
  unfold tailWord_7604711
  simp only [CollatzResearch.WordTrace]
  refine ⟨277366596752438303082653987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184911064501625535388435991 277366596752438303082653987)
  ·
    refine ⟨416049895128657454623980981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277366596752438303082653987 416049895128657454623980981)
    ·
      refine ⟨39004677668311636370998217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416049895128657454623980981 39004677668311636370998217)
      ·
        refine ⟨29253508251233727278248663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39004677668311636370998217 29253508251233727278248663)
        ·
          refine ⟨43880262376850590917372995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253508251233727278248663 43880262376850590917372995)
          ·
            refine ⟨65820393565275886376059493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43880262376850590917372995 65820393565275886376059493)
            ·
              refine ⟨12341323793489228695511155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65820393565275886376059493 12341323793489228695511155)
              ·
                refine ⟨18511985690233843043266733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341323793489228695511155 18511985690233843043266733)
                ·
                  refine ⟨6941994633837691141225025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18511985690233843043266733 6941994633837691141225025)
                  ·
                    refine ⟨5206495975378268355918769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6941994633837691141225025 5206495975378268355918769)
                    ·
                      refine ⟨3904871981533701266939077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206495975378268355918769 3904871981533701266939077)
                      ·
                        rfl

theorem cell23_7604711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_7604711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604711 prefixEnd_7604711 := by exact prefixLift 7604711
  have htrace : WordTrace (prefixWord ++ tailWord_7604711) baseStart_7604711 baseEnd_7604711 := by
    simpa [prefixWord, tailWord_7604711, baseEnd_7604711] using wordTrace_append hprefix tailTrace_7604711
  have hstable : (prefixWord ++ tailWord_7604711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604711).length < 2 ^ (prefixWord ++ tailWord_7604711).sum := by decide
  have hdescent : baseEnd_7604711 < baseStart_7604711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604778 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_7604778 : Nat := 118140960795 + 7604778 * 2 ^ 59
def prefixEnd_7604778 : Nat := 4983230072969 + 3 ^ 40 * 7604778 * 2
def baseEnd_7604778 : Nat := 3904906384737552504801269

theorem tailTrace_7604778 : CollatzResearch.WordTrace tailWord_7604778 prefixEnd_7604778 3904906384737552504801269 := by
  unfold tailWord_7604778
  simp only [CollatzResearch.WordTrace]
  refine ⟨69342260110798893381335747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184912693628797049016895325 69342260110798893381335747)
  ·
    refine ⟨104013390166198340072003621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69342260110798893381335747 104013390166198340072003621)
    ·
      refine ⟨19502510656162188763500679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104013390166198340072003621 19502510656162188763500679)
      ·
        refine ⟨29253765984243283145251019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19502510656162188763500679 29253765984243283145251019)
        ·
          refine ⟨43880648976364924717876529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253765984243283145251019 43880648976364924717876529)
          ·
            refine ⟨32910486732273693538407397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43880648976364924717876529 32910486732273693538407397)
            ·
              refine ⟨6170716262301317538451387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32910486732273693538407397 6170716262301317538451387)
              ·
                refine ⟨9256074393451976307677081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170716262301317538451387 9256074393451976307677081)
                ·
                  refine ⟨6942055795088982230757811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256074393451976307677081 6942055795088982230757811)
                  ·
                    refine ⟨10413083692633473346136717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942055795088982230757811 10413083692633473346136717)
                    ·
                      refine ⟨3904906384737552504801269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10413083692633473346136717 3904906384737552504801269)
                      ·
                        rfl

theorem cell23_7604778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_7604778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604778 prefixEnd_7604778 := by exact prefixLift 7604778
  have htrace : WordTrace (prefixWord ++ tailWord_7604778) baseStart_7604778 baseEnd_7604778 := by
    simpa [prefixWord, tailWord_7604778, baseEnd_7604778] using wordTrace_append hprefix tailTrace_7604778
  have hstable : (prefixWord ++ tailWord_7604778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604778).length < 2 ^ (prefixWord ++ tailWord_7604778).sum := by decide
  have hdescent : baseEnd_7604778 < baseStart_7604778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604780 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6]
def baseStart_7604780 : Nat := 118140960795 + 7604780 * 2 ^ 59
def prefixEnd_7604780 : Nat := 4983230072969 + 3 ^ 40 * 7604780 * 2
def baseEnd_7604780 : Nat := 3904907411698861496976259

theorem tailTrace_7604780 : CollatzResearch.WordTrace tailWord_7604780 prefixEnd_7604780 3904907411698861496976259 := by
  unfold tailWord_7604780
  simp only [CollatzResearch.WordTrace]
  refine ⟨138684556694594163933457897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184912742259458885244610529 138684556694594163933457897)
  ·
    refine ⟨104013417520945622950093423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138684556694594163933457897 104013417520945622950093423)
    ·
      refine ⟨156020126281418434425140135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104013417520945622950093423 156020126281418434425140135)
      ·
        refine ⟨234030189422127651637710203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156020126281418434425140135 234030189422127651637710203)
        ·
          refine ⟨351045284133191477456565305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234030189422127651637710203 351045284133191477456565305)
          ·
            refine ⟨263283963099893608092423979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351045284133191477456565305 263283963099893608092423979)
            ·
              refine ⟨394925944649840412138635969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263283963099893608092423979 394925944649840412138635969)
              ·
                refine ⟨296194458487380309103976977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 394925944649840412138635969 296194458487380309103976977)
                ·
                  refine ⟨222145843865535231827982733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 296194458487380309103976977 222145843865535231827982733)
                  ·
                    refine ⟨83304691449575711935493525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 222145843865535231827982733 83304691449575711935493525)
                    ·
                      refine ⟨3904907411698861496976259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83304691449575711935493525 3904907411698861496976259)
                      ·
                        rfl

theorem cell23_7604780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_7604780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604780 prefixEnd_7604780 := by exact prefixLift 7604780
  have htrace : WordTrace (prefixWord ++ tailWord_7604780) baseStart_7604780 baseEnd_7604780 := by
    simpa [prefixWord, tailWord_7604780, baseEnd_7604780] using wordTrace_append hprefix tailTrace_7604780
  have hstable : (prefixWord ++ tailWord_7604780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604780).length < 2 ^ (prefixWord ++ tailWord_7604780).sum := by decide
  have hdescent : baseEnd_7604780 < baseStart_7604780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604801 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_7604801 : Nat := 118140960795 + 7604801 * 2 ^ 59
def prefixEnd_7604801 : Nat := 4983230072969 + 3 ^ 40 * 7604801 * 2
def baseEnd_7604801 : Nat := 3904918194792605914813663

theorem tailTrace_7604801 : CollatzResearch.WordTrace tailWord_7604801 prefixEnd_7604801 3904918194792605914813663 := by
  unfold tailWord_7604801
  simp only [CollatzResearch.WordTrace]
  refine ⟨277369879322112248453430257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184913252881408165635620171 277369879322112248453430257)
  ·
    refine ⟨208027409491584186340072693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277369879322112248453430257 208027409491584186340072693)
    ·
      refine ⟨19502569639836017469381815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208027409491584186340072693 19502569639836017469381815)
      ·
        refine ⟨29253854459754026204072723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19502569639836017469381815 29253854459754026204072723)
        ·
          refine ⟨43880781689631039306109085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29253854459754026204072723 43880781689631039306109085)
          ·
            refine ⟨16455293133611639739790907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43880781689631039306109085 16455293133611639739790907)
            ·
              refine ⟨24682939700417459609686361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16455293133611639739790907 24682939700417459609686361)
              ·
                refine ⟨18512204775313094707264771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24682939700417459609686361 18512204775313094707264771)
                ·
                  refine ⟨27768307162969642060897157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18512204775313094707264771 27768307162969642060897157)
                  ·
                    refine ⟨5206557593056807886418217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27768307162969642060897157 5206557593056807886418217)
                    ·
                      refine ⟨3904918194792605914813663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206557593056807886418217 3904918194792605914813663)
                      ·
                        rfl

theorem cell23_7604801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_7604801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604801 prefixEnd_7604801 := by exact prefixLift 7604801
  have htrace : WordTrace (prefixWord ++ tailWord_7604801) baseStart_7604801 baseEnd_7604801 := by
    simpa [prefixWord, tailWord_7604801, baseEnd_7604801] using wordTrace_append hprefix tailTrace_7604801
  have hstable : (prefixWord ++ tailWord_7604801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604801).length < 2 ^ (prefixWord ++ tailWord_7604801).sum := by decide
  have hdescent : baseEnd_7604801 < baseStart_7604801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604818 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_7604818 : Nat := 118140960795 + 7604818 * 2 ^ 59
def prefixEnd_7604818 : Nat := 4983230072969 + 3 ^ 40 * 7604818 * 2
def baseEnd_7604818 : Nat := 3904926923963732348301085

theorem tailTrace_7604818 : CollatzResearch.WordTrace tailWord_7604818 prefixEnd_7604818 3904926923963732348301085 := by
  unfold tailWord_7604818
  simp only [CollatzResearch.WordTrace]
  refine ⟨69342624840762665089199777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184913666242033773571199405 69342624840762665089199777)
  ·
    refine ⟨52006968630571998816899833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69342624840762665089199777 52006968630571998816899833)
    ·
      refine ⟨39005226472928999112674875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52006968630571998816899833 39005226472928999112674875)
      ·
        refine ⟨58507839709393498669012313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39005226472928999112674875 58507839709393498669012313)
        ·
          refine ⟨43880879782045124001759235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58507839709393498669012313 43880879782045124001759235)
          ·
            refine ⟨65821319673067686002638853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43880879782045124001759235 65821319673067686002638853)
            ·
              refine ⟨12341497438700191125494785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65821319673067686002638853 12341497438700191125494785)
              ·
                refine ⟨9256123079025143344121089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12341497438700191125494785 9256123079025143344121089)
                ·
                  refine ⟨6942092309268857508090817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256123079025143344121089 6942092309268857508090817)
                  ·
                    refine ⟨5206569231951643131068113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942092309268857508090817 5206569231951643131068113)
                    ·
                      refine ⟨3904926923963732348301085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206569231951643131068113 3904926923963732348301085)
                      ·
                        rfl

theorem cell23_7604818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_7604818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604818 prefixEnd_7604818 := by exact prefixLift 7604818
  have htrace : WordTrace (prefixWord ++ tailWord_7604818) baseStart_7604818 baseEnd_7604818 := by
    simpa [prefixWord, tailWord_7604818, baseEnd_7604818] using wordTrace_append hprefix tailTrace_7604818
  have hstable : (prefixWord ++ tailWord_7604818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604818).length < 2 ^ (prefixWord ++ tailWord_7604818).sum := by decide
  have hdescent : baseEnd_7604818 < baseStart_7604818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604887 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7604887 : Nat := 118140960795 + 7604887 * 2 ^ 59
def prefixEnd_7604887 : Nat := 4983230072969 + 3 ^ 40 * 7604887 * 2
def baseEnd_7604887 : Nat := 3904962354128892578338267

theorem tailTrace_7604887 : CollatzResearch.WordTrace tailWord_7604887 prefixEnd_7604887 3904962354128892578338267 := by
  unfold tailWord_7604887
  simp only [CollatzResearch.WordTrace]
  refine ⟨277373015999800685141060915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184915343999867123427373943 277373015999800685141060915)
  ·
    refine ⟨416059523999701027711591373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277373015999800685141060915 416059523999701027711591373)
    ·
      refine ⟨156022321499887885391846765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416059523999701027711591373 156022321499887885391846765)
      ·
        refine ⟨58508370562457957021942537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156022321499887885391846765 58508370562457957021942537)
        ·
          refine ⟨43881277921843467766456903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58508370562457957021942537 43881277921843467766456903)
          ·
            refine ⟨65821916882765201649685355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43881277921843467766456903 65821916882765201649685355)
            ·
              refine ⟨98732875324147802474528033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65821916882765201649685355 98732875324147802474528033)
              ·
                refine ⟨74049656493110851855896025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98732875324147802474528033 74049656493110851855896025)
                ·
                  refine ⟨55537242369833138891922019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74049656493110851855896025 55537242369833138891922019)
                  ·
                    refine ⟨83305863554749708337883029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55537242369833138891922019 83305863554749708337883029)
                    ·
                      refine ⟨3904962354128892578338267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83305863554749708337883029 3904962354128892578338267)
                      ·
                        rfl

theorem cell23_7604887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7604887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604887 prefixEnd_7604887 := by exact prefixLift 7604887
  have htrace : WordTrace (prefixWord ++ tailWord_7604887) baseStart_7604887 baseEnd_7604887 := by
    simpa [prefixWord, tailWord_7604887, baseEnd_7604887] using wordTrace_append hprefix tailTrace_7604887
  have hstable : (prefixWord ++ tailWord_7604887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604887).length < 2 ^ (prefixWord ++ tailWord_7604887).sum := by decide
  have hdescent : baseEnd_7604887 < baseStart_7604887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604961 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 1, 5]
def baseStart_7604961 : Nat := 118140960795 + 7604961 * 2 ^ 59
def prefixEnd_7604961 : Nat := 4983230072969 + 3 ^ 40 * 7604961 * 2
def baseEnd_7604961 : Nat := 1301666783899108429604309

theorem tailTrace_7604961 : CollatzResearch.WordTrace tailWord_7604961 prefixEnd_7604961 1301666783899108429604309 := by
  unfold tailWord_7604961
  simp only [CollatzResearch.WordTrace]
  refine ⟨277375715001532595779254737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184917143334355063852836491 277375715001532595779254737)
  ·
    refine ⟨208031786251149446834441053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277375715001532595779254737 208031786251149446834441053)
    ·
      refine ⟨78011919844181042562915395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208031786251149446834441053 78011919844181042562915395)
      ·
        refine ⟨117017879766271563844373093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78011919844181042562915395 117017879766271563844373093)
        ·
          refine ⟨21940852456175918220819955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117017879766271563844373093 21940852456175918220819955)
          ·
            refine ⟨32911278684263877331229933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21940852456175918220819955 32911278684263877331229933)
            ·
              refine ⟨12341729506598953999211225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32911278684263877331229933 12341729506598953999211225)
              ·
                refine ⟨9256297129949215499408419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12341729506598953999211225 9256297129949215499408419)
                ·
                  refine ⟨13884445694923823249112629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256297129949215499408419 13884445694923823249112629)
                  ·
                    refine ⟨1301666783899108429604309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13884445694923823249112629 1301666783899108429604309)
                    ·
                      rfl

theorem cell23_7604961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_7604961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604961 prefixEnd_7604961 := by exact prefixLift 7604961
  have htrace : WordTrace (prefixWord ++ tailWord_7604961) baseStart_7604961 baseEnd_7604961 := by
    simpa [prefixWord, tailWord_7604961, baseEnd_7604961] using wordTrace_append hprefix tailTrace_7604961
  have hstable : (prefixWord ++ tailWord_7604961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604961).length < 2 ^ (prefixWord ++ tailWord_7604961).sum := by decide
  have hdescent : baseEnd_7604961 < baseStart_7604961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604974 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7604974 : Nat := 118140960795 + 7604974 * 2 ^ 59
def prefixEnd_7604974 : Nat := 4983230072969 + 3 ^ 40 * 7604974 * 2
def baseEnd_7604974 : Nat := 1301669008981944579316789

theorem tailTrace_7604974 : CollatzResearch.WordTrace tailWord_7604974 prefixEnd_7604974 1301669008981944579316789 := by
  unfold tailWord_7604974
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672023643810687374934747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184917459433656999332985317 34672023643810687374934747)
  ·
    refine ⟨52008035465716031062402121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34672023643810687374934747 52008035465716031062402121)
    ·
      refine ⟨39006026599287023296801591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52008035465716031062402121 39006026599287023296801591)
      ·
        refine ⟨58509039898930534945202387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39006026599287023296801591 58509039898930534945202387)
        ·
          refine ⟨87763559848395802417803581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58509039898930534945202387 87763559848395802417803581)
          ·
            refine ⟨32911334943148425906676343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87763559848395802417803581 32911334943148425906676343)
            ·
              refine ⟨49367002414722638860014515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32911334943148425906676343 49367002414722638860014515)
              ·
                refine ⟨74050503622083958290021773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49367002414722638860014515 74050503622083958290021773)
                ·
                  refine ⟨27768938858281484358758165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74050503622083958290021773 27768938858281484358758165)
                  ·
                    refine ⟨1301669008981944579316789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27768938858281484358758165 1301669008981944579316789)
                    ·
                      rfl

theorem cell23_7604974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7604974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604974 prefixEnd_7604974 := by exact prefixLift 7604974
  have htrace : WordTrace (prefixWord ++ tailWord_7604974) baseStart_7604974 baseEnd_7604974 := by
    simpa [prefixWord, tailWord_7604974, baseEnd_7604974] using wordTrace_append hprefix tailTrace_7604974
  have hstable : (prefixWord ++ tailWord_7604974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604974).length < 2 ^ (prefixWord ++ tailWord_7604974).sum := by decide
  have hdescent : baseEnd_7604974 < baseStart_7604974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7604978 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_7604978 : Nat := 118140960795 + 7604978 * 2 ^ 59
def prefixEnd_7604978 : Nat := 4983230072969 + 3 ^ 40 * 7604978 * 2
def baseEnd_7604978 : Nat := 1301669693622817240766783

theorem tailTrace_7604978 : CollatzResearch.WordTrace tailWord_7604978 prefixEnd_7604978 1301669693622817240766783 := by
  unfold tailWord_7604978
  simp only [CollatzResearch.WordTrace]
  refine ⟨69344083760617751920655897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184917556694980671788415725 69344083760617751920655897)
  ·
    refine ⟨52008062820463313940491923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69344083760617751920655897 52008062820463313940491923)
    ·
      refine ⟨78012094230694970910737885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52008062820463313940491923 78012094230694970910737885)
      ·
        refine ⟨29254535336510614091526707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78012094230694970910737885 29254535336510614091526707)
        ·
          refine ⟨43881803004765921137290061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29254535336510614091526707 43881803004765921137290061)
          ·
            refine ⟨16455676126787220426483773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43881803004765921137290061 16455676126787220426483773)
            ·
              refine ⟨6170878547545207659931415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455676126787220426483773 6170878547545207659931415)
              ·
                refine ⟨9256317821317811489897123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170878547545207659931415 9256317821317811489897123)
                ·
                  refine ⟨13884476731976717234845685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256317821317811489897123 13884476731976717234845685)
                  ·
                    refine ⟨1301669693622817240766783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13884476731976717234845685 1301669693622817240766783)
                    ·
                      rfl

theorem cell23_7604978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_7604978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7604978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7604978 prefixEnd_7604978 := by exact prefixLift 7604978
  have htrace : WordTrace (prefixWord ++ tailWord_7604978) baseStart_7604978 baseEnd_7604978 := by
    simpa [prefixWord, tailWord_7604978, baseEnd_7604978] using wordTrace_append hprefix tailTrace_7604978
  have hstable : (prefixWord ++ tailWord_7604978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7604978).length < 2 ^ (prefixWord ++ tailWord_7604978).sum := by decide
  have hdescent : baseEnd_7604978 < baseStart_7604978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7604978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605015 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_7605015 : Nat := 118140960795 + 7605015 * 2 ^ 59
def prefixEnd_7605015 : Nat := 4983230072969 + 3 ^ 40 * 7605015 * 2
def baseEnd_7605015 : Nat := 3905028079652668077537679

theorem tailTrace_7605015 : CollatzResearch.WordTrace tailWord_7605015 prefixEnd_7605015 3905028079652668077537679 := by
  unfold tailWord_7605015
  simp only [CollatzResearch.WordTrace]
  refine ⟨277377684543336963001720499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184918456362224642001146999 277377684543336963001720499)
  ·
    refine ⟨416066526815005444502580749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277377684543336963001720499 416066526815005444502580749)
    ·
      refine ⟨156024947555627041688467781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416066526815005444502580749 156024947555627041688467781)
      ·
        refine ⟨29254677666680070316587709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156024947555627041688467781 29254677666680070316587709)
        ·
          refine ⟨10970504125005026368720391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29254677666680070316587709 10970504125005026368720391)
          ·
            refine ⟨16455756187507539553080587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10970504125005026368720391 16455756187507539553080587)
            ·
              refine ⟨24683634281261309329620881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16455756187507539553080587 24683634281261309329620881)
              ·
                refine ⟨18512725710945981997215661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24683634281261309329620881 18512725710945981997215661)
                ·
                  refine ⟨6942272141604743248955873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18512725710945981997215661 6942272141604743248955873)
                  ·
                    refine ⟨5206704106203557436716905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942272141604743248955873 5206704106203557436716905)
                    ·
                      refine ⟨3905028079652668077537679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206704106203557436716905 3905028079652668077537679)
                      ·
                        rfl

theorem cell23_7605015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_7605015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605015 prefixEnd_7605015 := by exact prefixLift 7605015
  have htrace : WordTrace (prefixWord ++ tailWord_7605015) baseStart_7605015 baseEnd_7605015 := by
    simpa [prefixWord, tailWord_7605015, baseEnd_7605015] using wordTrace_append hprefix tailTrace_7605015
  have hstable : (prefixWord ++ tailWord_7605015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605015).length < 2 ^ (prefixWord ++ tailWord_7605015).sum := by decide
  have hdescent : baseEnd_7605015 < baseStart_7605015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605032 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_7605032 : Nat := 118140960795 + 7605032 * 2 ^ 59
def prefixEnd_7605032 : Nat := 4983230072969 + 3 ^ 40 * 7605032 * 2
def baseEnd_7605032 : Nat := 3905036808823794511025101

theorem tailTrace_7605032 : CollatzResearch.WordTrace tailWord_7605032 prefixEnd_7605032 3905036808823794511025101 := by
  unfold tailWord_7605032
  simp only [CollatzResearch.WordTrace]
  refine ⟨138689152292137687452544675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184918869722850249936726233 138689152292137687452544675)
  ·
    refine ⟨208033728438206531178817013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138689152292137687452544675 208033728438206531178817013)
    ·
      refine ⟨19503162041081862298014095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 208033728438206531178817013 19503162041081862298014095)
      ·
        refine ⟨29254743061622793447021143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503162041081862298014095 29254743061622793447021143)
        ·
          refine ⟨43882114592434190170531715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29254743061622793447021143 43882114592434190170531715)
          ·
            refine ⟨65823171888651285255797573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43882114592434190170531715 65823171888651285255797573)
            ·
              refine ⟨12341844729122115985462045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65823171888651285255797573 12341844729122115985462045)
              ·
                refine ⟨4628191773420793494548267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12341844729122115985462045 4628191773420793494548267)
                ·
                  refine ⟨6942287660131190241822401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628191773420793494548267 6942287660131190241822401)
                  ·
                    refine ⟨5206715745098392681366801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942287660131190241822401 5206715745098392681366801)
                    ·
                      refine ⟨3905036808823794511025101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206715745098392681366801 3905036808823794511025101)
                      ·
                        rfl

theorem cell23_7605032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_7605032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605032 prefixEnd_7605032 := by exact prefixLift 7605032
  have htrace : WordTrace (prefixWord ++ tailWord_7605032) baseStart_7605032 baseEnd_7605032 := by
    simpa [prefixWord, tailWord_7605032, baseEnd_7605032] using wordTrace_append hprefix tailTrace_7605032
  have hstable : (prefixWord ++ tailWord_7605032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605032).length < 2 ^ (prefixWord ++ tailWord_7605032).sum := by decide
  have hdescent : baseEnd_7605032 < baseStart_7605032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605062 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7605062 : Nat := 118140960795 + 7605062 * 2 ^ 59
def prefixEnd_7605062 : Nat := 4983230072969 + 3 ^ 40 * 7605062 * 2
def baseEnd_7605062 : Nat := 3905052213243429393649963

theorem tailTrace_7605062 : CollatzResearch.WordTrace tailWord_7605062 prefixEnd_7605062 3905052213243429393649963 := by
  unfold tailWord_7605062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8668106211692709063396295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 184919599182777793352454293 8668106211692709063396295)
  ·
    refine ⟨13002159317539063595094443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8668106211692709063396295 13002159317539063595094443)
    ·
      refine ⟨19503238976308595392641665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002159317539063595094443 19503238976308595392641665)
      ·
        refine ⟨14627429232231446544481249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19503238976308595392641665 14627429232231446544481249)
        ·
          refine ⟨10970571924173584908360937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627429232231446544481249 10970571924173584908360937)
          ·
            refine ⟨8227928943130188681270703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10970571924173584908360937 8227928943130188681270703)
            ·
              refine ⟨12341893414695283021906055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227928943130188681270703 12341893414695283021906055)
              ·
                refine ⟨18512840122042924532859083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12341893414695283021906055 18512840122042924532859083)
                ·
                  refine ⟨27769260183064386799288625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18512840122042924532859083 27769260183064386799288625)
                  ·
                    refine ⟨20826945137298290099466469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27769260183064386799288625 20826945137298290099466469)
                    ·
                      refine ⟨3905052213243429393649963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20826945137298290099466469 3905052213243429393649963)
                      ·
                        rfl

theorem cell23_7605062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7605062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605062 prefixEnd_7605062 := by exact prefixLift 7605062
  have htrace : WordTrace (prefixWord ++ tailWord_7605062) baseStart_7605062 baseEnd_7605062 := by
    simpa [prefixWord, tailWord_7605062, baseEnd_7605062] using wordTrace_append hprefix tailTrace_7605062
  have hstable : (prefixWord ++ tailWord_7605062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605062).length < 2 ^ (prefixWord ++ tailWord_7605062).sum := by decide
  have hdescent : baseEnd_7605062 < baseStart_7605062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605064 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_7605064 : Nat := 118140960795 + 7605064 * 2 ^ 59
def prefixEnd_7605064 : Nat := 4983230072969 + 3 ^ 40 * 7605064 * 2
def baseEnd_7605064 : Nat := 1301684413401579461941651

theorem tailTrace_7605064 : CollatzResearch.WordTrace tailWord_7605064 prefixEnd_7605064 1301684413401579461941651 := by
  unfold tailWord_7605064
  simp only [CollatzResearch.WordTrace]
  refine ⟨138689735860079722185127123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184919647813439629580169497 138689735860079722185127123)
  ·
    refine ⟨208034603790119583277690685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138689735860079722185127123 208034603790119583277690685)
    ·
      refine ⟨78012976421294843729134007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208034603790119583277690685 78012976421294843729134007)
      ·
        refine ⟨117019464631942265593701011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78012976421294843729134007 117019464631942265593701011)
        ·
          refine ⟨175529196947913398390551517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117019464631942265593701011 175529196947913398390551517)
          ·
            refine ⟨65823448855467524396456819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175529196947913398390551517 65823448855467524396456819)
            ·
              refine ⟨98735173283201286594685229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65823448855467524396456819 98735173283201286594685229)
              ·
                refine ⟨37025689981200482473006961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98735173283201286594685229 37025689981200482473006961)
                ·
                  refine ⟨27769267485900361854755221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37025689981200482473006961 27769267485900361854755221)
                  ·
                    refine ⟨1301684413401579461941651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27769267485900361854755221 1301684413401579461941651)
                    ·
                      rfl

theorem cell23_7605064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_7605064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605064 prefixEnd_7605064 := by exact prefixLift 7605064
  have htrace : WordTrace (prefixWord ++ tailWord_7605064) baseStart_7605064 baseEnd_7605064 := by
    simpa [prefixWord, tailWord_7605064, baseEnd_7605064] using wordTrace_append hprefix tailTrace_7605064
  have hstable : (prefixWord ++ tailWord_7605064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605064).length < 2 ^ (prefixWord ++ tailWord_7605064).sum := by decide
  have hdescent : baseEnd_7605064 < baseStart_7605064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605065 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 2, 1, 3]
def baseStart_7605065 : Nat := 118140960795 + 7605065 * 2 ^ 59
def prefixEnd_7605065 : Nat := 4983230072969 + 3 ^ 40 * 7605065 * 2
def baseEnd_7605065 : Nat := 3905053753685392881912449

theorem tailTrace_7605065 : CollatzResearch.WordTrace tailWord_7605065 prefixEnd_7605065 3905053753685392881912449 := by
  unfold tailWord_7605065
  simp only [CollatzResearch.WordTrace]
  refine ⟨277379508193155821541040649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184919672128770547694027099 277379508193155821541040649)
  ·
    refine ⟨208034631144866866155780487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277379508193155821541040649 208034631144866866155780487)
    ·
      refine ⟨312051946717300299233670731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208034631144866866155780487 312051946717300299233670731)
      ·
        refine ⟨468077920075950448850506097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312051946717300299233670731 468077920075950448850506097)
        ·
          refine ⟨351058440056962836637879573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468077920075950448850506097 351058440056962836637879573)
          ·
            refine ⟨16455864377670132967400605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351058440056962836637879573 16455864377670132967400605)
            ·
              refine ⟨6170949141626299862775227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455864377670132967400605 6170949141626299862775227)
              ·
                refine ⟨9256423712439449794162841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6170949141626299862775227 9256423712439449794162841)
                ·
                  refine ⟨6942317784329587345622131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256423712439449794162841 6942317784329587345622131)
                  ·
                    refine ⟨10413476676494381018433197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942317784329587345622131 10413476676494381018433197)
                    ·
                      refine ⟨3905053753685392881912449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10413476676494381018433197 3905053753685392881912449)
                      ·
                        rfl

theorem cell23_7605065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 1, 3].length) (baseStart_7605065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605065 prefixEnd_7605065 := by exact prefixLift 7605065
  have htrace : WordTrace (prefixWord ++ tailWord_7605065) baseStart_7605065 baseEnd_7605065 := by
    simpa [prefixWord, tailWord_7605065, baseEnd_7605065] using wordTrace_append hprefix tailTrace_7605065
  have hstable : (prefixWord ++ tailWord_7605065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605065).length < 2 ^ (prefixWord ++ tailWord_7605065).sum := by decide
  have hdescent : baseEnd_7605065 < baseStart_7605065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605088 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2]
def baseStart_7605088 : Nat := 118140960795 + 7605088 * 2 ^ 59
def prefixEnd_7605088 : Nat := 4983230072969 + 3 ^ 40 * 7605088 * 2
def baseEnd_7605088 : Nat := 3905065563740446291924843

theorem tailTrace_7605088 : CollatzResearch.WordTrace tailWord_7605088 prefixEnd_7605088 3905065563740446291924843 := by
  unfold tailWord_7605088
  simp only [CollatzResearch.WordTrace]
  refine ⟨138690173536036248234563959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184920231381381664312751945 138690173536036248234563959)
  ·
    refine ⟨208035260304054372351845939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138690173536036248234563959 208035260304054372351845939)
    ·
      refine ⟨312052890456081558527768909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208035260304054372351845939 312052890456081558527768909)
      ·
        refine ⟨117019833921030584447913341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 312052890456081558527768909 117019833921030584447913341)
        ·
          refine ⟨43882437720386469167967503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117019833921030584447913341 43882437720386469167967503)
          ·
            refine ⟨65823656580579703751951255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43882437720386469167967503 65823656580579703751951255)
            ·
              refine ⟨98735484870869555627926883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65823656580579703751951255 98735484870869555627926883)
              ·
                refine ⟨148103227306304333441890325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98735484870869555627926883 148103227306304333441890325)
                ·
                  refine ⟨6942338779983015630088609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 148103227306304333441890325 6942338779983015630088609)
                  ·
                    refine ⟨5206754084987261722566457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942338779983015630088609 5206754084987261722566457)
                    ·
                      refine ⟨3905065563740446291924843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206754084987261722566457 3905065563740446291924843)
                      ·
                        rfl

theorem cell23_7605088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_7605088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605088 prefixEnd_7605088 := by exact prefixLift 7605088
  have htrace : WordTrace (prefixWord ++ tailWord_7605088) baseStart_7605088 baseEnd_7605088 := by
    simpa [prefixWord, tailWord_7605088, baseEnd_7605088] using wordTrace_append hprefix tailTrace_7605088
  have hstable : (prefixWord ++ tailWord_7605088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605088).length < 2 ^ (prefixWord ++ tailWord_7605088).sum := by decide
  have hdescent : baseEnd_7605088 < baseStart_7605088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605091 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_7605091 : Nat := 118140960795 + 7605091 * 2 ^ 59
def prefixEnd_7605091 : Nat := 4983230072969 + 3 ^ 40 * 7605091 * 2
def baseEnd_7605091 : Nat := 3905067104182409780187329

theorem tailTrace_7605091 : CollatzResearch.WordTrace tailWord_7605091 prefixEnd_7605091 3905067104182409780187329 := by
  unfold tailWord_7605091
  simp only [CollatzResearch.WordTrace]
  refine ⟨277380456491061627981487127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184920304327374418654324751 277380456491061627981487127)
  ·
    refine ⟨416070684736592441972230691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277380456491061627981487127 416070684736592441972230691)
    ·
      refine ⟨624106027104888662958346037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416070684736592441972230691 624106027104888662958346037)
      ·
        refine ⟨58509940041083312152344941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624106027104888662958346037 58509940041083312152344941)
        ·
          refine ⟨21941227515406242057129353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58509940041083312152344941 21941227515406242057129353)
          ·
            refine ⟨16455920636554681542847015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21941227515406242057129353 16455920636554681542847015)
            ·
              refine ⟨24683880954832022314270523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16455920636554681542847015 24683880954832022314270523)
              ·
                refine ⟨37025821432248033471405785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24683880954832022314270523 37025821432248033471405785)
                ·
                  refine ⟨27769366074186025103554339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37025821432248033471405785 27769366074186025103554339)
                  ·
                    refine ⟨41654049111279037655331509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27769366074186025103554339 41654049111279037655331509)
                    ·
                      refine ⟨3905067104182409780187329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41654049111279037655331509 3905067104182409780187329)
                      ·
                        rfl

theorem cell23_7605091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_7605091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605091 prefixEnd_7605091 := by exact prefixLift 7605091
  have htrace : WordTrace (prefixWord ++ tailWord_7605091) baseStart_7605091 baseEnd_7605091 := by
    simpa [prefixWord, tailWord_7605091, baseEnd_7605091] using wordTrace_append hprefix tailTrace_7605091
  have hstable : (prefixWord ++ tailWord_7605091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605091).length < 2 ^ (prefixWord ++ tailWord_7605091).sum := by decide
  have hdescent : baseEnd_7605091 < baseStart_7605091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605111 : List Nat := [1, 1, 3, 1, 1, 2, 1, 8, 5]
def baseStart_7605111 : Nat := 118140960795 + 7605111 * 2 ^ 59
def prefixEnd_7605111 : Nat := 4983230072969 + 3 ^ 40 * 7605111 * 2
def baseEnd_7605111 : Nat := 433897485977277744659693

theorem tailTrace_7605111 : CollatzResearch.WordTrace tailWord_7605111 prefixEnd_7605111 433897485977277744659693 := by
  unfold tailWord_7605111
  simp only [CollatzResearch.WordTrace]
  refine ⟨277381185950989171397215187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184920790633992780931476791 277381185950989171397215187)
  ·
    refine ⟨416071778926483757095822781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277381185950989171397215187 416071778926483757095822781)
    ·
      refine ⟨156026917097431408910933543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416071778926483757095822781 156026917097431408910933543)
      ·
        refine ⟨234040375646147113366400315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156026917097431408910933543 234040375646147113366400315)
        ·
          refine ⟨351060563469220670049600473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234040375646147113366400315 351060563469220670049600473)
          ·
            refine ⟨263295422601915502537200355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351060563469220670049600473 263295422601915502537200355)
            ·
              refine ⟨394943133902873253805800533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263295422601915502537200355 394943133902873253805800533)
              ·
                refine ⟨4628239850424295943036725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 394943133902873253805800533 4628239850424295943036725)
                ·
                  refine ⟨433897485977277744659693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4628239850424295943036725 433897485977277744659693)
                  ·
                    rfl

theorem cell23_7605111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 8, 5].length) (baseStart_7605111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605111 prefixEnd_7605111 := by exact prefixLift 7605111
  have htrace : WordTrace (prefixWord ++ tailWord_7605111) baseStart_7605111 baseEnd_7605111 := by
    simpa [prefixWord, tailWord_7605111, baseEnd_7605111] using wordTrace_append hprefix tailTrace_7605111
  have hstable : (prefixWord ++ tailWord_7605111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605111).length < 2 ^ (prefixWord ++ tailWord_7605111).sum := by decide
  have hdescent : baseEnd_7605111 < baseStart_7605111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605141 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 2, 5]
def baseStart_7605141 : Nat := 118140960795 + 7605141 * 2 ^ 59
def prefixEnd_7605141 : Nat := 4983230072969 + 3 ^ 40 * 7605141 * 2
def baseEnd_7605141 : Nat := 1301697592738378194854033

theorem tailTrace_7605141 : CollatzResearch.WordTrace tailWord_7605141 prefixEnd_7605141 1301697592738378194854033 := by
  unfold tailWord_7605141
  simp only [CollatzResearch.WordTrace]
  refine ⟨277382280140880486520807277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184921520093920324347204851 277382280140880486520807277)
  ·
    refine ⟨104018355052830182445302729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277382280140880486520807277 104018355052830182445302729)
    ·
      refine ⟨78013766289622636833977047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104018355052830182445302729 78013766289622636833977047)
      ·
        refine ⟨117020649434433955250965571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78013766289622636833977047 117020649434433955250965571)
        ·
          refine ⟨175530974151650932876448357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117020649434433955250965571 175530974151650932876448357)
          ·
            refine ⟨32912057653434549914334067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175530974151650932876448357 32912057653434549914334067)
            ·
              refine ⟨49368086480151824871501101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32912057653434549914334067 49368086480151824871501101)
              ·
                refine ⟨18513032430056934326812913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49368086480151824871501101 18513032430056934326812913)
                ·
                  refine ⟨13884774322542700745109685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513032430056934326812913 13884774322542700745109685)
                  ·
                    refine ⟨1301697592738378194854033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13884774322542700745109685 1301697592738378194854033)
                    ·
                      rfl

theorem cell23_7605141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_7605141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605141 prefixEnd_7605141 := by exact prefixLift 7605141
  have htrace : WordTrace (prefixWord ++ tailWord_7605141) baseStart_7605141 baseEnd_7605141 := by
    simpa [prefixWord, tailWord_7605141, baseEnd_7605141] using wordTrace_append hprefix tailTrace_7605141
  have hstable : (prefixWord ++ tailWord_7605141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605141).length < 2 ^ (prefixWord ++ tailWord_7605141).sum := by decide
  have hdescent : baseEnd_7605141 < baseStart_7605141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605151 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7605151 : Nat := 118140960795 + 7605151 * 2 ^ 59
def prefixEnd_7605151 : Nat := 4983230072969 + 3 ^ 40 * 7605151 * 2
def baseEnd_7605151 : Nat := 3905097913021679545437053

theorem tailTrace_7605151 : CollatzResearch.WordTrace tailWord_7605151 prefixEnd_7605151 3905097913021679545437053 := by
  unfold tailWord_7605151
  simp only [CollatzResearch.WordTrace]
  refine ⟨277382644870844258228671307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184921763247229505485780871 277382644870844258228671307)
  ·
    refine ⟨416073967306266387343006961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277382644870844258228671307 416073967306266387343006961)
    ·
      refine ⟨312055475479699790507255221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416073967306266387343006961 312055475479699790507255221)
      ·
        refine ⟨29255200826221855360055177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312055475479699790507255221 29255200826221855360055177)
        ·
          refine ⟨21941400619666391520041383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29255200826221855360055177 21941400619666391520041383)
          ·
            refine ⟨32912100929499587280062075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21941400619666391520041383 32912100929499587280062075)
            ·
              refine ⟨49368151394249380920093113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32912100929499587280062075 49368151394249380920093113)
              ·
                refine ⟨37026113545687035690069835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49368151394249380920093113 37026113545687035690069835)
                ·
                  refine ⟨55539170318530553535104753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37026113545687035690069835 55539170318530553535104753)
                  ·
                    refine ⟨41654377738897915151328565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55539170318530553535104753 41654377738897915151328565)
                    ·
                      refine ⟨3905097913021679545437053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41654377738897915151328565 3905097913021679545437053)
                      ·
                        rfl

theorem cell23_7605151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7605151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605151 prefixEnd_7605151 := by exact prefixLift 7605151
  have htrace : WordTrace (prefixWord ++ tailWord_7605151) baseStart_7605151 baseEnd_7605151 := by
    simpa [prefixWord, tailWord_7605151, baseEnd_7605151] using wordTrace_append hprefix tailTrace_7605151
  have hstable : (prefixWord ++ tailWord_7605151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605151).length < 2 ^ (prefixWord ++ tailWord_7605151).sum := by decide
  have hdescent : baseEnd_7605151 < baseStart_7605151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605161 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 4]
def baseStart_7605161 : Nat := 118140960795 + 7605161 * 2 ^ 59
def prefixEnd_7605161 : Nat := 4983230072969 + 3 ^ 40 * 7605161 * 2
def baseEnd_7605161 : Nat := 3905103047828224506312007

theorem tailTrace_7605161 : CollatzResearch.WordTrace tailWord_7605161 prefixEnd_7605161 3905103047828224506312007 := by
  unfold tailWord_7605161
  simp only [CollatzResearch.WordTrace]
  refine ⟨277383009600808029936535337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184922006400538686624356891 277383009600808029936535337)
  ·
    refine ⟨208037257200606022452401503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277383009600808029936535337 208037257200606022452401503)
    ·
      refine ⟨312055885800909033678602255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208037257200606022452401503 312055885800909033678602255)
      ·
        refine ⟨468083828701363550517903383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312055885800909033678602255 468083828701363550517903383)
        ·
          refine ⟨702125743052045325776855075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468083828701363550517903383 702125743052045325776855075)
          ·
            refine ⟨1053188614578067988665282613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702125743052045325776855075 1053188614578067988665282613)
            ·
              refine ⟨98736432616693873937370245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1053188614578067988665282613 98736432616693873937370245)
              ·
                refine ⟨18513081115630101363256921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98736432616693873937370245 18513081115630101363256921)
                ·
                  refine ⟨13884810836722576022442691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513081115630101363256921 13884810836722576022442691)
                  ·
                    refine ⟨20827216255083864033664037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13884810836722576022442691 20827216255083864033664037)
                    ·
                      refine ⟨3905103047828224506312007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20827216255083864033664037 3905103047828224506312007)
                      ·
                        rfl

theorem cell23_7605161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_7605161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605161 prefixEnd_7605161 := by exact prefixLift 7605161
  have htrace : WordTrace (prefixWord ++ tailWord_7605161) baseStart_7605161 baseEnd_7605161 := by
    simpa [prefixWord, tailWord_7605161, baseEnd_7605161] using wordTrace_append hprefix tailTrace_7605161
  have hstable : (prefixWord ++ tailWord_7605161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605161).length < 2 ^ (prefixWord ++ tailWord_7605161).sum := by decide
  have hdescent : baseEnd_7605161 < baseStart_7605161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605178 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2]
def baseStart_7605178 : Nat := 118140960795 + 7605178 * 2 ^ 59
def prefixEnd_7605178 : Nat := 4983230072969 + 3 ^ 40 * 7605178 * 2
def baseEnd_7605178 : Nat := 3905111776999350939799429

theorem tailTrace_7605178 : CollatzResearch.WordTrace tailWord_7605178 prefixEnd_7605178 3905111776999350939799429 := by
  unfold tailWord_7605178
  simp only [CollatzResearch.WordTrace]
  refine ⟨69345907410436610459976047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184922419761164294559936125 69345907410436610459976047)
  ·
    refine ⟨104018861115654915689964071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69345907410436610459976047 104018861115654915689964071)
    ·
      refine ⟨156028291673482373534946107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104018861115654915689964071 156028291673482373534946107)
      ·
        refine ⟨234042437510223560302419161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156028291673482373534946107 234042437510223560302419161)
        ·
          refine ⟨175531828132667670226814371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234042437510223560302419161 175531828132667670226814371)
          ·
            refine ⟨263297742199001505340221557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175531828132667670226814371 263297742199001505340221557)
            ·
              refine ⟨24684163331156391125645771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 263297742199001505340221557 24684163331156391125645771)
              ·
                refine ⟨37026244996734586688468657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24684163331156391125645771 37026244996734586688468657)
                ·
                  refine ⟨27769683747550940016351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37026244996734586688468657 27769683747550940016351493)
                  ·
                    refine ⟨5206815702665801253065905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27769683747550940016351493 5206815702665801253065905)
                    ·
                      refine ⟨3905111776999350939799429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206815702665801253065905 3905111776999350939799429)
                      ·
                        rfl

theorem cell23_7605178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_7605178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605178 prefixEnd_7605178 := by exact prefixLift 7605178
  have htrace : WordTrace (prefixWord ++ tailWord_7605178) baseStart_7605178 baseEnd_7605178 := by
    simpa [prefixWord, tailWord_7605178, baseEnd_7605178] using wordTrace_append hprefix tailTrace_7605178
  have hstable : (prefixWord ++ tailWord_7605178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605178).length < 2 ^ (prefixWord ++ tailWord_7605178).sum := by decide
  have hdescent : baseEnd_7605178 < baseStart_7605178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605198 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_7605198 : Nat := 118140960795 + 7605198 * 2 ^ 59
def prefixEnd_7605198 : Nat := 4983230072969 + 3 ^ 40 * 7605198 * 2
def baseEnd_7605198 : Nat := 3905122046612440861549337

theorem tailTrace_7605198 : CollatzResearch.WordTrace tailWord_7605198 prefixEnd_7605198 3905122046612440861549337 := by
  unfold tailWord_7605198
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673044887709248156954031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184922906067782656837088165 34673044887709248156954031)
  ·
    refine ⟨52009567331563872235431047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34673044887709248156954031 52009567331563872235431047)
    ·
      refine ⟨78014350997345808353146571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52009567331563872235431047 78014350997345808353146571)
      ·
        refine ⟨117021526496018712529719857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78014350997345808353146571 117021526496018712529719857)
        ·
          refine ⟨87766144872014034397289893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117021526496018712529719857 87766144872014034397289893)
          ·
            refine ⟨16456152163502631449491855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87766144872014034397289893 16456152163502631449491855)
            ·
              refine ⟨24684228245253947174237783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16456152163502631449491855 24684228245253947174237783)
              ·
                refine ⟨37026342367880920761356675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24684228245253947174237783 37026342367880920761356675)
                ·
                  refine ⟨55539513551821381142035013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37026342367880920761356675 55539513551821381142035013)
                  ·
                    refine ⟨10413658790966508964131565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55539513551821381142035013 10413658790966508964131565)
                    ·
                      refine ⟨3905122046612440861549337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10413658790966508964131565 3905122046612440861549337)
                      ·
                        rfl

theorem cell23_7605198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_7605198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605198 prefixEnd_7605198 := by exact prefixLift 7605198
  have htrace : WordTrace (prefixWord ++ tailWord_7605198) baseStart_7605198 baseEnd_7605198 := by
    simpa [prefixWord, tailWord_7605198, baseEnd_7605198] using wordTrace_append hprefix tailTrace_7605198
  have hstable : (prefixWord ++ tailWord_7605198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605198).length < 2 ^ (prefixWord ++ tailWord_7605198).sum := by decide
  have hdescent : baseEnd_7605198 < baseStart_7605198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605255 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7605255 : Nat := 118140960795 + 7605255 * 2 ^ 59
def prefixEnd_7605255 : Nat := 4983230072969 + 3 ^ 40 * 7605255 * 2
def baseEnd_7605255 : Nat := 3905151315009747138536575

theorem tailTrace_7605255 : CollatzResearch.WordTrace tailWord_7605255 prefixEnd_7605255 3905151315009747138536575 := by
  unfold tailWord_7605255
  simp only [CollatzResearch.WordTrace]
  refine ⟨277386438062467483990457219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184924292041644989326971479 277386438062467483990457219)
  ·
    refine ⟨416079657093701225985685829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277386438062467483990457219 416079657093701225985685829)
    ·
      refine ⟨78014935705068979872316093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416079657093701225985685829 78014935705068979872316093)
      ·
        refine ⟨29255600889400867452118535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78014935705068979872316093 29255600889400867452118535)
        ·
          refine ⟨43883401334101301178177803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29255600889400867452118535 43883401334101301178177803)
          ·
            refine ⟨65825102001151951767266705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43883401334101301178177803 65825102001151951767266705)
            ·
              refine ⟨49368826500863963825450029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65825102001151951767266705 49368826500863963825450029)
              ·
                refine ⟨18513309937823986434543761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49368826500863963825450029 18513309937823986434543761)
                ·
                  refine ⟨13884982453367989825907821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513309937823986434543761 13884982453367989825907821)
                  ·
                    refine ⟨5206868420012996184715433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13884982453367989825907821 5206868420012996184715433)
                    ·
                      refine ⟨3905151315009747138536575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206868420012996184715433 3905151315009747138536575)
                      ·
                        rfl

theorem cell23_7605255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7605255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605255 prefixEnd_7605255 := by exact prefixLift 7605255
  have htrace : WordTrace (prefixWord ++ tailWord_7605255) baseStart_7605255 baseEnd_7605255 := by
    simpa [prefixWord, tailWord_7605255, baseEnd_7605255] using wordTrace_append hprefix tailTrace_7605255
  have hstable : (prefixWord ++ tailWord_7605255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605255).length < 2 ^ (prefixWord ++ tailWord_7605255).sum := by decide
  have hdescent : baseEnd_7605255 < baseStart_7605255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605279 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 1, 1, 3]
def baseStart_7605279 : Nat := 118140960795 + 7605279 * 2 ^ 59
def prefixEnd_7605279 : Nat := 4983230072969 + 3 ^ 40 * 7605279 * 2
def baseEnd_7605279 : Nat := 3905163638545455044636465

theorem tailTrace_7605279 : CollatzResearch.WordTrace tailWord_7605279 prefixEnd_7605279 3905163638545455044636465 := by
  unfold tailWord_7605279
  simp only [CollatzResearch.WordTrace]
  refine ⟨277387313414380536089330891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184924875609587024059553927 277387313414380536089330891)
  ·
    refine ⟨416080970121570804133996337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277387313414380536089330891 416080970121570804133996337)
    ·
      refine ⟨312060727591178103100497253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416080970121570804133996337 312060727591178103100497253)
      ·
        refine ⟨58511386423345894331343235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 312060727591178103100497253 58511386423345894331343235)
        ·
          refine ⟨87767079635018841497014853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58511386423345894331343235 87767079635018841497014853)
          ·
            refine ⟨16456327431566032780690285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87767079635018841497014853 16456327431566032780690285)
            ·
              refine ⟨6171122786837262292758857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16456327431566032780690285 6171122786837262292758857)
              ·
                refine ⟨4628342090127946719569143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171122786837262292758857 4628342090127946719569143)
                ·
                  refine ⟨6942513135191920079353715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628342090127946719569143 6942513135191920079353715)
                  ·
                    refine ⟨10413769702787880119030573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942513135191920079353715 10413769702787880119030573)
                    ·
                      refine ⟨3905163638545455044636465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10413769702787880119030573 3905163638545455044636465)
                      ·
                        rfl

theorem cell23_7605279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_7605279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605279 prefixEnd_7605279 := by exact prefixLift 7605279
  have htrace : WordTrace (prefixWord ++ tailWord_7605279) baseStart_7605279 baseEnd_7605279 := by
    simpa [prefixWord, tailWord_7605279, baseEnd_7605279] using wordTrace_append hprefix tailTrace_7605279
  have hstable : (prefixWord ++ tailWord_7605279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605279).length < 2 ^ (prefixWord ++ tailWord_7605279).sum := by decide
  have hdescent : baseEnd_7605279 < baseStart_7605279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605291 : List Nat := [1, 1, 1, 1, 2, 1, 8, 8]
def baseStart_7605291 : Nat := 118140960795 + 7605291 * 2 ^ 59
def prefixEnd_7605291 : Nat := 4983230072969 + 3 ^ 40 * 7605291 * 2
def baseEnd_7605291 : Nat := 144635918530122555469867

theorem tailTrace_7605291 : CollatzResearch.WordTrace tailWord_7605291 prefixEnd_7605291 144635918530122555469867 := by
  unfold tailWord_7605291
  simp only [CollatzResearch.WordTrace]
  refine ⟨277387751090337062138767727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184925167393558041425845151 277387751090337062138767727)
  ·
    refine ⟨416081626635505593208151591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277387751090337062138767727 416081626635505593208151591)
    ·
      refine ⟨624122439953258389812227387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416081626635505593208151591 624122439953258389812227387)
      ·
        refine ⟨936183659929887584718341081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 624122439953258389812227387 936183659929887584718341081)
        ·
          refine ⟨702137744947415688538755811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 936183659929887584718341081 702137744947415688538755811)
          ·
            refine ⟨1053206617421123532808133717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702137744947415688538755811 1053206617421123532808133717)
            ·
              refine ⟨12342265047903791400095317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1053206617421123532808133717 12342265047903791400095317)
              ·
                refine ⟨144635918530122555469867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12342265047903791400095317 144635918530122555469867)
                ·
                  rfl

theorem cell23_7605291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 8].length) (baseStart_7605291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605291 prefixEnd_7605291 := by exact prefixLift 7605291
  have htrace : WordTrace (prefixWord ++ tailWord_7605291) baseStart_7605291 baseEnd_7605291 := by
    simpa [prefixWord, tailWord_7605291, baseEnd_7605291] using wordTrace_append hprefix tailTrace_7605291
  have hstable : (prefixWord ++ tailWord_7605291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605291).length < 2 ^ (prefixWord ++ tailWord_7605291).sum := by decide
  have hdescent : baseEnd_7605291 < baseStart_7605291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605298 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_7605298 : Nat := 118140960795 + 7605298 * 2 ^ 59
def prefixEnd_7605298 : Nat := 4983230072969 + 3 ^ 40 * 7605298 * 2
def baseEnd_7605298 : Nat := 3905173394677890470298877

theorem tailTrace_7605298 : CollatzResearch.WordTrace tailWord_7605298 prefixEnd_7605298 3905173394677890470298877 := by
  unfold tailWord_7605298
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347001600327925583568137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184925337600874468222848365 69347001600327925583568137)
  ·
    refine ⟨52010251200245944187676103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69347001600327925583568137 52010251200245944187676103)
    ·
      refine ⟨78015376800368916281514155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52010251200245944187676103 78015376800368916281514155)
      ·
        refine ⟨117023065200553374422271233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78015376800368916281514155 117023065200553374422271233)
        ·
          refine ⟨87767298900415030816703425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117023065200553374422271233 87767298900415030816703425)
          ·
            refine ⟨65825474175311273112527569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87767298900415030816703425 65825474175311273112527569)
            ·
              refine ⟨49369105631483454834395677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65825474175311273112527569 49369105631483454834395677)
              ·
                refine ⟨18513414611806295562898379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49369105631483454834395677 18513414611806295562898379)
                ·
                  refine ⟨27770121917709443344347569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18513414611806295562898379 27770121917709443344347569)
                  ·
                    refine ⟨20827591438282082508260677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27770121917709443344347569 20827591438282082508260677)
                    ·
                      refine ⟨3905173394677890470298877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20827591438282082508260677 3905173394677890470298877)
                      ·
                        rfl

theorem cell23_7605298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_7605298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605298 prefixEnd_7605298 := by exact prefixLift 7605298
  have htrace : WordTrace (prefixWord ++ tailWord_7605298) baseStart_7605298 baseEnd_7605298 := by
    simpa [prefixWord, tailWord_7605298, baseEnd_7605298] using wordTrace_append hprefix tailTrace_7605298
  have hstable : (prefixWord ++ tailWord_7605298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605298).length < 2 ^ (prefixWord ++ tailWord_7605298).sum := by decide
  have hdescent : baseEnd_7605298 < baseStart_7605298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605302 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_7605302 : Nat := 118140960795 + 7605302 * 2 ^ 59
def prefixEnd_7605302 : Nat := 4983230072969 + 3 ^ 40 * 7605302 * 2
def baseEnd_7605302 : Nat := 3905175448600508454648859

theorem tailTrace_7605302 : CollatzResearch.WordTrace tailWord_7605302 prefixEnd_7605302 3905175448600508454648859 := by
  unfold tailWord_7605302
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336759518331075688588635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184925434862198140678278773 17336759518331075688588635)
  ·
    refine ⟨26005139277496613532882953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17336759518331075688588635 26005139277496613532882953)
    ·
      refine ⟨19503854458122460149662215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26005139277496613532882953 19503854458122460149662215)
      ·
        refine ⟨29255781687183690224493323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503854458122460149662215 29255781687183690224493323)
        ·
          refine ⟨43883672530775535336739985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29255781687183690224493323 43883672530775535336739985)
          ·
            refine ⟨32912754398081651502554989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43883672530775535336739985 32912754398081651502554989)
            ·
              refine ⟨12342282899280619313458121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32912754398081651502554989 12342282899280619313458121)
              ·
                refine ⟨9256712174460464485093591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12342282899280619313458121 9256712174460464485093591)
                ·
                  refine ⟨13885068261690696727640387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256712174460464485093591 13885068261690696727640387)
                  ·
                    refine ⟨20827602392536045091460581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13885068261690696727640387 20827602392536045091460581)
                    ·
                      refine ⟨3905175448600508454648859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20827602392536045091460581 3905175448600508454648859)
                      ·
                        rfl

theorem cell23_7605302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_7605302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605302 prefixEnd_7605302 := by exact prefixLift 7605302
  have htrace : WordTrace (prefixWord ++ tailWord_7605302) baseStart_7605302 baseEnd_7605302 := by
    simpa [prefixWord, tailWord_7605302, baseEnd_7605302] using wordTrace_append hprefix tailTrace_7605302
  have hstable : (prefixWord ++ tailWord_7605302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605302).length < 2 ^ (prefixWord ++ tailWord_7605302).sum := by decide
  have hdescent : baseEnd_7605302 < baseStart_7605302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605305 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7605305 : Nat := 118140960795 + 7605305 * 2 ^ 59
def prefixEnd_7605305 : Nat := 4983230072969 + 3 ^ 40 * 7605305 * 2
def baseEnd_7605305 : Nat := 3905176989042471942911345

theorem tailTrace_7605305 : CollatzResearch.WordTrace tailWord_7605305 prefixEnd_7605305 3905176989042471942911345 := by
  unfold tailWord_7605305
  simp only [CollatzResearch.WordTrace]
  refine ⟨277388261712286342529777369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184925507808190895019851579 277388261712286342529777369)
  ·
    refine ⟨208041196284214756897333027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277388261712286342529777369 208041196284214756897333027)
    ·
      refine ⟨312061794426322135345999541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208041196284214756897333027 312061794426322135345999541)
      ·
        refine ⟨29255793227467700188687457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312061794426322135345999541 29255793227467700188687457)
        ·
          refine ⟨21941844920600775141515593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29255793227467700188687457 21941844920600775141515593)
          ·
            refine ⟨16456383690450581356136695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21941844920600775141515593 16456383690450581356136695)
            ·
              refine ⟨24684575535675872034205043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16456383690450581356136695 24684575535675872034205043)
              ·
                refine ⟨37026863303513808051307565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24684575535675872034205043 37026863303513808051307565)
                ·
                  refine ⟨13885073738817678019240337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37026863303513808051307565 13885073738817678019240337)
                  ·
                    refine ⟨10413805304113258514430253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13885073738817678019240337 10413805304113258514430253)
                    ·
                      refine ⟨3905176989042471942911345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10413805304113258514430253 3905176989042471942911345)
                      ·
                        rfl

theorem cell23_7605305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7605305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605305 prefixEnd_7605305 := by exact prefixLift 7605305
  have htrace : WordTrace (prefixWord ++ tailWord_7605305) baseStart_7605305 baseEnd_7605305 := by
    simpa [prefixWord, tailWord_7605305, baseEnd_7605305] using wordTrace_append hprefix tailTrace_7605305
  have hstable : (prefixWord ++ tailWord_7605305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605305).length < 2 ^ (prefixWord ++ tailWord_7605305).sum := by decide
  have hdescent : baseEnd_7605305 < baseStart_7605305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605331 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_7605331 : Nat := 118140960795 + 7605331 * 2 ^ 59
def prefixEnd_7605331 : Nat := 4983230072969 + 3 ^ 40 * 7605331 * 2
def baseEnd_7605331 : Nat := 3905190339539488841186225

theorem tailTrace_7605331 : CollatzResearch.WordTrace tailWord_7605331 prefixEnd_7605331 3905190339539488841186225 := by
  unfold tailWord_7605331
  simp only [CollatzResearch.WordTrace]
  refine ⟨277389210010192148970223847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184926140006794765980149231 277389210010192148970223847)
  ·
    refine ⟨416083815015288223455335771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277389210010192148970223847 416083815015288223455335771)
    ·
      refine ⟨624125722522932335183003657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416083815015288223455335771 624125722522932335183003657)
      ·
        refine ⟨468094291892199251387252743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624125722522932335183003657 468094291892199251387252743)
        ·
          refine ⟨702141437838298877080879115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468094291892199251387252743 702141437838298877080879115)
          ·
            refine ⟨1053212156757448315621318673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702141437838298877080879115 1053212156757448315621318673)
            ·
              refine ⟨789909117568086236715989005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1053212156757448315621318673 789909117568086236715989005)
              ·
                refine ⟨296215919088032338768495877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 789909117568086236715989005 296215919088032338768495877)
                ·
                  refine ⟨55540484829006063519092977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 296215919088032338768495877 55540484829006063519092977)
                  ·
                    refine ⟨41655363621754547639319733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55540484829006063519092977 41655363621754547639319733)
                    ·
                      refine ⟨3905190339539488841186225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41655363621754547639319733 3905190339539488841186225)
                      ·
                        rfl

theorem cell23_7605331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_7605331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605331 prefixEnd_7605331 := by exact prefixLift 7605331
  have htrace : WordTrace (prefixWord ++ tailWord_7605331) baseStart_7605331 baseEnd_7605331 := by
    simpa [prefixWord, tailWord_7605331, baseEnd_7605331] using wordTrace_append hprefix tailTrace_7605331
  have hstable : (prefixWord ++ tailWord_7605331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605331).length < 2 ^ (prefixWord ++ tailWord_7605331).sum := by decide
  have hdescent : baseEnd_7605331 < baseStart_7605331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605342 : List Nat := [4, 4, 1, 1, 1, 1, 3, 8]
def baseStart_7605342 : Nat := 118140960795 + 7605342 * 2 ^ 59
def prefixEnd_7605342 : Nat := 4983230072969 + 3 ^ 40 * 7605342 * 2
def baseEnd_7605342 : Nat := 144636888438025492524025

theorem tailTrace_7605342 : CollatzResearch.WordTrace tailWord_7605342 prefixEnd_7605342 144636888438025492524025 := by
  unfold tailWord_7605342
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673701401644037231109285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184926407475434865232582853 34673701401644037231109285)
  ·
    refine ⟨6501319012808256980832991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34673701401644037231109285 6501319012808256980832991)
    ·
      refine ⟨9751978519212385471249487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501319012808256980832991 9751978519212385471249487)
      ·
        refine ⟨14627967778818578206874231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751978519212385471249487 14627967778818578206874231)
        ·
          refine ⟨21941951668227867310311347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627967778818578206874231 21941951668227867310311347)
          ·
            refine ⟨32912927502341800965467021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21941951668227867310311347 32912927502341800965467021)
            ·
              refine ⟨12342347813378175362050133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32912927502341800965467021 12342347813378175362050133)
              ·
                refine ⟨144636888438025492524025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12342347813378175362050133 144636888438025492524025)
                ·
                  rfl

theorem cell23_7605342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_7605342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605342 prefixEnd_7605342 := by exact prefixLift 7605342
  have htrace : WordTrace (prefixWord ++ tailWord_7605342) baseStart_7605342 baseEnd_7605342 := by
    simpa [prefixWord, tailWord_7605342, baseEnd_7605342] using wordTrace_append hprefix tailTrace_7605342
  have hstable : (prefixWord ++ tailWord_7605342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605342).length < 2 ^ (prefixWord ++ tailWord_7605342).sum := by decide
  have hdescent : baseEnd_7605342 < baseStart_7605342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605345 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 3, 3, 2]
def baseStart_7605345 : Nat := 118140960795 + 7605345 * 2 ^ 59
def prefixEnd_7605345 : Nat := 4983230072969 + 3 ^ 40 * 7605345 * 2
def baseEnd_7605345 : Nat := 3905197528268651786411161

theorem tailTrace_7605345 : CollatzResearch.WordTrace tailWord_7605345 prefixEnd_7605345 3905197528268651786411161 := by
  unfold tailWord_7605345
  simp only [CollatzResearch.WordTrace]
  refine ⟨277389720632141429361233489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184926480421427619574155659 277389720632141429361233489)
  ·
    refine ⟨208042290474106072020925117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277389720632141429361233489 208042290474106072020925117)
    ·
      refine ⟨78015858927789777007846919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208042290474106072020925117 78015858927789777007846919)
      ·
        refine ⟨117023788391684665511770379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78015858927789777007846919 117023788391684665511770379)
        ·
          refine ⟨175535682587526998267655569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117023788391684665511770379 175535682587526998267655569)
          ·
            refine ⟨131651761940645248700741677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175535682587526998267655569 131651761940645248700741677)
            ·
              refine ⟨49369410727741968262778129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131651761940645248700741677 49369410727741968262778129)
              ·
                refine ⟨37027058045806476197083597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49369410727741968262778129 37027058045806476197083597)
                ·
                  refine ⟨13885146767177428573906349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37027058045806476197083597 13885146767177428573906349)
                  ·
                    refine ⟨5206930037691535715214881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13885146767177428573906349 5206930037691535715214881)
                    ·
                      refine ⟨3905197528268651786411161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206930037691535715214881 3905197528268651786411161)
                      ·
                        rfl

theorem cell23_7605345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_7605345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605345 prefixEnd_7605345 := by exact prefixLift 7605345
  have htrace : WordTrace (prefixWord ++ tailWord_7605345) baseStart_7605345 baseEnd_7605345 := by
    simpa [prefixWord, tailWord_7605345, baseEnd_7605345] using wordTrace_append hprefix tailTrace_7605345
  have hstable : (prefixWord ++ tailWord_7605345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605345).length < 2 ^ (prefixWord ++ tailWord_7605345).sum := by decide
  have hdescent : baseEnd_7605345 < baseStart_7605345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605362 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_7605362 : Nat := 118140960795 + 7605362 * 2 ^ 59
def prefixEnd_7605362 : Nat := 4983230072969 + 3 ^ 40 * 7605362 * 2
def baseEnd_7605362 : Nat := 3905206257439778219898583

theorem tailTrace_7605362 : CollatzResearch.WordTrace tailWord_7605362 prefixEnd_7605362 3905206257439778219898583 := by
  unfold tailWord_7605362
  simp only [CollatzResearch.WordTrace]
  refine ⟨69347585168269960316150585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184926893782053227509734893 69347585168269960316150585)
  ·
    refine ⟨52010688876202470237112939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69347585168269960316150585 52010688876202470237112939)
    ·
      refine ⟨78016033314303705355669409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52010688876202470237112939 78016033314303705355669409)
      ·
        refine ⟨58512024985727779016752057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78016033314303705355669409 58512024985727779016752057)
        ·
          refine ⟨43884018739295834262564043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58512024985727779016752057 43884018739295834262564043)
          ·
            refine ⟨65826028108943751393846065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43884018739295834262564043 65826028108943751393846065)
            ·
              refine ⟨49369521081707813545384549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65826028108943751393846065 49369521081707813545384549)
              ·
                refine ⟨9256785202820215039759603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49369521081707813545384549 9256785202820215039759603)
                ·
                  refine ⟨13885177804230322559639405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9256785202820215039759603 13885177804230322559639405)
                  ·
                    refine ⟨5206941676586370959864777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13885177804230322559639405 5206941676586370959864777)
                    ·
                      refine ⟨3905206257439778219898583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206941676586370959864777 3905206257439778219898583)
                      ·
                        rfl

theorem cell23_7605362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_7605362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605362 prefixEnd_7605362 := by exact prefixLift 7605362
  have htrace : WordTrace (prefixWord ++ tailWord_7605362) baseStart_7605362 baseEnd_7605362 := by
    simpa [prefixWord, tailWord_7605362, baseEnd_7605362] using wordTrace_append hprefix tailTrace_7605362
  have hstable : (prefixWord ++ tailWord_7605362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605362).length < 2 ^ (prefixWord ++ tailWord_7605362).sum := by decide
  have hdescent : baseEnd_7605362 < baseStart_7605362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605392 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2]
def baseStart_7605392 : Nat := 118140960795 + 7605392 * 2 ^ 59
def prefixEnd_7605392 : Nat := 4983230072969 + 3 ^ 40 * 7605392 * 2
def baseEnd_7605392 : Nat := 3905221661859413102523445

theorem tailTrace_7605392 : CollatzResearch.WordTrace tailWord_7605392 prefixEnd_7605392 3905221661859413102523445 := by
  unfold tailWord_7605392
  simp only [CollatzResearch.WordTrace]
  refine ⟨138695717431485578194097215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184927623241980770925462953 138695717431485578194097215)
  ·
    refine ⟨208043576147228367291145823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138695717431485578194097215 208043576147228367291145823)
    ·
      refine ⟨312065364220842550936718735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208043576147228367291145823 312065364220842550936718735)
      ·
        refine ⟨468098046331263826405078103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312065364220842550936718735 468098046331263826405078103)
        ·
          refine ⟨702147069496895739607617155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468098046331263826405078103 702147069496895739607617155)
          ·
            refine ⟨1053220604245343609411425733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702147069496895739607617155 1053220604245343609411425733)
            ·
              refine ⟨197478863296001926764642325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1053220604245343609411425733 197478863296001926764642325)
              ·
                refine ⟨9256821717000090317092609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197478863296001926764642325 9256821717000090317092609)
                ·
                  refine ⟨6942616287750067737819457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256821717000090317092609 6942616287750067737819457)
                  ·
                    refine ⟨5206962215812550803364593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942616287750067737819457 5206962215812550803364593)
                    ·
                      refine ⟨3905221661859413102523445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5206962215812550803364593 3905221661859413102523445)
                      ·
                        rfl

theorem cell23_7605392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 2, 2].length) (baseStart_7605392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605392 prefixEnd_7605392 := by exact prefixLift 7605392
  have htrace : WordTrace (prefixWord ++ tailWord_7605392) baseStart_7605392 baseEnd_7605392 := by
    simpa [prefixWord, tailWord_7605392, baseEnd_7605392] using wordTrace_append hprefix tailTrace_7605392
  have hstable : (prefixWord ++ tailWord_7605392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605392).length < 2 ^ (prefixWord ++ tailWord_7605392).sum := by decide
  have hdescent : baseEnd_7605392 < baseStart_7605392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605415 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 7]
def baseStart_7605415 : Nat := 118140960795 + 7605415 * 2 ^ 59
def prefixEnd_7605415 : Nat := 4983230072969 + 3 ^ 40 * 7605415 * 2
def baseEnd_7605415 : Nat := 433914830212718501392871

theorem tailTrace_7605415 : CollatzResearch.WordTrace tailWord_7605415 prefixEnd_7605415 433914830212718501392871 := by
  unfold tailWord_7605415
  simp only [CollatzResearch.WordTrace]
  refine ⟨277392273741887831316281699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184928182494591887544187799 277392273741887831316281699)
  ·
    refine ⟨416088410612831746974422549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277392273741887831316281699 416088410612831746974422549)
    ·
      refine ⟨19504144247476488139426057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 416088410612831746974422549 19504144247476488139426057)
      ·
        refine ⟨14628108185607366104569543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19504144247476488139426057 14628108185607366104569543)
        ·
          refine ⟨21942162278411049156854315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14628108185607366104569543 21942162278411049156854315)
          ·
            refine ⟨32913243417616573735281473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21942162278411049156854315 32913243417616573735281473)
            ·
              refine ⟨24684932563212430301461105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32913243417616573735281473 24684932563212430301461105)
              ·
                refine ⟨18513699422409322726095829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24684932563212430301461105 18513699422409322726095829)
                ·
                  refine ⟨433914830212718501392871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18513699422409322726095829 433914830212718501392871)
                  ·
                    rfl

theorem cell23_7605415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 7].length) (baseStart_7605415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605415 prefixEnd_7605415 := by exact prefixLift 7605415
  have htrace : WordTrace (prefixWord ++ tailWord_7605415) baseStart_7605415 baseEnd_7605415 := by
    simpa [prefixWord, tailWord_7605415, baseEnd_7605415] using wordTrace_append hprefix tailTrace_7605415
  have hstable : (prefixWord ++ tailWord_7605415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605415).length < 2 ^ (prefixWord ++ tailWord_7605415).sum := by decide
  have hdescent : baseEnd_7605415 < baseStart_7605415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605460 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_7605460 : Nat := 118140960795 + 7605460 * 2 ^ 59
def prefixEnd_7605460 : Nat := 4983230072969 + 3 ^ 40 * 7605460 * 2
def baseEnd_7605460 : Nat := 3905256578543918836473133

theorem tailTrace_7605460 : CollatzResearch.WordTrace tailWord_7605460 prefixEnd_7605460 3905256578543918836473133 := by
  unfold tailWord_7605460
  simp only [CollatzResearch.WordTrace]
  refine ⟨138696957513362402000834917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184929276684483202667779889 138696957513362402000834917)
  ·
    refine ⟨26005679533755450375156547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 138696957513362402000834917 26005679533755450375156547)
    ·
      refine ⟨39008519300633175562734821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26005679533755450375156547 39008519300633175562734821)
      ·
        refine ⟨7314097368868720418012779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39008519300633175562734821 7314097368868720418012779)
        ·
          refine ⟨10971146053303080627019169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314097368868720418012779 10971146053303080627019169)
          ·
            refine ⟨8228359539977310470264377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10971146053303080627019169 8228359539977310470264377)
            ·
              refine ⟨6171269654982982852698283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228359539977310470264377 6171269654982982852698283)
              ·
                refine ⟨9256904482474474279047425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171269654982982852698283 9256904482474474279047425)
                ·
                  refine ⟨6942678361855855709285569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256904482474474279047425 6942678361855855709285569)
                  ·
                    refine ⟨5207008771391891781964177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942678361855855709285569 5207008771391891781964177)
                    ·
                      refine ⟨3905256578543918836473133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207008771391891781964177 3905256578543918836473133)
                      ·
                        rfl

theorem cell23_7605460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_7605460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605460 prefixEnd_7605460 := by exact prefixLift 7605460
  have htrace : WordTrace (prefixWord ++ tailWord_7605460) baseStart_7605460 baseEnd_7605460 := by
    simpa [prefixWord, tailWord_7605460, baseEnd_7605460] using wordTrace_append hprefix tailTrace_7605460
  have hstable : (prefixWord ++ tailWord_7605460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605460).length < 2 ^ (prefixWord ++ tailWord_7605460).sum := by decide
  have hdescent : baseEnd_7605460 < baseStart_7605460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605465 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 6, 2]
def baseStart_7605465 : Nat := 118140960795 + 7605465 * 2 ^ 59
def prefixEnd_7605465 : Nat := 4983230072969 + 3 ^ 40 * 7605465 * 2
def baseEnd_7605465 : Nat := 3905259145947191316910609

theorem tailTrace_7605465 : CollatzResearch.WordTrace tailWord_7605465 prefixEnd_7605465 3905259145947191316910609 := by
  unfold tailWord_7605465
  simp only [CollatzResearch.WordTrace]
  refine ⟨277394097391706689855601849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184929398261137793237067899 277394097391706689855601849)
  ·
    refine ⟨208045573043780017391701387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277394097391706689855601849 208045573043780017391701387)
    ·
      refine ⟨312068359565670026087552081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208045573043780017391701387 312068359565670026087552081)
      ·
        refine ⟨234051269674252519565664061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312068359565670026087552081 234051269674252519565664061)
        ·
          refine ⟨87769226127844694837124023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234051269674252519565664061 87769226127844694837124023)
          ·
            refine ⟨131653839191767042255686035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87769226127844694837124023 131653839191767042255686035)
            ·
              refine ⟨197480758787650563383529053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131653839191767042255686035 197480758787650563383529053)
              ·
                refine ⟨74055284545368961268823395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 197480758787650563383529053 74055284545368961268823395)
                ·
                  refine ⟨111082926818053441903235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74055284545368961268823395 111082926818053441903235093)
                  ·
                    refine ⟨5207012194596255089214145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111082926818053441903235093 5207012194596255089214145)
                    ·
                      refine ⟨3905259145947191316910609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207012194596255089214145 3905259145947191316910609)
                      ·
                        rfl

theorem cell23_7605465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6, 2].length) (baseStart_7605465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605465 prefixEnd_7605465 := by exact prefixLift 7605465
  have htrace : WordTrace (prefixWord ++ tailWord_7605465) baseStart_7605465 baseEnd_7605465 := by
    simpa [prefixWord, tailWord_7605465, baseEnd_7605465] using wordTrace_append hprefix tailTrace_7605465
  have hstable : (prefixWord ++ tailWord_7605465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605465).length < 2 ^ (prefixWord ++ tailWord_7605465).sum := by decide
  have hdescent : baseEnd_7605465 < baseStart_7605465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605482 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_7605482 : Nat := 118140960795 + 7605482 * 2 ^ 59
def prefixEnd_7605482 : Nat := 4983230072969 + 3 ^ 40 * 7605482 * 2
def baseEnd_7605482 : Nat := 3905267875118317750398031

theorem tailTrace_7605482 : CollatzResearch.WordTrace tailWord_7605482 prefixEnd_7605482 3905267875118317750398031 := by
  unfold tailWord_7605482
  simp only [CollatzResearch.WordTrace]
  refine ⟨69348679358161275439742675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184929811621763401172647133 69348679358161275439742675)
  ·
    refine ⟨104023019037241913159614013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69348679358161275439742675 104023019037241913159614013)
    ·
      refine ⟨39008632138965717434855255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104023019037241913159614013 39008632138965717434855255)
      ·
        refine ⟨58512948208448576152282883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39008632138965717434855255 58512948208448576152282883)
        ·
          refine ⟨87769422312672864228424325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58512948208448576152282883 87769422312672864228424325)
          ·
            refine ⟨16456766683626162042829561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87769422312672864228424325 16456766683626162042829561)
            ·
              refine ⟨12342575012719621532122171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16456766683626162042829561 12342575012719621532122171)
              ·
                refine ⟨18513862519079432298183257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342575012719621532122171 18513862519079432298183257)
                ·
                  refine ⟨13885396889309574223637443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513862519079432298183257 13885396889309574223637443)
                  ·
                    refine ⟨20828095333964361335456165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13885396889309574223637443 20828095333964361335456165)
                    ·
                      refine ⟨3905267875118317750398031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20828095333964361335456165 3905267875118317750398031)
                      ·
                        rfl

theorem cell23_7605482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_7605482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605482 prefixEnd_7605482 := by exact prefixLift 7605482
  have htrace : WordTrace (prefixWord ++ tailWord_7605482) baseStart_7605482 baseEnd_7605482 := by
    simpa [prefixWord, tailWord_7605482, baseEnd_7605482] using wordTrace_append hprefix tailTrace_7605482
  have hstable : (prefixWord ++ tailWord_7605482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605482).length < 2 ^ (prefixWord ++ tailWord_7605482).sum := by decide
  have hdescent : baseEnd_7605482 < baseStart_7605482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605505 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 6]
def baseStart_7605505 : Nat := 118140960795 + 7605505 * 2 ^ 59
def prefixEnd_7605505 : Nat := 4983230072969 + 3 ^ 40 * 7605505 * 2
def baseEnd_7605505 : Nat := 433919965019263462267825

theorem tailTrace_7605505 : CollatzResearch.WordTrace tailWord_7605505 prefixEnd_7605505 433919965019263462267825 := by
  unfold tailWord_7605505
  simp only [CollatzResearch.WordTrace]
  refine ⟨277395556311561776687057969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184930370874374517791371979 277395556311561776687057969)
  ·
    refine ⟨208046667233671332515293477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277395556311561776687057969 208046667233671332515293477)
    ·
      refine ⟨39008750106313374846617527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208046667233671332515293477 39008750106313374846617527)
      ·
        refine ⟨58513125159470062269926291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39008750106313374846617527 58513125159470062269926291)
        ·
          refine ⟨87769687739205093404889437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58513125159470062269926291 87769687739205093404889437)
          ·
            refine ⟨32913632902201910026833539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87769687739205093404889437 32913632902201910026833539)
            ·
              refine ⟨49370449353302865040250309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32913632902201910026833539 49370449353302865040250309)
              ·
                refine ⟨9256959253744287195046933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49370449353302865040250309 9256959253744287195046933)
                ·
                  refine ⟨433919965019263462267825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9256959253744287195046933 433919965019263462267825)
                  ·
                    rfl

theorem cell23_7605505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 6].length) (baseStart_7605505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605505 prefixEnd_7605505 := by exact prefixLift 7605505
  have htrace : WordTrace (prefixWord ++ tailWord_7605505) baseStart_7605505 baseEnd_7605505 := by
    simpa [prefixWord, tailWord_7605505, baseEnd_7605505] using wordTrace_append hprefix tailTrace_7605505
  have hstable : (prefixWord ++ tailWord_7605505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605505).length < 2 ^ (prefixWord ++ tailWord_7605505).sum := by decide
  have hdescent : baseEnd_7605505 < baseStart_7605505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605532 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_7605532 : Nat := 118140960795 + 7605532 * 2 ^ 59
def prefixEnd_7605532 : Nat := 4983230072969 + 3 ^ 40 * 7605532 * 2
def baseEnd_7605532 : Nat := 3905293549151042554772801

theorem tailTrace_7605532 : CollatzResearch.WordTrace tailWord_7605532 prefixEnd_7605532 3905293549151042554772801 := by
  unfold tailWord_7605532
  simp only [CollatzResearch.WordTrace]
  refine ⟨138698270541231980149145425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184931027388309306865527233 138698270541231980149145425)
  ·
    refine ⟨104023702905923985111859069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138698270541231980149145425 104023702905923985111859069)
    ·
      refine ⟨39008888589721494416947151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104023702905923985111859069 39008888589721494416947151)
      ·
        refine ⟨58513332884582241625420727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39008888589721494416947151 58513332884582241625420727)
        ·
          refine ⟨87769999326873362438131091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58513332884582241625420727 87769999326873362438131091)
          ·
            refine ⟨131654998990310043657196637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87769999326873362438131091 131654998990310043657196637)
            ·
              refine ⟨49370624621366266371448739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131654998990310043657196637 49370624621366266371448739)
              ·
                refine ⟨74055936932049399557173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49370624621366266371448739 74055936932049399557173109)
                ·
                  refine ⟨6942744087379631208484979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74055936932049399557173109 6942744087379631208484979)
                  ·
                    refine ⟨10414116131069446812727469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942744087379631208484979 10414116131069446812727469)
                    ·
                      refine ⟨3905293549151042554772801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10414116131069446812727469 3905293549151042554772801)
                      ·
                        rfl

theorem cell23_7605532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_7605532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605532 prefixEnd_7605532 := by exact prefixLift 7605532
  have htrace : WordTrace (prefixWord ++ tailWord_7605532) baseStart_7605532 baseEnd_7605532 := by
    simpa [prefixWord, tailWord_7605532, baseEnd_7605532] using wordTrace_append hprefix tailTrace_7605532
  have hstable : (prefixWord ++ tailWord_7605532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605532).length < 2 ^ (prefixWord ++ tailWord_7605532).sum := by decide
  have hdescent : baseEnd_7605532 < baseStart_7605532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605536 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7605536 : Nat := 118140960795 + 7605536 * 2 ^ 59
def prefixEnd_7605536 : Nat := 4983230072969 + 3 ^ 40 * 7605536 * 2
def baseEnd_7605536 : Nat := 3905295603073660539122783

theorem tailTrace_7605536 : CollatzResearch.WordTrace tailWord_7605536 prefixEnd_7605536 3905295603073660539122783 := by
  unfold tailWord_7605536
  simp only [CollatzResearch.WordTrace]
  refine ⟨138698343487224734490718231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184931124649632979320957641 138698343487224734490718231)
  ·
    refine ⟨208047515230837101736077347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138698343487224734490718231 208047515230837101736077347)
    ·
      refine ⟨312071272846255652604116021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208047515230837101736077347 312071272846255652604116021)
      ·
        refine ⟨29256681829336467431635877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 312071272846255652604116021 29256681829336467431635877)
        ·
          refine ⟨5485627843000587643431727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29256681829336467431635877 5485627843000587643431727)
          ·
            refine ⟨8228441764500881465147591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485627843000587643431727 8228441764500881465147591)
            ·
              refine ⟨12342662646751322197721387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8228441764500881465147591 12342662646751322197721387)
              ·
                refine ⟨18513993970126983296582081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12342662646751322197721387 18513993970126983296582081)
                ·
                  refine ⟨13885495477595237472436561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18513993970126983296582081 13885495477595237472436561)
                  ·
                    refine ⟨10414121608196428104327421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13885495477595237472436561 10414121608196428104327421)
                    ·
                      refine ⟨3905295603073660539122783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10414121608196428104327421 3905295603073660539122783)
                      ·
                        rfl

theorem cell23_7605536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7605536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605536 prefixEnd_7605536 := by exact prefixLift 7605536
  have htrace : WordTrace (prefixWord ++ tailWord_7605536) baseStart_7605536 baseEnd_7605536 := by
    simpa [prefixWord, tailWord_7605536, baseEnd_7605536] using wordTrace_append hprefix tailTrace_7605536
  have hstable : (prefixWord ++ tailWord_7605536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605536).length < 2 ^ (prefixWord ++ tailWord_7605536).sum := by decide
  have hdescent : baseEnd_7605536 < baseStart_7605536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605566 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_7605566 : Nat := 118140960795 + 7605566 * 2 ^ 59
def prefixEnd_7605566 : Nat := 4983230072969 + 3 ^ 40 * 7605566 * 2
def baseEnd_7605566 : Nat := 3905311007493295421747645

theorem tailTrace_7605566 : CollatzResearch.WordTrace tailWord_7605566 prefixEnd_7605566 3905311007493295421747645 := by
  unfold tailWord_7605566
  simp only [CollatzResearch.WordTrace]
  refine ⟨34674722645542598013128569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184931854109560522736685701 34674722645542598013128569)
  ·
    refine ⟨26006041984156948509846427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34674722645542598013128569 26006041984156948509846427)
    ·
      refine ⟨39009062976235422764769641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26006041984156948509846427 39009062976235422764769641)
      ·
        refine ⟨29256797232176567073577231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39009062976235422764769641 29256797232176567073577231)
        ·
          refine ⟨43885195848264850610365847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29256797232176567073577231 43885195848264850610365847)
          ·
            refine ⟨65827793772397275915548771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43885195848264850610365847 65827793772397275915548771)
            ·
              refine ⟨98741690658595913873323157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65827793772397275915548771 98741690658595913873323157)
              ·
                refine ⟨4628516749621683462812023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 98741690658595913873323157 4628516749621683462812023)
                ·
                  refine ⟨6942775124432525194218035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628516749621683462812023 6942775124432525194218035)
                  ·
                    refine ⟨10414162686648787791327053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6942775124432525194218035 10414162686648787791327053)
                    ·
                      refine ⟨3905311007493295421747645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10414162686648787791327053 3905311007493295421747645)
                      ·
                        rfl

theorem cell23_7605566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_7605566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605566 prefixEnd_7605566 := by exact prefixLift 7605566
  have htrace : WordTrace (prefixWord ++ tailWord_7605566) baseStart_7605566 baseEnd_7605566 := by
    simpa [prefixWord, tailWord_7605566, baseEnd_7605566] using wordTrace_append hprefix tailTrace_7605566
  have hstable : (prefixWord ++ tailWord_7605566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605566).length < 2 ^ (prefixWord ++ tailWord_7605566).sum := by decide
  have hdescent : baseEnd_7605566 < baseStart_7605566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605575 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_7605575 : Nat := 118140960795 + 7605575 * 2 ^ 59
def prefixEnd_7605575 : Nat := 4983230072969 + 3 ^ 40 * 7605575 * 2
def baseEnd_7605575 : Nat := 3905315628819185886535103

theorem tailTrace_7605575 : CollatzResearch.WordTrace tailWord_7605575 prefixEnd_7605575 3905315628819185886535103 := by
  unfold tailWord_7605575
  simp only [CollatzResearch.WordTrace]
  refine ⟨277398109421308178642106179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184932072947538785761404119 277398109421308178642106179)
  ·
    refine ⟨416097164131962267963159269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277398109421308178642106179 416097164131962267963159269)
    ·
      refine ⟨78018218274742925243092363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416097164131962267963159269 78018218274742925243092363)
      ·
        refine ⟨117027327412114387864638545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78018218274742925243092363 117027327412114387864638545)
        ·
          refine ⟨87770495559085790898478909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117027327412114387864638545 87770495559085790898478909)
          ·
            refine ⟨32913935834657171586929591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87770495559085790898478909 32913935834657171586929591)
            ·
              refine ⟨49370903751985757380394387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32913935834657171586929591 49370903751985757380394387)
              ·
                refine ⟨74056355627978636070591581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49370903751985757380394387 74056355627978636070591581)
                ·
                  refine ⟨27771133360491988526471843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74056355627978636070591581 27771133360491988526471843)
                  ·
                    refine ⟨41656700040737982789707765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27771133360491988526471843 41656700040737982789707765)
                    ·
                      refine ⟨3905315628819185886535103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41656700040737982789707765 3905315628819185886535103)
                      ·
                        rfl

theorem cell23_7605575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_7605575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605575 prefixEnd_7605575 := by exact prefixLift 7605575
  have htrace : WordTrace (prefixWord ++ tailWord_7605575) baseStart_7605575 baseEnd_7605575 := by
    simpa [prefixWord, tailWord_7605575, baseEnd_7605575] using wordTrace_append hprefix tailTrace_7605575
  have hstable : (prefixWord ++ tailWord_7605575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605575).length < 2 ^ (prefixWord ++ tailWord_7605575).sum := by decide
  have hdescent : baseEnd_7605575 < baseStart_7605575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605585 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 6]
def baseStart_7605585 : Nat := 118140960795 + 7605585 * 2 ^ 59
def prefixEnd_7605585 : Nat := 4983230072969 + 3 ^ 40 * 7605585 * 2
def baseEnd_7605585 : Nat := 3905320763625730847410057

theorem tailTrace_7605585 : CollatzResearch.WordTrace tailWord_7605585 prefixEnd_7605585 3905320763625730847410057 := by
  unfold tailWord_7605585
  simp only [CollatzResearch.WordTrace]
  refine ⟨277398474151271950349970209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184932316100847966899980139 277398474151271950349970209)
  ·
    refine ⟨208048855613453962762477657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277398474151271950349970209 208048855613453962762477657)
    ·
      refine ⟨156036641710090472071858243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208048855613453962762477657 156036641710090472071858243)
      ·
        refine ⟨234054962565135708107787365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156036641710090472071858243 234054962565135708107787365)
        ·
          refine ⟨43885305480962945270210131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 234054962565135708107787365 43885305480962945270210131)
          ·
            refine ⟨65827958221444417905315197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43885305480962945270210131 65827958221444417905315197)
            ·
              refine ⟨24685484333041656714493199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65827958221444417905315197 24685484333041656714493199)
              ·
                refine ⟨37028226499562485071739799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24685484333041656714493199 37028226499562485071739799)
                ·
                  refine ⟨55542339749343727607609699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37028226499562485071739799 55542339749343727607609699)
                  ·
                    refine ⟨83313509624015591411414549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55542339749343727607609699 83313509624015591411414549)
                    ·
                      refine ⟨3905320763625730847410057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 83313509624015591411414549 3905320763625730847410057)
                      ·
                        rfl

theorem cell23_7605585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_7605585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605585 prefixEnd_7605585 := by exact prefixLift 7605585
  have htrace : WordTrace (prefixWord ++ tailWord_7605585) baseStart_7605585 baseEnd_7605585 := by
    simpa [prefixWord, tailWord_7605585, baseEnd_7605585] using wordTrace_append hprefix tailTrace_7605585
  have hstable : (prefixWord ++ tailWord_7605585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605585).length < 2 ^ (prefixWord ++ tailWord_7605585).sum := by decide
  have hdescent : baseEnd_7605585 < baseStart_7605585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605589 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_7605589 : Nat := 118140960795 + 7605589 * 2 ^ 59
def prefixEnd_7605589 : Nat := 4983230072969 + 3 ^ 40 * 7605589 * 2
def baseEnd_7605589 : Nat := 3905322817548348831760039

theorem tailTrace_7605589 : CollatzResearch.WordTrace tailWord_7605589 prefixEnd_7605589 3905322817548348831760039 := by
  unfold tailWord_7605589
  simp only [CollatzResearch.WordTrace]
  refine ⟨277398620043257459033115821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184932413362171639355410547 277398620043257459033115821)
  ·
    refine ⟨104024482516221547137418433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277398620043257459033115821 104024482516221547137418433)
    ·
      refine ⟨78018361887166160353063825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104024482516221547137418433 78018361887166160353063825)
      ·
        refine ⟨58513771415374620264797869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78018361887166160353063825 58513771415374620264797869)
        ·
          refine ⟨21942664280765482599299201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58513771415374620264797869 21942664280765482599299201)
          ·
            refine ⟨16456998210574111949474401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21942664280765482599299201 16456998210574111949474401)
            ·
              refine ⟨12342748657930583962105801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16456998210574111949474401 12342748657930583962105801)
              ·
                refine ⟨9257061493447937971579351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12342748657930583962105801 9257061493447937971579351)
                ·
                  refine ⟨13885592240171906957369027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257061493447937971579351 13885592240171906957369027)
                  ·
                    refine ⟨20828388360257860436053541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13885592240171906957369027 20828388360257860436053541)
                    ·
                      refine ⟨3905322817548348831760039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20828388360257860436053541 3905322817548348831760039)
                      ·
                        rfl

theorem cell23_7605589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_7605589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605589 prefixEnd_7605589 := by exact prefixLift 7605589
  have htrace : WordTrace (prefixWord ++ tailWord_7605589) baseStart_7605589 baseEnd_7605589 := by
    simpa [prefixWord, tailWord_7605589, baseEnd_7605589] using wordTrace_append hprefix tailTrace_7605589
  have hstable : (prefixWord ++ tailWord_7605589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605589).length < 2 ^ (prefixWord ++ tailWord_7605589).sum := by decide
  have hdescent : baseEnd_7605589 < baseStart_7605589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605602 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7605602 : Nat := 118140960795 + 7605602 * 2 ^ 59
def prefixEnd_7605602 : Nat := 4983230072969 + 3 ^ 40 * 7605602 * 2
def baseEnd_7605602 : Nat := 3905329492796857280897479

theorem tailTrace_7605602 : CollatzResearch.WordTrace tailWord_7605602 prefixEnd_7605602 3905329492796857280897479 := by
  unfold tailWord_7605602
  simp only [CollatzResearch.WordTrace]
  refine ⟨69349773548052590563334765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184932729461473574835559373 69349773548052590563334765)
  ·
    refine ⟨26006165080519721461250537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69349773548052590563334765 26006165080519721461250537)
    ·
      refine ⟨19504623810389791095937903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26006165080519721461250537 19504623810389791095937903)
      ·
        refine ⟨29256935715584686643906855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19504623810389791095937903 29256935715584686643906855)
        ·
          refine ⟨43885403573377029965860283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29256935715584686643906855 43885403573377029965860283)
          ·
            refine ⟨65828105360065544948790425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43885403573377029965860283 65828105360065544948790425)
            ·
              refine ⟨49371079020049158711592819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65828105360065544948790425 49371079020049158711592819)
              ·
                refine ⟨74056618530073738067389229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49371079020049158711592819 74056618530073738067389229)
                ·
                  refine ⟨27771231948777651775270961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74056618530073738067389229 27771231948777651775270961)
                  ·
                    refine ⟨20828423961583238831453221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27771231948777651775270961 20828423961583238831453221)
                    ·
                      refine ⟨3905329492796857280897479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20828423961583238831453221 3905329492796857280897479)
                      ·
                        rfl

theorem cell23_7605602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7605602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605602 prefixEnd_7605602 := by exact prefixLift 7605602
  have htrace : WordTrace (prefixWord ++ tailWord_7605602) baseStart_7605602 baseEnd_7605602 := by
    simpa [prefixWord, tailWord_7605602, baseEnd_7605602] using wordTrace_append hprefix tailTrace_7605602
  have hstable : (prefixWord ++ tailWord_7605602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605602).length < 2 ^ (prefixWord ++ tailWord_7605602).sum := by decide
  have hdescent : baseEnd_7605602 < baseStart_7605602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605623 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_7605623 : Nat := 118140960795 + 7605623 * 2 ^ 59
def prefixEnd_7605623 : Nat := 4983230072969 + 3 ^ 40 * 7605623 * 2
def baseEnd_7605623 : Nat := 3905340275890601698734883

theorem tailTrace_7605623 : CollatzResearch.WordTrace tailWord_7605623 prefixEnd_7605623 3905340275890601698734883 := by
  unfold tailWord_7605623
  simp only [CollatzResearch.WordTrace]
  refine ⟨277399860125134282839853523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184933240083422855226569015 277399860125134282839853523)
  ·
    refine ⟨416099790187701424259780285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277399860125134282839853523 416099790187701424259780285)
    ·
      refine ⟨156037421320388034097417607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416099790187701424259780285 156037421320388034097417607)
      ·
        refine ⟨234056131980582051146126411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156037421320388034097417607 234056131980582051146126411)
        ·
          refine ⟨351084197970873076719189617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234056131980582051146126411 351084197970873076719189617)
          ·
            refine ⟨263313148478154807539392213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351084197970873076719189617 263313148478154807539392213)
            ·
              refine ⟨6171401917456753301704505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 263313148478154807539392213 6171401917456753301704505)
              ·
                refine ⟨4628551438092564976278379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6171401917456753301704505 4628551438092564976278379)
                ·
                  refine ⟨6942827157138847464417569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4628551438092564976278379 6942827157138847464417569)
                  ·
                    refine ⟨5207120367854135598313177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942827157138847464417569 5207120367854135598313177)
                    ·
                      refine ⟨3905340275890601698734883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207120367854135598313177 3905340275890601698734883)
                      ·
                        rfl

theorem cell23_7605623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_7605623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605623 prefixEnd_7605623 := by exact prefixLift 7605623
  have htrace : WordTrace (prefixWord ++ tailWord_7605623) baseStart_7605623 baseEnd_7605623 := by
    simpa [prefixWord, tailWord_7605623, baseEnd_7605623] using wordTrace_append hprefix tailTrace_7605623
  have hstable : (prefixWord ++ tailWord_7605623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605623).length < 2 ^ (prefixWord ++ tailWord_7605623).sum := by decide
  have hdescent : baseEnd_7605623 < baseStart_7605623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605633 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 2, 4]
def baseStart_7605633 : Nat := 118140960795 + 7605633 * 2 ^ 59
def prefixEnd_7605633 : Nat := 4983230072969 + 3 ^ 40 * 7605633 * 2
def baseEnd_7605633 : Nat := 1301781803565715553203279

theorem tailTrace_7605633 : CollatzResearch.WordTrace tailWord_7605633 prefixEnd_7605633 1301781803565715553203279 := by
  unfold tailWord_7605633
  simp only [CollatzResearch.WordTrace]
  refine ⟨277400224855098054547717553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184933483236732036365145035 277400224855098054547717553)
  ·
    refine ⟨208050168641323540910788165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277400224855098054547717553 208050168641323540910788165)
    ·
      refine ⟨39009406620248163920772781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208050168641323540910788165 39009406620248163920772781)
      ·
        refine ⟨14628527482593061470289793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39009406620248163920772781 14628527482593061470289793)
        ·
          refine ⟨10971395611944796102717345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14628527482593061470289793 10971395611944796102717345)
          ·
            refine ⟨8228546708958597077038009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10971395611944796102717345 8228546708958597077038009)
            ·
              refine ⟨6171410031718947807778507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8228546708958597077038009 6171410031718947807778507)
              ·
                refine ⟨9257115047578421711667761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171410031718947807778507 9257115047578421711667761)
                ·
                  refine ⟨6942836285683816283750821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9257115047578421711667761 6942836285683816283750821)
                  ·
                    refine ⟨1301781803565715553203279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6942836285683816283750821 1301781803565715553203279)
                    ·
                      rfl

theorem cell23_7605633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_7605633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605633 prefixEnd_7605633 := by exact prefixLift 7605633
  have htrace : WordTrace (prefixWord ++ tailWord_7605633) baseStart_7605633 baseEnd_7605633 := by
    simpa [prefixWord, tailWord_7605633, baseEnd_7605633] using wordTrace_append hprefix tailTrace_7605633
  have hstable : (prefixWord ++ tailWord_7605633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605633).length < 2 ^ (prefixWord ++ tailWord_7605633).sum := by decide
  have hdescent : baseEnd_7605633 < baseStart_7605633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605655 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 4, 6]
def baseStart_7605655 : Nat := 118140960795 + 7605655 * 2 ^ 59
def prefixEnd_7605655 : Nat := 4983230072969 + 3 ^ 40 * 7605655 * 2
def baseEnd_7605655 : Nat := 1301785569090515191178245

theorem tailTrace_7605655 : CollatzResearch.WordTrace tailWord_7605655 prefixEnd_7605655 1301785569090515191178245 := by
  unfold tailWord_7605655
  simp only [CollatzResearch.WordTrace]
  refine ⟨277401027261018352305018419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184934018174012234870012279 277401027261018352305018419)
  ·
    refine ⟨416101540891527528457527629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277401027261018352305018419 416101540891527528457527629)
    ·
      refine ⟨156038077834322823171572861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 416101540891527528457527629 156038077834322823171572861)
      ·
        refine ⟨58514279187871058689339823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156038077834322823171572861 58514279187871058689339823)
        ·
          refine ⟨87771418781806588034009735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58514279187871058689339823 87771418781806588034009735)
          ·
            refine ⟨131657128172709882051014603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87771418781806588034009735 131657128172709882051014603)
            ·
              refine ⟨197485692259064823076521905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131657128172709882051014603 197485692259064823076521905)
              ·
                refine ⟨148114269194298617307391429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 197485692259064823076521905 148114269194298617307391429)
                ·
                  refine ⟨27771425473930990745135893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 148114269194298617307391429 27771425473930990745135893)
                  ·
                    refine ⟨1301785569090515191178245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27771425473930990745135893 1301785569090515191178245)
                    ·
                      rfl

theorem cell23_7605655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_7605655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605655 prefixEnd_7605655 := by exact prefixLift 7605655
  have htrace : WordTrace (prefixWord ++ tailWord_7605655) baseStart_7605655 baseEnd_7605655 := by
    simpa [prefixWord, tailWord_7605655, baseEnd_7605655] using wordTrace_append hprefix tailTrace_7605655
  have hstable : (prefixWord ++ tailWord_7605655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605655).length < 2 ^ (prefixWord ++ tailWord_7605655).sum := by decide
  have hdescent : baseEnd_7605655 < baseStart_7605655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605679 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 4, 2, 2]
def baseStart_7605679 : Nat := 118140960795 + 7605679 * 2 ^ 59
def prefixEnd_7605679 : Nat := 4983230072969 + 3 ^ 40 * 7605679 * 2
def baseEnd_7605679 : Nat := 3905369030807253479634625

theorem tailTrace_7605679 : CollatzResearch.WordTrace tailWord_7605679 prefixEnd_7605679 3905369030807253479634625 := by
  unfold tailWord_7605679
  simp only [CollatzResearch.WordTrace]
  refine ⟨277401902612931404403892091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184934601741954269602594727 277401902612931404403892091)
  ·
    refine ⟨416102853919397106605838137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277401902612931404403892091 416102853919397106605838137)
    ·
      refine ⟨312077140439547829954378603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 416102853919397106605838137 312077140439547829954378603)
      ·
        refine ⟨468115710659321744931567905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312077140439547829954378603 468115710659321744931567905)
        ·
          refine ⟨351086782994491308698675929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468115710659321744931567905 351086782994491308698675929)
          ·
            refine ⟨263315087245868481524006947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351086782994491308698675929 263315087245868481524006947)
            ·
              refine ⟨394972630868802722286010421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263315087245868481524006947 394972630868802722286010421)
              ·
                refine ⟨37028684143950255214313477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394972630868802722286010421 37028684143950255214313477)
                ·
                  refine ⟨6942878276990672852683777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37028684143950255214313477 6942878276990672852683777)
                  ·
                    refine ⟨5207158707743004639512833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942878276990672852683777 5207158707743004639512833)
                    ·
                      refine ⟨3905369030807253479634625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207158707743004639512833 3905369030807253479634625)
                      ·
                        rfl

theorem cell23_7605679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 2, 2].length) (baseStart_7605679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605679 prefixEnd_7605679 := by exact prefixLift 7605679
  have htrace : WordTrace (prefixWord ++ tailWord_7605679) baseStart_7605679 baseEnd_7605679 := by
    simpa [prefixWord, tailWord_7605679, baseEnd_7605679] using wordTrace_append hprefix tailTrace_7605679
  have hstable : (prefixWord ++ tailWord_7605679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605679).length < 2 ^ (prefixWord ++ tailWord_7605679).sum := by decide
  have hdescent : baseEnd_7605679 < baseStart_7605679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605696 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2]
def baseStart_7605696 : Nat := 118140960795 + 7605696 * 2 ^ 59
def prefixEnd_7605696 : Nat := 4983230072969 + 3 ^ 40 * 7605696 * 2
def baseEnd_7605696 : Nat := 3905377759978379913122047

theorem tailTrace_7605696 : CollatzResearch.WordTrace tailWord_7605696 prefixEnd_7605696 3905377759978379913122047 := by
  unfold tailWord_7605696
  simp only [CollatzResearch.WordTrace]
  refine ⟨138701261326934908153630471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184935015102579877538173961 138701261326934908153630471)
  ·
    refine ⟨208051891990402362230445707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138701261326934908153630471 208051891990402362230445707)
    ·
      refine ⟨312077837985603543345668561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208051891990402362230445707 312077837985603543345668561)
      ·
        refine ⟨234058378489202657509251421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 312077837985603543345668561 234058378489202657509251421)
        ·
          refine ⟨87771891933450996565969283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234058378489202657509251421 87771891933450996565969283)
          ·
            refine ⟨131657837900176494848953925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87771891933450996565969283 131657837900176494848953925)
            ·
              refine ⟨24685844606283092784178861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131657837900176494848953925 24685844606283092784178861)
              ·
                refine ⟨9257191727356159794067073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24685844606283092784178861 9257191727356159794067073)
                ·
                  refine ⟨6942893795517119845550305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9257191727356159794067073 6942893795517119845550305)
                  ·
                    refine ⟨5207170346637839884162729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6942893795517119845550305 5207170346637839884162729)
                    ·
                      refine ⟨3905377759978379913122047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207170346637839884162729 3905377759978379913122047)
                      ·
                        rfl

theorem cell23_7605696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_7605696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605696 prefixEnd_7605696 := by exact prefixLift 7605696
  have htrace : WordTrace (prefixWord ++ tailWord_7605696) baseStart_7605696 baseEnd_7605696 := by
    simpa [prefixWord, tailWord_7605696, baseEnd_7605696] using wordTrace_append hprefix tailTrace_7605696
  have hstable : (prefixWord ++ tailWord_7605696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605696).length < 2 ^ (prefixWord ++ tailWord_7605696).sum := by decide
  have hdescent : baseEnd_7605696 < baseStart_7605696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605732 : List Nat := [2, 3, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_7605732 : Nat := 118140960795 + 7605732 * 2 ^ 59
def prefixEnd_7605732 : Nat := 4983230072969 + 3 ^ 40 * 7605732 * 2
def baseEnd_7605732 : Nat := 1301798748427313924090627

theorem tailTrace_7605732 : CollatzResearch.WordTrace tailWord_7605732 prefixEnd_7605732 1301798748427313924090627 := by
  unfold tailWord_7605732
  simp only [CollatzResearch.WordTrace]
  refine ⟨138701917840869697227785725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184935890454492929637047633 138701917840869697227785725)
  ·
    refine ⟨52013219190326136460419647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138701917840869697227785725 52013219190326136460419647)
    ·
      refine ⟨78019828785489204690629471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52013219190326136460419647 78019828785489204690629471)
      ·
        refine ⟨117029743178233807035944207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78019828785489204690629471 117029743178233807035944207)
        ·
          refine ⟨175544614767350710553916311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117029743178233807035944207 175544614767350710553916311)
          ·
            refine ⟨263316922151026065830874467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175544614767350710553916311 263316922151026065830874467)
            ·
              refine ⟨394975383226539098746311701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263316922151026065830874467 394975383226539098746311701)
              ·
                refine ⟨18514471088744020253733361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 394975383226539098746311701 18514471088744020253733361)
                ·
                  refine ⟨13885853316558015190300021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18514471088744020253733361 13885853316558015190300021)
                  ·
                    refine ⟨1301798748427313924090627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13885853316558015190300021 1301798748427313924090627)
                    ·
                      rfl

theorem cell23_7605732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_7605732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605732 prefixEnd_7605732 := by exact prefixLift 7605732
  have htrace : WordTrace (prefixWord ++ tailWord_7605732) baseStart_7605732 baseEnd_7605732 := by
    simpa [prefixWord, tailWord_7605732, baseEnd_7605732] using wordTrace_append hprefix tailTrace_7605732
  have hstable : (prefixWord ++ tailWord_7605732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605732).length < 2 ^ (prefixWord ++ tailWord_7605732).sum := by decide
  have hdescent : baseEnd_7605732 < baseStart_7605732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605742 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7605742 : Nat := 118140960795 + 7605742 * 2 ^ 59
def prefixEnd_7605742 : Nat := 4983230072969 + 3 ^ 40 * 7605742 * 2
def baseEnd_7605742 : Nat := 3905401380088486733146835

theorem tailTrace_7605742 : CollatzResearch.WordTrace tailWord_7605742 prefixEnd_7605742 3905401380088486733146835 := by
  unfold tailWord_7605742
  simp only [CollatzResearch.WordTrace]
  refine ⟨34675525051462895770429435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184936133607802110775623653 34675525051462895770429435)
  ·
    refine ⟨52013287577194343655644153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34675525051462895770429435 52013287577194343655644153)
    ·
      refine ⟨39009965682895757741733115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52013287577194343655644153 39009965682895757741733115)
      ·
        refine ⟨58514948524343636612599673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39009965682895757741733115 58514948524343636612599673)
        ·
          refine ⟨43886211393257727459449755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58514948524343636612599673 43886211393257727459449755)
          ·
            refine ⟨65829317089886591189174633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43886211393257727459449755 65829317089886591189174633)
            ·
              refine ⟨49371987817414943391880975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65829317089886591189174633 49371987817414943391880975)
              ·
                refine ⟨74057981726122415087821463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49371987817414943391880975 74057981726122415087821463)
                ·
                  refine ⟨111086972589183622631732195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74057981726122415087821463 111086972589183622631732195)
                  ·
                    refine ⟨166630458883775433947598293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111086972589183622631732195 166630458883775433947598293)
                    ·
                      refine ⟨3905401380088486733146835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166630458883775433947598293 3905401380088486733146835)
                      ·
                        rfl

theorem cell23_7605742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7605742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605742 prefixEnd_7605742 := by exact prefixLift 7605742
  have htrace : WordTrace (prefixWord ++ tailWord_7605742) baseStart_7605742 baseEnd_7605742 := by
    simpa [prefixWord, tailWord_7605742, baseEnd_7605742] using wordTrace_append hprefix tailTrace_7605742
  have hstable : (prefixWord ++ tailWord_7605742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605742).length < 2 ^ (prefixWord ++ tailWord_7605742).sum := by decide
  have hdescent : baseEnd_7605742 < baseStart_7605742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605749 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 1, 7]
def baseStart_7605749 : Nat := 118140960795 + 7605749 * 2 ^ 59
def prefixEnd_7605749 : Nat := 4983230072969 + 3 ^ 40 * 7605749 * 2
def baseEnd_7605749 : Nat := 1301801658151022735253101

theorem tailTrace_7605749 : CollatzResearch.WordTrace tailWord_7605749 prefixEnd_7605749 1301801658151022735253101 := by
  unfold tailWord_7605749
  simp only [CollatzResearch.WordTrace]
  refine ⟨277404455722677806358940301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184936303815118537572626867 277404455722677806358940301)
  ·
    refine ⟨104026670896004177384602613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277404455722677806358940301 104026670896004177384602613)
    ·
      refine ⟨9752500396500391629806495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104026670896004177384602613 9752500396500391629806495)
      ·
        refine ⟨14628750594750587444709743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9752500396500391629806495 14628750594750587444709743)
        ·
          refine ⟨21943125892125881167064615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14628750594750587444709743 21943125892125881167064615)
          ·
            refine ⟨32914688838188821750596923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21943125892125881167064615 32914688838188821750596923)
            ·
              refine ⟨49372033257283232625895385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32914688838188821750596923 49372033257283232625895385)
              ·
                refine ⟨37029024942962424469421539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49372033257283232625895385 37029024942962424469421539)
                ·
                  refine ⟨55543537414443636704132309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37029024942962424469421539 55543537414443636704132309)
                  ·
                    refine ⟨1301801658151022735253101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55543537414443636704132309 1301801658151022735253101)
                    ·
                      rfl

theorem cell23_7605749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_7605749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605749 prefixEnd_7605749 := by exact prefixLift 7605749
  have htrace : WordTrace (prefixWord ++ tailWord_7605749) baseStart_7605749 baseEnd_7605749 := by
    simpa [prefixWord, tailWord_7605749, baseEnd_7605749] using wordTrace_append hprefix tailTrace_7605749
  have hstable : (prefixWord ++ tailWord_7605749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605749).length < 2 ^ (prefixWord ++ tailWord_7605749).sum := by decide
  have hdescent : baseEnd_7605749 < baseStart_7605749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605752 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_7605752 : Nat := 118140960795 + 7605752 * 2 ^ 59
def prefixEnd_7605752 : Nat := 4983230072969 + 3 ^ 40 * 7605752 * 2
def baseEnd_7605752 : Nat := 3905406514895031694021789

theorem tailTrace_7605752 : CollatzResearch.WordTrace tailWord_7605752 prefixEnd_7605752 3905406514895031694021789 := by
  unfold tailWord_7605752
  simp only [CollatzResearch.WordTrace]
  refine ⟨138702282570833468935649755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184936376761111291914199673 138702282570833468935649755)
  ·
    refine ⟨208053423856250203403474633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138702282570833468935649755 208053423856250203403474633)
    ·
      refine ⟨156040067892187652552605975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208053423856250203403474633 156040067892187652552605975)
      ·
        refine ⟨234060101838281478828908963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156040067892187652552605975 234060101838281478828908963)
        ·
          refine ⟨351090152757422218243363445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234060101838281478828908963 351090152757422218243363445)
          ·
            refine ⟨32914701821008332960315323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 351090152757422218243363445 32914701821008332960315323)
            ·
              refine ⟨49372052731512499440472985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32914701821008332960315323 49372052731512499440472985)
              ·
                refine ⟨37029039548634374580354739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49372052731512499440472985 37029039548634374580354739)
                ·
                  refine ⟨55543559322951561870532109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37029039548634374580354739 55543559322951561870532109)
                  ·
                    refine ⟨20828834746106835701449541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 55543559322951561870532109 20828834746106835701449541)
                    ·
                      refine ⟨3905406514895031694021789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20828834746106835701449541 3905406514895031694021789)
                      ·
                        rfl

theorem cell23_7605752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_7605752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605752 prefixEnd_7605752 := by exact prefixLift 7605752
  have htrace : WordTrace (prefixWord ++ tailWord_7605752) baseStart_7605752 baseEnd_7605752 := by
    simpa [prefixWord, tailWord_7605752, baseEnd_7605752] using wordTrace_append hprefix tailTrace_7605752
  have hstable : (prefixWord ++ tailWord_7605752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605752).length < 2 ^ (prefixWord ++ tailWord_7605752).sum := by decide
  have hdescent : baseEnd_7605752 < baseStart_7605752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605859 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4]
def baseStart_7605859 : Nat := 118140960795 + 7605859 * 2 ^ 59
def prefixEnd_7605859 : Nat := 4983230072969 + 3 ^ 40 * 7605859 * 2
def baseEnd_7605859 : Nat := 3905461457325062775383797

theorem tailTrace_7605859 : CollatzResearch.WordTrace tailWord_7605859 prefixEnd_7605859 3905461457325062775383797 := by
  unfold tailWord_7605859
  simp only [CollatzResearch.WordTrace]
  refine ⟨277408467752279295145444631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184938978501519530096963087 277408467752279295145444631)
  ·
    refine ⟨416112701628418942718166947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277408467752279295145444631 416112701628418942718166947)
    ·
      refine ⟨624169052442628414077250421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416112701628418942718166947 624169052442628414077250421)
      ·
        refine ⟨58515848666496413819742227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624169052442628414077250421 58515848666496413819742227)
        ·
          refine ⟨87773772999744620729613341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58515848666496413819742227 87773772999744620729613341)
          ·
            refine ⟨32915164874904232773605003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87773772999744620729613341 32915164874904232773605003)
            ·
              refine ⟨49372747312356349160407505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32915164874904232773605003 49372747312356349160407505)
              ·
                refine ⟨37029560484267261870305629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49372747312356349160407505 37029560484267261870305629)
                ·
                  refine ⟨13886085181600223201364611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37029560484267261870305629 13886085181600223201364611)
                  ·
                    refine ⟨20829127772400334802046917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13886085181600223201364611 20829127772400334802046917)
                    ·
                      refine ⟨3905461457325062775383797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20829127772400334802046917 3905461457325062775383797)
                      ·
                        rfl

theorem cell23_7605859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_7605859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605859 prefixEnd_7605859 := by exact prefixLift 7605859
  have htrace : WordTrace (prefixWord ++ tailWord_7605859) baseStart_7605859 baseEnd_7605859 := by
    simpa [prefixWord, tailWord_7605859, baseEnd_7605859] using wordTrace_append hprefix tailTrace_7605859
  have hstable : (prefixWord ++ tailWord_7605859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605859).length < 2 ^ (prefixWord ++ tailWord_7605859).sum := by decide
  have hdescent : baseEnd_7605859 < baseStart_7605859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605909 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_7605909 : Nat := 118140960795 + 7605909 * 2 ^ 59
def prefixEnd_7605909 : Nat := 4983230072969 + 3 ^ 40 * 7605909 * 2
def baseEnd_7605909 : Nat := 3905487131357787579758567

theorem tailTrace_7605909 : CollatzResearch.WordTrace tailWord_7605909 prefixEnd_7605909 3905487131357787579758567 := by
  unfold tailWord_7605909
  simp only [CollatzResearch.WordTrace]
  refine ⟨277410291402098153684764781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184940194268065435789843187 277410291402098153684764781)
  ·
    refine ⟨104028859275786807631786793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277410291402098153684764781 104028859275786807631786793)
    ·
      refine ⟨78021644456840105723840095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104028859275786807631786793 78021644456840105723840095)
      ·
        refine ⟨117032466685260158585760143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78021644456840105723840095 117032466685260158585760143)
        ·
          refine ⟨175548700027890237878640215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117032466685260158585760143 175548700027890237878640215)
          ·
            refine ⟨263323050041835356817960323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175548700027890237878640215 263323050041835356817960323)
            ·
              refine ⟨394984575062753035226940485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263323050041835356817960323 394984575062753035226940485)
              ·
                refine ⟨74059607824266194105051341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 394984575062753035226940485 74059607824266194105051341)
                ·
                  refine ⟨27772352934099822789394253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74059607824266194105051341 27772352934099822789394253)
                  ·
                    refine ⟨10414632350287433546022845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27772352934099822789394253 10414632350287433546022845)
                    ·
                      refine ⟨3905487131357787579758567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10414632350287433546022845 3905487131357787579758567)
                      ·
                        rfl

theorem cell23_7605909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_7605909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605909 prefixEnd_7605909 := by exact prefixLift 7605909
  have htrace : WordTrace (prefixWord ++ tailWord_7605909) baseStart_7605909 baseEnd_7605909 := by
    simpa [prefixWord, tailWord_7605909, baseEnd_7605909] using wordTrace_append hprefix tailTrace_7605909
  have hstable : (prefixWord ++ tailWord_7605909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605909).length < 2 ^ (prefixWord ++ tailWord_7605909).sum := by decide
  have hdescent : baseEnd_7605909 < baseStart_7605909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605936 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2]
def baseStart_7605936 : Nat := 118140960795 + 7605936 * 2 ^ 59
def prefixEnd_7605936 : Nat := 4983230072969 + 3 ^ 40 * 7605936 * 2
def baseEnd_7605936 : Nat := 3905500995335458974120943

theorem tailTrace_7605936 : CollatzResearch.WordTrace tailWord_7605936 prefixEnd_7605936 3905500995335458974120943 := by
  unfold tailWord_7605936
  simp only [CollatzResearch.WordTrace]
  refine ⟨138705638086500168647998831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184940850782000224863998441 138705638086500168647998831)
  ·
    refine ⟨208058457129750252971998247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138705638086500168647998831 208058457129750252971998247)
    ·
      refine ⟨312087685694625379457997371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208058457129750252971998247 312087685694625379457997371)
      ·
        refine ⟨468131528541938069186996057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312087685694625379457997371 468131528541938069186996057)
        ·
          refine ⟨351098646406453551890247043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 468131528541938069186996057 351098646406453551890247043)
          ·
            refine ⟨526647969609680327835370565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351098646406453551890247043 526647969609680327835370565)
            ·
              refine ⟨98746494301815061469131981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 526647969609680327835370565 98746494301815061469131981)
              ·
                refine ⟨37029935363180648050924493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98746494301815061469131981 37029935363180648050924493)
                ·
                  refine ⟨13886225761192743019096685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37029935363180648050924493 13886225761192743019096685)
                  ·
                    refine ⟨5207334660447278632161257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13886225761192743019096685 5207334660447278632161257)
                    ·
                      refine ⟨3905500995335458974120943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207334660447278632161257 3905500995335458974120943)
                      ·
                        rfl

theorem cell23_7605936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 3, 2].length) (baseStart_7605936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605936 prefixEnd_7605936 := by exact prefixLift 7605936
  have htrace : WordTrace (prefixWord ++ tailWord_7605936) baseStart_7605936 baseEnd_7605936 := by
    simpa [prefixWord, tailWord_7605936, baseEnd_7605936] using wordTrace_append hprefix tailTrace_7605936
  have hstable : (prefixWord ++ tailWord_7605936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605936).length < 2 ^ (prefixWord ++ tailWord_7605936).sum := by decide
  have hdescent : baseEnd_7605936 < baseStart_7605936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605987 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 1, 3, 2]
def baseStart_7605987 : Nat := 118140960795 + 7605987 * 2 ^ 59
def prefixEnd_7605987 : Nat := 4983230072969 + 3 ^ 40 * 7605987 * 2
def baseEnd_7605987 : Nat := 3905527182848838274583209

theorem tailTrace_7605987 : CollatzResearch.WordTrace tailWord_7605987 prefixEnd_7605987 3905527182848838274583209 := by
  unfold tailWord_7605987
  simp only [CollatzResearch.WordTrace]
  refine ⟨277413136295815573006104215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184942090863877048670736143 277413136295815573006104215)
  ·
    refine ⟨416119704443723359509156323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277413136295815573006104215 416119704443723359509156323)
    ·
      refine ⟨624179556665585039263734485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416119704443723359509156323 624179556665585039263734485)
      ·
        refine ⟨14629208359349649357743777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 624179556665585039263734485 14629208359349649357743777)
        ·
          refine ⟨10971906269512237018307833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14629208359349649357743777 10971906269512237018307833)
          ·
            refine ⟨8228929702134177763730875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10971906269512237018307833 8228929702134177763730875)
            ·
              refine ⟨12343394553201266645596313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8228929702134177763730875 12343394553201266645596313)
              ·
                refine ⟨9257545914900949984197235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12343394553201266645596313 9257545914900949984197235)
                ·
                  refine ⟨13886318872351424976295853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257545914900949984197235 13886318872351424976295853)
                  ·
                    refine ⟨5207369577131784366110945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13886318872351424976295853 5207369577131784366110945)
                    ·
                      refine ⟨3905527182848838274583209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207369577131784366110945 3905527182848838274583209)
                      ·
                        rfl

theorem cell23_7605987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_7605987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605987 prefixEnd_7605987 := by exact prefixLift 7605987
  have htrace : WordTrace (prefixWord ++ tailWord_7605987) baseStart_7605987 baseEnd_7605987 := by
    simpa [prefixWord, tailWord_7605987, baseEnd_7605987] using wordTrace_append hprefix tailTrace_7605987
  have hstable : (prefixWord ++ tailWord_7605987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605987).length < 2 ^ (prefixWord ++ tailWord_7605987).sum := by decide
  have hdescent : baseEnd_7605987 < baseStart_7605987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7605989 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 9]
def baseStart_7605989 : Nat := 118140960795 + 7605989 * 2 ^ 59
def prefixEnd_7605989 : Nat := 4983230072969 + 3 ^ 40 * 7605989 * 2
def baseEnd_7605989 : Nat := 433947578867794140750911

theorem tailTrace_7605989 : CollatzResearch.WordTrace tailWord_7605989 prefixEnd_7605989 433947578867794140750911 := by
  unfold tailWord_7605989
  simp only [CollatzResearch.WordTrace]
  refine ⟨277413209241808327347677021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184942139494538884898451347 277413209241808327347677021)
  ·
    refine ⟨104029953465678122755378883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277413209241808327347677021 104029953465678122755378883)
    ·
      refine ⟨156044930198517184133068325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104029953465678122755378883 156044930198517184133068325)
      ·
        refine ⟨29258424412221972024950311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156044930198517184133068325 29258424412221972024950311)
        ·
          refine ⟨43887636618332958037425467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29258424412221972024950311 43887636618332958037425467)
          ·
            refine ⟨65831454927499437056138201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43887636618332958037425467 65831454927499437056138201)
            ·
              refine ⟨49373591195624577792103651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65831454927499437056138201 49373591195624577792103651)
              ·
                refine ⟨74060386793436866688155477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49373591195624577792103651 74060386793436866688155477)
                ·
                  refine ⟨433947578867794140750911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74060386793436866688155477 433947578867794140750911)
                  ·
                    rfl

theorem cell23_7605989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 9].length) (baseStart_7605989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7605989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7605989 prefixEnd_7605989 := by exact prefixLift 7605989
  have htrace : WordTrace (prefixWord ++ tailWord_7605989) baseStart_7605989 baseEnd_7605989 := by
    simpa [prefixWord, tailWord_7605989, baseEnd_7605989] using wordTrace_append hprefix tailTrace_7605989
  have hstable : (prefixWord ++ tailWord_7605989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7605989).length < 2 ^ (prefixWord ++ tailWord_7605989).sum := by decide
  have hdescent : baseEnd_7605989 < baseStart_7605989 := by decide
  rcases family_descends (prefixWord ++ tailWord_7605989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606053 : List Nat := [1, 3, 1, 2, 3, 4, 1, 1, 2, 5]
def baseStart_7606053 : Nat := 118140960795 + 7606053 * 2 ^ 59
def prefixEnd_7606053 : Nat := 4983230072969 + 3 ^ 40 * 7606053 * 2
def baseEnd_7606053 : Nat := 1301853690857345005452635

theorem tailTrace_7606053 : CollatzResearch.WordTrace tailWord_7606053 prefixEnd_7606053 1301853690857345005452635 := by
  unfold tailWord_7606053
  simp only [CollatzResearch.WordTrace]
  refine ⟨277415543513576466278006813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184943695675717644185337875 277415543513576466278006813)
  ·
    refine ⟨104030828817591174854252555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 277415543513576466278006813 104030828817591174854252555)
    ·
      refine ⟨156046243226386762281378833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104030828817591174854252555 156046243226386762281378833)
      ·
        refine ⟨117034682419790071711034125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156046243226386762281378833 117034682419790071711034125)
        ·
          refine ⟨43888005907421276891637797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117034682419790071711034125 43888005907421276891637797)
          ·
            refine ⟨8229001107641489417182087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43888005907421276891637797 8229001107641489417182087)
            ·
              refine ⟨12343501661462234125773131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229001107641489417182087 12343501661462234125773131)
              ·
                refine ⟨18515252492193351188659697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12343501661462234125773131 18515252492193351188659697)
                ·
                  refine ⟨13886439369145013391494773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18515252492193351188659697 13886439369145013391494773)
                  ·
                    refine ⟨1301853690857345005452635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13886439369145013391494773 1301853690857345005452635)
                    ·
                      rfl

theorem cell23_7606053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_7606053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606053 prefixEnd_7606053 := by exact prefixLift 7606053
  have htrace : WordTrace (prefixWord ++ tailWord_7606053) baseStart_7606053 baseEnd_7606053 := by
    simpa [prefixWord, tailWord_7606053, baseEnd_7606053] using wordTrace_append hprefix tailTrace_7606053
  have hstable : (prefixWord ++ tailWord_7606053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606053).length < 2 ^ (prefixWord ++ tailWord_7606053).sum := by decide
  have hdescent : baseEnd_7606053 < baseStart_7606053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606083 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 3, 4]
def baseStart_7606083 : Nat := 118140960795 + 7606083 * 2 ^ 59
def prefixEnd_7606083 : Nat := 4983230072969 + 3 ^ 40 * 7606083 * 2
def baseEnd_7606083 : Nat := 1301858825663889966327589

theorem tailTrace_7606083 : CollatzResearch.WordTrace tailWord_7606083 prefixEnd_7606083 1301858825663889966327589 := by
  unfold tailWord_7606083
  simp only [CollatzResearch.WordTrace]
  refine ⟨277416637703467781401598903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184944425135645187601065935 277416637703467781401598903)
  ·
    refine ⟨416124956555201672102398355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277416637703467781401598903 416124956555201672102398355)
    ·
      refine ⟨624187434832802508153597533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416124956555201672102398355 624187434832802508153597533)
      ·
        refine ⟨234070288062300940557599075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 624187434832802508153597533 234070288062300940557599075)
        ·
          refine ⟨351105432093451410836398613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234070288062300940557599075 351105432093451410836398613)
          ·
            refine ⟨16458067129380534882956185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 351105432093451410836398613 16458067129380534882956185)
            ·
              refine ⟨12343550347035401162217139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16458067129380534882956185 12343550347035401162217139)
              ·
                refine ⟨18515325520553101743325709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12343550347035401162217139 18515325520553101743325709)
                ·
                  refine ⟨6943247070207413153747141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18515325520553101743325709 6943247070207413153747141)
                  ·
                    refine ⟨1301858825663889966327589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943247070207413153747141 1301858825663889966327589)
                    ·
                      rfl

theorem cell23_7606083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 4].length) (baseStart_7606083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606083 prefixEnd_7606083 := by exact prefixLift 7606083
  have htrace : WordTrace (prefixWord ++ tailWord_7606083) baseStart_7606083 baseEnd_7606083 := by
    simpa [prefixWord, tailWord_7606083, baseEnd_7606083] using wordTrace_append hprefix tailTrace_7606083
  have hstable : (prefixWord ++ tailWord_7606083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606083).length < 2 ^ (prefixWord ++ tailWord_7606083).sum := by decide
  have hdescent : baseEnd_7606083 < baseStart_7606083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606106 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_7606106 : Nat := 118140960795 + 7606106 * 2 ^ 59
def prefixEnd_7606106 : Nat := 4983230072969 + 3 ^ 40 * 7606106 * 2
def baseEnd_7606106 : Nat := 3905588287046723308995161

theorem tailTrace_7606106 : CollatzResearch.WordTrace tailWord_7606106 prefixEnd_7606106 3905588287046723308995161 := by
  unfold tailWord_7606106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69354369145596114082421543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184944984388256304219790781 69354369145596114082421543)
  ·
    refine ⟨104031553718394171123632315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69354369145596114082421543 104031553718394171123632315)
    ·
      refine ⟨156047330577591256685448473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104031553718394171123632315 156047330577591256685448473)
      ·
        refine ⟨117035497933193442514086355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156047330577591256685448473 117035497933193442514086355)
        ·
          refine ⟨175553246899790163771129533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117035497933193442514086355 175553246899790163771129533)
          ·
            refine ⟨65832467587421311414173575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 175553246899790163771129533 65832467587421311414173575)
            ·
              refine ⟨98748701381131967121260363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65832467587421311414173575 98748701381131967121260363)
              ·
                refine ⟨148123052071697950681890545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98748701381131967121260363 148123052071697950681890545)
                ·
                  refine ⟨111092289053773463011417909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 148123052071697950681890545 111092289053773463011417909)
                  ·
                    refine ⟨10414902098791262157320429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 111092289053773463011417909 10414902098791262157320429)
                    ·
                      refine ⟨3905588287046723308995161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10414902098791262157320429 3905588287046723308995161)
                      ·
                        rfl

theorem cell23_7606106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_7606106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606106 prefixEnd_7606106 := by exact prefixLift 7606106
  have htrace : WordTrace (prefixWord ++ tailWord_7606106) baseStart_7606106 baseEnd_7606106 := by
    simpa [prefixWord, tailWord_7606106, baseEnd_7606106] using wordTrace_append hprefix tailTrace_7606106
  have hstable : (prefixWord ++ tailWord_7606106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606106).length < 2 ^ (prefixWord ++ tailWord_7606106).sum := by decide
  have hdescent : baseEnd_7606106 < baseStart_7606106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606134 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_7606134 : Nat := 118140960795 + 7606134 * 2 ^ 59
def prefixEnd_7606134 : Nat := 4983230072969 + 3 ^ 40 * 7606134 * 2
def baseEnd_7606134 : Nat := 1301867554835016399815011

theorem tailTrace_7606134 : CollatzResearch.WordTrace tailWord_7606134 prefixEnd_7606134 1301867554835016399815011 := by
  unfold tailWord_7606134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17338656114142688569481591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 184945665217522011407803637 17338656114142688569481591)
  ·
    refine ⟨26007984171214032854222387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17338656114142688569481591 26007984171214032854222387)
    ·
      refine ⟨39011976256821049281333581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26007984171214032854222387 39011976256821049281333581)
      ·
        refine ⟨14629491096307893480500093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39011976256821049281333581 14629491096307893480500093)
        ·
          refine ⟨5486059161115460055187535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14629491096307893480500093 5486059161115460055187535)
          ·
            refine ⟨8229088741673190082781303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5486059161115460055187535 8229088741673190082781303)
            ·
              refine ⟨12343633112509785124171955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229088741673190082781303 12343633112509785124171955)
              ·
                refine ⟨18515449668764677686257933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12343633112509785124171955 18515449668764677686257933)
                ·
                  refine ⟨6943293625786754132346725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18515449668764677686257933 6943293625786754132346725)
                  ·
                    refine ⟨1301867554835016399815011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943293625786754132346725 1301867554835016399815011)
                    ·
                      rfl

theorem cell23_7606134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_7606134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606134 prefixEnd_7606134 := by exact prefixLift 7606134
  have htrace : WordTrace (prefixWord ++ tailWord_7606134) baseStart_7606134 baseEnd_7606134 := by
    simpa [prefixWord, tailWord_7606134, baseEnd_7606134] using wordTrace_append hprefix tailTrace_7606134
  have hstable : (prefixWord ++ tailWord_7606134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606134).length < 2 ^ (prefixWord ++ tailWord_7606134).sum := by decide
  have hdescent : baseEnd_7606134 < baseStart_7606134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606156 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_7606156 : Nat := 118140960795 + 7606156 * 2 ^ 59
def prefixEnd_7606156 : Nat := 4983230072969 + 3 ^ 40 * 7606156 * 2
def baseEnd_7606156 : Nat := 1301871320359816037789977

theorem tailTrace_7606156 : CollatzResearch.WordTrace tailWord_7606156 prefixEnd_7606156 1301871320359816037789977 := by
  unfold tailWord_7606156
  simp only [CollatzResearch.WordTrace]
  refine ⟨138709650116101657434503161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184946200154802209912670881 138709650116101657434503161)
  ·
    refine ⟨104032237587076243075877371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138709650116101657434503161 104032237587076243075877371)
    ·
      refine ⟨156048356380614364613816057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104032237587076243075877371 156048356380614364613816057)
      ·
        refine ⟨117036267285460773460362043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156048356380614364613816057 117036267285460773460362043)
        ·
          refine ⟨175554400928191160190543065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117036267285460773460362043 175554400928191160190543065)
          ·
            refine ⟨131665800696143370142907299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175554400928191160190543065 131665800696143370142907299)
            ·
              refine ⟨197498701044215055214360949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131665800696143370142907299 197498701044215055214360949)
              ·
                refine ⟨18515503222895161426346339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197498701044215055214360949 18515503222895161426346339)
                ·
                  refine ⟨27773254834342742139519509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18515503222895161426346339 27773254834342742139519509)
                  ·
                    refine ⟨1301871320359816037789977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27773254834342742139519509 1301871320359816037789977)
                    ·
                      rfl

theorem cell23_7606156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_7606156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606156 prefixEnd_7606156 := by exact prefixLift 7606156
  have htrace : WordTrace (prefixWord ++ tailWord_7606156) baseStart_7606156 baseEnd_7606156 := by
    simpa [prefixWord, tailWord_7606156, baseEnd_7606156] using wordTrace_append hprefix tailTrace_7606156
  have hstable : (prefixWord ++ tailWord_7606156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606156).length < 2 ^ (prefixWord ++ tailWord_7606156).sum := by decide
  have hdescent : baseEnd_7606156 < baseStart_7606156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606173 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 1, 6]
def baseStart_7606173 : Nat := 118140960795 + 7606173 * 2 ^ 59
def prefixEnd_7606173 : Nat := 4983230072969 + 3 ^ 40 * 7606173 * 2
def baseEnd_7606173 : Nat := 1301874230083524848952451

theorem tailTrace_7606173 : CollatzResearch.WordTrace tailWord_7606173 prefixEnd_7606173 1301874230083524848952451 := by
  unfold tailWord_7606173
  simp only [CollatzResearch.WordTrace]
  refine ⟨277419920273141726772375173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184946613515427817848250115 277419920273141726772375173)
  ·
    refine ⟨52016235051214073769820345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277419920273141726772375173 52016235051214073769820345)
    ·
      refine ⟨39012176288410555327365259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52016235051214073769820345 39012176288410555327365259)
      ·
        refine ⟨58518264432615832991047889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39012176288410555327365259 58518264432615832991047889)
        ·
          refine ⟨43888698324461874743285917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58518264432615832991047889 43888698324461874743285917)
          ·
            refine ⟨16458261871673203028732219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43888698324461874743285917 16458261871673203028732219)
            ·
              refine ⟨24687392807509804543098329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16458261871673203028732219 24687392807509804543098329)
              ·
                refine ⟨18515544605632353407323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24687392807509804543098329 18515544605632353407323747)
                ·
                  refine ⟨27773316908448530110985621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18515544605632353407323747 27773316908448530110985621)
                  ·
                    refine ⟨1301874230083524848952451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27773316908448530110985621 1301874230083524848952451)
                    ·
                      rfl

theorem cell23_7606173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_7606173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606173 prefixEnd_7606173 := by exact prefixLift 7606173
  have htrace : WordTrace (prefixWord ++ tailWord_7606173) baseStart_7606173 baseEnd_7606173 := by
    simpa [prefixWord, tailWord_7606173, baseEnd_7606173] using wordTrace_append hprefix tailTrace_7606173
  have hstable : (prefixWord ++ tailWord_7606173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606173).length < 2 ^ (prefixWord ++ tailWord_7606173).sum := by decide
  have hdescent : baseEnd_7606173 < baseStart_7606173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606177 : List Nat := [1, 2, 3, 4, 2, 1, 3, 1, 1, 5]
def baseStart_7606177 : Nat := 118140960795 + 7606177 * 2 ^ 59
def prefixEnd_7606177 : Nat := 4983230072969 + 3 ^ 40 * 7606177 * 2
def baseEnd_7606177 : Nat := 1301874914724397510402445

theorem tailTrace_7606177 : CollatzResearch.WordTrace tailWord_7606177 prefixEnd_7606177 1301874914724397510402445 := by
  unfold tailWord_7606177
  simp only [CollatzResearch.WordTrace]
  refine ⟨277420066165127235455520785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184946710776751490303680523 277420066165127235455520785)
  ·
    refine ⟨208065049623845426591640589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277420066165127235455520785 208065049623845426591640589)
    ·
      refine ⟨78024393608942034971865221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208065049623845426591640589 78024393608942034971865221)
      ·
        refine ⟨14629573801676631557224729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78024393608942034971865221 14629573801676631557224729)
        ·
          refine ⟨10972180351257473667918547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14629573801676631557224729 10972180351257473667918547)
          ·
            refine ⟨16458270526886210501877821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10972180351257473667918547 16458270526886210501877821)
            ·
              refine ⟨6171851447582328938204183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16458270526886210501877821 6171851447582328938204183)
              ·
                refine ⟨9257777171373493407306275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171851447582328938204183 9257777171373493407306275)
                ·
                  refine ⟨13886665757060240110959413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257777171373493407306275 13886665757060240110959413)
                  ·
                    refine ⟨1301874914724397510402445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13886665757060240110959413 1301874914724397510402445)
                    ·
                      rfl

theorem cell23_7606177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_7606177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606177 prefixEnd_7606177 := by exact prefixLift 7606177
  have htrace : WordTrace (prefixWord ++ tailWord_7606177) baseStart_7606177 baseEnd_7606177 := by
    simpa [prefixWord, tailWord_7606177, baseEnd_7606177] using wordTrace_append hprefix tailTrace_7606177
  have hstable : (prefixWord ++ tailWord_7606177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606177).length < 2 ^ (prefixWord ++ tailWord_7606177).sum := by decide
  have hdescent : baseEnd_7606177 < baseStart_7606177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606234 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3]
def baseStart_7606234 : Nat := 118140960795 + 7606234 * 2 ^ 59
def prefixEnd_7606234 : Nat := 4983230072969 + 3 ^ 40 * 7606234 * 2
def baseEnd_7606234 : Nat := 3905654012570498808194573

theorem tailTrace_7606234 : CollatzResearch.WordTrace tailWord_7606234 prefixEnd_7606234 3905654012570498808194573 := by
  unfold tailWord_7606234
  simp only [CollatzResearch.WordTrace]
  refine ⟨69355536281480183547586439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184948096750613822793563837 69355536281480183547586439)
  ·
    refine ⟨104033304422220275321379659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69355536281480183547586439 104033304422220275321379659)
    ·
      refine ⟨156049956633330412982069489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104033304422220275321379659 156049956633330412982069489)
      ·
        refine ⟨117037467474997809736552117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156049956633330412982069489 117037467474997809736552117)
        ·
          refine ⟨10972262575781044662801761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117037467474997809736552117 10972262575781044662801761)
          ·
            refine ⟨8229196931835783497101321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10972262575781044662801761 8229196931835783497101321)
            ·
              refine ⟨6171897698876837622825991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229196931835783497101321 6171897698876837622825991)
              ·
                refine ⟨9257846548315256434238987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171897698876837622825991 9257846548315256434238987)
                ·
                  refine ⟨13886769822472884651358481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9257846548315256434238987 13886769822472884651358481)
                  ·
                    refine ⟨10415077366854663488518861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13886769822472884651358481 10415077366854663488518861)
                    ·
                      refine ⟨3905654012570498808194573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415077366854663488518861 3905654012570498808194573)
                      ·
                        rfl

theorem cell23_7606234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_7606234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606234 prefixEnd_7606234 := by exact prefixLift 7606234
  have htrace : WordTrace (prefixWord ++ tailWord_7606234) baseStart_7606234 baseEnd_7606234 := by
    simpa [prefixWord, tailWord_7606234, baseEnd_7606234] using wordTrace_append hprefix tailTrace_7606234
  have hstable : (prefixWord ++ tailWord_7606234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606234).length < 2 ^ (prefixWord ++ tailWord_7606234).sum := by decide
  have hdescent : baseEnd_7606234 < baseStart_7606234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606247 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7606247 : Nat := 118140960795 + 7606247 * 2 ^ 59
def prefixEnd_7606247 : Nat := 4983230072969 + 3 ^ 40 * 7606247 * 2
def baseEnd_7606247 : Nat := 3905660687819007257332013

theorem tailTrace_7606247 : CollatzResearch.WordTrace tailWord_7606247 prefixEnd_7606247 3905660687819007257332013 := by
  unfold tailWord_7606247
  simp only [CollatzResearch.WordTrace]
  refine ⟨277422619274873637410568995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184948412849915758273712663 277422619274873637410568995)
  ·
    refine ⟨416133928912310456115853493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277422619274873637410568995 416133928912310456115853493)
    ·
      refine ⟨39012555835529105260861265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416133928912310456115853493 39012555835529105260861265)
      ·
        refine ⟨29259416876646828945645949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39012555835529105260861265 29259416876646828945645949)
        ·
          refine ⟨10972281328742560854617231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29259416876646828945645949 10972281328742560854617231)
          ·
            refine ⟨16458421993113841281925847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10972281328742560854617231 16458421993113841281925847)
            ·
              refine ⟨24687632989670761922888771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16458421993113841281925847 24687632989670761922888771)
              ·
                refine ⟨37031449484506142884333157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24687632989670761922888771 37031449484506142884333157)
                ·
                  refine ⟨6943396778344901790812467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37031449484506142884333157 6943396778344901790812467)
                  ·
                    refine ⟨10415095167517352686218701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943396778344901790812467 10415095167517352686218701)
                    ·
                      refine ⟨3905660687819007257332013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415095167517352686218701 3905660687819007257332013)
                      ·
                        rfl

theorem cell23_7606247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7606247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606247 prefixEnd_7606247 := by exact prefixLift 7606247
  have htrace : WordTrace (prefixWord ++ tailWord_7606247) baseStart_7606247 baseEnd_7606247 := by
    simpa [prefixWord, tailWord_7606247, baseEnd_7606247] using wordTrace_append hprefix tailTrace_7606247
  have hstable : (prefixWord ++ tailWord_7606247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606247).length < 2 ^ (prefixWord ++ tailWord_7606247).sum := by decide
  have hdescent : baseEnd_7606247 < baseStart_7606247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606273 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_7606273 : Nat := 118140960795 + 7606273 * 2 ^ 59
def prefixEnd_7606273 : Nat := 4983230072969 + 3 ^ 40 * 7606273 * 2
def baseEnd_7606273 : Nat := 3905674038316024155606893

theorem tailTrace_7606273 : CollatzResearch.WordTrace tailWord_7606273 prefixEnd_7606273 3905674038316024155606893 := by
  unfold tailWord_7606273
  simp only [CollatzResearch.WordTrace]
  refine ⟨277423567572779443851015473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184949045048519629234010315 277423567572779443851015473)
  ·
    refine ⟨208067675679584582888261605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277423567572779443851015473 208067675679584582888261605)
    ·
      refine ⟨39012689189922109291549051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208067675679584582888261605 39012689189922109291549051)
      ·
        refine ⟨58519033784883163937323577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39012689189922109291549051 58519033784883163937323577)
        ·
          refine ⟨43889275338662372952992683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58519033784883163937323577 43889275338662372952992683)
          ·
            refine ⟨65833913007993559429489025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43889275338662372952992683 65833913007993559429489025)
            ·
              refine ⟨49375434755995169572116769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65833913007993559429489025 49375434755995169572116769)
              ·
                refine ⟨37031576066996377179087577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49375434755995169572116769 37031576066996377179087577)
                ·
                  refine ⟨27773682050247282884315683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37031576066996377179087577 27773682050247282884315683)
                  ·
                    refine ⟨41660523075370924326473525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27773682050247282884315683 41660523075370924326473525)
                    ·
                      refine ⟨3905674038316024155606893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41660523075370924326473525 3905674038316024155606893)
                      ·
                        rfl

theorem cell23_7606273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_7606273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606273 prefixEnd_7606273 := by exact prefixLift 7606273
  have htrace : WordTrace (prefixWord ++ tailWord_7606273) baseStart_7606273 baseEnd_7606273 := by
    simpa [prefixWord, tailWord_7606273, baseEnd_7606273] using wordTrace_append hprefix tailTrace_7606273
  have hstable : (prefixWord ++ tailWord_7606273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606273).length < 2 ^ (prefixWord ++ tailWord_7606273).sum := by decide
  have hdescent : baseEnd_7606273 < baseStart_7606273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606321 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 2, 2, 2]
def baseStart_7606321 : Nat := 118140960795 + 7606321 * 2 ^ 59
def prefixEnd_7606321 : Nat := 4983230072969 + 3 ^ 40 * 7606321 * 2
def baseEnd_7606321 : Nat := 3905698685387439967806673

theorem tailTrace_7606321 : CollatzResearch.WordTrace tailWord_7606321 prefixEnd_7606321 3905698685387439967806673 := by
  unfold tailWord_7606321
  simp only [CollatzResearch.WordTrace]
  refine ⟨277425318276605548048762817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184950212184403698699175211 277425318276605548048762817)
  ·
    refine ⟨208068988707454161036572113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277425318276605548048762817 208068988707454161036572113)
    ·
      refine ⟨156051741530590620777429085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208068988707454161036572113 156051741530590620777429085)
      ·
        refine ⟨58519403073971482791535907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156051741530590620777429085 58519403073971482791535907)
        ·
          refine ⟨87779104610957224187303861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58519403073971482791535907 87779104610957224187303861)
          ·
            refine ⟨8229291057277239767559737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87779104610957224187303861 8229291057277239767559737)
            ·
              refine ⟨6171968292957929825669803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8229291057277239767559737 6171968292957929825669803)
              ·
                refine ⟨9257952439436894738504705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6171968292957929825669803 9257952439436894738504705)
                ·
                  refine ⟨6943464329577671053878529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9257952439436894738504705 6943464329577671053878529)
                  ·
                    refine ⟨5207598247183253290408897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943464329577671053878529 5207598247183253290408897)
                    ·
                      refine ⟨3905698685387439967806673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207598247183253290408897 3905698685387439967806673)
                      ·
                        rfl

theorem cell23_7606321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_7606321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606321 prefixEnd_7606321 := by exact prefixLift 7606321
  have htrace : WordTrace (prefixWord ++ tailWord_7606321) baseStart_7606321 baseEnd_7606321 := by
    simpa [prefixWord, tailWord_7606321, baseEnd_7606321] using wordTrace_append hprefix tailTrace_7606321
  have hstable : (prefixWord ++ tailWord_7606321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606321).length < 2 ^ (prefixWord ++ tailWord_7606321).sum := by decide
  have hdescent : baseEnd_7606321 < baseStart_7606321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606333 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7606333 : Nat := 118140960795 + 7606333 * 2 ^ 59
def prefixEnd_7606333 : Nat := 4983230072969 + 3 ^ 40 * 7606333 * 2
def baseEnd_7606333 : Nat := 3905704847155293920856617

theorem tailTrace_7606333 : CollatzResearch.WordTrace tailWord_7606333 prefixEnd_7606333 3905704847155293920856617 := by
  unfold tailWord_7606333
  simp only [CollatzResearch.WordTrace]
  refine ⟨277425755952562074098199653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184950503968374716065466435 277425755952562074098199653)
  ·
    refine ⟨52017329241105388893412435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277425755952562074098199653 52017329241105388893412435)
    ·
      refine ⟨78025993861658083340118653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52017329241105388893412435 78025993861658083340118653)
      ·
        refine ⟨29259747698121781252544495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78025993861658083340118653 29259747698121781252544495)
        ·
          refine ⟨43889621547182671878816743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29259747698121781252544495 43889621547182671878816743)
          ·
            refine ⟨65834432320774007818225115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43889621547182671878816743 65834432320774007818225115)
            ·
              refine ⟨98751648481161011727337673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65834432320774007818225115 98751648481161011727337673)
              ·
                refine ⟨74063736360870758795503255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98751648481161011727337673 74063736360870758795503255)
                ·
                  refine ⟨111095604541306138193254883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74063736360870758795503255 111095604541306138193254883)
                  ·
                    refine ⟨166643406811959207289882325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 111095604541306138193254883 166643406811959207289882325)
                    ·
                      refine ⟨3905704847155293920856617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166643406811959207289882325 3905704847155293920856617)
                      ·
                        rfl

theorem cell23_7606333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7606333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606333 prefixEnd_7606333 := by exact prefixLift 7606333
  have htrace : WordTrace (prefixWord ++ tailWord_7606333) baseStart_7606333 baseEnd_7606333 := by
    simpa [prefixWord, tailWord_7606333, baseEnd_7606333] using wordTrace_append hprefix tailTrace_7606333
  have hstable : (prefixWord ++ tailWord_7606333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606333).length < 2 ^ (prefixWord ++ tailWord_7606333).sum := by decide
  have hdescent : baseEnd_7606333 < baseStart_7606333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606360 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_7606360 : Nat := 118140960795 + 7606360 * 2 ^ 59
def prefixEnd_7606360 : Nat := 4983230072969 + 3 ^ 40 * 7606360 * 2
def baseEnd_7606360 : Nat := 3905718711132965315218993

theorem tailTrace_7606360 : CollatzResearch.WordTrace tailWord_7606360 prefixEnd_7606360 3905718711132965315218993 := by
  unfold tailWord_7606360
  simp only [CollatzResearch.WordTrace]
  refine ⟨138713370361732128854716267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184951160482309505139621689 138713370361732128854716267)
  ·
    refine ⟨208070055542598193282074401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138713370361732128854716267 208070055542598193282074401)
    ·
      refine ⟨156052541656948644961555801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208070055542598193282074401 156052541656948644961555801)
      ·
        refine ⟨117039406242711483721166851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156052541656948644961555801 117039406242711483721166851)
        ·
          refine ⟨175559109364067225581750277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117039406242711483721166851 175559109364067225581750277)
          ·
            refine ⟨32917333005762604796578177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 175559109364067225581750277 32917333005762604796578177)
            ·
              refine ⟨24687999754321953597433633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32917333005762604796578177 24687999754321953597433633)
              ·
                refine ⟨18515999815741465198075225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24687999754321953597433633 18515999815741465198075225)
                ·
                  refine ⟨13886999861806098898556419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18515999815741465198075225 13886999861806098898556419)
                  ·
                    refine ⟨20830499792709148347834629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13886999861806098898556419 20830499792709148347834629)
                    ·
                      refine ⟨3905718711132965315218993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20830499792709148347834629 3905718711132965315218993)
                      ·
                        rfl

theorem cell23_7606360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_7606360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606360 prefixEnd_7606360 := by exact prefixLift 7606360
  have htrace : WordTrace (prefixWord ++ tailWord_7606360) baseStart_7606360 baseEnd_7606360 := by
    simpa [prefixWord, tailWord_7606360, baseEnd_7606360] using wordTrace_append hprefix tailTrace_7606360
  have hstable : (prefixWord ++ tailWord_7606360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606360).length < 2 ^ (prefixWord ++ tailWord_7606360).sum := by decide
  have hdescent : baseEnd_7606360 < baseStart_7606360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606397 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_7606397 : Nat := 118140960795 + 7606397 * 2 ^ 59
def prefixEnd_7606397 : Nat := 4983230072969 + 3 ^ 40 * 7606397 * 2
def baseEnd_7606397 : Nat := 3905737709917181670456323

theorem tailTrace_7606397 : CollatzResearch.WordTrace tailWord_7606397 prefixEnd_7606397 3905737709917181670456323 := by
  unfold tailWord_7606397
  simp only [CollatzResearch.WordTrace]
  refine ⟨277428090224330213028529445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184952060149553475352352963 277428090224330213028529445)
  ·
    refine ⟨52017766917061914942849271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 277428090224330213028529445 52017766917061914942849271)
    ·
      refine ⟨78026650375592872414273907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52017766917061914942849271 78026650375592872414273907)
      ·
        refine ⟨117039975563389308621410861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78026650375592872414273907 117039975563389308621410861)
        ·
          refine ⟨43889990836270990733029073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117039975563389308621410861 43889990836270990733029073)
          ·
            refine ⟨32917493127203243049771805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43889990836270990733029073 32917493127203243049771805)
            ·
              refine ⟨12344059922701216143664427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32917493127203243049771805 12344059922701216143664427)
              ·
                refine ⟨18516089884051824215496641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12344059922701216143664427 18516089884051824215496641)
                ·
                  refine ⟨13887067413038868161622481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18516089884051824215496641 13887067413038868161622481)
                  ·
                    refine ⟨10415300559779151121216861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13887067413038868161622481 10415300559779151121216861)
                    ·
                      refine ⟨3905737709917181670456323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415300559779151121216861 3905737709917181670456323)
                      ·
                        rfl

theorem cell23_7606397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_7606397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606397 prefixEnd_7606397 := by exact prefixLift 7606397
  have htrace : WordTrace (prefixWord ++ tailWord_7606397) baseStart_7606397 baseEnd_7606397 := by
    simpa [prefixWord, tailWord_7606397, baseEnd_7606397] using wordTrace_append hprefix tailTrace_7606397
  have hstable : (prefixWord ++ tailWord_7606397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606397).length < 2 ^ (prefixWord ++ tailWord_7606397).sum := by decide
  have hdescent : baseEnd_7606397 < baseStart_7606397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606404 : List Nat := [2, 3, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_7606404 : Nat := 118140960795 + 7606404 * 2 ^ 59
def prefixEnd_7606404 : Nat := 4983230072969 + 3 ^ 40 * 7606404 * 2
def baseEnd_7606404 : Nat := 1301913768093921047689597

theorem tailTrace_7606404 : CollatzResearch.WordTrace tailWord_7606404 prefixEnd_7606404 1301913768093921047689597 := by
  unfold tailWord_7606404
  simp only [CollatzResearch.WordTrace]
  refine ⟨138714172767652426612017133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184952230356869902149356177 138714172767652426612017133)
  ·
    refine ⟨52017814787869659979506425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 138714172767652426612017133 52017814787869659979506425)
    ·
      refine ⟨39013361090902244984629819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52017814787869659979506425 39013361090902244984629819)
      ·
        refine ⟨58520041636353367476944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39013361090902244984629819 58520041636353367476944729)
        ·
          refine ⟨43890031227265025607708547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58520041636353367476944729 43890031227265025607708547)
          ·
            refine ⟨65835046840897538411562821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43890031227265025607708547 65835046840897538411562821)
            ·
              refine ⟨12344071282668288452168029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65835046840897538411562821 12344071282668288452168029)
              ·
                refine ⟨4629026731000608169563011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12344071282668288452168029 4629026731000608169563011)
                ·
                  refine ⟨6943540096500912254344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629026731000608169563011 6943540096500912254344517)
                  ·
                    refine ⟨1301913768093921047689597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6943540096500912254344517 1301913768093921047689597)
                    ·
                      rfl

theorem cell23_7606404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_7606404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606404 prefixEnd_7606404 := by exact prefixLift 7606404
  have htrace : WordTrace (prefixWord ++ tailWord_7606404) baseStart_7606404 baseEnd_7606404 := by
    simpa [prefixWord, tailWord_7606404, baseEnd_7606404] using wordTrace_append hprefix tailTrace_7606404
  have hstable : (prefixWord ++ tailWord_7606404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606404).length < 2 ^ (prefixWord ++ tailWord_7606404).sum := by decide
  have hdescent : baseEnd_7606404 < baseStart_7606404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606434 : List Nat := [3, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_7606434 : Nat := 118140960795 + 7606434 * 2 ^ 59
def prefixEnd_7606434 : Nat := 4983230072969 + 3 ^ 40 * 7606434 * 2
def baseEnd_7606434 : Nat := 433972967633488669521517

theorem tailTrace_7606434 : CollatzResearch.WordTrace tailWord_7606434 prefixEnd_7606434 433972967633488669521517 := by
  unfold tailWord_7606434
  simp only [CollatzResearch.WordTrace]
  refine ⟨69357359931299042086906589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 184952959816797445565084237 69357359931299042086906589)
  ·
    refine ⟨26009009974237140782589971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69357359931299042086906589 26009009974237140782589971)
    ·
      refine ⟨39013514961355711173884957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26009009974237140782589971 39013514961355711173884957)
      ·
        refine ⟨14630068110508391690206859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39013514961355711173884957 14630068110508391690206859)
        ·
          refine ⟨21945102165762587535310289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14630068110508391690206859 21945102165762587535310289)
          ·
            refine ⟨16458826624321940651482717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21945102165762587535310289 16458826624321940651482717)
            ·
              refine ⟨6172059984120727744306019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16458826624321940651482717 6172059984120727744306019)
              ·
                refine ⟨9258089976181091616459029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172059984120727744306019 9258089976181091616459029)
                ·
                  refine ⟨433972967633488669521517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9258089976181091616459029 433972967633488669521517)
                  ·
                    rfl

theorem cell23_7606434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_7606434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606434 prefixEnd_7606434 := by exact prefixLift 7606434
  have htrace : WordTrace (prefixWord ++ tailWord_7606434) baseStart_7606434 baseEnd_7606434 := by
    simpa [prefixWord, tailWord_7606434, baseEnd_7606434] using wordTrace_append hprefix tailTrace_7606434
  have hstable : (prefixWord ++ tailWord_7606434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606434).length < 2 ^ (prefixWord ++ tailWord_7606434).sum := by decide
  have hdescent : baseEnd_7606434 < baseStart_7606434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606478 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_7606478 : Nat := 118140960795 + 7606478 * 2 ^ 59
def prefixEnd_7606478 : Nat := 4983230072969 + 3 ^ 40 * 7606478 * 2
def baseEnd_7606478 : Nat := 3905779301850195853543451

theorem tailTrace_7606478 : CollatzResearch.WordTrace tailWord_7606478 prefixEnd_7606478 3905779301850195853543451 := by
  unfold tailWord_7606478
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678880567129595482778511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 184954029691357842574818725 34678880567129595482778511)
  ·
    refine ⟨52018320850694393224167767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34678880567129595482778511 52018320850694393224167767)
    ·
      refine ⟨78027481276041589836251651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52018320850694393224167767 78027481276041589836251651)
      ·
        refine ⟨117041221914062384754377477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78027481276041589836251651 117041221914062384754377477)
        ·
          refine ⟨21945229108886697141445777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117041221914062384754377477 21945229108886697141445777)
          ·
            refine ⟨16458921831665022856084333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21945229108886697141445777 16458921831665022856084333)
            ·
              refine ⟨6172095686874383571031625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16458921831665022856084333 6172095686874383571031625)
              ·
                refine ⟨4629071765155787678273719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172095686874383571031625 4629071765155787678273719)
                ·
                  refine ⟨6943607647733681517410579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629071765155787678273719 6943607647733681517410579)
                  ·
                    refine ⟨10415411471600522276115869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6943607647733681517410579 10415411471600522276115869)
                    ·
                      refine ⟨3905779301850195853543451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415411471600522276115869 3905779301850195853543451)
                      ·
                        rfl

theorem cell23_7606478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_7606478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606478 prefixEnd_7606478 := by exact prefixLift 7606478
  have htrace : WordTrace (prefixWord ++ tailWord_7606478) baseStart_7606478 baseEnd_7606478 := by
    simpa [prefixWord, tailWord_7606478, baseEnd_7606478] using wordTrace_append hprefix tailTrace_7606478
  have hstable : (prefixWord ++ tailWord_7606478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606478).length < 2 ^ (prefixWord ++ tailWord_7606478).sum := by decide
  have hdescent : baseEnd_7606478 < baseStart_7606478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606483 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_7606483 : Nat := 118140960795 + 7606483 * 2 ^ 59
def prefixEnd_7606483 : Nat := 4983230072969 + 3 ^ 40 * 7606483 * 2
def baseEnd_7606483 : Nat := 3905781869253468333980927

theorem tailTrace_7606483 : CollatzResearch.WordTrace tailWord_7606483 prefixEnd_7606483 3905781869253468333980927 := by
  unfold tailWord_7606483
  simp only [CollatzResearch.WordTrace]
  refine ⟨277431226902018649716160103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184954151268012433144106735 277431226902018649716160103)
  ·
    refine ⟨416146840353027974574240155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277431226902018649716160103 416146840353027974574240155)
    ·
      refine ⟨624220260529541961861360233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416146840353027974574240155 624220260529541961861360233)
      ·
        refine ⟨468165195397156471396020175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 624220260529541961861360233 468165195397156471396020175)
        ·
          refine ⟨702247793095734707094030263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468165195397156471396020175 702247793095734707094030263)
          ·
            refine ⟨1053371689643602060641045395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 702247793095734707094030263 1053371689643602060641045395)
            ·
              refine ⟨1580057534465403090961568093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1053371689643602060641045395 1580057534465403090961568093)
              ·
                refine ⟨592521575424526159110588035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1580057534465403090961568093 592521575424526159110588035)
                ·
                  refine ⟨888782363136789238665882053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 592521575424526159110588035 888782363136789238665882053)
                  ·
                    refine ⟨166646693088147982249852885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 888782363136789238665882053 166646693088147982249852885)
                    ·
                      refine ⟨3905781869253468333980927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 166646693088147982249852885 3905781869253468333980927)
                      ·
                        rfl

theorem cell23_7606483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_7606483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606483 prefixEnd_7606483 := by exact prefixLift 7606483
  have htrace : WordTrace (prefixWord ++ tailWord_7606483) baseStart_7606483 baseEnd_7606483 := by
    simpa [prefixWord, tailWord_7606483, baseEnd_7606483] using wordTrace_append hprefix tailTrace_7606483
  have hstable : (prefixWord ++ tailWord_7606483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606483).length < 2 ^ (prefixWord ++ tailWord_7606483).sum := by decide
  have hdescent : baseEnd_7606483 < baseStart_7606483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606504 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7606504 : Nat := 118140960795 + 7606504 * 2 ^ 59
def prefixEnd_7606504 : Nat := 4983230072969 + 3 ^ 40 * 7606504 * 2
def baseEnd_7606504 : Nat := 3905792652347212751818331

theorem tailTrace_7606504 : CollatzResearch.WordTrace tailWord_7606504 prefixEnd_7606504 3905792652347212751818331 := by
  unfold tailWord_7606504
  simp only [CollatzResearch.WordTrace]
  refine ⟨138715996417471285151337283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184954661889961713535116377 138715996417471285151337283)
  ·
    refine ⟨208073994626206927727005925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138715996417471285151337283 208073994626206927727005925)
    ·
      refine ⟨39013873992413798948813611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208073994626206927727005925 39013873992413798948813611)
      ·
        refine ⟨58520810988620698423220417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39013873992413798948813611 58520810988620698423220417)
        ·
          refine ⟨43890608241465523817415313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58520810988620698423220417 43890608241465523817415313)
          ·
            refine ⟨32917956181099142863061485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43890608241465523817415313 32917956181099142863061485)
            ·
              refine ⟨12344233567912178573648057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32917956181099142863061485 12344233567912178573648057)
              ·
                refine ⟨9258175175934133930236043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12344233567912178573648057 9258175175934133930236043)
                ·
                  refine ⟨13887262763901200895354065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9258175175934133930236043 13887262763901200895354065)
                  ·
                    refine ⟨10415447072925900671515549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13887262763901200895354065 10415447072925900671515549)
                    ·
                      refine ⟨3905792652347212751818331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10415447072925900671515549 3905792652347212751818331)
                      ·
                        rfl

theorem cell23_7606504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7606504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606504 prefixEnd_7606504 := by exact prefixLift 7606504
  have htrace : WordTrace (prefixWord ++ tailWord_7606504) baseStart_7606504 baseEnd_7606504 := by
    simpa [prefixWord, tailWord_7606504, baseEnd_7606504] using wordTrace_append hprefix tailTrace_7606504
  have hstable : (prefixWord ++ tailWord_7606504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606504).length < 2 ^ (prefixWord ++ tailWord_7606504).sum := by decide
  have hdescent : baseEnd_7606504 < baseStart_7606504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606535 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7606535 : Nat := 118140960795 + 7606535 * 2 ^ 59
def prefixEnd_7606535 : Nat := 4983230072969 + 3 ^ 40 * 7606535 * 2
def baseEnd_7606535 : Nat := 3905808570247502130530689

theorem tailTrace_7606535 : CollatzResearch.WordTrace tailWord_7606535 prefixEnd_7606535 3905808570247502130530689 := by
  unfold tailWord_7606535
  simp only [CollatzResearch.WordTrace]
  refine ⟨277433123497830262597053059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184955415665220175064702039 277433123497830262597053059)
  ·
    refine ⟨416149685246745393895579589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277433123497830262597053059 416149685246745393895579589)
    ·
      refine ⟨78028065983764761355421173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 416149685246745393895579589 78028065983764761355421173)
      ·
        refine ⟨7315131185977946377070735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78028065983764761355421173 7315131185977946377070735)
        ·
          refine ⟨10972696778966919565606103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7315131185977946377070735 10972696778966919565606103)
          ·
            refine ⟨16459045168450379348409155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10972696778966919565606103 16459045168450379348409155)
            ·
              refine ⟨24688567752675569022613733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16459045168450379348409155 24688567752675569022613733)
              ·
                refine ⟨4629106453626669191740075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24688567752675569022613733 4629106453626669191740075)
                ·
                  refine ⟨6943659680440003787610113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4629106453626669191740075 6943659680440003787610113)
                  ·
                    refine ⟨5207744760330002840707585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943659680440003787610113 5207744760330002840707585)
                    ·
                      refine ⟨3905808570247502130530689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207744760330002840707585 3905808570247502130530689)
                      ·
                        rfl

theorem cell23_7606535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7606535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606535 prefixEnd_7606535 := by exact prefixLift 7606535
  have htrace : WordTrace (prefixWord ++ tailWord_7606535) baseStart_7606535 baseEnd_7606535 := by
    simpa [prefixWord, tailWord_7606535, baseEnd_7606535] using wordTrace_append hprefix tailTrace_7606535
  have hstable : (prefixWord ++ tailWord_7606535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606535).length < 2 ^ (prefixWord ++ tailWord_7606535).sum := by decide
  have hdescent : baseEnd_7606535 < baseStart_7606535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606540 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7606540 : Nat := 118140960795 + 7606540 * 2 ^ 59
def prefixEnd_7606540 : Nat := 4983230072969 + 3 ^ 40 * 7606540 * 2
def baseEnd_7606540 : Nat := 3905811137650774610968165

theorem tailTrace_7606540 : CollatzResearch.WordTrace tailWord_7606540 prefixEnd_7606540 3905811137650774610968165 := by
  unfold tailWord_7606540
  simp only [CollatzResearch.WordTrace]
  refine ⟨138716652931406074225492537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184955537241874765633990049 138716652931406074225492537)
  ·
    refine ⟨104037489698554555669119403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 138716652931406074225492537 104037489698554555669119403)
    ·
      refine ⟨156056234547831833503679105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104037489698554555669119403 156056234547831833503679105)
      ·
        refine ⟨117042175910873875127759329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156056234547831833503679105 117042175910873875127759329)
        ·
          refine ⟨87781631933155406345819497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117042175910873875127759329 87781631933155406345819497)
          ·
            refine ⟨65836223949866554759364623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87781631933155406345819497 65836223949866554759364623)
            ·
              refine ⟨98754335924799832139046935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65836223949866554759364623 98754335924799832139046935)
              ·
                refine ⟨148131503887199748208570403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98754335924799832139046935 148131503887199748208570403)
                ·
                  refine ⟨222197255830799622312855605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148131503887199748208570403 222197255830799622312855605)
                  ·
                    refine ⟨20830992734137464591830213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 222197255830799622312855605 20830992734137464591830213)
                    ·
                      refine ⟨3905811137650774610968165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20830992734137464591830213 3905811137650774610968165)
                      ·
                        rfl

theorem cell23_7606540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7606540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606540 prefixEnd_7606540 := by exact prefixLift 7606540
  have htrace : WordTrace (prefixWord ++ tailWord_7606540) baseStart_7606540 baseEnd_7606540 := by
    simpa [prefixWord, tailWord_7606540, baseEnd_7606540] using wordTrace_append hprefix tailTrace_7606540
  have hstable : (prefixWord ++ tailWord_7606540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606540).length < 2 ^ (prefixWord ++ tailWord_7606540).sum := by decide
  have hdescent : baseEnd_7606540 < baseStart_7606540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606608 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2]
def baseStart_7606608 : Nat := 118140960795 + 7606608 * 2 ^ 59
def prefixEnd_7606608 : Nat := 4983230072969 + 3 ^ 40 * 7606608 * 2
def baseEnd_7606608 : Nat := 3905846054335280344917853

theorem tailTrace_7606608 : CollatzResearch.WordTrace tailWord_7606608 prefixEnd_7606608 3905846054335280344917853 := by
  unfold tailWord_7606608
  simp only [CollatzResearch.WordTrace]
  refine ⟨138717893013282898032230239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184957190684377197376306985 138717893013282898032230239)
  ·
    refine ⟨208076839519924347048345359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138717893013282898032230239 208076839519924347048345359)
    ·
      refine ⟨312115259279886520572518039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208076839519924347048345359 312115259279886520572518039)
      ·
        refine ⟨468172888919829780858777059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312115259279886520572518039 468172888919829780858777059)
        ·
          refine ⟨702259333379744671288165589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 468172888919829780858777059 702259333379744671288165589)
          ·
            refine ⟨16459203126087765733316381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 702259333379744671288165589 16459203126087765733316381)
            ·
              refine ⟨6172201172282912149993643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16459203126087765733316381 6172201172282912149993643)
              ·
                refine ⟨9258301758424368224990465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6172201172282912149993643 9258301758424368224990465)
                ·
                  refine ⟨6943726318818276168742849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9258301758424368224990465 6943726318818276168742849)
                  ·
                    refine ⟨5207794739113707126557137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6943726318818276168742849 5207794739113707126557137)
                    ·
                      refine ⟨3905846054335280344917853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207794739113707126557137 3905846054335280344917853)
                      ·
                        rfl

theorem cell23_7606608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 2, 2].length) (baseStart_7606608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606608 prefixEnd_7606608 := by exact prefixLift 7606608
  have htrace : WordTrace (prefixWord ++ tailWord_7606608) baseStart_7606608 baseEnd_7606608 := by
    simpa [prefixWord, tailWord_7606608, baseEnd_7606608] using wordTrace_append hprefix tailTrace_7606608
  have hstable : (prefixWord ++ tailWord_7606608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606608).length < 2 ^ (prefixWord ++ tailWord_7606608).sum := by decide
  have hdescent : baseEnd_7606608 < baseStart_7606608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606627 : List Nat := [1, 1, 1, 5, 2, 1, 2, 3, 2, 5]
def baseStart_7606627 : Nat := 118140960795 + 7606627 * 2 ^ 59
def prefixEnd_7606627 : Nat := 4983230072969 + 3 ^ 40 * 7606627 * 2
def baseEnd_7606627 : Nat := 1301951936822571923526755

theorem tailTrace_7606627 : CollatzResearch.WordTrace tailWord_7606627 prefixEnd_7606627 1301951936822571923526755 := by
  unfold tailWord_7606627
  simp only [CollatzResearch.WordTrace]
  refine ⟨277436479013496962309402135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184957652675664641539601423 277436479013496962309402135)
  ·
    refine ⟨416154718520245443464103203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277436479013496962309402135 416154718520245443464103203)
    ·
      refine ⟨624232077780368165196154805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 416154718520245443464103203 624232077780368165196154805)
      ·
        refine ⟨58521757291909515487139513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 624232077780368165196154805 58521757291909515487139513)
        ·
          refine ⟨43891317968932136615354635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58521757291909515487139513 43891317968932136615354635)
          ·
            refine ⟨65836976953398204923031953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43891317968932136615354635 65836976953398204923031953)
            ·
              refine ⟨49377732715048653692273965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65836976953398204923031953 49377732715048653692273965)
              ·
                refine ⟨18516649768143245134602737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49377732715048653692273965 18516649768143245134602737)
                ·
                  refine ⟨13887487326107433850952053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18516649768143245134602737 13887487326107433850952053)
                  ·
                    refine ⟨1301951936822571923526755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13887487326107433850952053 1301951936822571923526755)
                    ·
                      rfl

theorem cell23_7606627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].length) (baseStart_7606627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606627 prefixEnd_7606627 := by exact prefixLift 7606627
  have htrace : WordTrace (prefixWord ++ tailWord_7606627) baseStart_7606627 baseEnd_7606627 := by
    simpa [prefixWord, tailWord_7606627, baseEnd_7606627] using wordTrace_append hprefix tailTrace_7606627
  have hstable : (prefixWord ++ tailWord_7606627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606627).length < 2 ^ (prefixWord ++ tailWord_7606627).sum := by decide
  have hdescent : baseEnd_7606627 < baseStart_7606627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606631 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 5]
def baseStart_7606631 : Nat := 118140960795 + 7606631 * 2 ^ 59
def prefixEnd_7606631 : Nat := 4983230072969 + 3 ^ 40 * 7606631 * 2
def baseEnd_7606631 : Nat := 433984207154481528325583

theorem tailTrace_7606631 : CollatzResearch.WordTrace tailWord_7606631 prefixEnd_7606631 433984207154481528325583 := by
  unfold tailWord_7606631
  simp only [CollatzResearch.WordTrace]
  refine ⟨277436624905482470992547747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184957749936988313995031831 277436624905482470992547747)
  ·
    refine ⟨416154937358223706488821621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277436624905482470992547747 416154937358223706488821621)
    ·
      refine ⟨39014525377333472483327027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 416154937358223706488821621 39014525377333472483327027)
      ·
        refine ⟨58521788066000208724990541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39014525377333472483327027 58521788066000208724990541)
        ·
          refine ⟨21945670524750078271871453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58521788066000208724990541 21945670524750078271871453)
          ·
            refine ⟨8229626446781279351951795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21945670524750078271871453 8229626446781279351951795)
            ·
              refine ⟨12344439670171919027927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8229626446781279351951795 12344439670171919027927693)
              ·
                refine ⟨4629164876314469635472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12344439670171919027927693 4629164876314469635472885)
                ·
                  refine ⟨433984207154481528325583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4629164876314469635472885 433984207154481528325583)
                  ·
                    rfl

theorem cell23_7606631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 5].length) (baseStart_7606631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606631 prefixEnd_7606631 := by exact prefixLift 7606631
  have htrace : WordTrace (prefixWord ++ tailWord_7606631) baseStart_7606631 baseEnd_7606631 := by
    simpa [prefixWord, tailWord_7606631, baseEnd_7606631] using wordTrace_append hprefix tailTrace_7606631
  have hstable : (prefixWord ++ tailWord_7606631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606631).length < 2 ^ (prefixWord ++ tailWord_7606631).sum := by decide
  have hdescent : baseEnd_7606631 < baseStart_7606631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606637 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_7606637 : Nat := 118140960795 + 7606637 * 2 ^ 59
def prefixEnd_7606637 : Nat := 4983230072969 + 3 ^ 40 * 7606637 * 2
def baseEnd_7606637 : Nat := 3905860945274260731455219

theorem tailTrace_7606637 : CollatzResearch.WordTrace tailWord_7606637 prefixEnd_7606637 3905860945274260731455219 := by
  unfold tailWord_7606637
  simp only [CollatzResearch.WordTrace]
  refine ⟨277436843743460734017266165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 184957895828973822678177443 277436843743460734017266165)
  ·
    refine ⟨26009704100949443814118703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 277436843743460734017266165 26009704100949443814118703)
    ·
      refine ⟨39014556151424165721178055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26009704100949443814118703 39014556151424165721178055)
      ·
        refine ⟨58521834227136248581767083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39014556151424165721178055 58521834227136248581767083)
        ·
          refine ⟨87782751340704372872650625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58521834227136248581767083 87782751340704372872650625)
          ·
            refine ⟨65837063505528279654487969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87782751340704372872650625 65837063505528279654487969)
            ·
              refine ⟨49377797629146209740865977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65837063505528279654487969 49377797629146209740865977)
              ·
                refine ⟨37033348221859657305649483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49377797629146209740865977 37033348221859657305649483)
                ·
                  refine ⟨55550022332789485958474225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37033348221859657305649483 55550022332789485958474225)
                  ·
                    refine ⟨41662516749592114468855669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55550022332789485958474225 41662516749592114468855669)
                    ·
                      refine ⟨3905860945274260731455219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 41662516749592114468855669 3905860945274260731455219)
                      ·
                        rfl

theorem cell23_7606637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_7606637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606637 prefixEnd_7606637 := by exact prefixLift 7606637
  have htrace : WordTrace (prefixWord ++ tailWord_7606637) baseStart_7606637 baseEnd_7606637 := by
    simpa [prefixWord, tailWord_7606637, baseEnd_7606637] using wordTrace_append hprefix tailTrace_7606637
  have hstable : (prefixWord ++ tailWord_7606637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606637).length < 2 ^ (prefixWord ++ tailWord_7606637).sum := by decide
  have hdescent : baseEnd_7606637 < baseStart_7606637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7606664 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7606664 : Nat := 118140960795 + 7606664 * 2 ^ 59
def prefixEnd_7606664 : Nat := 4983230072969 + 3 ^ 40 * 7606664 * 2
def baseEnd_7606664 : Nat := 3905874809251932125817595

theorem tailTrace_7606664 : CollatzResearch.WordTrace tailWord_7606664 prefixEnd_7606664 3905874809251932125817595 := by
  unfold tailWord_7606664
  simp only [CollatzResearch.WordTrace]
  refine ⟨138718914257181458814249523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 184958552342908611752332697 138718914257181458814249523)
  ·
    refine ⟨208078371385772188221374285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138718914257181458814249523 208078371385772188221374285)
    ·
      refine ⟨78029389269664570583015357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208078371385772188221374285 78029389269664570583015357)
      ·
        refine ⟨29261020976124213968630759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78029389269664570583015357 29261020976124213968630759)
        ·
          refine ⟨43891531464186320952946139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29261020976124213968630759 43891531464186320952946139)
          ·
            refine ⟨65837297196279481429419209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43891531464186320952946139 65837297196279481429419209)
            ·
              refine ⟨49377972897209611072064407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65837297196279481429419209 49377972897209611072064407)
              ·
                refine ⟨74066959345814416608096611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49377972897209611072064407 74066959345814416608096611)
                ·
                  refine ⟨111100439018721624912144917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74066959345814416608096611 111100439018721624912144917)
                  ·
                    refine ⟨5207833079002576167756793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 111100439018721624912144917 5207833079002576167756793)
                    ·
                      refine ⟨3905874809251932125817595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5207833079002576167756793 3905874809251932125817595)
                      ·
                        rfl

theorem cell23_7606664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7606664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7606664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7606664 prefixEnd_7606664 := by exact prefixLift 7606664
  have htrace : WordTrace (prefixWord ++ tailWord_7606664) baseStart_7606664 baseEnd_7606664 := by
    simpa [prefixWord, tailWord_7606664, baseEnd_7606664] using wordTrace_append hprefix tailTrace_7606664
  have hstable : (prefixWord ++ tailWord_7606664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7606664).length < 2 ^ (prefixWord ++ tailWord_7606664).sum := by decide
  have hdescent : baseEnd_7606664 < baseStart_7606664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7606664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
