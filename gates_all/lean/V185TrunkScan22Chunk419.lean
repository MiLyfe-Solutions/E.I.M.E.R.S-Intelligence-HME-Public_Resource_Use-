import V185TrunkScan22Chunk418

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3736172 : List Nat := [2, 2, 1, 1, 3, 1, 2, 5, 5]
def baseStart_3736172 : Nat := 118140960795 + 3736172 * 2 ^ 59
def prefixEnd_3736172 : Nat := 4983230072969 + 3 ^ 40 * 3736172 * 2
def baseEnd_3736172 : Nat := 426322676415569209681703

theorem tailTrace_3736172 : CollatzResearch.WordTrace tailWord_3736172 prefixEnd_3736172 426322676415569209681703 := by
  unfold tailWord_3736172
  simp only [CollatzResearch.WordTrace]
  refine ⟨68134693910247203110989385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90846258546996270814652513 68134693910247203110989385)
  ·
    refine ⟨51101020432685402333242039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68134693910247203110989385 51101020432685402333242039)
    ·
      refine ⟨76651530649028103499863059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51101020432685402333242039 76651530649028103499863059)
      ·
        refine ⟨114977295973542155249794589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76651530649028103499863059 114977295973542155249794589)
        ·
          refine ⟨43116485990078308218672971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114977295973542155249794589 43116485990078308218672971)
          ·
            refine ⟨64674728985117462328009457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43116485990078308218672971 64674728985117462328009457)
            ·
              refine ⟨48506046738838096746007093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64674728985117462328009457 48506046738838096746007093)
              ·
                refine ⟨4547441881766071569938165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48506046738838096746007093 4547441881766071569938165)
                ·
                  refine ⟨426322676415569209681703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4547441881766071569938165 426322676415569209681703)
                  ·
                    rfl

theorem cell22_3736172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_3736172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736172 prefixEnd_3736172 := by exact prefixLift 3736172
  have htrace : WordTrace (prefixWord ++ tailWord_3736172) baseStart_3736172 baseEnd_3736172 := by
    simpa [prefixWord, tailWord_3736172, baseEnd_3736172] using wordTrace_append hprefix tailTrace_3736172
  have hstable : (prefixWord ++ tailWord_3736172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736172).length < 2 ^ (prefixWord ++ tailWord_3736172).sum := by decide
  have hdescent : baseEnd_3736172 < baseStart_3736172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736210 : List Nat := [3, 2, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3736210 : Nat := 118140960795 + 3736210 * 2 ^ 59
def prefixEnd_3736210 : Nat := 4983230072969 + 3 ^ 40 * 3736210 * 2
def baseEnd_3736210 : Nat := 1278981037423288196594993

theorem tailTrace_3736210 : CollatzResearch.WordTrace tailWord_3736210 prefixEnd_3736210 1278981037423288196594993 := by
  unfold tailWord_3736210
  simp only [CollatzResearch.WordTrace]
  refine ⟨34067693448589184677965521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90847182529571159141241389 34067693448589184677965521)
  ·
    refine ⟨25550770086441888508474141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34067693448589184677965521 25550770086441888508474141)
    ·
      refine ⟨9581538782415708190677803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25550770086441888508474141 9581538782415708190677803)
      ·
        refine ⟨14372308173623562286016705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9581538782415708190677803 14372308173623562286016705)
        ·
          refine ⟨10779231130217671714512529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14372308173623562286016705 10779231130217671714512529)
          ·
            refine ⟨8084423347663253785884397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10779231130217671714512529 8084423347663253785884397)
            ·
              refine ⟨3031658755373720169706649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8084423347663253785884397 3031658755373720169706649)
              ·
                refine ⟨2273744066530290127279987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031658755373720169706649 2273744066530290127279987)
                ·
                  refine ⟨3410616099795435190919981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273744066530290127279987 3410616099795435190919981)
                  ·
                    refine ⟨1278981037423288196594993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410616099795435190919981 1278981037423288196594993)
                    ·
                      rfl

theorem cell22_3736210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3736210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736210 prefixEnd_3736210 := by exact prefixLift 3736210
  have htrace : WordTrace (prefixWord ++ tailWord_3736210) baseStart_3736210 baseEnd_3736210 := by
    simpa [prefixWord, tailWord_3736210, baseEnd_3736210] using wordTrace_append hprefix tailTrace_3736210
  have hstable : (prefixWord ++ tailWord_3736210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736210).length < 2 ^ (prefixWord ++ tailWord_3736210).sum := by decide
  have hdescent : baseEnd_3736210 < baseStart_3736210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736264 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_3736264 : Nat := 118140960795 + 3736264 * 2 ^ 59
def prefixEnd_3736264 : Nat := 4983230072969 + 3 ^ 40 * 3736264 * 2
def baseEnd_3736264 : Nat := 1278999522726850055744827

theorem tailTrace_3736264 : CollatzResearch.WordTrace tailWord_3736264 prefixEnd_3736264 1278999522726850055744827 := by
  unfold tailWord_3736264
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136371668080552967163923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90848495557440737289551897 68136371668080552967163923)
  ·
    refine ⟨102204557502120829450745885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68136371668080552967163923 102204557502120829450745885)
    ·
      refine ⟨38326709063295311044029707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102204557502120829450745885 38326709063295311044029707)
      ·
        refine ⟨57490063594942966566044561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38326709063295311044029707 57490063594942966566044561)
        ·
          refine ⟨43117547696207224924533421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57490063594942966566044561 43117547696207224924533421)
          ·
            refine ⟨16169080386077709346700033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43117547696207224924533421 16169080386077709346700033)
            ·
              refine ⟨12126810289558282010025025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169080386077709346700033 12126810289558282010025025)
              ·
                refine ⟨9095107717168711507518769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12126810289558282010025025 9095107717168711507518769)
                ·
                  refine ⟨6821330787876533630639077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095107717168711507518769 6821330787876533630639077)
                  ·
                    refine ⟨1278999522726850055744827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821330787876533630639077 1278999522726850055744827)
                    ·
                      rfl

theorem cell22_3736264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_3736264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736264 prefixEnd_3736264 := by exact prefixLift 3736264
  have htrace : WordTrace (prefixWord ++ tailWord_3736264) baseStart_3736264 baseEnd_3736264 := by
    simpa [prefixWord, tailWord_3736264, baseEnd_3736264] using wordTrace_append hprefix tailTrace_3736264
  have hstable : (prefixWord ++ tailWord_3736264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736264).length < 2 ^ (prefixWord ++ tailWord_3736264).sum := by decide
  have hdescent : baseEnd_3736264 < baseStart_3736264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736266 : List Nat := [3, 1, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3736266 : Nat := 118140960795 + 3736266 * 2 ^ 59
def prefixEnd_3736266 : Nat := 4983230072969 + 3 ^ 40 * 3736266 * 2
def baseEnd_3736266 : Nat := 1279000207367722717194821

theorem tailTrace_3736266 : CollatzResearch.WordTrace tailWord_3736266 prefixEnd_3736266 1279000207367722717194821 := by
  unfold tailWord_3736266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34068204070538465068975163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90848544188102573517267101 34068204070538465068975163)
  ·
    refine ⟨51102306105807697603462745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34068204070538465068975163 51102306105807697603462745)
    ·
      refine ⟨38326729579355773202597059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51102306105807697603462745 38326729579355773202597059)
      ·
        refine ⟨57490094369033659803895589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38326729579355773202597059 57490094369033659803895589)
        ·
          refine ⟨10779392694193811213230423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57490094369033659803895589 10779392694193811213230423)
          ·
            refine ⟨16169089041290716819845635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779392694193811213230423 16169089041290716819845635)
            ·
              refine ⟨24253633561936075229768453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16169089041290716819845635 24253633561936075229768453)
              ·
                refine ⟨4547556292863014105581585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24253633561936075229768453 4547556292863014105581585)
                ·
                  refine ⟨3410667219647260579186189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4547556292863014105581585 3410667219647260579186189)
                  ·
                    refine ⟨1279000207367722717194821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410667219647260579186189 1279000207367722717194821)
                    ·
                      rfl

theorem cell22_3736266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3736266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736266 prefixEnd_3736266 := by exact prefixLift 3736266
  have htrace : WordTrace (prefixWord ++ tailWord_3736266) baseStart_3736266 baseEnd_3736266 := by
    simpa [prefixWord, tailWord_3736266, baseEnd_3736266] using wordTrace_append hprefix tailTrace_3736266
  have hstable : (prefixWord ++ tailWord_3736266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736266).length < 2 ^ (prefixWord ++ tailWord_3736266).sum := by decide
  have hdescent : baseEnd_3736266 < baseStart_3736266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736268 : List Nat := [2, 2, 1, 5, 1, 1, 4, 2, 4]
def baseStart_3736268 : Nat := 118140960795 + 3736268 * 2 ^ 59
def prefixEnd_3736268 : Nat := 4983230072969 + 3 ^ 40 * 3736268 * 2
def baseEnd_3736268 : Nat := 426333630669531792881605

theorem tailTrace_3736268 : CollatzResearch.WordTrace tailWord_3736268 prefixEnd_3736268 426333630669531792881605 := by
  unfold tailWord_3736268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136444614073307308736729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90848592818764409744982305 68136444614073307308736729)
  ·
    refine ⟨51102333460554980481552547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68136444614073307308736729 51102333460554980481552547)
    ·
      refine ⟨76653500190832470722328821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51102333460554980481552547 76653500190832470722328821)
      ·
        refine ⟨7186265642890544130218327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76653500190832470722328821 7186265642890544130218327)
        ·
          refine ⟨10779398464335816195327491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7186265642890544130218327 10779398464335816195327491)
          ·
            refine ⟨16169097696503724292991237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779398464335816195327491 16169097696503724292991237)
            ·
              refine ⟨3031705818094448304935857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16169097696503724292991237 3031705818094448304935857)
              ·
                refine ⟨2273779363570836228701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031705818094448304935857 2273779363570836228701893)
                ·
                  refine ⟨426333630669531792881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273779363570836228701893 426333630669531792881605)
                  ·
                    rfl

theorem cell22_3736268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_3736268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736268 prefixEnd_3736268 := by exact prefixLift 3736268
  have htrace : WordTrace (prefixWord ++ tailWord_3736268) baseStart_3736268 baseEnd_3736268 := by
    simpa [prefixWord, tailWord_3736268, baseEnd_3736268] using wordTrace_append hprefix tailTrace_3736268
  have hstable : (prefixWord ++ tailWord_3736268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736268).length < 2 ^ (prefixWord ++ tailWord_3736268).sum := by decide
  have hdescent : baseEnd_3736268 < baseStart_3736268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736279 : List Nat := [1, 1, 3, 2, 1, 6, 1, 7]
def baseStart_3736279 : Nat := 118140960795 + 3736279 * 2 ^ 59
def prefixEnd_3736279 : Nat := 4983230072969 + 3 ^ 40 * 3736279 * 2
def baseEnd_3736279 : Nat := 142111628614821668513309

theorem tailTrace_3736279 : CollatzResearch.WordTrace tailWord_3736279 prefixEnd_3736279 142111628614821668513309 := by
  unfold tailWord_3736279
  simp only [CollatzResearch.WordTrace]
  refine ⟨136273290431106763496123891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90848860287404508997415927 136273290431106763496123891)
  ·
    refine ⟨204409935646660145244185837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136273290431106763496123891 204409935646660145244185837)
    ·
      refine ⟨76653725867497554466569689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204409935646660145244185837 76653725867497554466569689)
      ·
        refine ⟨57490294400623165849927267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76653725867497554466569689 57490294400623165849927267)
        ·
          refine ⟨86235441600934748774890901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57490294400623165849927267 86235441600934748774890901)
          ·
            refine ⟨4042286325043816348823011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86235441600934748774890901 4042286325043816348823011)
            ·
              refine ⟨6063429487565724523234517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042286325043816348823011 6063429487565724523234517)
              ·
                refine ⟨142111628614821668513309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6063429487565724523234517 142111628614821668513309)
                ·
                  rfl

theorem cell22_3736279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 7].length) (baseStart_3736279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736279 prefixEnd_3736279 := by exact prefixLift 3736279
  have htrace : WordTrace (prefixWord ++ tailWord_3736279) baseStart_3736279 baseEnd_3736279 := by
    simpa [prefixWord, tailWord_3736279, baseEnd_3736279] using wordTrace_append hprefix tailTrace_3736279
  have hstable : (prefixWord ++ tailWord_3736279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736279).length < 2 ^ (prefixWord ++ tailWord_3736279).sum := by decide
  have hdescent : baseEnd_3736279 < baseStart_3736279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736296 : List Nat := [2, 1, 4, 1, 4, 1, 3, 6]
def baseStart_3736296 : Nat := 118140960795 + 3736296 * 2 ^ 59
def prefixEnd_3736296 : Nat := 4983230072969 + 3 ^ 40 * 3736296 * 2
def baseEnd_3736296 : Nat := 142112275220090293216081

theorem tailTrace_3736296 : CollatzResearch.WordTrace tailWord_3736296 prefixEnd_3736296 142112275220090293216081 := by
  unfold tailWord_3736296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136955236022587699746371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90849273648030116932995161 68136955236022587699746371)
  ·
    refine ⟨102205432854033881549619557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68136955236022587699746371 102205432854033881549619557)
    ·
      refine ⟨19163518660131352790553667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102205432854033881549619557 19163518660131352790553667)
      ·
        refine ⟨28745277990197029185830501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19163518660131352790553667 28745277990197029185830501)
        ·
          refine ⟨5389739623161942972343219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28745277990197029185830501 5389739623161942972343219)
          ·
            refine ⟨8084609434742914458514829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389739623161942972343219 8084609434742914458514829)
            ·
              refine ⟨3031728538028592921943061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8084609434742914458514829 3031728538028592921943061)
              ·
                refine ⟨142112275220090293216081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3031728538028592921943061 142112275220090293216081)
                ·
                  rfl

theorem cell22_3736296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 6].length) (baseStart_3736296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736296 prefixEnd_3736296 := by exact prefixLift 3736296
  have htrace : WordTrace (prefixWord ++ tailWord_3736296) baseStart_3736296 baseEnd_3736296 := by
    simpa [prefixWord, tailWord_3736296, baseEnd_3736296] using wordTrace_append hprefix tailTrace_3736296
  have hstable : (prefixWord ++ tailWord_3736296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736296).length < 2 ^ (prefixWord ++ tailWord_3736296).sum := by decide
  have hdescent : baseEnd_3736296 < baseStart_3736296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736307 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 7]
def baseStart_3736307 : Nat := 118140960795 + 3736307 * 2 ^ 59
def prefixEnd_3736307 : Nat := 4983230072969 + 3 ^ 40 * 3736307 * 2
def baseEnd_3736307 : Nat := 426338080835204092306565

theorem tailTrace_3736307 : CollatzResearch.WordTrace tailWord_3736307 prefixEnd_3736307 426338080835204092306565 := by
  unfold tailWord_3736307
  simp only [CollatzResearch.WordTrace]
  refine ⟨136274311675005324278143175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90849541116670216185428783 136274311675005324278143175)
  ·
    refine ⟨204411467512507986417214763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136274311675005324278143175 204411467512507986417214763)
    ·
      refine ⟨306617201268761979625822145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204411467512507986417214763 306617201268761979625822145)
      ·
        refine ⟨229962900951571484719366609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306617201268761979625822145 229962900951571484719366609)
        ·
          refine ⟨172472175713678613539524957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229962900951571484719366609 172472175713678613539524957)
          ·
            refine ⟨64677065892629480077321859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172472175713678613539524957 64677065892629480077321859)
            ·
              refine ⟨97015598838944220115982789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64677065892629480077321859 97015598838944220115982789)
              ·
                refine ⟨18190424782302041271746773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97015598838944220115982789 18190424782302041271746773)
                ·
                  refine ⟨426338080835204092306565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18190424782302041271746773 426338080835204092306565)
                  ·
                    rfl

theorem cell22_3736307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_3736307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736307 prefixEnd_3736307 := by exact prefixLift 3736307
  have htrace : WordTrace (prefixWord ++ tailWord_3736307) baseStart_3736307 baseEnd_3736307 := by
    simpa [prefixWord, tailWord_3736307, baseEnd_3736307] using wordTrace_append hprefix tailTrace_3736307
  have hstable : (prefixWord ++ tailWord_3736307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736307).length < 2 ^ (prefixWord ++ tailWord_3736307).sum := by decide
  have hdescent : baseEnd_3736307 < baseStart_3736307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736324 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3736324 : Nat := 118140960795 + 3736324 * 2 ^ 59
def prefixEnd_3736324 : Nat := 4983230072969 + 3 ^ 40 * 3736324 * 2
def baseEnd_3736324 : Nat := 426340020651009966414881

theorem tailTrace_3736324 : CollatzResearch.WordTrace tailWord_3736324 prefixEnd_3736324 426340020651009966414881 := by
  unfold tailWord_3736324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137465857971868090756013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90849954477295824121008017 68137465857971868090756013)
  ·
    refine ⟨25551549696739450534033505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68137465857971868090756013 25551549696739450534033505)
    ·
      refine ⟨19163662272554587900525129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25551549696739450534033505 19163662272554587900525129)
      ·
        refine ⟨14372746704415940925393847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19163662272554587900525129 14372746704415940925393847)
        ·
          refine ⟨21559120056623911388090771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14372746704415940925393847 21559120056623911388090771)
          ·
            refine ⟨32338680084935867082136157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559120056623911388090771 32338680084935867082136157)
            ·
              refine ⟨12127005031850950155801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32338680084935867082136157 12127005031850950155801059)
              ·
                refine ⟨18190507547776425233701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12127005031850950155801059 18190507547776425233701589)
                ·
                  refine ⟨426340020651009966414881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18190507547776425233701589 426340020651009966414881)
                  ·
                    rfl

theorem cell22_3736324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3736324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736324 prefixEnd_3736324 := by exact prefixLift 3736324
  have htrace : WordTrace (prefixWord ++ tailWord_3736324) baseStart_3736324 baseEnd_3736324 := by
    simpa [prefixWord, tailWord_3736324, baseEnd_3736324] using wordTrace_append hprefix tailTrace_3736324
  have hstable : (prefixWord ++ tailWord_3736324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736324).length < 2 ^ (prefixWord ++ tailWord_3736324).sum := by decide
  have hdescent : baseEnd_3736324 < baseStart_3736324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736328 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 1, 3]
def baseStart_3736328 : Nat := 118140960795 + 3736328 * 2 ^ 59
def prefixEnd_3736328 : Nat := 4983230072969 + 3 ^ 40 * 3736328 * 2
def baseEnd_3736328 : Nat := 1279021431234775222144631

theorem tailTrace_3736328 : CollatzResearch.WordTrace tailWord_3736328 prefixEnd_3736328 1279021431234775222144631 := by
  unfold tailWord_3736328
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137538803964622432328819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90850051738619496576438425 68137538803964622432328819)
  ·
    refine ⟨102206308205946933648493229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68137538803964622432328819 102206308205946933648493229)
    ·
      refine ⟨38327365577230100118184961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102206308205946933648493229 38327365577230100118184961)
      ·
        refine ⟨28745524182922575088638721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38327365577230100118184961 28745524182922575088638721)
        ·
          refine ⟨21559143137191931316479041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28745524182922575088638721 21559143137191931316479041)
          ·
            refine ⟨16169357352893948487359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21559143137191931316479041 16169357352893948487359281)
            ·
              refine ⟨12127018014670461365519461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169357352893948487359281 12127018014670461365519461)
              ·
                refine ⟨2273815877750711506034899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12127018014670461365519461 2273815877750711506034899)
                ·
                  refine ⟨3410723816626067259052349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2273815877750711506034899 3410723816626067259052349)
                  ·
                    refine ⟨1279021431234775222144631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3410723816626067259052349 1279021431234775222144631)
                    ·
                      rfl

theorem cell22_3736328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_3736328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736328 prefixEnd_3736328 := by exact prefixLift 3736328
  have htrace : WordTrace (prefixWord ++ tailWord_3736328) baseStart_3736328 baseEnd_3736328 := by
    simpa [prefixWord, tailWord_3736328, baseEnd_3736328] using wordTrace_append hprefix tailTrace_3736328
  have hstable : (prefixWord ++ tailWord_3736328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736328).length < 2 ^ (prefixWord ++ tailWord_3736328).sum := by decide
  have hdescent : baseEnd_3736328 < baseStart_3736328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736341 : List Nat := [1, 3, 2, 1, 2, 2, 5, 1, 5]
def baseStart_3736341 : Nat := 118140960795 + 3736341 * 2 ^ 59
def prefixEnd_3736341 : Nat := 4983230072969 + 3 ^ 40 * 3736341 * 2
def baseEnd_3736341 : Nat := 426341960466815840523197

theorem tailTrace_3736341 : CollatzResearch.WordTrace tailWord_3736341 prefixEnd_3736341 426341960466815840523197 := by
  unfold tailWord_3736341
  simp only [CollatzResearch.WordTrace]
  refine ⟨136275551756882148084880877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90850367837921432056587251 136275551756882148084880877)
  ·
    refine ⟨51103331908830805531830329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136275551756882148084880877 51103331908830805531830329)
    ·
      refine ⟨38327498931623104148872747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51103331908830805531830329 38327498931623104148872747)
      ·
        refine ⟨57491248397434656223309121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38327498931623104148872747 57491248397434656223309121)
        ·
          refine ⟨43118436298075992167481841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57491248397434656223309121 43118436298075992167481841)
          ·
            refine ⟨32338827223556994125611381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43118436298075992167481841 32338827223556994125611381)
            ·
              refine ⟨3031765052208468199276067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32338827223556994125611381 3031765052208468199276067)
              ·
                refine ⟨4547647578312702298914101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3031765052208468199276067 4547647578312702298914101)
                ·
                  refine ⟨426341960466815840523197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4547647578312702298914101 426341960466815840523197)
                  ·
                    rfl

theorem cell22_3736341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_3736341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736341 prefixEnd_3736341 := by exact prefixLift 3736341
  have htrace : WordTrace (prefixWord ++ tailWord_3736341) baseStart_3736341 baseEnd_3736341 := by
    simpa [prefixWord, tailWord_3736341, baseEnd_3736341] using wordTrace_append hprefix tailTrace_3736341
  have hstable : (prefixWord ++ tailWord_3736341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736341).length < 2 ^ (prefixWord ++ tailWord_3736341).sum := by decide
  have hdescent : baseEnd_3736341 < baseStart_3736341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736371 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 1, 4]
def baseStart_3736371 : Nat := 118140960795 + 3736371 * 2 ^ 59
def prefixEnd_3736371 : Nat := 4983230072969 + 3 ^ 40 * 3736371 * 2
def baseEnd_3736371 : Nat := 1279036151013537443319499

theorem tailTrace_3736371 : CollatzResearch.WordTrace tailWord_3736371 prefixEnd_3736371 1279036151013537443319499 := by
  unfold tailWord_3736371
  simp only [CollatzResearch.WordTrace]
  refine ⟨136276645946773463208472967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90851097297848975472315311 136276645946773463208472967)
  ·
    refine ⟨204414968920160194812709451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136276645946773463208472967 204414968920160194812709451)
    ·
      refine ⟨306622453380240292219064177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204414968920160194812709451 306622453380240292219064177)
      ·
        refine ⟨229966840035180219164298133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306622453380240292219064177 229966840035180219164298133)
        ·
          refine ⟨10779695626649072773326475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 229966840035180219164298133 10779695626649072773326475)
          ·
            refine ⟨16169543439973609159989713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779695626649072773326475 16169543439973609159989713)
            ·
              refine ⟨12127157579980206869992285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16169543439973609159989713 12127157579980206869992285)
              ·
                refine ⟨4547684092492577576247107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12127157579980206869992285 4547684092492577576247107)
                ·
                  refine ⟨6821526138738866364370661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547684092492577576247107 6821526138738866364370661)
                  ·
                    refine ⟨1279036151013537443319499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821526138738866364370661 1279036151013537443319499)
                    ·
                      rfl

theorem cell22_3736371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 4].length) (baseStart_3736371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736371 prefixEnd_3736371 := by exact prefixLift 3736371
  have htrace : WordTrace (prefixWord ++ tailWord_3736371) baseStart_3736371 baseEnd_3736371 := by
    simpa [prefixWord, tailWord_3736371, baseEnd_3736371] using wordTrace_append hprefix tailTrace_3736371
  have hstable : (prefixWord ++ tailWord_3736371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736371).length < 2 ^ (prefixWord ++ tailWord_3736371).sum := by decide
  have hdescent : baseEnd_3736371 < baseStart_3736371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736416 : List Nat := [2, 1, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_3736416 : Nat := 118140960795 + 3736416 * 2 ^ 59
def prefixEnd_3736416 : Nat := 4983230072969 + 3 ^ 40 * 3736416 * 2
def baseEnd_3736416 : Nat := 1279051555433172325944361

theorem tailTrace_3736416 : CollatzResearch.WordTrace tailWord_3736416 prefixEnd_3736416 1279051555433172325944361 := by
  unfold tailWord_3736416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68139143615805217946930551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90852191487740290595907401 68139143615805217946930551)
  ·
    refine ⟨102208715423707826920395827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68139143615805217946930551 102208715423707826920395827)
    ·
      refine ⟨153313073135561740380593741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102208715423707826920395827 153313073135561740380593741)
      ·
        refine ⟨57492402425835652642722653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153313073135561740380593741 57492402425835652642722653)
        ·
          refine ⟨21559650909688369741020995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57492402425835652642722653 21559650909688369741020995)
          ·
            refine ⟨32339476364532554611531493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21559650909688369741020995 32339476364532554611531493)
            ·
              refine ⟨6063651818349853989662155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32339476364532554611531493 6063651818349853989662155)
              ·
                refine ⟨9095477727524780984493233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063651818349853989662155 9095477727524780984493233)
                ·
                  refine ⟨6821608295643585738369925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9095477727524780984493233 6821608295643585738369925)
                  ·
                    refine ⟨1279051555433172325944361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821608295643585738369925 1279051555433172325944361)
                    ·
                      rfl

theorem cell22_3736416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_3736416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736416 prefixEnd_3736416 := by exact prefixLift 3736416
  have htrace : WordTrace (prefixWord ++ tailWord_3736416) baseStart_3736416 baseEnd_3736416 := by
    simpa [prefixWord, tailWord_3736416, baseEnd_3736416] using wordTrace_append hprefix tailTrace_3736416
  have hstable : (prefixWord ++ tailWord_3736416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736416).length < 2 ^ (prefixWord ++ tailWord_3736416).sum := by decide
  have hdescent : baseEnd_3736416 < baseStart_3736416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736418 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3736418 : Nat := 118140960795 + 3736418 * 2 ^ 59
def prefixEnd_3736418 : Nat := 4983230072969 + 3 ^ 40 * 3736418 * 2
def baseEnd_3736418 : Nat := 1279052240074044987394355

theorem tailTrace_3736418 : CollatzResearch.WordTrace tailWord_3736418 prefixEnd_3736418 1279052240074044987394355 := by
  unfold tailWord_3736418
  simp only [CollatzResearch.WordTrace]
  refine ⟨34069590044400797558858477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90852240118402126823622605 34069590044400797558858477)
  ·
    refine ⟨12776096266650299084571929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34069590044400797558858477 12776096266650299084571929)
    ·
      refine ⟨9582072199987724313428947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12776096266650299084571929 9582072199987724313428947)
      ·
        refine ⟨14373108299981586470143421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9582072199987724313428947 14373108299981586470143421)
        ·
          refine ⟨5389915612493094926303783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14373108299981586470143421 5389915612493094926303783)
          ·
            refine ⟨8084873418739642389455675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5389915612493094926303783 8084873418739642389455675)
            ·
              refine ⟨12127310128109463584183513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084873418739642389455675 12127310128109463584183513)
              ·
                refine ⟨9095482596082097688137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12127310128109463584183513 9095482596082097688137635)
                ·
                  refine ⟨13643223894123146532206453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9095482596082097688137635 13643223894123146532206453)
                  ·
                    refine ⟨1279052240074044987394355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13643223894123146532206453 1279052240074044987394355)
                    ·
                      rfl

theorem cell22_3736418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3736418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736418 prefixEnd_3736418 := by exact prefixLift 3736418
  have htrace : WordTrace (prefixWord ++ tailWord_3736418) baseStart_3736418 baseEnd_3736418 := by
    simpa [prefixWord, tailWord_3736418, baseEnd_3736418] using wordTrace_append hprefix tailTrace_3736418
  have hstable : (prefixWord ++ tailWord_3736418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736418).length < 2 ^ (prefixWord ++ tailWord_3736418).sum := by decide
  have hdescent : baseEnd_3736418 < baseStart_3736418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736523 : List Nat := [1, 1, 1, 1, 3, 6, 2, 2, 1, 4]
def baseStart_3736523 : Nat := 118140960795 + 3736523 * 2 ^ 59
def prefixEnd_3736523 : Nat := 4983230072969 + 3 ^ 40 * 3736523 * 2
def baseEnd_3736523 : Nat := 1279088183719859713519033

theorem tailTrace_3736523 : CollatzResearch.WordTrace tailWord_3736523 prefixEnd_3736523 1279088183719859713519033 := by
  unfold tailWord_3736523
  simp only [CollatzResearch.WordTrace]
  refine ⟨136282189842222793168006223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90854793228148528778670815 136282189842222793168006223)
  ·
    refine ⟨204423284763334189752009335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136282189842222793168006223 204423284763334189752009335)
    ·
      refine ⟨306634927145001284628014003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204423284763334189752009335 306634927145001284628014003)
      ·
        refine ⟨459952390717501926942021005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306634927145001284628014003 459952390717501926942021005)
        ·
          refine ⟨172482146519063222603257877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 459952390717501926942021005 172482146519063222603257877)
          ·
            refine ⟨8085100618081088559527713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172482146519063222603257877 8085100618081088559527713)
            ·
              refine ⟨6063825463560816419645785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085100618081088559527713 6063825463560816419645785)
              ·
                refine ⟨4547869097670612314734339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063825463560816419645785 4547869097670612314734339)
                ·
                  refine ⟨6821803646505918472101509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547869097670612314734339 6821803646505918472101509)
                  ·
                    refine ⟨1279088183719859713519033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821803646505918472101509 1279088183719859713519033)
                    ·
                      rfl

theorem cell22_3736523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 4].length) (baseStart_3736523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736523 prefixEnd_3736523 := by exact prefixLift 3736523
  have htrace : WordTrace (prefixWord ++ tailWord_3736523) baseStart_3736523 baseEnd_3736523 := by
    simpa [prefixWord, tailWord_3736523, baseEnd_3736523] using wordTrace_append hprefix tailTrace_3736523
  have hstable : (prefixWord ++ tailWord_3736523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736523).length < 2 ^ (prefixWord ++ tailWord_3736523).sum := by decide
  have hdescent : baseEnd_3736523 < baseStart_3736523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736574 : List Nat := [4, 2, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3736574 : Nat := 118140960795 + 3736574 * 2 ^ 59
def prefixEnd_3736574 : Nat := 4983230072969 + 3 ^ 40 * 3736574 * 2
def baseEnd_3736574 : Nat := 1279105642062112580493877

theorem tailTrace_3736574 : CollatzResearch.WordTrace tailWord_3736574 prefixEnd_3736574 1279105642062112580493877 := by
  unfold tailWord_3736574
  simp only [CollatzResearch.WordTrace]
  refine ⟨17035506245629753609764097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90856033310025352585408517 17035506245629753609764097)
  ·
    refine ⟨12776629684222315207323073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17035506245629753609764097 12776629684222315207323073)
    ·
      refine ⟨9582472263166736405492305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12776629684222315207323073 9582472263166736405492305)
      ·
        refine ⟨7186854197375052304119229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9582472263166736405492305 7186854197375052304119229)
        ·
          refine ⟨2695070324015644614044711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7186854197375052304119229 2695070324015644614044711)
          ·
            refine ⟨4042605486023466921067067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695070324015644614044711 4042605486023466921067067)
            ·
              refine ⟨6063908229035200381600601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042605486023466921067067 6063908229035200381600601)
              ·
                refine ⟨4547931171776400286200451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6063908229035200381600601 4547931171776400286200451)
                ·
                  refine ⟨6821896757664600429300677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4547931171776400286200451 6821896757664600429300677)
                  ·
                    refine ⟨1279105642062112580493877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6821896757664600429300677 1279105642062112580493877)
                    ·
                      rfl

theorem cell22_3736574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3736574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736574 prefixEnd_3736574 := by exact prefixLift 3736574
  have htrace : WordTrace (prefixWord ++ tailWord_3736574) baseStart_3736574 baseEnd_3736574 := by
    simpa [prefixWord, tailWord_3736574, baseEnd_3736574] using wordTrace_append hprefix tailTrace_3736574
  have hstable : (prefixWord ++ tailWord_3736574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736574).length < 2 ^ (prefixWord ++ tailWord_3736574).sum := by decide
  have hdescent : baseEnd_3736574 < baseStart_3736574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736662 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3736662 : Nat := 118140960795 + 3736662 * 2 ^ 59
def prefixEnd_3736662 : Nat := 4983230072969 + 3 ^ 40 * 3736662 * 2
def baseEnd_3736662 : Nat := 426378588753503228097869

theorem tailTrace_3736662 : CollatzResearch.WordTrace tailWord_3736662 prefixEnd_3736662 426378588753503228097869 := by
  unfold tailWord_3736662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8517953724294951244207265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90858173059146146604877493 8517953724294951244207265)
  ·
    refine ⟨6388465293221213433155449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8517953724294951244207265 6388465293221213433155449)
    ·
      refine ⟨4791348969915910074866587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6388465293221213433155449 4791348969915910074866587)
      ·
        refine ⟨7187023454873865112299881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791348969915910074866587 7187023454873865112299881)
        ·
          refine ⟨5390267591155398834224911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187023454873865112299881 5390267591155398834224911)
          ·
            refine ⟨8085401386733098251337367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390267591155398834224911 8085401386733098251337367)
            ·
              refine ⟨12128102080099647377006051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8085401386733098251337367 12128102080099647377006051)
              ·
                refine ⟨18192153120149471065509077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12128102080099647377006051 18192153120149471065509077)
                ·
                  refine ⟨426378588753503228097869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18192153120149471065509077 426378588753503228097869)
                  ·
                    rfl

theorem cell22_3736662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3736662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736662 prefixEnd_3736662 := by exact prefixLift 3736662
  have htrace : WordTrace (prefixWord ++ tailWord_3736662) baseStart_3736662 baseEnd_3736662 := by
    simpa [prefixWord, tailWord_3736662, baseEnd_3736662] using wordTrace_append hprefix tailTrace_3736662
  have hstable : (prefixWord ++ tailWord_3736662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736662).length < 2 ^ (prefixWord ++ tailWord_3736662).sum := by decide
  have hdescent : baseEnd_3736662 < baseStart_3736662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736705 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_3736705 : Nat := 118140960795 + 3736705 * 2 ^ 59
def prefixEnd_3736705 : Nat := 4983230072969 + 3 ^ 40 * 3736705 * 2
def baseEnd_3736705 : Nat := 1279150486039271905468475

theorem tailTrace_3736705 : CollatzResearch.WordTrace tailWord_3736705 prefixEnd_3736705 1279150486039271905468475 := by
  unfold tailWord_3736705
  simp only [CollatzResearch.WordTrace]
  refine ⟨136288827927563438251131569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90859218618375625500754379 136288827927563438251131569)
  ·
    refine ⟨102216620945672578688348677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136288827927563438251131569 102216620945672578688348677)
    ·
      refine ⟨19165616427313608504065377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102216620945672578688348677 19165616427313608504065377)
      ·
        refine ⟨14374212320485206378049033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19165616427313608504065377 14374212320485206378049033)
        ·
          refine ⟨10780659240363904783536775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14374212320485206378049033 10780659240363904783536775)
          ·
            refine ⟨16170988860545857175305163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780659240363904783536775 16170988860545857175305163)
            ·
              refine ⟨24256483290818785762957745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16170988860545857175305163 24256483290818785762957745)
              ·
                refine ⟨18192362468114089322218309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24256483290818785762957745 18192362468114089322218309)
                ·
                  refine ⟨3411067962771391747915933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18192362468114089322218309 3411067962771391747915933)
                  ·
                    refine ⟨1279150486039271905468475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411067962771391747915933 1279150486039271905468475)
                    ·
                      rfl

theorem cell22_3736705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_3736705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736705 prefixEnd_3736705 := by exact prefixLift 3736705
  have htrace : WordTrace (prefixWord ++ tailWord_3736705) baseStart_3736705 baseEnd_3736705 := by
    simpa [prefixWord, tailWord_3736705, baseEnd_3736705] using wordTrace_append hprefix tailTrace_3736705
  have hstable : (prefixWord ++ tailWord_3736705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736705).length < 2 ^ (prefixWord ++ tailWord_3736705).sum := by decide
  have hdescent : baseEnd_3736705 < baseStart_3736705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736718 : List Nat := [4, 1, 1, 3, 2, 1, 10]
def baseStart_3736718 : Nat := 118140960795 + 3736718 * 2 ^ 59
def prefixEnd_3736718 : Nat := 4983230072969 + 3 ^ 40 * 3736718 * 2
def baseEnd_3736718 : Nat := 47376108748331266847905

theorem tailTrace_3736718 : CollatzResearch.WordTrace tailWord_3736718 prefixEnd_3736718 47376108748331266847905 := by
  unfold tailWord_3736718
  simp only [CollatzResearch.WordTrace]
  refine ⟨17036162759564542683919351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90859534717677560980903205 17036162759564542683919351)
  ·
    refine ⟨25554244139346814025879027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17036162759564542683919351 25554244139346814025879027)
    ·
      refine ⟨38331366209020221038818541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25554244139346814025879027 38331366209020221038818541)
      ·
        refine ⟨14374262328382582889556953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38331366209020221038818541 14374262328382582889556953)
        ·
          refine ⟨10780696746286937167167715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14374262328382582889556953 10780696746286937167167715)
          ·
            refine ⟨16171045119430405750751573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780696746286937167167715 16171045119430405750751573)
            ·
              refine ⟨47376108748331266847905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16171045119430405750751573 47376108748331266847905)
              ·
                rfl

theorem cell22_3736718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 10].length) (baseStart_3736718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736718 prefixEnd_3736718 := by exact prefixLift 3736718
  have htrace : WordTrace (prefixWord ++ tailWord_3736718) baseStart_3736718 baseEnd_3736718 := by
    simpa [prefixWord, tailWord_3736718, baseEnd_3736718] using wordTrace_append hprefix tailTrace_3736718
  have hstable : (prefixWord ++ tailWord_3736718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736718).length < 2 ^ (prefixWord ++ tailWord_3736718).sum := by decide
  have hdescent : baseEnd_3736718 < baseStart_3736718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736735 : List Nat := [1, 1, 2, 6, 2, 1, 2, 7]
def baseStart_3736735 : Nat := 118140960795 + 3736735 * 2 ^ 59
def prefixEnd_3736735 : Nat := 4983230072969 + 3 ^ 40 * 3736735 * 2
def baseEnd_3736735 : Nat := 142128972850262425246487

theorem tailTrace_3736735 : CollatzResearch.WordTrace tailWord_3736735 prefixEnd_3736735 142128972850262425246487 := by
  unfold tailWord_3736735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136289922117454753374723659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90859948078303168916482439 136289922117454753374723659)
  ·
    refine ⟨204434883176182130062085489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136289922117454753374723659 204434883176182130062085489)
    ·
      refine ⟨153326162382136597546564117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204434883176182130062085489 153326162382136597546564117)
      ·
        refine ⟨7187163861662653009995193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153326162382136597546564117 7187163861662653009995193)
        ·
          refine ⟨5390372896246989757496395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187163861662653009995193 5390372896246989757496395)
          ·
            refine ⟨8085559344370484636244593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390372896246989757496395 8085559344370484636244593)
            ·
              refine ⟨6064169508277863477183445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085559344370484636244593 6064169508277863477183445)
              ·
                refine ⟨142128972850262425246487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6064169508277863477183445 142128972850262425246487)
                ·
                  rfl

theorem cell22_3736735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 7].length) (baseStart_3736735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736735 prefixEnd_3736735 := by exact prefixLift 3736735
  have htrace : WordTrace (prefixWord ++ tailWord_3736735) baseStart_3736735 baseEnd_3736735 := by
    simpa [prefixWord, tailWord_3736735, baseEnd_3736735] using wordTrace_append hprefix tailTrace_3736735
  have hstable : (prefixWord ++ tailWord_3736735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736735).length < 2 ^ (prefixWord ++ tailWord_3736735).sum := by decide
  have hdescent : baseEnd_3736735 < baseStart_3736735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736810 : List Nat := [3, 1, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3736810 : Nat := 118140960795 + 3736810 * 2 ^ 59
def prefixEnd_3736810 : Nat := 4983230072969 + 3 ^ 40 * 3736810 * 2
def baseEnd_3736810 : Nat := 1279186429685086631593153

theorem tailTrace_3736810 : CollatzResearch.WordTrace tailWord_3736810 prefixEnd_3736810 1279186429685086631593153 := by
  unfold tailWord_3736810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34073164398045760295925971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90861771728122027455802589 34073164398045760295925971)
  ·
    refine ⟨51109746597068640443888957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34073164398045760295925971 51109746597068640443888957)
    ·
      refine ⟨19166154973900740166458359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51109746597068640443888957 19166154973900740166458359)
      ·
        refine ⟨28749232460851110249687539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19166154973900740166458359 28749232460851110249687539)
        ·
          refine ⟨43123848691276665374531309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28749232460851110249687539 43123848691276665374531309)
          ·
            refine ⟨16171443259228749515449241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43123848691276665374531309 16171443259228749515449241)
            ·
              refine ⟨12128582444421562136586931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16171443259228749515449241 12128582444421562136586931)
              ·
                refine ⟨18192873666632343204880397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12128582444421562136586931 18192873666632343204880397)
                ·
                  refine ⟨6822327624987128701830149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18192873666632343204880397 6822327624987128701830149)
                  ·
                    refine ⟨1279186429685086631593153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822327624987128701830149 1279186429685086631593153)
                    ·
                      rfl

theorem cell22_3736810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3736810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736810 prefixEnd_3736810 := by exact prefixLift 3736810
  have htrace : WordTrace (prefixWord ++ tailWord_3736810) baseStart_3736810 baseEnd_3736810 := by
    simpa [prefixWord, tailWord_3736810, baseEnd_3736810] using wordTrace_append hprefix tailTrace_3736810
  have hstable : (prefixWord ++ tailWord_3736810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736810).length < 2 ^ (prefixWord ++ tailWord_3736810).sum := by decide
  have hdescent : baseEnd_3736810 < baseStart_3736810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736853 : List Nat := [1, 3, 2, 1, 2, 1, 1, 11]
def baseStart_3736853 : Nat := 118140960795 + 3736853 * 2 ^ 59
def prefixEnd_3736853 : Nat := 4983230072969 + 3 ^ 40 * 3736853 * 2
def baseEnd_3736853 : Nat := 142133461051538761418669

theorem tailTrace_3736853 : CollatzResearch.WordTrace tailWord_3736853 prefixEnd_3736853 142133461051538761418669 := by
  unfold tailWord_3736853
  simp only [CollatzResearch.WordTrace]
  refine ⟨136294225931027259527519213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90862817287351506351679475 136294225931027259527519213)
  ·
    refine ⟨51110334724135222322819705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136294225931027259527519213 51110334724135222322819705)
    ·
      refine ⟨38332751043101416742114779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51110334724135222322819705 38332751043101416742114779)
      ·
        refine ⟨57499126564652125113172169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38332751043101416742114779 57499126564652125113172169)
        ·
          refine ⟨43124344923489093834879127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57499126564652125113172169 43124344923489093834879127)
          ·
            refine ⟨64686517385233640752318691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43124344923489093834879127 64686517385233640752318691)
            ·
              refine ⟨97029776077850461128478037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64686517385233640752318691 97029776077850461128478037)
              ·
                refine ⟨142133461051538761418669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 97029776077850461128478037 142133461051538761418669)
                ·
                  rfl

theorem cell22_3736853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 11].length) (baseStart_3736853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736853 prefixEnd_3736853 := by exact prefixLift 3736853
  have htrace : WordTrace (prefixWord ++ tailWord_3736853) baseStart_3736853 baseEnd_3736853 := by
    simpa [prefixWord, tailWord_3736853, baseEnd_3736853] using wordTrace_append hprefix tailTrace_3736853
  have hstable : (prefixWord ++ tailWord_3736853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736853).length < 2 ^ (prefixWord ++ tailWord_3736853).sum := by decide
  have hdescent : baseEnd_3736853 < baseStart_3736853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736915 : List Nat := [1, 1, 1, 2, 1, 1, 7, 3, 5]
def baseStart_3736915 : Nat := 118140960795 + 3736915 * 2 ^ 59
def prefixEnd_3736915 : Nat := 4983230072969 + 3 ^ 40 * 3736915 * 2
def baseEnd_3736915 : Nat := 426407457776967119239277

theorem tailTrace_3736915 : CollatzResearch.WordTrace tailWord_3736915 prefixEnd_3736915 426407457776967119239277 := by
  unfold tailWord_3736915
  simp only [CollatzResearch.WordTrace]
  refine ⟨136296487256802644116276199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90864324837868429410850799 136296487256802644116276199)
  ·
    refine ⟨204444730885203966174414299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136296487256802644116276199 204444730885203966174414299)
    ·
      refine ⟨306667096327805949261621449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204444730885203966174414299 306667096327805949261621449)
      ·
        refine ⟨230000322245854461946216087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306667096327805949261621449 230000322245854461946216087)
        ·
          refine ⟨345000483368781692919324131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230000322245854461946216087 345000483368781692919324131)
          ·
            refine ⟨517500725053172539378986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345000483368781692919324131 517500725053172539378986197)
            ·
              refine ⟨12128923243433731391694989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 517500725053172539378986197 12128923243433731391694989)
              ·
                refine ⟨4548346216287649271885621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12128923243433731391694989 4548346216287649271885621)
                ·
                  refine ⟨426407457776967119239277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548346216287649271885621 426407457776967119239277)
                  ·
                    rfl

theorem cell22_3736915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].length) (baseStart_3736915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736915 prefixEnd_3736915 := by exact prefixLift 3736915
  have htrace : WordTrace (prefixWord ++ tailWord_3736915) baseStart_3736915 baseEnd_3736915 := by
    simpa [prefixWord, tailWord_3736915, baseEnd_3736915] using wordTrace_append hprefix tailTrace_3736915
  have hstable : (prefixWord ++ tailWord_3736915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736915).length < 2 ^ (prefixWord ++ tailWord_3736915).sum := by decide
  have hdescent : baseEnd_3736915 < baseStart_3736915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736949 : List Nat := [1, 3, 4, 1, 3, 1, 2, 2, 5]
def baseStart_3736949 : Nat := 118140960795 + 3736949 * 2 ^ 59
def prefixEnd_3736949 : Nat := 4983230072969 + 3 ^ 40 * 3736949 * 2
def baseEnd_3736949 : Nat := 426411337408578867455909

theorem tailTrace_3736949 : CollatzResearch.WordTrace tailWord_3736949 prefixEnd_3736949 426411337408578867455909 := by
  unfold tailWord_3736949
  simp only [CollatzResearch.WordTrace]
  refine ⟨136297727338679467923013901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90865151559119645282009267 136297727338679467923013901)
  ·
    refine ⟨51111647752004800471130213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136297727338679467923013901 51111647752004800471130213)
    ·
      refine ⟨9583433953500900088336915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51111647752004800471130213 9583433953500900088336915)
      ·
        refine ⟨14375150930251350132505373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583433953500900088336915 14375150930251350132505373)
        ·
          refine ⟨5390681598844256299689515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14375150930251350132505373 5390681598844256299689515)
          ·
            refine ⟨8086022398266384449534273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390681598844256299689515 8086022398266384449534273)
            ·
              refine ⟨6064516798699788337150705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086022398266384449534273 6064516798699788337150705)
              ·
                refine ⟨4548387599024841252863029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6064516798699788337150705 4548387599024841252863029)
                ·
                  refine ⟨426411337408578867455909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548387599024841252863029 426411337408578867455909)
                  ·
                    rfl

theorem cell22_3736949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 2, 5].length) (baseStart_3736949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736949 prefixEnd_3736949 := by exact prefixLift 3736949
  have htrace : WordTrace (prefixWord ++ tailWord_3736949) baseStart_3736949 baseEnd_3736949 := by
    simpa [prefixWord, tailWord_3736949, baseEnd_3736949] using wordTrace_append hprefix tailTrace_3736949
  have hstable : (prefixWord ++ tailWord_3736949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736949).length < 2 ^ (prefixWord ++ tailWord_3736949).sum := by decide
  have hdescent : baseEnd_3736949 < baseStart_3736949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736992 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_3736992 : Nat := 118140960795 + 3736992 * 2 ^ 59
def prefixEnd_3736992 : Nat := 4983230072969 + 3 ^ 40 * 3736992 * 2
def baseEnd_3736992 : Nat := 1279248732004498823542595

theorem tailTrace_3736992 : CollatzResearch.WordTrace tailWord_3736992 prefixEnd_3736992 1279248732004498823542595 := by
  unfold tailWord_3736992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68149647838761843133414615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90866197118349124177886153 68149647838761843133414615)
  ·
    refine ⟨102224471758142764700121923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68149647838761843133414615 102224471758142764700121923)
    ·
      refine ⟨153336707637214147050182885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102224471758142764700121923 153336707637214147050182885)
      ·
        refine ⟨28750632681977652571909291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153336707637214147050182885 28750632681977652571909291)
        ·
          refine ⟨43125949022966478857863937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28750632681977652571909291 43125949022966478857863937)
          ·
            refine ⟨32344461767224859143397953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43125949022966478857863937 32344461767224859143397953)
            ·
              refine ⟨24258346325418644357548465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32344461767224859143397953 24258346325418644357548465)
              ·
                refine ⟨18193759744063983268161349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24258346325418644357548465 18193759744063983268161349)
                ·
                  refine ⟨3411329952011996862780253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18193759744063983268161349 3411329952011996862780253)
                  ·
                    refine ⟨1279248732004498823542595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411329952011996862780253 1279248732004498823542595)
                    ·
                      rfl

theorem cell22_3736992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_3736992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736992 prefixEnd_3736992 := by exact prefixLift 3736992
  have htrace : WordTrace (prefixWord ++ tailWord_3736992) baseStart_3736992 baseEnd_3736992 := by
    simpa [prefixWord, tailWord_3736992, baseEnd_3736992] using wordTrace_append hprefix tailTrace_3736992
  have hstable : (prefixWord ++ tailWord_3736992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736992).length < 2 ^ (prefixWord ++ tailWord_3736992).sum := by decide
  have hdescent : baseEnd_3736992 < baseStart_3736992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3736994 : List Nat := [3, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3736994 : Nat := 118140960795 + 3736994 * 2 ^ 59
def prefixEnd_3736994 : Nat := 4983230072969 + 3 ^ 40 * 3736994 * 2
def baseEnd_3736994 : Nat := 426416472215123828330863

theorem tailTrace_3736994 : CollatzResearch.WordTrace tailWord_3736994 prefixEnd_3736994 426416472215123828330863 := by
  unfold tailWord_3736994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34074842155879110152100509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90866245749010960405601357 34074842155879110152100509)
  ·
    refine ⟨12778065808454666307037691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34074842155879110152100509 12778065808454666307037691)
    ·
      refine ⟨19167098712681999460556537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12778065808454666307037691 19167098712681999460556537)
      ·
        refine ⟨14375324034511499595417403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19167098712681999460556537 14375324034511499595417403)
        ·
          refine ⟨21562986051767249393126105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14375324034511499595417403 21562986051767249393126105)
          ·
            refine ⟨16172239538825437044844579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21562986051767249393126105 16172239538825437044844579)
            ·
              refine ⟨24258359308238155567266869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16172239538825437044844579 24258359308238155567266869)
              ·
                refine ⟨2274221185147327084431269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24258359308238155567266869 2274221185147327084431269)
                ·
                  refine ⟨426416472215123828330863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274221185147327084431269 426416472215123828330863)
                  ·
                    rfl

theorem cell22_3736994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3736994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3736994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3736994 prefixEnd_3736994 := by exact prefixLift 3736994
  have htrace : WordTrace (prefixWord ++ tailWord_3736994) baseStart_3736994 baseEnd_3736994 := by
    simpa [prefixWord, tailWord_3736994, baseEnd_3736994] using wordTrace_append hprefix tailTrace_3736994
  have hstable : (prefixWord ++ tailWord_3736994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3736994).length < 2 ^ (prefixWord ++ tailWord_3736994).sum := by decide
  have hdescent : baseEnd_3736994 < baseStart_3736994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3736994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737035 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_3737035 : Nat := 118140960795 + 3737035 * 2 ^ 59
def prefixEnd_3737035 : Nat := 4983230072969 + 3 ^ 40 * 3737035 * 2
def baseEnd_3737035 : Nat := 1279263451783261044717463

theorem tailTrace_3737035 : CollatzResearch.WordTrace tailWord_3737035 prefixEnd_3737035 1279263451783261044717463 := by
  unfold tailWord_3737035
  simp only [CollatzResearch.WordTrace]
  refine ⟨136300864016367904610644559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90867242677578603073763039 136300864016367904610644559)
  ·
    refine ⟨204451296024551856915966839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136300864016367904610644559 204451296024551856915966839)
    ·
      refine ⟨306676944036827785373950259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204451296024551856915966839 306676944036827785373950259)
      ·
        refine ⟨460015416055241678060925389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306676944036827785373950259 460015416055241678060925389)
        ·
          refine ⟨172505781020715629272847021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460015416055241678060925389 172505781020715629272847021)
          ·
            refine ⟨64689667882768360977317633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172505781020715629272847021 64689667882768360977317633)
            ·
              refine ⟨48517250912076270732988225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64689667882768360977317633 48517250912076270732988225)
              ·
                refine ⟨36387938184057203049741169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48517250912076270732988225 36387938184057203049741169)
                ·
                  refine ⟨27290953638042902287305877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36387938184057203049741169 27290953638042902287305877)
                  ·
                    refine ⟨1279263451783261044717463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27290953638042902287305877 1279263451783261044717463)
                    ·
                      rfl

theorem cell22_3737035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_3737035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737035 prefixEnd_3737035 := by exact prefixLift 3737035
  have htrace : WordTrace (prefixWord ++ tailWord_3737035) baseStart_3737035 baseEnd_3737035 := by
    simpa [prefixWord, tailWord_3737035, baseEnd_3737035] using wordTrace_append hprefix tailTrace_3737035
  have hstable : (prefixWord ++ tailWord_3737035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737035).length < 2 ^ (prefixWord ++ tailWord_3737035).sum := by decide
  have hdescent : baseEnd_3737035 < baseStart_3737035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737084 : List Nat := [2, 2, 2, 1, 2, 1, 6, 1, 5]
def baseStart_3737084 : Nat := 118140960795 + 3737084 * 2 ^ 59
def prefixEnd_3737084 : Nat := 4983230072969 + 3 ^ 40 * 3737084 * 2
def baseEnd_3737084 : Nat := 426426741828213750080771

theorem tailTrace_3737084 : CollatzResearch.WordTrace tailWord_3737084 prefixEnd_3737084 426426741828213750080771 := by
  unfold tailWord_3737084
  simp only [CollatzResearch.WordTrace]
  refine ⟨68151325596595192989589153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90868434128793590652785537 68151325596595192989589153)
  ·
    refine ⟨51113494197446394742191865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68151325596595192989589153 51113494197446394742191865)
    ·
      refine ⟨38335120648084796056643899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51113494197446394742191865 38335120648084796056643899)
      ·
        refine ⟨57502680972127194084965849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38335120648084796056643899 57502680972127194084965849)
        ·
          refine ⟨43127010729095395563724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57502680972127194084965849 43127010729095395563724387)
          ·
            refine ⟨64690516093643093345586581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43127010729095395563724387 64690516093643093345586581)
            ·
              refine ⟨3032367941889520000574371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64690516093643093345586581 3032367941889520000574371)
              ·
                refine ⟨4548551912834280000861557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032367941889520000574371 4548551912834280000861557)
                ·
                  refine ⟨426426741828213750080771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548551912834280000861557 426426741828213750080771)
                  ·
                    rfl

theorem cell22_3737084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_3737084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737084 prefixEnd_3737084 := by exact prefixLift 3737084
  have htrace : WordTrace (prefixWord ++ tailWord_3737084) baseStart_3737084 baseEnd_3737084 := by
    simpa [prefixWord, tailWord_3737084, baseEnd_3737084] using wordTrace_append hprefix tailTrace_3737084
  have hstable : (prefixWord ++ tailWord_3737084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737084).length < 2 ^ (prefixWord ++ tailWord_3737084).sum := by decide
  have hdescent : baseEnd_3737084 < baseStart_3737084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737097 : List Nat := [1, 2, 1, 1, 3, 1, 5, 1, 3, 4]
def baseStart_3737097 : Nat := 118140960795 + 3737097 * 2 ^ 59
def prefixEnd_3737097 : Nat := 4983230072969 + 3 ^ 40 * 3737097 * 2
def baseEnd_3737097 : Nat := 1279284675650313549667273

theorem tailTrace_3737097 : CollatzResearch.WordTrace tailWord_3737097 prefixEnd_3737097 1279284675650313549667273 := by
  unfold tailWord_3737097
  simp only [CollatzResearch.WordTrace]
  refine ⟨136303125342143289199401545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90868750228095526132934363 136303125342143289199401545)
  ·
    refine ⟨102227344006607466899551159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136303125342143289199401545 102227344006607466899551159)
    ·
      refine ⟨153341016009911200349326739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102227344006607466899551159 153341016009911200349326739)
      ·
        refine ⟨230011524014866800523990109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153341016009911200349326739 230011524014866800523990109)
        ·
          refine ⟨86254321505575050196496291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230011524014866800523990109 86254321505575050196496291)
          ·
            refine ⟨129381482258362575294744437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86254321505575050196496291 129381482258362575294744437)
            ·
              refine ⟨12129513961721491433882291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129381482258362575294744437 12129513961721491433882291)
              ·
                refine ⟨18194270942582237150823437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12129513961721491433882291 18194270942582237150823437)
                ·
                  refine ⟨6822851603468338931558789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18194270942582237150823437 6822851603468338931558789)
                  ·
                    refine ⟨1279284675650313549667273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822851603468338931558789 1279284675650313549667273)
                    ·
                      rfl

theorem cell22_3737097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_3737097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737097 prefixEnd_3737097 := by exact prefixLift 3737097
  have htrace : WordTrace (prefixWord ++ tailWord_3737097) baseStart_3737097 baseEnd_3737097 := by
    simpa [prefixWord, tailWord_3737097, baseEnd_3737097] using wordTrace_append hprefix tailTrace_3737097
  have hstable : (prefixWord ++ tailWord_3737097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737097).length < 2 ^ (prefixWord ++ tailWord_3737097).sum := by decide
  have hdescent : baseEnd_3737097 < baseStart_3737097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737144 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 1, 5]
def baseStart_3737144 : Nat := 118140960795 + 3737144 * 2 ^ 59
def prefixEnd_3737144 : Nat := 4983230072969 + 3 ^ 40 * 3737144 * 2
def baseEnd_3737144 : Nat := 1279300764710821093742129

theorem tailTrace_3737144 : CollatzResearch.WordTrace tailWord_3737144 prefixEnd_3737144 1279300764710821093742129 := by
  unfold tailWord_3737144
  simp only [CollatzResearch.WordTrace]
  refine ⟨68152419786486508113181243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90869893048648677484241657 68152419786486508113181243)
  ·
    refine ⟨102228629679729762169771865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68152419786486508113181243 102228629679729762169771865)
    ·
      refine ⟨76671472259797321627328899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102228629679729762169771865 76671472259797321627328899)
      ·
        refine ⟨115007208389695982440993349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76671472259797321627328899 115007208389695982440993349)
        ·
          refine ⟨21563851573067996707686253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115007208389695982440993349 21563851573067996707686253)
          ·
            refine ⟨8086444339900498765382345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21563851573067996707686253 8086444339900498765382345)
            ·
              refine ⟨6064833254925374074036759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086444339900498765382345 6064833254925374074036759)
              ·
                refine ⟨9097249882388061111055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064833254925374074036759 9097249882388061111055139)
                ·
                  refine ⟨13645874823582091666582709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097249882388061111055139 13645874823582091666582709)
                  ·
                    refine ⟨1279300764710821093742129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13645874823582091666582709 1279300764710821093742129)
                    ·
                      rfl

theorem cell22_3737144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_3737144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737144 prefixEnd_3737144 := by exact prefixLift 3737144
  have htrace : WordTrace (prefixWord ++ tailWord_3737144) baseStart_3737144 baseEnd_3737144 := by
    simpa [prefixWord, tailWord_3737144, baseEnd_3737144] using wordTrace_append hprefix tailTrace_3737144
  have hstable : (prefixWord ++ tailWord_3737144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737144).length < 2 ^ (prefixWord ++ tailWord_3737144).sum := by decide
  have hdescent : baseEnd_3737144 < baseStart_3737144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737159 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_3737159 : Nat := 118140960795 + 3737159 * 2 ^ 59
def prefixEnd_3737159 : Nat := 4983230072969 + 3 ^ 40 * 3737159 * 2
def baseEnd_3737159 : Nat := 1279305899517366054617083

theorem tailTrace_3737159 : CollatzResearch.WordTrace tailWord_3737159 prefixEnd_3737159 1279305899517366054617083 := by
  unfold tailWord_3737159
  simp only [CollatzResearch.WordTrace]
  refine ⟨136305386667918673788158531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90870257778612449192105687 136305386667918673788158531)
  ·
    refine ⟨204458080001878010682237797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136305386667918673788158531 204458080001878010682237797)
    ·
      refine ⟨38335890000352127002919587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204458080001878010682237797 38335890000352127002919587)
      ·
        refine ⟨57503835000528190504379381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38335890000352127002919587 57503835000528190504379381)
        ·
          refine ⟨5390984531299517859785567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57503835000528190504379381 5390984531299517859785567)
          ·
            refine ⟨8086476796949276789678351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390984531299517859785567 8086476796949276789678351)
            ·
              refine ⟨12129715195423915184517527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086476796949276789678351 12129715195423915184517527)
              ·
                refine ⟨18194572793135872776776291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12129715195423915184517527 18194572793135872776776291)
                ·
                  refine ⟨27291859189703809165164437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18194572793135872776776291 27291859189703809165164437)
                  ·
                    refine ⟨1279305899517366054617083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27291859189703809165164437 1279305899517366054617083)
                    ·
                      rfl

theorem cell22_3737159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_3737159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737159 prefixEnd_3737159 := by exact prefixLift 3737159
  have htrace : WordTrace (prefixWord ++ tailWord_3737159) baseStart_3737159 baseEnd_3737159 := by
    simpa [prefixWord, tailWord_3737159, baseEnd_3737159] using wordTrace_append hprefix tailTrace_3737159
  have hstable : (prefixWord ++ tailWord_3737159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737159).length < 2 ^ (prefixWord ++ tailWord_3737159).sum := by decide
  have hdescent : baseEnd_3737159 < baseStart_3737159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737165 : List Nat := [1, 6, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3737165 : Nat := 118140960795 + 3737165 * 2 ^ 59
def prefixEnd_3737165 : Nat := 4983230072969 + 3 ^ 40 * 3737165 * 2
def baseEnd_3737165 : Nat := 1279307953439984038967065

theorem tailTrace_3737165 : CollatzResearch.WordTrace tailWord_3737165 prefixEnd_3737165 1279307953439984038967065 := by
  unfold tailWord_3737165
  simp only [CollatzResearch.WordTrace]
  refine ⟨136305605505896936812876949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90870403670597957875251299 136305605505896936812876949)
  ·
    refine ⟨6389325258088918913103607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136305605505896936812876949 6389325258088918913103607)
    ·
      refine ⟨9583987887133378369655411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389325258088918913103607 9583987887133378369655411)
      ·
        refine ⟨14375981830700067554483117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9583987887133378369655411 14375981830700067554483117)
        ·
          refine ⟨5390993186512525332931169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14375981830700067554483117 5390993186512525332931169)
          ·
            refine ⟨4043244889884393999698377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5390993186512525332931169 4043244889884393999698377)
            ·
              refine ⟨3032433667413295499773783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043244889884393999698377 3032433667413295499773783)
              ·
                refine ⟨4548650501119943249660675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032433667413295499773783 4548650501119943249660675)
                ·
                  refine ⟨6822975751679914874491013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548650501119943249660675 6822975751679914874491013)
                  ·
                    refine ⟨1279307953439984038967065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6822975751679914874491013 1279307953439984038967065)
                    ·
                      rfl

theorem cell22_3737165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3737165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737165 prefixEnd_3737165 := by exact prefixLift 3737165
  have htrace : WordTrace (prefixWord ++ tailWord_3737165) baseStart_3737165 baseEnd_3737165 := by
    simpa [prefixWord, tailWord_3737165, baseEnd_3737165] using wordTrace_append hprefix tailTrace_3737165
  have hstable : (prefixWord ++ tailWord_3737165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737165).length < 2 ^ (prefixWord ++ tailWord_3737165).sum := by decide
  have hdescent : baseEnd_3737165 < baseStart_3737165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737223 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 1, 3]
def baseStart_3737223 : Nat := 118140960795 + 3737223 * 2 ^ 59
def prefixEnd_3737223 : Nat := 4983230072969 + 3 ^ 40 * 3737223 * 2
def baseEnd_3737223 : Nat := 1279327808025291221016887

theorem tailTrace_3737223 : CollatzResearch.WordTrace tailWord_3737223 prefixEnd_3737223 1279327808025291221016887 := by
  unfold tailWord_3737223
  simp only [CollatzResearch.WordTrace]
  refine ⟨136307720939686812718488323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90871813959791208478992215 136307720939686812718488323)
  ·
    refine ⟨204461581409530219077732485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136307720939686812718488323 204461581409530219077732485)
    ·
      refine ⟨38336546514286916077074841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204461581409530219077732485 38336546514286916077074841)
      ·
        refine ⟨28752409885715187057806131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38336546514286916077074841 28752409885715187057806131)
        ·
          refine ⟨43128614828572780586709197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28752409885715187057806131 43128614828572780586709197)
          ·
            refine ⟨16173230560714792720015949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43128614828572780586709197 16173230560714792720015949)
            ·
              refine ⟨6064961460268047270005981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16173230560714792720015949 6064961460268047270005981)
              ·
                refine ⟨2274360547600517726252243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064961460268047270005981 2274360547600517726252243)
                ·
                  refine ⟨3411540821400776589378365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274360547600517726252243 3411540821400776589378365)
                  ·
                    refine ⟨1279327808025291221016887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411540821400776589378365 1279327808025291221016887)
                    ·
                      rfl

theorem cell22_3737223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_3737223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737223 prefixEnd_3737223 := by exact prefixLift 3737223
  have htrace : WordTrace (prefixWord ++ tailWord_3737223) baseStart_3737223 baseEnd_3737223 := by
    simpa [prefixWord, tailWord_3737223, baseEnd_3737223] using wordTrace_append hprefix tailTrace_3737223
  have hstable : (prefixWord ++ tailWord_3737223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737223).length < 2 ^ (prefixWord ++ tailWord_3737223).sum := by decide
  have hdescent : baseEnd_3737223 < baseStart_3737223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737240 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 1, 3]
def baseStart_3737240 : Nat := 118140960795 + 3737240 * 2 ^ 59
def prefixEnd_3737240 : Nat := 4983230072969 + 3 ^ 40 * 3737240 * 2
def baseEnd_3737240 : Nat := 1279333627472708843341835

theorem tailTrace_3737240 : CollatzResearch.WordTrace tailWord_3737240 prefixEnd_3737240 1279333627472708843341835 := by
  unfold tailWord_3737240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68154170490312612310928587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90872227320416816414571449 68154170490312612310928587)
  ·
    refine ⟨102231255735468918466392881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68154170490312612310928587 102231255735468918466392881)
    ·
      refine ⟨76673441801601688849794661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102231255735468918466392881 76673441801601688849794661)
      ·
        refine ⟨14376270337800316659336499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76673441801601688849794661 14376270337800316659336499)
        ·
          refine ⟨21564405506700474989004749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14376270337800316659336499 21564405506700474989004749)
          ·
            refine ⟨8086652065012678120876781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21564405506700474989004749 8086652065012678120876781)
            ·
              refine ⟨3032494524379754295328793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8086652065012678120876781 3032494524379754295328793)
              ·
                refine ⟨2274370893284815721496595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032494524379754295328793 2274370893284815721496595)
                ·
                  refine ⟨3411556339927223582244893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274370893284815721496595 3411556339927223582244893)
                  ·
                    refine ⟨1279333627472708843341835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411556339927223582244893 1279333627472708843341835)
                    ·
                      rfl

theorem cell22_3737240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_3737240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737240 prefixEnd_3737240 := by exact prefixLift 3737240
  have htrace : WordTrace (prefixWord ++ tailWord_3737240) baseStart_3737240 baseEnd_3737240 := by
    simpa [prefixWord, tailWord_3737240, baseEnd_3737240] using wordTrace_append hprefix tailTrace_3737240
  have hstable : (prefixWord ++ tailWord_3737240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737240).length < 2 ^ (prefixWord ++ tailWord_3737240).sum := by decide
  have hdescent : baseEnd_3737240 < baseStart_3737240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737266 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3737266 : Nat := 118140960795 + 3737266 * 2 ^ 59
def prefixEnd_3737266 : Nat := 4983230072969 + 3 ^ 40 * 3737266 * 2
def baseEnd_3737266 : Nat := 1279342527804053442191755

theorem tailTrace_3737266 : CollatzResearch.WordTrace tailWord_3737266 prefixEnd_3737266 1279342527804053442191755 := by
  unfold tailWord_3737266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077322319632757765575913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90872859519020687374869101 34077322319632757765575913)
  ·
    refine ⟨25557991739724568324181935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34077322319632757765575913 25557991739724568324181935)
    ·
      refine ⟨38336987609586852486272903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25557991739724568324181935 38336987609586852486272903)
      ·
        refine ⟨57505481414380278729409355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38336987609586852486272903 57505481414380278729409355)
        ·
          refine ⟨86258222121570418094114033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57505481414380278729409355 86258222121570418094114033)
          ·
            refine ⟨64693666591177813570585525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86258222121570418094114033 64693666591177813570585525)
            ·
              refine ⟨6065031242922920022242393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64693666591177813570585525 6065031242922920022242393)
              ·
                refine ⟨4548773432192190016681795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065031242922920022242393 4548773432192190016681795)
                ·
                  refine ⟨6823160148288285025022693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4548773432192190016681795 6823160148288285025022693)
                  ·
                    refine ⟨1279342527804053442191755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823160148288285025022693 1279342527804053442191755)
                    ·
                      rfl

theorem cell22_3737266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3737266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737266 prefixEnd_3737266 := by exact prefixLift 3737266
  have htrace : WordTrace (prefixWord ++ tailWord_3737266) baseStart_3737266 baseEnd_3737266 := by
    simpa [prefixWord, tailWord_3737266, baseEnd_3737266] using wordTrace_append hprefix tailTrace_3737266
  have hstable : (prefixWord ++ tailWord_3737266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737266).length < 2 ^ (prefixWord ++ tailWord_3737266).sum := by decide
  have hdescent : baseEnd_3737266 < baseStart_3737266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737279 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_3737279 : Nat := 118140960795 + 3737279 * 2 ^ 59
def prefixEnd_3737279 : Nat := 4983230072969 + 3 ^ 40 * 3737279 * 2
def baseEnd_3737279 : Nat := 1279346977969725741616715

theorem tailTrace_3737279 : CollatzResearch.WordTrace tailWord_3737279 prefixEnd_3737279 1279346977969725741616715 := by
  unfold tailWord_3737279
  simp only [CollatzResearch.WordTrace]
  refine ⟨136309763427483934282526891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90873175618322622855017927 136309763427483934282526891)
  ·
    refine ⟨204464645141225901423790337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136309763427483934282526891 204464645141225901423790337)
    ·
      refine ⟨153348483855919426067842753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204464645141225901423790337 153348483855919426067842753)
      ·
        refine ⟨115011362891939569550882065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153348483855919426067842753 115011362891939569550882065)
        ·
          refine ⟨86258522168954677163161549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115011362891939569550882065 86258522168954677163161549)
          ·
            refine ⟨32346945813358003936185581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86258522168954677163161549 32346945813358003936185581)
            ·
              refine ⟨12130104680009251476069593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32346945813358003936185581 12130104680009251476069593)
              ·
                refine ⟨9097578510006938607052195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12130104680009251476069593 9097578510006938607052195)
                ·
                  refine ⟨13646367765010407910578293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097578510006938607052195 13646367765010407910578293)
                  ·
                    refine ⟨1279346977969725741616715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13646367765010407910578293 1279346977969725741616715)
                    ·
                      rfl

theorem cell22_3737279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_3737279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737279 prefixEnd_3737279 := by exact prefixLift 3737279
  have htrace : WordTrace (prefixWord ++ tailWord_3737279) baseStart_3737279 baseEnd_3737279 := by
    simpa [prefixWord, tailWord_3737279, baseEnd_3737279] using wordTrace_append hprefix tailTrace_3737279
  have hstable : (prefixWord ++ tailWord_3737279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737279).length < 2 ^ (prefixWord ++ tailWord_3737279).sum := by decide
  have hdescent : baseEnd_3737279 < baseStart_3737279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737298 : List Nat := [3, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3737298 : Nat := 118140960795 + 3737298 * 2 ^ 59
def prefixEnd_3737298 : Nat := 4983230072969 + 3 ^ 40 * 3737298 * 2
def baseEnd_3737298 : Nat := 426451160686005341797219

theorem tailTrace_3737298 : CollatzResearch.WordTrace tailWord_3737298 prefixEnd_3737298 426451160686005341797219 := by
  unfold tailWord_3737298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077614103603775131867137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90873637609610067018312365 34077614103603775131867137)
  ·
    refine ⟨25558210577702831348900353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34077614103603775131867137 25558210577702831348900353)
    ·
      refine ⟨19168657933277123511675265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25558210577702831348900353 19168657933277123511675265)
      ·
        refine ⟨14376493449957842633756449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19168657933277123511675265 14376493449957842633756449)
        ·
          refine ⟨10782370087468381975317337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14376493449957842633756449 10782370087468381975317337)
          ·
            refine ⟨8086777565601286481488003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10782370087468381975317337 8086777565601286481488003)
            ·
              refine ⟨12130166348401929722232005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8086777565601286481488003 12130166348401929722232005)
              ·
                refine ⟨2274406190325361822918501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12130166348401929722232005 2274406190325361822918501)
                ·
                  refine ⟨426451160686005341797219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274406190325361822918501 426451160686005341797219)
                  ·
                    rfl

theorem cell22_3737298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3737298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737298 prefixEnd_3737298 := by exact prefixLift 3737298
  have htrace : WordTrace (prefixWord ++ tailWord_3737298) baseStart_3737298 baseEnd_3737298 := by
    simpa [prefixWord, tailWord_3737298, baseEnd_3737298] using wordTrace_append hprefix tailTrace_3737298
  have hstable : (prefixWord ++ tailWord_3737298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737298).length < 2 ^ (prefixWord ++ tailWord_3737298).sum := by decide
  have hdescent : baseEnd_3737298 < baseStart_3737298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737326 : List Nat := [4, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3737326 : Nat := 118140960795 + 3737326 * 2 ^ 59
def prefixEnd_3737326 : Nat := 4983230072969 + 3 ^ 40 * 3737326 * 2
def baseEnd_3737326 : Nat := 142151451892248142854619

theorem tailTrace_3737326 : CollatzResearch.WordTrace tailWord_3737326 prefixEnd_3737326 142151451892248142854619 := by
  unfold tailWord_3737326
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038934707289207663685979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90874318438875774206325221 17038934707289207663685979)
  ·
    refine ⟨25558402060933811495528969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17038934707289207663685979 25558402060933811495528969)
    ·
      refine ⟨19168801545700358621646727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25558402060933811495528969 19168801545700358621646727)
      ·
        refine ⟨28753202318550537932470091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19168801545700358621646727 28753202318550537932470091)
        ·
          refine ⟨43129803477825806898705137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28753202318550537932470091 43129803477825806898705137)
          ·
            refine ⟨32347352608369355174028853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43129803477825806898705137 32347352608369355174028853)
            ·
              refine ⟨3032564307034627047565205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32347352608369355174028853 3032564307034627047565205)
              ·
                refine ⟨142151451892248142854619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3032564307034627047565205 142151451892248142854619)
                ·
                  rfl

theorem cell22_3737326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3737326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737326 prefixEnd_3737326 := by exact prefixLift 3737326
  have htrace : WordTrace (prefixWord ++ tailWord_3737326) baseStart_3737326 baseEnd_3737326 := by
    simpa [prefixWord, tailWord_3737326, baseEnd_3737326] using wordTrace_append hprefix tailTrace_3737326
  have hstable : (prefixWord ++ tailWord_3737326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737326).length < 2 ^ (prefixWord ++ tailWord_3737326).sum := by decide
  have hdescent : baseEnd_3737326 < baseStart_3737326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737332 : List Nat := [2, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3737332 : Nat := 118140960795 + 3737332 * 2 ^ 59
def prefixEnd_3737332 : Nat := 4983230072969 + 3 ^ 40 * 3737332 * 2
def baseEnd_3737332 : Nat := 426455040317617090013851

theorem tailTrace_3737332 : CollatzResearch.WordTrace tailWord_3737332 prefixEnd_3737332 426455040317617090013851 := by
  unfold tailWord_3737332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68155848248145962167103125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90874464330861282889470833 68155848248145962167103125)
  ·
    refine ⟨3194805386631841976582959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68155848248145962167103125 3194805386631841976582959)
    ·
      refine ⟨4792208079947762964874439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194805386631841976582959 4792208079947762964874439)
      ·
        refine ⟨7188312119921644447311659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4792208079947762964874439 7188312119921644447311659)
        ·
          refine ⟨10782468179882466670967489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188312119921644447311659 10782468179882466670967489)
          ·
            refine ⟨8086851134911850003225617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10782468179882466670967489 8086851134911850003225617)
            ·
              refine ⟨6065138351183887502419213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8086851134911850003225617 6065138351183887502419213)
              ·
                refine ⟨2274426881693957813407205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6065138351183887502419213 2274426881693957813407205)
                ·
                  refine ⟨426455040317617090013851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274426881693957813407205 426455040317617090013851)
                  ·
                    rfl

theorem cell22_3737332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3737332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737332 prefixEnd_3737332 := by exact prefixLift 3737332
  have htrace : WordTrace (prefixWord ++ tailWord_3737332) baseStart_3737332 baseEnd_3737332 := by
    simpa [prefixWord, tailWord_3737332, baseEnd_3737332] using wordTrace_append hprefix tailTrace_3737332
  have hstable : (prefixWord ++ tailWord_3737332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737332).length < 2 ^ (prefixWord ++ tailWord_3737332).sum := by decide
  have hdescent : baseEnd_3737332 < baseStart_3737332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737364 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3737364 : Nat := 118140960795 + 3737364 * 2 ^ 59
def prefixEnd_3737364 : Nat := 4983230072969 + 3 ^ 40 * 3737364 * 2
def baseEnd_3737364 : Nat := 1279376075206813853241455

theorem tailTrace_3737364 : CollatzResearch.WordTrace tailWord_3737364 prefixEnd_3737364 1279376075206813853241455 := by
  unfold tailWord_3737364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68156431816087996899685573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90875242421450662532914097 68156431816087996899685573)
  ·
    refine ⟨12779330965516499418691045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68156431816087996899685573 12779330965516499418691045)
    ·
      refine ⟨2396124556034343641004571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12779330965516499418691045 2396124556034343641004571)
      ·
        refine ⟨3594186834051515461506857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396124556034343641004571 3594186834051515461506857)
        ·
          refine ⟨2695640125538636596130143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3594186834051515461506857 2695640125538636596130143)
          ·
            refine ⟨4043460188307954894195215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695640125538636596130143 4043460188307954894195215)
            ·
              refine ⟨6065190282461932341292823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043460188307954894195215 6065190282461932341292823)
              ·
                refine ⟨9097785423692898511939235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065190282461932341292823 9097785423692898511939235)
                ·
                  refine ⟨13646678135539347767908853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9097785423692898511939235 13646678135539347767908853)
                  ·
                    refine ⟨1279376075206813853241455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13646678135539347767908853 1279376075206813853241455)
                    ·
                      rfl

theorem cell22_3737364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3737364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737364 prefixEnd_3737364 := by exact prefixLift 3737364
  have htrace : WordTrace (prefixWord ++ tailWord_3737364) baseStart_3737364 baseEnd_3737364 := by
    simpa [prefixWord, tailWord_3737364, baseEnd_3737364] using wordTrace_append hprefix tailTrace_3737364
  have hstable : (prefixWord ++ tailWord_3737364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737364).length < 2 ^ (prefixWord ++ tailWord_3737364).sum := by decide
  have hdescent : baseEnd_3737364 < baseStart_3737364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737416 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_3737416 : Nat := 118140960795 + 3737416 * 2 ^ 59
def prefixEnd_3737416 : Nat := 4983230072969 + 3 ^ 40 * 3737416 * 2
def baseEnd_3737416 : Nat := 426464625289834350313765

theorem tailTrace_3737416 : CollatzResearch.WordTrace tailWord_3737416 prefixEnd_3737416 426464625289834350313765 := by
  unfold tailWord_3737416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68157380113993803340132051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90876506818658404453509401 68157380113993803340132051)
  ·
    refine ⟨102236070170990705010198077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68157380113993803340132051 102236070170990705010198077)
    ·
      refine ⟨38338526314121514378824279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102236070170990705010198077 38338526314121514378824279)
      ·
        refine ⟨57507789471182271568236419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38338526314121514378824279 57507789471182271568236419)
        ·
          refine ⟨86261684206773407352354629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57507789471182271568236419 86261684206773407352354629)
          ·
            refine ⟨16174065788770013878566493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86261684206773407352354629 16174065788770013878566493)
            ·
              refine ⟨6065274670788755204462435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16174065788770013878566493 6065274670788755204462435)
              ·
                refine ⟨9097912006183132806693653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065274670788755204462435 9097912006183132806693653)
                ·
                  refine ⟨426464625289834350313765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9097912006183132806693653 426464625289834350313765)
                  ·
                    rfl

theorem cell22_3737416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_3737416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737416 prefixEnd_3737416 := by exact prefixLift 3737416
  have htrace : WordTrace (prefixWord ++ tailWord_3737416) baseStart_3737416 baseEnd_3737416 := by
    simpa [prefixWord, tailWord_3737416, baseEnd_3737416] using wordTrace_append hprefix tailTrace_3737416
  have hstable : (prefixWord ++ tailWord_3737416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737416).length < 2 ^ (prefixWord ++ tailWord_3737416).sum := by decide
  have hdescent : baseEnd_3737416 < baseStart_3737416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737493 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3737493 : Nat := 118140960795 + 3737493 * 2 ^ 59
def prefixEnd_3737493 : Nat := 4983230072969 + 3 ^ 40 * 3737493 * 2
def baseEnd_3737493 : Nat := 1279420234543100516766059

theorem tailTrace_3737493 : CollatzResearch.WordTrace tailWord_3737493 prefixEnd_3737493 1279420234543100516766059 := by
  unfold tailWord_3737493
  simp only [CollatzResearch.WordTrace]
  refine ⟨136317568648708648830817133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90878379099139099220544755 136317568648708648830817133)
  ·
    refine ⟨51119088243265743311556425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136317568648708648830817133 51119088243265743311556425)
    ·
      refine ⟨38339316182449307483667319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51119088243265743311556425 38339316182449307483667319)
      ·
        refine ⟨57508974273673961225500979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38339316182449307483667319 57508974273673961225500979)
        ·
          refine ⟨86263461410510941838251469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57508974273673961225500979 86263461410510941838251469)
          ·
            refine ⟨32348798028941603189344301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86263461410510941838251469 32348798028941603189344301)
            ·
              refine ⟨12130799260853101196004113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32348798028941603189344301 12130799260853101196004113)
              ·
                refine ⟨9098099445639825897003085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12130799260853101196004113 9098099445639825897003085)
                ·
                  refine ⟨3411787292114934711376157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9098099445639825897003085 3411787292114934711376157)
                  ·
                    refine ⟨1279420234543100516766059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411787292114934711376157 1279420234543100516766059)
                    ·
                      rfl

theorem cell22_3737493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3737493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737493 prefixEnd_3737493 := by exact prefixLift 3737493
  have htrace : WordTrace (prefixWord ++ tailWord_3737493) baseStart_3737493 baseEnd_3737493 := by
    simpa [prefixWord, tailWord_3737493, baseEnd_3737493] using wordTrace_append hprefix tailTrace_3737493
  have hstable : (prefixWord ++ tailWord_3737493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737493).length < 2 ^ (prefixWord ++ tailWord_3737493).sum := by decide
  have hdescent : baseEnd_3737493 < baseStart_3737493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737551 : List Nat := [1, 1, 2, 1, 1, 5, 1, 4, 6]
def baseStart_3737551 : Nat := 118140960795 + 3737551 * 2 ^ 59
def prefixEnd_3737551 : Nat := 4983230072969 + 3 ^ 40 * 3737551 * 2
def baseEnd_3737551 : Nat := 426480029709469232938627

theorem tailTrace_3737551 : CollatzResearch.WordTrace tailWord_3737551 prefixEnd_3737551 426480029709469232938627 := by
  unfold tailWord_3737551
  simp only [CollatzResearch.WordTrace]
  refine ⟨136319684082498524736428507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90879789388332349824285671 136319684082498524736428507)
  ·
    refine ⟨204479526123747787104642761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136319684082498524736428507 204479526123747787104642761)
    ·
      refine ⟨153359644592810840328482071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204479526123747787104642761 153359644592810840328482071)
      ·
        refine ⟨230039466889216260492723107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153359644592810840328482071 230039466889216260492723107)
        ·
          refine ⟨345059200333824390739084661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230039466889216260492723107 345059200333824390739084661)
          ·
            refine ⟨32349300031296036631789187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 345059200333824390739084661 32349300031296036631789187)
            ·
              refine ⟨48523950046944054947683781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32349300031296036631789187 48523950046944054947683781)
              ·
                refine ⟨9098240633802010302690709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48523950046944054947683781 9098240633802010302690709)
                ·
                  refine ⟨426480029709469232938627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9098240633802010302690709 426480029709469232938627)
                  ·
                    rfl

theorem cell22_3737551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_3737551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737551 prefixEnd_3737551 := by exact prefixLift 3737551
  have htrace : WordTrace (prefixWord ++ tailWord_3737551) baseStart_3737551 baseEnd_3737551 := by
    simpa [prefixWord, tailWord_3737551, baseEnd_3737551] using wordTrace_append hprefix tailTrace_3737551
  have hstable : (prefixWord ++ tailWord_3737551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737551).length < 2 ^ (prefixWord ++ tailWord_3737551).sum := by decide
  have hdescent : baseEnd_3737551 < baseStart_3737551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737583 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 4, 3]
def baseStart_3737583 : Nat := 118140960795 + 3737583 * 2 ^ 59
def prefixEnd_3737583 : Nat := 4983230072969 + 3 ^ 40 * 3737583 * 2
def baseEnd_3737583 : Nat := 1279451043382370282015783

theorem tailTrace_3737583 : CollatzResearch.WordTrace tailWord_3737583 prefixEnd_3737583 1279451043382370282015783 := by
  unfold tailWord_3737583
  simp only [CollatzResearch.WordTrace]
  refine ⟨136320851218382594201593403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90880567478921729467728935 136320851218382594201593403)
  ·
    refine ⟨204481276827573891302390105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136320851218382594201593403 204481276827573891302390105)
    ·
      refine ⟨153360957620680418476792579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204481276827573891302390105 153360957620680418476792579)
      ·
        refine ⟨230041436431020627715188869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153360957620680418476792579 230041436431020627715188869)
        ·
          refine ⟨43132769330816367696597913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230041436431020627715188869 43132769330816367696597913)
          ·
            refine ⟨32349576998112275772448435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43132769330816367696597913 32349576998112275772448435)
            ·
              refine ⟨48524365497168413658672653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32349576998112275772448435 48524365497168413658672653)
              ·
                refine ⟨18196637061438155122002245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48524365497168413658672653 18196637061438155122002245)
                ·
                  refine ⟨3411869449019654085375421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18196637061438155122002245 3411869449019654085375421)
                  ·
                    refine ⟨1279451043382370282015783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3411869449019654085375421 1279451043382370282015783)
                    ·
                      rfl

theorem cell22_3737583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_3737583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737583 prefixEnd_3737583 := by exact prefixLift 3737583
  have htrace : WordTrace (prefixWord ++ tailWord_3737583) baseStart_3737583 baseEnd_3737583 := by
    simpa [prefixWord, tailWord_3737583, baseEnd_3737583] using wordTrace_append hprefix tailTrace_3737583
  have hstable : (prefixWord ++ tailWord_3737583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737583).length < 2 ^ (prefixWord ++ tailWord_3737583).sum := by decide
  have hdescent : baseEnd_3737583 < baseStart_3737583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737585 : List Nat := [1, 2, 2, 2, 5, 2, 1, 1, 6]
def baseStart_3737585 : Nat := 118140960795 + 3737585 * 2 ^ 59
def prefixEnd_3737585 : Nat := 4983230072969 + 3 ^ 40 * 3737585 * 2
def baseEnd_3737585 : Nat := 426483909341080981155259

theorem tailTrace_3737585 : CollatzResearch.WordTrace tailWord_3737585 prefixEnd_3737585 426483909341080981155259 := by
  unfold tailWord_3737585
  simp only [CollatzResearch.WordTrace]
  refine ⟨136320924164375348543166209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90880616109583565695444139 136320924164375348543166209)
  ·
    refine ⟨102240693123281511407374657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136320924164375348543166209 102240693123281511407374657)
    ·
      refine ⟨76680519842461133555530993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102240693123281511407374657 76680519842461133555530993)
      ·
        refine ⟨57510389881845850166648245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76680519842461133555530993 57510389881845850166648245)
        ·
          refine ⟨5391599051423048453123273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57510389881845850166648245 5391599051423048453123273)
          ·
            refine ⟨4043699288567286339842455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391599051423048453123273 4043699288567286339842455)
            ·
              refine ⟨6065548932850929509763683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043699288567286339842455 6065548932850929509763683)
              ·
                refine ⟨9098323399276394264645525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065548932850929509763683 9098323399276394264645525)
                ·
                  refine ⟨426483909341080981155259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9098323399276394264645525 426483909341080981155259)
                  ·
                    rfl

theorem cell22_3737585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 1, 6].length) (baseStart_3737585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737585 prefixEnd_3737585 := by exact prefixLift 3737585
  have htrace : WordTrace (prefixWord ++ tailWord_3737585) baseStart_3737585 baseEnd_3737585 := by
    simpa [prefixWord, tailWord_3737585, baseEnd_3737585] using wordTrace_append hprefix tailTrace_3737585
  have hstable : (prefixWord ++ tailWord_3737585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737585).length < 2 ^ (prefixWord ++ tailWord_3737585).sum := by decide
  have hdescent : baseEnd_3737585 < baseStart_3737585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737604 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3737604 : Nat := 118140960795 + 3737604 * 2 ^ 59
def prefixEnd_3737604 : Nat := 4983230072969 + 3 ^ 40 * 3737604 * 2
def baseEnd_3737604 : Nat := 1279458232111533227240719

theorem tailTrace_3737604 : CollatzResearch.WordTrace tailWord_3737604 prefixEnd_3737604 1279458232111533227240719 := by
  unfold tailWord_3737604
  simp only [CollatzResearch.WordTrace]
  refine ⟨68160808575653257394053933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90881078100871009858738577 68160808575653257394053933)
  ·
    refine ⟨25560303215869971522770225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68160808575653257394053933 25560303215869971522770225)
    ·
      refine ⟨19170227411902478642077669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25560303215869971522770225 19170227411902478642077669)
      ·
        refine ⟨3594417639731714745389563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19170227411902478642077669 3594417639731714745389563)
        ·
          refine ⟨5391626459597572118084345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594417639731714745389563 5391626459597572118084345)
          ·
            refine ⟨4043719844698179088563259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391626459597572118084345 4043719844698179088563259)
            ·
              refine ⟨6065579767047268632844889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043719844698179088563259 6065579767047268632844889)
              ·
                refine ⟨4549184825285451474633667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065579767047268632844889 4549184825285451474633667)
                ·
                  refine ⟨6823777237928177211950501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549184825285451474633667 6823777237928177211950501)
                  ·
                    refine ⟨1279458232111533227240719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6823777237928177211950501 1279458232111533227240719)
                    ·
                      rfl

theorem cell22_3737604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3737604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737604 prefixEnd_3737604 := by exact prefixLift 3737604
  have htrace : WordTrace (prefixWord ++ tailWord_3737604) baseStart_3737604 baseEnd_3737604 := by
    simpa [prefixWord, tailWord_3737604, baseEnd_3737604] using wordTrace_append hprefix tailTrace_3737604
  have hstable : (prefixWord ++ tailWord_3737604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737604).length < 2 ^ (prefixWord ++ tailWord_3737604).sum := by decide
  have hdescent : baseEnd_3737604 < baseStart_3737604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737636 : List Nat := [2, 3, 1, 4, 3, 1, 2, 2, 4]
def baseStart_3737636 : Nat := 118140960795 + 3737636 * 2 ^ 59
def prefixEnd_3737636 : Nat := 4983230072969 + 3 ^ 40 * 3737636 * 2
def baseEnd_3737636 : Nat := 426489728788498603480207

theorem tailTrace_3737636 : CollatzResearch.WordTrace tailWord_3737636 prefixEnd_3737636 426489728788498603480207 := by
  unfold tailWord_3737636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68161392143595292126636381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90881856191460389502181841 68161392143595292126636381)
  ·
    refine ⟨25560522053848234547488643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68161392143595292126636381 25560522053848234547488643)
    ·
      refine ⟨38340783080772351821232965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25560522053848234547488643 38340783080772351821232965)
      ·
        refine ⟨7188896827644815966481181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38340783080772351821232965 7188896827644815966481181)
        ·
          refine ⟨2695836310366805987430443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7188896827644815966481181 2695836310366805987430443)
          ·
            refine ⟨4043754465550208981145665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695836310366805987430443 4043754465550208981145665)
            ·
              refine ⟨3032815849162656735859249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043754465550208981145665 3032815849162656735859249)
              ·
                refine ⟨2274611886871992551894437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032815849162656735859249 2274611886871992551894437)
                ·
                  refine ⟨426489728788498603480207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274611886871992551894437 426489728788498603480207)
                  ·
                    rfl

theorem cell22_3737636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_3737636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737636 prefixEnd_3737636 := by exact prefixLift 3737636
  have htrace : WordTrace (prefixWord ++ tailWord_3737636) baseStart_3737636 baseEnd_3737636 := by
    simpa [prefixWord, tailWord_3737636, baseEnd_3737636] using wordTrace_append hprefix tailTrace_3737636
  have hstable : (prefixWord ++ tailWord_3737636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737636).length < 2 ^ (prefixWord ++ tailWord_3737636).sum := by decide
  have hdescent : baseEnd_3737636 < baseStart_3737636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737641 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 13]
def baseStart_3737641 : Nat := 118140960795 + 3737641 * 2 ^ 59
def prefixEnd_3737641 : Nat := 4983230072969 + 3 ^ 40 * 3737641 * 2
def baseEnd_3737641 : Nat := 426490299322559154688535

theorem tailTrace_3737641 : CollatzResearch.WordTrace tailWord_3737641 prefixEnd_3737641 426490299322559154688535 := by
  unfold tailWord_3737641
  simp only [CollatzResearch.WordTrace]
  refine ⟨136322966652172470107204777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90881977768114980071469851 136322966652172470107204777)
  ·
    refine ⟨102242224989129352580403583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136322966652172470107204777 102242224989129352580403583)
    ·
      refine ⟨153363337483694028870605375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102242224989129352580403583 153363337483694028870605375)
      ·
        refine ⟨230045006225541043305908063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153363337483694028870605375 230045006225541043305908063)
        ·
          refine ⟨345067509338311564958862095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230045006225541043305908063 345067509338311564958862095)
          ·
            refine ⟨517601264007467347438293143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345067509338311564958862095 517601264007467347438293143)
            ·
              refine ⟨776401896011201021157439715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517601264007467347438293143 776401896011201021157439715)
              ·
                refine ⟨1164602844016801531736159573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 776401896011201021157439715 1164602844016801531736159573)
                ·
                  refine ⟨426490299322559154688535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1164602844016801531736159573 426490299322559154688535)
                  ·
                    rfl

theorem cell22_3737641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_3737641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737641 prefixEnd_3737641 := by exact prefixLift 3737641
  have htrace : WordTrace (prefixWord ++ tailWord_3737641) baseStart_3737641 baseEnd_3737641 := by
    simpa [prefixWord, tailWord_3737641, baseEnd_3737641] using wordTrace_append hprefix tailTrace_3737641
  have hstable : (prefixWord ++ tailWord_3737641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737641).length < 2 ^ (prefixWord ++ tailWord_3737641).sum := by decide
  have hdescent : baseEnd_3737641 < baseStart_3737641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737692 : List Nat := [2, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_3737692 : Nat := 118140960795 + 3737692 * 2 ^ 59
def prefixEnd_3737692 : Nat := 4983230072969 + 3 ^ 40 * 3737692 * 2
def baseEnd_3737692 : Nat := 426496118769976777013483

theorem tailTrace_3737692 : CollatzResearch.WordTrace tailWord_3737692 prefixEnd_3737692 426496118769976777013483 := by
  unfold tailWord_3737692
  simp only [CollatzResearch.WordTrace]
  refine ⟨68162413387493852908655665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90883217849991803878207553 68162413387493852908655665)
  ·
    refine ⟨51121810040620389681491749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68162413387493852908655665 51121810040620389681491749)
    ·
      refine ⟨9585339382616323065279703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51121810040620389681491749 9585339382616323065279703)
      ·
        refine ⟨14378009073924484597919555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9585339382616323065279703 14378009073924484597919555)
        ·
          refine ⟨21567013610886726896879333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14378009073924484597919555 21567013610886726896879333)
          ·
            refine ⟨4043815052041261293164875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21567013610886726896879333 4043815052041261293164875)
            ·
              refine ⟨6065722578061891939747313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043815052041261293164875 6065722578061891939747313)
              ·
                refine ⟨4549291933546418954810485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6065722578061891939747313 4549291933546418954810485)
                ·
                  refine ⟨426496118769976777013483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4549291933546418954810485 426496118769976777013483)
                  ·
                    rfl

theorem cell22_3737692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_3737692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737692 prefixEnd_3737692 := by exact prefixLift 3737692
  have htrace : WordTrace (prefixWord ++ tailWord_3737692) baseStart_3737692 baseEnd_3737692 := by
    simpa [prefixWord, tailWord_3737692, baseEnd_3737692] using wordTrace_append hprefix tailTrace_3737692
  have hstable : (prefixWord ++ tailWord_3737692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737692).length < 2 ^ (prefixWord ++ tailWord_3737692).sum := by decide
  have hdescent : baseEnd_3737692 < baseStart_3737692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737735 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 4, 3]
def baseStart_3737735 : Nat := 118140960795 + 3737735 * 2 ^ 59
def prefixEnd_3737735 : Nat := 4983230072969 + 3 ^ 40 * 3737735 * 2
def baseEnd_3737735 : Nat := 1279503076088692552215317

theorem tailTrace_3737735 : CollatzResearch.WordTrace tailWord_3737735 prefixEnd_3737735 1279503076088692552215317 := by
  unfold tailWord_3737735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136326395113831924161126659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90884263409221282774084439 136326395113831924161126659)
  ·
    refine ⟨204489592670747886241689989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136326395113831924161126659 204489592670747886241689989)
    ·
      refine ⟨38341798625765228670316873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204489592670747886241689989 38341798625765228670316873)
      ·
        refine ⟨28756348969323921502737655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38341798625765228670316873 28756348969323921502737655)
        ·
          refine ⟨43134523453985882254106483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28756348969323921502737655 43134523453985882254106483)
          ·
            refine ⟨64701785180978823381159725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43134523453985882254106483 64701785180978823381159725)
            ·
              refine ⟨24263169442867058767934897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64701785180978823381159725 24263169442867058767934897)
              ·
                refine ⟨18197377082150294075951173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24263169442867058767934897 18197377082150294075951173)
                ·
                  refine ⟨3412008202903180139240845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18197377082150294075951173 3412008202903180139240845)
                  ·
                    refine ⟨1279503076088692552215317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412008202903180139240845 1279503076088692552215317)
                    ·
                      rfl

theorem cell22_3737735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_3737735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737735 prefixEnd_3737735 := by exact prefixLift 3737735
  have htrace : WordTrace (prefixWord ++ tailWord_3737735) baseStart_3737735 baseEnd_3737735 := by
    simpa [prefixWord, tailWord_3737735, baseEnd_3737735] using wordTrace_append hprefix tailTrace_3737735
  have hstable : (prefixWord ++ tailWord_3737735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737735).length < 2 ^ (prefixWord ++ tailWord_3737735).sum := by decide
  have hdescent : baseEnd_3737735 < baseStart_3737735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737754 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_3737754 : Nat := 118140960795 + 3737754 * 2 ^ 59
def prefixEnd_3737754 : Nat := 4983230072969 + 3 ^ 40 * 3737754 * 2
def baseEnd_3737754 : Nat := 426503193392327611996753

theorem tailTrace_3737754 : CollatzResearch.WordTrace tailWord_3737754 prefixEnd_3737754 426503193392327611996753 := by
  unfold tailWord_3737754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34081772025190772601517079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90884725400508726937378877 34081772025190772601517079)
  ·
    refine ⟨51122658037786158902275619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34081772025190772601517079 51122658037786158902275619)
    ·
      refine ⟨76683987056679238353413429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51122658037786158902275619 76683987056679238353413429)
      ·
        refine ⟨7189123786563678595632509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76683987056679238353413429 7189123786563678595632509)
        ·
          refine ⟨2695921419961379473362191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7189123786563678595632509 2695921419961379473362191)
          ·
            refine ⟨4043882129942069210043287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2695921419961379473362191 4043882129942069210043287)
            ·
              refine ⟨6065823194913103815064931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043882129942069210043287 6065823194913103815064931)
              ·
                refine ⟨9098734792369655722597397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6065823194913103815064931 9098734792369655722597397)
                ·
                  refine ⟨426503193392327611996753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9098734792369655722597397 426503193392327611996753)
                  ·
                    rfl

theorem cell22_3737754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_3737754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737754 prefixEnd_3737754 := by exact prefixLift 3737754
  have htrace : WordTrace (prefixWord ++ tailWord_3737754) baseStart_3737754 baseEnd_3737754 := by
    simpa [prefixWord, tailWord_3737754, baseEnd_3737754] using wordTrace_append hprefix tailTrace_3737754
  have hstable : (prefixWord ++ tailWord_3737754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737754).length < 2 ^ (prefixWord ++ tailWord_3737754).sum := by decide
  have hdescent : baseEnd_3737754 < baseStart_3737754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737808 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_3737808 : Nat := 118140960795 + 3737808 * 2 ^ 59
def prefixEnd_3737808 : Nat := 4983230072969 + 3 ^ 40 * 3737808 * 2
def baseEnd_3737808 : Nat := 1279528065480544695140093

theorem tailTrace_3737808 : CollatzResearch.WordTrace tailWord_3737808 prefixEnd_3737808 1279528065480544695140093 := by
  unfold tailWord_3737808
  simp only [CollatzResearch.WordTrace]
  refine ⟨68164528821283728814267039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90886038428378305085689385 68164528821283728814267039)
  ·
    refine ⟨102246793231925593221400559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68164528821283728814267039 102246793231925593221400559)
    ·
      refine ⟨153370189847888389832100839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102246793231925593221400559 153370189847888389832100839)
      ·
        refine ⟨230055284771832584748151259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153370189847888389832100839 230055284771832584748151259)
        ·
          refine ⟨345082927157748877122226889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230055284771832584748151259 345082927157748877122226889)
          ·
            refine ⟨258812195368311657841670167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345082927157748877122226889 258812195368311657841670167)
            ·
              refine ⟨388218293052467486762505251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258812195368311657841670167 388218293052467486762505251)
              ·
                refine ⟨582327439578701230143757877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388218293052467486762505251 582327439578701230143757877)
                ·
                  refine ⟨54593197460503240325977301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 582327439578701230143757877 54593197460503240325977301)
                  ·
                    refine ⟨1279528065480544695140093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54593197460503240325977301 1279528065480544695140093)
                    ·
                      rfl

theorem cell22_3737808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_3737808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737808 prefixEnd_3737808 := by exact prefixLift 3737808
  have htrace : WordTrace (prefixWord ++ tailWord_3737808) baseStart_3737808 baseEnd_3737808 := by
    simpa [prefixWord, tailWord_3737808, baseEnd_3737808] using wordTrace_append hprefix tailTrace_3737808
  have hstable : (prefixWord ++ tailWord_3737808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737808).length < 2 ^ (prefixWord ++ tailWord_3737808).sum := by decide
  have hdescent : baseEnd_3737808 < baseStart_3737808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737825 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 2, 5]
def baseStart_3737825 : Nat := 118140960795 + 3737825 * 2 ^ 59
def prefixEnd_3737825 : Nat := 4983230072969 + 3 ^ 40 * 3737825 * 2
def baseEnd_3737825 : Nat := 1279533884927962317465041

theorem tailTrace_3737825 : CollatzResearch.WordTrace tailWord_3737825 prefixEnd_3737825 1279533884927962317465041 := by
  unfold tailWord_3737825
  simp only [CollatzResearch.WordTrace]
  refine ⟨136329677683505869531902929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90886451789003913021268619 136329677683505869531902929)
  ·
    refine ⟨102247258262629402148927197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136329677683505869531902929 102247258262629402148927197)
    ·
      refine ⟨38342721848486025805847699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102247258262629402148927197 38342721848486025805847699)
      ·
        refine ⟨57514082772729038708771549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38342721848486025805847699 57514082772729038708771549)
        ·
          refine ⟨21567781039773389515789331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57514082772729038708771549 21567781039773389515789331)
          ·
            refine ⟨32351671559660084273683997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21567781039773389515789331 32351671559660084273683997)
            ·
              refine ⟨12131876834872531602631499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32351671559660084273683997 12131876834872531602631499)
              ·
                refine ⟨18197815252308797403947249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12131876834872531602631499 18197815252308797403947249)
                ·
                  refine ⟨13648361439231598052960437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18197815252308797403947249 13648361439231598052960437)
                  ·
                    refine ⟨1279533884927962317465041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13648361439231598052960437 1279533884927962317465041)
                    ·
                      rfl

theorem cell22_3737825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_3737825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737825 prefixEnd_3737825 := by exact prefixLift 3737825
  have htrace : WordTrace (prefixWord ++ tailWord_3737825) baseStart_3737825 baseEnd_3737825 := by
    simpa [prefixWord, tailWord_3737825, baseEnd_3737825] using wordTrace_append hprefix tailTrace_3737825
  have hstable : (prefixWord ++ tailWord_3737825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737825).length < 2 ^ (prefixWord ++ tailWord_3737825).sum := by decide
  have hdescent : baseEnd_3737825 < baseStart_3737825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737857 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_3737857 : Nat := 118140960795 + 3737857 * 2 ^ 59
def prefixEnd_3737857 : Nat := 4983230072969 + 3 ^ 40 * 3737857 * 2
def baseEnd_3737857 : Nat := 1279544839181924900664943

theorem tailTrace_3737857 : CollatzResearch.WordTrace tailWord_3737857 prefixEnd_3737857 1279544839181924900664943 := by
  unfold tailWord_3737857
  simp only [CollatzResearch.WordTrace]
  refine ⟨136330844819389938997067825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90887229879593292664711883 136330844819389938997067825)
  ·
    refine ⟨102248133614542454247800869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136330844819389938997067825 102248133614542454247800869)
    ·
      refine ⟨19171525052726710171462663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102248133614542454247800869 19171525052726710171462663)
      ·
        refine ⟨28757287579090065257193995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19171525052726710171462663 28757287579090065257193995)
        ·
          refine ⟨43135931368635097885790993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28757287579090065257193995 43135931368635097885790993)
          ·
            refine ⟨32351948526476323414343245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43135931368635097885790993 32351948526476323414343245)
            ·
              refine ⟨12131980697428621280378717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32351948526476323414343245 12131980697428621280378717)
              ·
                refine ⟨4549492761535732980142019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12131980697428621280378717 4549492761535732980142019)
                ·
                  refine ⟨6824239142303599470213029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4549492761535732980142019 6824239142303599470213029)
                  ·
                    refine ⟨1279544839181924900664943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824239142303599470213029 1279544839181924900664943)
                    ·
                      rfl

theorem cell22_3737857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_3737857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737857 prefixEnd_3737857 := by exact prefixLift 3737857
  have htrace : WordTrace (prefixWord ++ tailWord_3737857) baseStart_3737857 baseEnd_3737857 := by
    simpa [prefixWord, tailWord_3737857, baseEnd_3737857] using wordTrace_append hprefix tailTrace_3737857
  have hstable : (prefixWord ++ tailWord_3737857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737857).length < 2 ^ (prefixWord ++ tailWord_3737857).sum := by decide
  have hdescent : baseEnd_3737857 < baseStart_3737857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737887 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_3737887 : Nat := 118140960795 + 3737887 * 2 ^ 59
def prefixEnd_3737887 : Nat := 4983230072969 + 3 ^ 40 * 3737887 * 2
def baseEnd_3737887 : Nat := 1279555108795014822414851

theorem tailTrace_3737887 : CollatzResearch.WordTrace tailWord_3737887 prefixEnd_3737887 1279555108795014822414851 := by
  unfold tailWord_3737887
  simp only [CollatzResearch.WordTrace]
  refine ⟨136331939009281254120659915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90887959339520836080439943 136331939009281254120659915)
  ·
    refine ⟨204497908513921881180989873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136331939009281254120659915 204497908513921881180989873)
    ·
      refine ⟨153373431385441410885742405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204497908513921881180989873 153373431385441410885742405)
      ·
        refine ⟨28757518384770264541076701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153373431385441410885742405 28757518384770264541076701)
        ·
          refine ⟨10784069394288849202903763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28757518384770264541076701 10784069394288849202903763)
          ·
            refine ⟨16176104091433273804355645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10784069394288849202903763 16176104091433273804355645)
            ·
              refine ⟨6066039034287477676633367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16176104091433273804355645 6066039034287477676633367)
              ·
                refine ⟨9099058551431216514950051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6066039034287477676633367 9099058551431216514950051)
                ·
                  refine ⟨13648587827146824772425077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9099058551431216514950051 13648587827146824772425077)
                  ·
                    refine ⟨1279555108795014822414851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13648587827146824772425077 1279555108795014822414851)
                    ·
                      rfl

theorem cell22_3737887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_3737887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737887 prefixEnd_3737887 := by exact prefixLift 3737887
  have htrace : WordTrace (prefixWord ++ tailWord_3737887) baseStart_3737887 baseEnd_3737887 := by
    simpa [prefixWord, tailWord_3737887, baseEnd_3737887] using wordTrace_append hprefix tailTrace_3737887
  have hstable : (prefixWord ++ tailWord_3737887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737887).length < 2 ^ (prefixWord ++ tailWord_3737887).sum := by decide
  have hdescent : baseEnd_3737887 < baseStart_3737887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737906 : List Nat := [3, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_3737906 : Nat := 118140960795 + 3737906 * 2 ^ 59
def prefixEnd_3737906 : Nat := 4983230072969 + 3 ^ 40 * 3737906 * 2
def baseEnd_3737906 : Nat := 426520537627768368729931

theorem tailTrace_3737906 : CollatzResearch.WordTrace tailWord_3737906 prefixEnd_3737906 426520537627768368729931 := by
  unfold tailWord_3737906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34083157999053105091400393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90888421330808280243734381 34083157999053105091400393)
  ·
    refine ⟨25562368499289828818550295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34083157999053105091400393 25562368499289828818550295)
    ·
      refine ⟨38343552748934743227825443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25562368499289828818550295 38343552748934743227825443)
      ·
        refine ⟨57515329123402114841738165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38343552748934743227825443 57515329123402114841738165)
        ·
          refine ⟨5392062105318948266412953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57515329123402114841738165 5392062105318948266412953)
          ·
            refine ⟨4044046578989211199809715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392062105318948266412953 4044046578989211199809715)
            ·
              refine ⟨6066069868483816799714573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044046578989211199809715 6066069868483816799714573)
              ·
                refine ⟨2274776200681431299892965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6066069868483816799714573 2274776200681431299892965)
                ·
                  refine ⟨426520537627768368729931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274776200681431299892965 426520537627768368729931)
                  ·
                    rfl

theorem cell22_3737906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_3737906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737906 prefixEnd_3737906 := by exact prefixLift 3737906
  have htrace : WordTrace (prefixWord ++ tailWord_3737906) baseStart_3737906 baseEnd_3737906 := by
    simpa [prefixWord, tailWord_3737906, baseEnd_3737906] using wordTrace_append hprefix tailTrace_3737906
  have hstable : (prefixWord ++ tailWord_3737906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737906).length < 2 ^ (prefixWord ++ tailWord_3737906).sum := by decide
  have hdescent : baseEnd_3737906 < baseStart_3737906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3737992 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_3737992 : Nat := 118140960795 + 3737992 * 2 ^ 59
def prefixEnd_3737992 : Nat := 4983230072969 + 3 ^ 40 * 3737992 * 2
def baseEnd_3737992 : Nat := 1279591052440829548539529

theorem tailTrace_3737992 : CollatzResearch.WordTrace tailWord_3737992 prefixEnd_3737992 1279591052440829548539529 := by
  unfold tailWord_3737992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68167884336950428526616115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90890512449267238035488153 68167884336950428526616115)
  ·
    refine ⟨102251826505425642789924173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68167884336950428526616115 102251826505425642789924173)
    ·
      refine ⟨38344434939534616046221565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102251826505425642789924173 38344434939534616046221565)
      ·
        refine ⟨14379163102325481017333087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38344434939534616046221565 14379163102325481017333087)
        ·
          refine ⟨21568744653488221525999631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379163102325481017333087 21568744653488221525999631)
          ·
            refine ⟨32353116980232332288999447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21568744653488221525999631 32353116980232332288999447)
            ·
              refine ⟨48529675470348498433499171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32353116980232332288999447 48529675470348498433499171)
              ·
                refine ⟨72794513205522747650248757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48529675470348498433499171 72794513205522747650248757)
                ·
                  refine ⟨6824485613017757592210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72794513205522747650248757 6824485613017757592210821)
                  ·
                    refine ⟨1279591052440829548539529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6824485613017757592210821 1279591052440829548539529)
                    ·
                      rfl

theorem cell22_3737992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_3737992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3737992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3737992 prefixEnd_3737992 := by exact prefixLift 3737992
  have htrace : WordTrace (prefixWord ++ tailWord_3737992) baseStart_3737992 baseEnd_3737992 := by
    simpa [prefixWord, tailWord_3737992, baseEnd_3737992] using wordTrace_append hprefix tailTrace_3737992
  have hstable : (prefixWord ++ tailWord_3737992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3737992).length < 2 ^ (prefixWord ++ tailWord_3737992).sum := by decide
  have hdescent : baseEnd_3737992 < baseStart_3737992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3737992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738039 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 4, 3]
def baseStart_3738039 : Nat := 118140960795 + 3738039 * 2 ^ 59
def prefixEnd_3738039 : Nat := 4983230072969 + 3 ^ 40 * 3738039 * 2
def baseEnd_3738039 : Nat := 1279607141501337092614385

theorem tailTrace_3738039 : CollatzResearch.WordTrace tailWord_3738039 prefixEnd_3738039 1279607141501337092614385 := by
  unfold tailWord_3738039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136337482904730584080193171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90891655269820389386795447 136337482904730584080193171)
  ·
    refine ⟨204506224357095876120289757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136337482904730584080193171 204506224357095876120289757)
    ·
      refine ⟨76689834133910953545108659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204506224357095876120289757 76689834133910953545108659)
      ·
        refine ⟨115034751200866430317662989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76689834133910953545108659 115034751200866430317662989)
        ·
          refine ⟨43138031700324911369123621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115034751200866430317662989 43138031700324911369123621)
          ·
            refine ⟨8088380943810920881710679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43138031700324911369123621 8088380943810920881710679)
            ·
              refine ⟨12132571415716381322566019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8088380943810920881710679 12132571415716381322566019)
              ·
                refine ⟨18198857123574571983849029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12132571415716381322566019 18198857123574571983849029)
                ·
                  refine ⟨3412285710670232246971693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18198857123574571983849029 3412285710670232246971693)
                  ·
                    refine ⟨1279607141501337092614385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412285710670232246971693 1279607141501337092614385)
                    ·
                      rfl

theorem cell22_3738039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_3738039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738039 prefixEnd_3738039 := by exact prefixLift 3738039
  have htrace : WordTrace (prefixWord ++ tailWord_3738039) baseStart_3738039 baseEnd_3738039 := by
    simpa [prefixWord, tailWord_3738039, baseEnd_3738039] using wordTrace_append hprefix tailTrace_3738039
  have hstable : (prefixWord ++ tailWord_3738039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738039).length < 2 ^ (prefixWord ++ tailWord_3738039).sum := by decide
  have hdescent : baseEnd_3738039 < baseStart_3738039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738069 : List Nat := [1, 3, 2, 3, 1, 2, 4, 6]
def baseStart_3738069 : Nat := 118140960795 + 3738069 * 2 ^ 59
def prefixEnd_3738069 : Nat := 4983230072969 + 3 ^ 40 * 3738069 * 2
def baseEnd_3738069 : Nat := 142179712346047446040477

theorem tailTrace_3738069 : CollatzResearch.WordTrace tailWord_3738069 prefixEnd_3738069 142179712346047446040477 := by
  unfold tailWord_3738069
  simp only [CollatzResearch.WordTrace]
  refine ⟨136338577094621899203785261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90892384729747932802523507 136338577094621899203785261)
  ·
    refine ⟨51126966410483212201419473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136338577094621899203785261 51126966410483212201419473)
    ·
      refine ⟨38345224807862409151064605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51126966410483212201419473 38345224807862409151064605)
      ·
        refine ⟨14379459302948403431649227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38345224807862409151064605 14379459302948403431649227)
        ·
          refine ⟨21569188954422605147473841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379459302948403431649227 21569188954422605147473841)
          ·
            refine ⟨16176891715816953860605381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21569188954422605147473841 16176891715816953860605381)
            ·
              refine ⟨3033167196715678848863509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16176891715816953860605381 3033167196715678848863509)
              ·
                refine ⟨142179712346047446040477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3033167196715678848863509 142179712346047446040477)
                ·
                  rfl

theorem cell22_3738069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 6].length) (baseStart_3738069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738069 prefixEnd_3738069 := by exact prefixLift 3738069
  have htrace : WordTrace (prefixWord ++ tailWord_3738069) baseStart_3738069 baseEnd_3738069 := by
    simpa [prefixWord, tailWord_3738069, baseEnd_3738069] using wordTrace_append hprefix tailTrace_3738069
  have hstable : (prefixWord ++ tailWord_3738069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738069).length < 2 ^ (prefixWord ++ tailWord_3738069).sum := by decide
  have hdescent : baseEnd_3738069 < baseStart_3738069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738097 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 7]
def baseStart_3738097 : Nat := 118140960795 + 3738097 * 2 ^ 59
def prefixEnd_3738097 : Nat := 4983230072969 + 3 ^ 40 * 3738097 * 2
def baseEnd_3738097 : Nat := 426542332028881424888069

theorem tailTrace_3738097 : CollatzResearch.WordTrace tailWord_3738097 prefixEnd_3738097 426542332028881424888069 := by
  unfold tailWord_3738097
  simp only [CollatzResearch.WordTrace]
  refine ⟨136339598338520459985804545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90893065559013639990536363 136339598338520459985804545)
  ·
    refine ⟨102254698753890344989353409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136339598338520459985804545 102254698753890344989353409)
    ·
      refine ⟨76691024065417758742015057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102254698753890344989353409 76691024065417758742015057)
      ·
        refine ⟨57518268049063319056511293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76691024065417758742015057 57518268049063319056511293)
        ·
          refine ⟨21569350518398744646191735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57518268049063319056511293 21569350518398744646191735)
          ·
            refine ⟨32354025777598116969287603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21569350518398744646191735 32354025777598116969287603)
            ·
              refine ⟨48531038666397175453931405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32354025777598116969287603 48531038666397175453931405)
              ·
                refine ⟨18199139499898940795224277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48531038666397175453931405 18199139499898940795224277)
                ·
                  refine ⟨426542332028881424888069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18199139499898940795224277 426542332028881424888069)
                  ·
                    rfl

theorem cell22_3738097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_3738097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738097 prefixEnd_3738097 := by exact prefixLift 3738097
  have htrace : WordTrace (prefixWord ++ tailWord_3738097) baseStart_3738097 baseEnd_3738097 := by
    simpa [prefixWord, tailWord_3738097, baseEnd_3738097] using wordTrace_append hprefix tailTrace_3738097
  have hstable : (prefixWord ++ tailWord_3738097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738097).length < 2 ^ (prefixWord ++ tailWord_3738097).sum := by decide
  have hdescent : baseEnd_3738097 < baseStart_3738097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738148 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3738148 : Nat := 118140960795 + 3738148 * 2 ^ 59
def prefixEnd_3738148 : Nat := 4983230072969 + 3 ^ 40 * 3738148 * 2
def baseEnd_3738148 : Nat := 426548151476299047213017

theorem tailTrace_3738148 : CollatzResearch.WordTrace tailWord_3738148 prefixEnd_3738148 426548151476299047213017 := by
  unfold tailWord_3738148
  simp only [CollatzResearch.WordTrace]
  refine ⟨68170729230667847847955549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90894305640890463797274065 68170729230667847847955549)
  ·
    refine ⟨25564023461500442942983331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68170729230667847847955549 25564023461500442942983331)
    ·
      refine ⟨38346035192250664414474997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25564023461500442942983331 38346035192250664414474997)
      ·
        refine ⟨3594940799273499788857031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38346035192250664414474997 3594940799273499788857031)
        ·
          refine ⟨5392411198910249683285547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594940799273499788857031 5392411198910249683285547)
          ·
            refine ⟨8088616798365374524928321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392411198910249683285547 8088616798365374524928321)
            ·
              refine ⟨6066462598774030893696241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8088616798365374524928321 6066462598774030893696241)
              ·
                refine ⟨4549846949080523170272181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066462598774030893696241 4549846949080523170272181)
                ·
                  refine ⟨426548151476299047213017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4549846949080523170272181 426548151476299047213017)
                  ·
                    rfl

theorem cell22_3738148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3738148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738148 prefixEnd_3738148 := by exact prefixLift 3738148
  have htrace : WordTrace (prefixWord ++ tailWord_3738148) baseStart_3738148 baseEnd_3738148 := by
    simpa [prefixWord, tailWord_3738148, baseEnd_3738148] using wordTrace_append hprefix tailTrace_3738148
  have hstable : (prefixWord ++ tailWord_3738148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738148).length < 2 ^ (prefixWord ++ tailWord_3738148).sum := by decide
  have hdescent : baseEnd_3738148 < baseStart_3738148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738152 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 1, 3]
def baseStart_3738152 : Nat := 118140960795 + 3738152 * 2 ^ 59
def prefixEnd_3738152 : Nat := 4983230072969 + 3 ^ 40 * 3738152 * 2
def baseEnd_3738152 : Nat := 1279645823710642464539039

theorem tailTrace_3738152 : CollatzResearch.WordTrace tailWord_3738152 prefixEnd_3738152 1279645823710642464539039 := by
  unfold tailWord_3738152
  simp only [CollatzResearch.WordTrace]
  refine ⟨68170802176660602189528355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90894402902214136252704473 68170802176660602189528355)
  ·
    refine ⟨102256203264990903284292533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68170802176660602189528355 102256203264990903284292533)
    ·
      refine ⟨9586519056092897182902425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102256203264990903284292533 9586519056092897182902425)
      ·
        refine ⟨7189889292069672887176819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9586519056092897182902425 7189889292069672887176819)
        ·
          refine ⟨10784833938104509330765229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7189889292069672887176819 10784833938104509330765229)
          ·
            refine ⟨4044312726789190999036961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10784833938104509330765229 4044312726789190999036961)
            ·
              refine ⟨3033234545091893249277721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044312726789190999036961 3033234545091893249277721)
              ·
                refine ⟨2274925908818919936958291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033234545091893249277721 2274925908818919936958291)
                ·
                  refine ⟨3412388863228379905437437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2274925908818919936958291 3412388863228379905437437)
                  ·
                    refine ⟨1279645823710642464539039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412388863228379905437437 1279645823710642464539039)
                    ·
                      rfl

theorem cell22_3738152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_3738152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738152 prefixEnd_3738152 := by exact prefixLift 3738152
  have htrace : WordTrace (prefixWord ++ tailWord_3738152) baseStart_3738152 baseEnd_3738152 := by
    simpa [prefixWord, tailWord_3738152, baseEnd_3738152] using wordTrace_append hprefix tailTrace_3738152
  have hstable : (prefixWord ++ tailWord_3738152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738152).length < 2 ^ (prefixWord ++ tailWord_3738152).sum := by decide
  have hdescent : baseEnd_3738152 < baseStart_3738152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738187 : List Nat := [1, 1, 1, 1, 3, 1, 4, 10]
def baseStart_3738187 : Nat := 118140960795 + 3738187 * 2 ^ 59
def prefixEnd_3738187 : Nat := 4983230072969 + 3 ^ 40 * 3738187 * 2
def baseEnd_3738187 : Nat := 142184200547323782212659

theorem tailTrace_3738187 : CollatzResearch.WordTrace tailWord_3738187 prefixEnd_3738187 142184200547323782212659 := by
  unfold tailWord_3738187
  simp only [CollatzResearch.WordTrace]
  refine ⟨136342880908194405356580815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90895253938796270237720543 136342880908194405356580815)
  ·
    refine ⟨204514321362291608034871223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136342880908194405356580815 204514321362291608034871223)
    ·
      refine ⟨306771482043437412052306835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204514321362291608034871223 306771482043437412052306835)
      ·
        refine ⟨460157223065156118078460253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306771482043437412052306835 460157223065156118078460253)
        ·
          refine ⟨172558958649433544279422595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460157223065156118078460253 172558958649433544279422595)
          ·
            refine ⟨258838437974150316419133893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172558958649433544279422595 258838437974150316419133893)
            ·
              refine ⟨48532207120153184328587605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258838437974150316419133893 48532207120153184328587605)
              ·
                refine ⟨142184200547323782212659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48532207120153184328587605 142184200547323782212659)
                ·
                  rfl

theorem cell22_3738187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_3738187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738187 prefixEnd_3738187 := by exact prefixLift 3738187
  have htrace : WordTrace (prefixWord ++ tailWord_3738187) baseStart_3738187 baseEnd_3738187 := by
    simpa [prefixWord, tailWord_3738187, baseEnd_3738187] using wordTrace_append hprefix tailTrace_3738187
  have hstable : (prefixWord ++ tailWord_3738187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738187).length < 2 ^ (prefixWord ++ tailWord_3738187).sum := by decide
  have hdescent : baseEnd_3738187 < baseStart_3738187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738236 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_3738236 : Nat := 118140960795 + 3738236 * 2 ^ 59
def prefixEnd_3738236 : Nat := 4983230072969 + 3 ^ 40 * 3738236 * 2
def baseEnd_3738236 : Nat := 1279674578627294245438781

theorem tailTrace_3738236 : CollatzResearch.WordTrace tailWord_3738236 prefixEnd_3738236 1279674578627294245438781 := by
  unfold tailWord_3738236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68172334042508443362557281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90896445390011257816743041 68172334042508443362557281)
  ·
    refine ⟨51129250531881332521917961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68172334042508443362557281 51129250531881332521917961)
    ·
      refine ⟨38346937898910999391438471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51129250531881332521917961 38346937898910999391438471)
      ·
        refine ⟨57520406848366499087157707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38346937898910999391438471 57520406848366499087157707)
        ·
          refine ⟨86280610272549748630736561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57520406848366499087157707 86280610272549748630736561)
          ·
            refine ⟨64710457704412311473052421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86280610272549748630736561 64710457704412311473052421)
            ·
              refine ⟨12133210819577308401197329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64710457704412311473052421 12133210819577308401197329)
              ·
                refine ⟨9099908114682981300897997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12133210819577308401197329 9099908114682981300897997)
                ·
                  refine ⟨3412465543006117987836749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9099908114682981300897997 3412465543006117987836749)
                  ·
                    refine ⟨1279674578627294245438781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412465543006117987836749 1279674578627294245438781)
                    ·
                      rfl

theorem cell22_3738236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_3738236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738236 prefixEnd_3738236 := by exact prefixLift 3738236
  have htrace : WordTrace (prefixWord ++ tailWord_3738236) baseStart_3738236 baseEnd_3738236 := by
    simpa [prefixWord, tailWord_3738236, baseEnd_3738236] using wordTrace_append hprefix tailTrace_3738236
  have hstable : (prefixWord ++ tailWord_3738236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738236).length < 2 ^ (prefixWord ++ tailWord_3738236).sum := by decide
  have hdescent : baseEnd_3738236 < baseStart_3738236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738328 : List Nat := [2, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_3738328 : Nat := 118140960795 + 3738328 * 2 ^ 59
def prefixEnd_3738328 : Nat := 4983230072969 + 3 ^ 40 * 3738328 * 2
def baseEnd_3738328 : Nat := 426568690702478890712833

theorem tailTrace_3738328 : CollatzResearch.WordTrace tailWord_3738328 prefixEnd_3738328 426568690702478890712833 := by
  unfold tailWord_3738328
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174011800341793218731819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90898682400455724291642425 68174011800341793218731819)
  ·
    refine ⟨102261017700512689828097729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68174011800341793218731819 102261017700512689828097729)
    ·
      refine ⟨76695763275384517371073297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102261017700512689828097729 76695763275384517371073297)
      ·
        refine ⟨57521822456538388028304973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76695763275384517371073297 57521822456538388028304973)
        ·
          refine ⟨21570683421201895510614365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57521822456538388028304973 21570683421201895510614365)
          ·
            refine ⟨8089006282950710816480387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21570683421201895510614365 8089006282950710816480387)
            ·
              refine ⟨12133509424426066224720581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089006282950710816480387 12133509424426066224720581)
              ·
                refine ⟨2275033017079887417135109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12133509424426066224720581 2275033017079887417135109)
                ·
                  refine ⟨426568690702478890712833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275033017079887417135109 426568690702478890712833)
                  ·
                    rfl

theorem cell22_3738328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_3738328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738328 prefixEnd_3738328 := by exact prefixLift 3738328
  have htrace : WordTrace (prefixWord ++ tailWord_3738328) baseStart_3738328 baseEnd_3738328 := by
    simpa [prefixWord, tailWord_3738328, baseEnd_3738328] using wordTrace_append hprefix tailTrace_3738328
  have hstable : (prefixWord ++ tailWord_3738328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738328).length < 2 ^ (prefixWord ++ tailWord_3738328).sum := by decide
  have hdescent : baseEnd_3738328 < baseStart_3738328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738371 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 7, 3]
def baseStart_3738371 : Nat := 118140960795 + 3738371 * 2 ^ 59
def prefixEnd_3738371 : Nat := 4983230072969 + 3 ^ 40 * 3738371 * 2
def baseEnd_3738371 : Nat := 1279720791886198893313367

theorem tailTrace_3738371 : CollatzResearch.WordTrace tailWord_3738371 prefixEnd_3738371 1279720791886198893313367 := by
  unfold tailWord_3738371
  simp only [CollatzResearch.WordTrace]
  refine ⟨136349591939527804781278967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90899727959685203187519311 136349591939527804781278967)
  ·
    refine ⟨204524387909291707171918451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136349591939527804781278967 204524387909291707171918451)
    ·
      refine ⟨306786581863937560757877677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204524387909291707171918451 306786581863937560757877677)
      ·
        refine ⟨115044968198976585284204129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 306786581863937560757877677 115044968198976585284204129)
        ·
          refine ⟨86283726149232438963153097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115044968198976585284204129 86283726149232438963153097)
          ·
            refine ⟨64712794611924329222364823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86283726149232438963153097 64712794611924329222364823)
            ·
              refine ⟨97069191917886493833547235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64712794611924329222364823 97069191917886493833547235)
              ·
                refine ⟨145603787876829740750320853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97069191917886493833547235 145603787876829740750320853)
                ·
                  refine ⟨3412588778363197048835645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145603787876829740750320853 3412588778363197048835645)
                  ·
                    refine ⟨1279720791886198893313367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412588778363197048835645 1279720791886198893313367)
                    ·
                      rfl

theorem cell22_3738371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 3].length) (baseStart_3738371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738371 prefixEnd_3738371 := by exact prefixLift 3738371
  have htrace : WordTrace (prefixWord ++ tailWord_3738371) baseStart_3738371 baseEnd_3738371 := by
    simpa [prefixWord, tailWord_3738371, baseEnd_3738371] using wordTrace_append hprefix tailTrace_3738371
  have hstable : (prefixWord ++ tailWord_3738371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738371).length < 2 ^ (prefixWord ++ tailWord_3738371).sum := by decide
  have hdescent : baseEnd_3738371 < baseStart_3738371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738452 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 5]
def baseStart_3738452 : Nat := 118140960795 + 3738452 * 2 ^ 59
def prefixEnd_3738452 : Nat := 4983230072969 + 3 ^ 40 * 3738452 * 2
def baseEnd_3738452 : Nat := 426582839947180560679373

theorem tailTrace_3738452 : CollatzResearch.WordTrace tailWord_3738452 prefixEnd_3738452 426582839947180560679373 := by
  unfold tailWord_3738452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68176273126117177807488805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90901697501489570409985073 68176273126117177807488805)
  ·
    refine ⟨12783051211146970838904151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68176273126117177807488805 12783051211146970838904151)
    ·
      refine ⟨19174576816720456258356227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12783051211146970838904151 19174576816720456258356227)
      ·
        refine ⟨28761865225080684387534341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19174576816720456258356227 28761865225080684387534341)
        ·
          refine ⟨5392849729702628322662689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28761865225080684387534341 5392849729702628322662689)
          ·
            refine ⟨4044637297276971241997017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5392849729702628322662689 4044637297276971241997017)
            ·
              refine ⟨3033477972957728431497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044637297276971241997017 3033477972957728431497763)
              ·
                refine ⟨4550216959436592647246645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033477972957728431497763 4550216959436592647246645)
                ·
                  refine ⟨426582839947180560679373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550216959436592647246645 426582839947180560679373)
                  ·
                    rfl

theorem cell22_3738452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_3738452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738452 prefixEnd_3738452 := by exact prefixLift 3738452
  have htrace : WordTrace (prefixWord ++ tailWord_3738452) baseStart_3738452 baseEnd_3738452 := by
    simpa [prefixWord, tailWord_3738452, baseEnd_3738452] using wordTrace_append hprefix tailTrace_3738452
  have hstable : (prefixWord ++ tailWord_3738452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738452).length < 2 ^ (prefixWord ++ tailWord_3738452).sum := by decide
  have hdescent : baseEnd_3738452 < baseStart_3738452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738493 : List Nat := [1, 4, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_3738493 : Nat := 118140960795 + 3738493 * 2 ^ 59
def prefixEnd_3738493 : Nat := 4983230072969 + 3 ^ 40 * 3738493 * 2
def baseEnd_3738493 : Nat := 1279762554979431241762993

theorem tailTrace_3738493 : CollatzResearch.WordTrace tailWord_3738493 prefixEnd_3738493 1279762554979431241762993 := by
  unfold tailWord_3738493
  simp only [CollatzResearch.WordTrace]
  refine ⟨136354041645085819617220133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90902694430057213078146755 136354041645085819617220133)
  ·
    refine ⟨25566382808453591178228775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136354041645085819617220133 25566382808453591178228775)
    ·
      refine ⟨38349574212680386767343163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566382808453591178228775 38349574212680386767343163)
      ·
        refine ⟨57524361319020580151014745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38349574212680386767343163 57524361319020580151014745)
        ·
          refine ⟨43143270989265435113261059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57524361319020580151014745 43143270989265435113261059)
          ·
            refine ⟨64714906483898152669891589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43143270989265435113261059 64714906483898152669891589)
            ·
              refine ⟨12134044965730903625604673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64714906483898152669891589 12134044965730903625604673)
              ·
                refine ⟨9100533724298177719203505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12134044965730903625604673 9100533724298177719203505)
                ·
                  refine ⟨6825400293223633289402629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100533724298177719203505 6825400293223633289402629)
                  ·
                    refine ⟨1279762554979431241762993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825400293223633289402629 1279762554979431241762993)
                    ·
                      rfl

theorem cell22_3738493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_3738493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738493 prefixEnd_3738493 := by exact prefixLift 3738493
  have htrace : WordTrace (prefixWord ++ tailWord_3738493) baseStart_3738493 baseEnd_3738493 := by
    simpa [prefixWord, tailWord_3738493, baseEnd_3738493] using wordTrace_append hprefix tailTrace_3738493
  have hstable : (prefixWord ++ tailWord_3738493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738493).length < 2 ^ (prefixWord ++ tailWord_3738493).sum := by decide
  have hdescent : baseEnd_3738493 < baseStart_3738493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738521 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_3738521 : Nat := 118140960795 + 3738521 * 2 ^ 59
def prefixEnd_3738521 : Nat := 4983230072969 + 3 ^ 40 * 3738521 * 2
def baseEnd_3738521 : Nat := 1279772139951648502062907

theorem tailTrace_3738521 : CollatzResearch.WordTrace tailWord_3738521 prefixEnd_3738521 1279772139951648502062907 := by
  unfold tailWord_3738521
  simp only [CollatzResearch.WordTrace]
  refine ⟨136355062888984380399239417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90903375259322920266159611 136355062888984380399239417)
  ·
    refine ⟨102266297166738285299429563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136355062888984380399239417 102266297166738285299429563)
    ·
      refine ⟨153399445750107427949144345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102266297166738285299429563 153399445750107427949144345)
      ·
        refine ⟨115049584312580570961858259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153399445750107427949144345 115049584312580570961858259)
        ·
          refine ⟨172574376468870856442787389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115049584312580570961858259 172574376468870856442787389)
          ·
            refine ⟨64715391175826571166045271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172574376468870856442787389 64715391175826571166045271)
            ·
              refine ⟨97073086763739856749067907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64715391175826571166045271 97073086763739856749067907)
              ·
                refine ⟨145609630145609785123601861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97073086763739856749067907 145609630145609785123601861)
                ·
                  refine ⟨27301805652301834710675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145609630145609785123601861 27301805652301834710675349)
                  ·
                    refine ⟨1279772139951648502062907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27301805652301834710675349 1279772139951648502062907)
                    ·
                      rfl

theorem cell22_3738521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_3738521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738521 prefixEnd_3738521 := by exact prefixLift 3738521
  have htrace : WordTrace (prefixWord ++ tailWord_3738521) baseStart_3738521 baseEnd_3738521 := by
    simpa [prefixWord, tailWord_3738521, baseEnd_3738521] using wordTrace_append hprefix tailTrace_3738521
  have hstable : (prefixWord ++ tailWord_3738521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738521).length < 2 ^ (prefixWord ++ tailWord_3738521).sum := by decide
  have hdescent : baseEnd_3738521 < baseStart_3738521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738553 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 7]
def baseStart_3738553 : Nat := 118140960795 + 3738553 * 2 ^ 59
def prefixEnd_3738553 : Nat := 4983230072969 + 3 ^ 40 * 3738553 * 2
def baseEnd_3738553 : Nat := 426594364735203695087603

theorem tailTrace_3738553 : CollatzResearch.WordTrace tailWord_3738553 prefixEnd_3738553 426594364735203695087603 := by
  unfold tailWord_3738553
  simp only [CollatzResearch.WordTrace]
  refine ⟨136356230024868449864404313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90904153349912299909602875 136356230024868449864404313)
  ·
    refine ⟨102267172518651337398303235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136356230024868449864404313 102267172518651337398303235)
    ·
      refine ⟨153400758777977006097454853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102267172518651337398303235 153400758777977006097454853)
      ·
        refine ⟨28762642270870688643272785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153400758777977006097454853 28762642270870688643272785)
        ·
          refine ⟨21571981703153016482454589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28762642270870688643272785 21571981703153016482454589)
          ·
            refine ⟨8089493138682381180920471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21571981703153016482454589 8089493138682381180920471)
            ·
              refine ⟨12134239708023571771380707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089493138682381180920471 12134239708023571771380707)
              ·
                refine ⟨18201359562035357657071061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134239708023571771380707 18201359562035357657071061)
                ·
                  refine ⟨426594364735203695087603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18201359562035357657071061 426594364735203695087603)
                  ·
                    rfl

theorem cell22_3738553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_3738553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738553 prefixEnd_3738553 := by exact prefixLift 3738553
  have htrace : WordTrace (prefixWord ++ tailWord_3738553) baseStart_3738553 baseEnd_3738553 := by
    simpa [prefixWord, tailWord_3738553, baseEnd_3738553] using wordTrace_append hprefix tailTrace_3738553
  have hstable : (prefixWord ++ tailWord_3738553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738553).length < 2 ^ (prefixWord ++ tailWord_3738553).sum := by decide
  have hdescent : baseEnd_3738553 < baseStart_3738553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738557 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_3738557 : Nat := 118140960795 + 3738557 * 2 ^ 59
def prefixEnd_3738557 : Nat := 4983230072969 + 3 ^ 40 * 3738557 * 2
def baseEnd_3738557 : Nat := 1279784463487356408162797

theorem tailTrace_3738557 : CollatzResearch.WordTrace tailWord_3738557 prefixEnd_3738557 1279784463487356408162797 := by
  unfold tailWord_3738557
  simp only [CollatzResearch.WordTrace]
  refine ⟨136356375916853958547549925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90904250611235972365033283 136356375916853958547549925)
  ·
    refine ⟨25566820484410117227665611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136356375916853958547549925 25566820484410117227665611)
    ·
      refine ⟨38350230726615175841498417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566820484410117227665611 38350230726615175841498417)
      ·
        refine ⟨28762673044961381881123813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38350230726615175841498417 28762673044961381881123813)
        ·
          refine ⟨5393001195930259102710715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28762673044961381881123813 5393001195930259102710715)
          ·
            refine ⟨8089501793895388654066073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393001195930259102710715 8089501793895388654066073)
            ·
              refine ⟨6067126345421541490549555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8089501793895388654066073 6067126345421541490549555)
              ·
                refine ⟨9100689518132312235824333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067126345421541490549555 9100689518132312235824333)
                ·
                  refine ⟨3412758569299617088434125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9100689518132312235824333 3412758569299617088434125)
                  ·
                    refine ⟨1279784463487356408162797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412758569299617088434125 1279784463487356408162797)
                    ·
                      rfl

theorem cell22_3738557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_3738557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738557 prefixEnd_3738557 := by exact prefixLift 3738557
  have htrace : WordTrace (prefixWord ++ tailWord_3738557) baseStart_3738557 baseEnd_3738557 := by
    simpa [prefixWord, tailWord_3738557, baseEnd_3738557] using wordTrace_append hprefix tailTrace_3738557
  have hstable : (prefixWord ++ tailWord_3738557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738557).length < 2 ^ (prefixWord ++ tailWord_3738557).sum := by decide
  have hdescent : baseEnd_3738557 < baseStart_3738557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738591 : List Nat := [1, 1, 2, 3, 6, 1, 1, 3, 1, 3]
def baseStart_3738591 : Nat := 118140960795 + 3738591 * 2 ^ 59
def prefixEnd_3738591 : Nat := 4983230072969 + 3 ^ 40 * 3738591 * 2
def baseEnd_3738591 : Nat := 1279796102382191652812693

theorem tailTrace_3738591 : CollatzResearch.WordTrace tailWord_3738591 prefixEnd_3738591 1279796102382191652812693 := by
  unfold tailWord_3738591
  simp only [CollatzResearch.WordTrace]
  refine ⟨136357615998730782354287627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90905077332487188236191751 136357615998730782354287627)
  ·
    refine ⟨204536423998096173531431441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136357615998730782354287627 204536423998096173531431441)
    ·
      refine ⟨153402317998572130148573581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204536423998096173531431441 153402317998572130148573581)
      ·
        refine ⟨57525869249464548805715093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153402317998572130148573581 57525869249464548805715093)
        ·
          refine ⟨2696525121068650725267895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57525869249464548805715093 2696525121068650725267895)
          ·
            refine ⟨4044787681602976087901843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696525121068650725267895 4044787681602976087901843)
            ·
              refine ⟨6067181522404464131852765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044787681602976087901843 6067181522404464131852765)
              ·
                refine ⟨2275193070901674049444787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6067181522404464131852765 2275193070901674049444787)
                ·
                  refine ⟨3412789606352511074167181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275193070901674049444787 3412789606352511074167181)
                  ·
                    refine ⟨1279796102382191652812693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412789606352511074167181 1279796102382191652812693)
                    ·
                      rfl

theorem cell22_3738591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_3738591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738591 prefixEnd_3738591 := by exact prefixLift 3738591
  have htrace : WordTrace (prefixWord ++ tailWord_3738591) baseStart_3738591 baseEnd_3738591 := by
    simpa [prefixWord, tailWord_3738591, baseEnd_3738591] using wordTrace_append hprefix tailTrace_3738591
  have hstable : (prefixWord ++ tailWord_3738591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738591).length < 2 ^ (prefixWord ++ tailWord_3738591).sum := by decide
  have hdescent : baseEnd_3738591 < baseStart_3738591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738600 : List Nat := [2, 1, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3738600 : Nat := 118140960795 + 3738600 * 2 ^ 59
def prefixEnd_3738600 : Nat := 4983230072969 + 3 ^ 40 * 3738600 * 2
def baseEnd_3738600 : Nat := 1279799183266118629337665

theorem tailTrace_3738600 : CollatzResearch.WordTrace tailWord_3738600 prefixEnd_3738600 1279799183266118629337665 := by
  unfold tailWord_3738600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68178972127849088445682627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90905296170465451260910169 68178972127849088445682627)
  ·
    refine ⟨102268458191773632668523941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68178972127849088445682627 102268458191773632668523941)
    ·
      refine ⟨19175335910957556125348239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102268458191773632668523941 19175335910957556125348239)
      ·
        refine ⟨28763003866436334188022359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19175335910957556125348239 28763003866436334188022359)
        ·
          refine ⟨43144505799654501282033539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763003866436334188022359 43144505799654501282033539)
          ·
            refine ⟨64716758699481751923050309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43144505799654501282033539 64716758699481751923050309)
            ·
              refine ⟨12134392256152828485571933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64716758699481751923050309 12134392256152828485571933)
              ·
                refine ⟨4550397096057310682089475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12134392256152828485571933 4550397096057310682089475)
                ·
                  refine ⟨6825595644085966023134213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4550397096057310682089475 6825595644085966023134213)
                  ·
                    refine ⟨1279799183266118629337665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825595644085966023134213 1279799183266118629337665)
                    ·
                      rfl

theorem cell22_3738600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3738600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738600 prefixEnd_3738600 := by exact prefixLift 3738600
  have htrace : WordTrace (prefixWord ++ tailWord_3738600) baseStart_3738600 baseEnd_3738600 := by
    simpa [prefixWord, tailWord_3738600, baseEnd_3738600] using wordTrace_append hprefix tailTrace_3738600
  have hstable : (prefixWord ++ tailWord_3738600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738600).length < 2 ^ (prefixWord ++ tailWord_3738600).sum := by decide
  have hdescent : baseEnd_3738600 < baseStart_3738600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738645 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3738645 : Nat := 118140960795 + 3738645 * 2 ^ 59
def prefixEnd_3738645 : Nat := 4983230072969 + 3 ^ 40 * 3738645 * 2
def baseEnd_3738645 : Nat := 1279814587685753511962527

theorem tailTrace_3738645 : CollatzResearch.WordTrace tailWord_3738645 prefixEnd_3738645 1279814587685753511962527 := by
  unfold tailWord_3738645
  simp only [CollatzResearch.WordTrace]
  refine ⟨136359585540535149576753389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90906390360356766384502259 136359585540535149576753389)
  ·
    refine ⟨51134844577700681091282521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136359585540535149576753389 51134844577700681091282521)
    ·
      refine ⟨38351133433275510818461891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51134844577700681091282521 38351133433275510818461891)
      ·
        refine ⟨57526700149913266227692837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38351133433275510818461891 57526700149913266227692837)
        ·
          refine ⟨10786256278108737417692407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57526700149913266227692837 10786256278108737417692407)
          ·
            refine ⟨16179384417163106126538611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10786256278108737417692407 16179384417163106126538611)
            ·
              refine ⟨24269076625744659189807917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16179384417163106126538611 24269076625744659189807917)
              ·
                refine ⟨9100903734654247196177969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24269076625744659189807917 9100903734654247196177969)
                ·
                  refine ⟨6825677800990685397133477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9100903734654247196177969 6825677800990685397133477)
                  ·
                    refine ⟨1279814587685753511962527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825677800990685397133477 1279814587685753511962527)
                    ·
                      rfl

theorem cell22_3738645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3738645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738645 prefixEnd_3738645 := by exact prefixLift 3738645
  have htrace : WordTrace (prefixWord ++ tailWord_3738645) baseStart_3738645 baseEnd_3738645 := by
    simpa [prefixWord, tailWord_3738645, baseEnd_3738645] using wordTrace_append hprefix tailTrace_3738645
  have hstable : (prefixWord ++ tailWord_3738645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738645).length < 2 ^ (prefixWord ++ tailWord_3738645).sum := by decide
  have hdescent : baseEnd_3738645 < baseStart_3738645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738666 : List Nat := [3, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_3738666 : Nat := 118140960795 + 3738666 * 2 ^ 59
def prefixEnd_3738666 : Nat := 4983230072969 + 3 ^ 40 * 3738666 * 2
def baseEnd_3738666 : Nat := 426607258804972152395821

theorem tailTrace_3738666 : CollatzResearch.WordTrace tailWord_3738666 prefixEnd_3738666 426607258804972152395821 := by
  unfold tailWord_3738666
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090087868364767540816963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90906900982306046775511901 34090087868364767540816963)
  ·
    refine ⟨51135131802547151311225445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34090087868364767540816963 51135131802547151311225445)
    ·
      refine ⟨9587837212977590870854771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51135131802547151311225445 9587837212977590870854771)
      ·
        refine ⟨14381755819466386306282157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587837212977590870854771 14381755819466386306282157)
        ·
          refine ⟨5393158432299894864855809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14381755819466386306282157 5393158432299894864855809)
          ·
            refine ⟨4044868824224921148641857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5393158432299894864855809 4044868824224921148641857)
            ·
              refine ⟨3033651618168690861481393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044868824224921148641857 3033651618168690861481393)
              ·
                refine ⟨2275238713626518146111045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033651618168690861481393 2275238713626518146111045)
                ·
                  refine ⟨426607258804972152395821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275238713626518146111045 426607258804972152395821)
                  ·
                    rfl

theorem cell22_3738666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_3738666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738666 prefixEnd_3738666 := by exact prefixLift 3738666
  have htrace : WordTrace (prefixWord ++ tailWord_3738666) baseStart_3738666 baseEnd_3738666 := by
    simpa [prefixWord, tailWord_3738666, baseEnd_3738666] using wordTrace_append hprefix tailTrace_3738666
  have hstable : (prefixWord ++ tailWord_3738666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738666).length < 2 ^ (prefixWord ++ tailWord_3738666).sum := by decide
  have hdescent : baseEnd_3738666 < baseStart_3738666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738673 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_3738673 : Nat := 118140960795 + 3738673 * 2 ^ 59
def prefixEnd_3738673 : Nat := 4983230072969 + 3 ^ 40 * 3738673 * 2
def baseEnd_3738673 : Nat := 1279824172657970772262441

theorem tailTrace_3738673 : CollatzResearch.WordTrace tailWord_3738673 prefixEnd_3738673 1279824172657970772262441 := by
  unfold tailWord_3738673
  simp only [CollatzResearch.WordTrace]
  refine ⟨136360606784433710358772673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907071189622473572515115 136360606784433710358772673)
  ·
    refine ⟨102270455088325282769079505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136360606784433710358772673 102270455088325282769079505)
    ·
      refine ⟨76702841316243962076809629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102270455088325282769079505 76702841316243962076809629)
      ·
        refine ⟨28763565493591485778803611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76702841316243962076809629 28763565493591485778803611)
        ·
          refine ⟨43145348240387228668205417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763565493591485778803611 43145348240387228668205417)
          ·
            refine ⟨32359011180290421501154063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43145348240387228668205417 32359011180290421501154063)
            ·
              refine ⟨48538516770435632251731095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32359011180290421501154063 48538516770435632251731095)
              ·
                refine ⟨72807775155653448377596643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48538516770435632251731095 72807775155653448377596643)
                ·
                  refine ⟨109211662733480172566394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72807775155653448377596643 109211662733480172566394965)
                  ·
                    refine ⟨1279824172657970772262441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109211662733480172566394965 1279824172657970772262441)
                    ·
                      rfl

theorem cell22_3738673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_3738673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738673 prefixEnd_3738673 := by exact prefixLift 3738673
  have htrace : WordTrace (prefixWord ++ tailWord_3738673) baseStart_3738673 baseEnd_3738673 := by
    simpa [prefixWord, tailWord_3738673, baseEnd_3738673] using wordTrace_append hprefix tailTrace_3738673
  have hstable : (prefixWord ++ tailWord_3738673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738673).length < 2 ^ (prefixWord ++ tailWord_3738673).sum := by decide
  have hdescent : baseEnd_3738673 < baseStart_3738673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738675 : List Nat := [1, 1, 1, 2, 4, 1, 1, 5, 3, 3]
def baseStart_3738675 : Nat := 118140960795 + 3738675 * 2 ^ 59
def prefixEnd_3738675 : Nat := 4983230072969 + 3 ^ 40 * 3738675 * 2
def baseEnd_3738675 : Nat := 1279824857298843433712435

theorem tailTrace_3738675 : CollatzResearch.WordTrace tailWord_3738675 prefixEnd_3738675 1279824857298843433712435 := by
  unfold tailWord_3738675
  simp only [CollatzResearch.WordTrace]
  refine ⟨136360679730426464700345479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907119820284309800230319 136360679730426464700345479)
  ·
    refine ⟨204541019595639697050518219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136360679730426464700345479 204541019595639697050518219)
    ·
      refine ⟨306811529393459545575777329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204541019595639697050518219 306811529393459545575777329)
      ·
        refine ⟨230108647045094659181832997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306811529393459545575777329 230108647045094659181832997)
        ·
          refine ⟨43145371320955248596593687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230108647045094659181832997 43145371320955248596593687)
          ·
            refine ⟨64718056981432872894890531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43145371320955248596593687 64718056981432872894890531)
            ·
              refine ⟨97077085472149309342335797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64718056981432872894890531 97077085472149309342335797)
              ·
                refine ⟨9100976763013997750843981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97077085472149309342335797 9100976763013997750843981)
                ·
                  refine ⟨3412866286130249156566493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9100976763013997750843981 3412866286130249156566493)
                  ·
                    refine ⟨1279824857298843433712435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412866286130249156566493 1279824857298843433712435)
                    ·
                      rfl

theorem cell22_3738675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 3].length) (baseStart_3738675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738675 prefixEnd_3738675 := by exact prefixLift 3738675
  have htrace : WordTrace (prefixWord ++ tailWord_3738675) baseStart_3738675 baseEnd_3738675 := by
    simpa [prefixWord, tailWord_3738675, baseEnd_3738675] using wordTrace_append hprefix tailTrace_3738675
  have hstable : (prefixWord ++ tailWord_3738675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738675).length < 2 ^ (prefixWord ++ tailWord_3738675).sum := by decide
  have hdescent : baseEnd_3738675 < baseStart_3738675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738694 : List Nat := [6, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3738694 : Nat := 118140960795 + 3738694 * 2 ^ 59
def prefixEnd_3738694 : Nat := 4983230072969 + 3 ^ 40 * 3738694 * 2
def baseEnd_3738694 : Nat := 142203484598570413054153

theorem tailTrace_3738694 : CollatzResearch.WordTrace tailWord_3738694 prefixEnd_3738694 142203484598570413054153 := by
  unfold tailWord_3738694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261292897417425967040223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90907581811571753963524757 4261292897417425967040223)
  ·
    refine ⟨6391939346126138950560335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261292897417425967040223 6391939346126138950560335)
    ·
      refine ⟨9587909019189208425840503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6391939346126138950560335 9587909019189208425840503)
      ·
        refine ⟨14381863528783812638760755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9587909019189208425840503 14381863528783812638760755)
        ·
          refine ⟨21572795293175718958141133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14381863528783812638760755 21572795293175718958141133)
          ·
            refine ⟨8089798234940894609302925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21572795293175718958141133 8089798234940894609302925)
            ·
              refine ⟨3033674338102835478488597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8089798234940894609302925 3033674338102835478488597)
              ·
                refine ⟨142203484598570413054153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3033674338102835478488597 142203484598570413054153)
                ·
                  rfl

theorem cell22_3738694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3738694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738694 prefixEnd_3738694 := by exact prefixLift 3738694
  have htrace : WordTrace (prefixWord ++ tailWord_3738694) baseStart_3738694 baseEnd_3738694 := by
    simpa [prefixWord, tailWord_3738694, baseEnd_3738694] using wordTrace_append hprefix tailTrace_3738694
  have hstable : (prefixWord ++ tailWord_3738694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738694).length < 2 ^ (prefixWord ++ tailWord_3738694).sum := by decide
  have hdescent : baseEnd_3738694 < baseStart_3738694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738703 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_3738703 : Nat := 118140960795 + 3738703 * 2 ^ 59
def prefixEnd_3738703 : Nat := 4983230072969 + 3 ^ 40 * 3738703 * 2
def baseEnd_3738703 : Nat := 1279834442271060694012349

theorem tailTrace_3738703 : CollatzResearch.WordTrace tailWord_3738703 prefixEnd_3738703 1279834442271060694012349 := by
  unfold tailWord_3738703
  simp only [CollatzResearch.WordTrace]
  refine ⟨136361700974325025482364763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907800649550016988243175 136361700974325025482364763)
  ·
    refine ⟨204542551461487538223547145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136361700974325025482364763 204542551461487538223547145)
    ·
      refine ⟨153406913596115653667660359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204542551461487538223547145 153406913596115653667660359)
      ·
        refine ⟨230110370394173480501490539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153406913596115653667660359 230110370394173480501490539)
        ·
          refine ⟨345165555591260220752235809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230110370394173480501490539 345165555591260220752235809)
          ·
            refine ⟨258874166693445165564176857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345165555591260220752235809 258874166693445165564176857)
            ·
              refine ⟨194155625020083874173132643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258874166693445165564176857 194155625020083874173132643)
              ·
                refine ⟨291233437530125811259698965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194155625020083874173132643 291233437530125811259698965)
                ·
                  refine ⟨13651567384224647402798389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 291233437530125811259698965 13651567384224647402798389)
                  ·
                    refine ⟨1279834442271060694012349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13651567384224647402798389 1279834442271060694012349)
                    ·
                      rfl

theorem cell22_3738703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_3738703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738703 prefixEnd_3738703 := by exact prefixLift 3738703
  have htrace : WordTrace (prefixWord ++ tailWord_3738703) baseStart_3738703 baseEnd_3738703 := by
    simpa [prefixWord, tailWord_3738703, baseEnd_3738703] using wordTrace_append hprefix tailTrace_3738703
  have hstable : (prefixWord ++ tailWord_3738703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738703).length < 2 ^ (prefixWord ++ tailWord_3738703).sum := by decide
  have hdescent : baseEnd_3738703 < baseStart_3738703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738709 : List Nat := [1, 3, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3738709 : Nat := 118140960795 + 3738709 * 2 ^ 59
def prefixEnd_3738709 : Nat := 4983230072969 + 3 ^ 40 * 3738709 * 2
def baseEnd_3738709 : Nat := 1279836496193678678362331

theorem tailTrace_3738709 : CollatzResearch.WordTrace tailWord_3738709 prefixEnd_3738709 1279836496193678678362331 := by
  unfold tailWord_3738709
  simp only [CollatzResearch.WordTrace]
  refine ⟨136361919812303288507083181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90907946541535525671388787 136361919812303288507083181)
  ·
    refine ⟨51135719929613733190156193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136361919812303288507083181 51135719929613733190156193)
    ·
      refine ⟨38351789947210299892617145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51135719929613733190156193 38351789947210299892617145)
      ·
        refine ⟨28763842460407724919462859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38351789947210299892617145 28763842460407724919462859)
        ·
          refine ⟨43145763690611587379194289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28763842460407724919462859 43145763690611587379194289)
          ·
            refine ⟨32359322767958690534395717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43145763690611587379194289 32359322767958690534395717)
            ·
              refine ⟨6067373018992254475199197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32359322767958690534395717 6067373018992254475199197)
              ·
                refine ⟨2275264882122095428199699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6067373018992254475199197 2275264882122095428199699)
                ·
                  refine ⟨3412897323183143142299549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275264882122095428199699 3412897323183143142299549)
                  ·
                    refine ⟨1279836496193678678362331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412897323183143142299549 1279836496193678678362331)
                    ·
                      rfl

theorem cell22_3738709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3738709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738709 prefixEnd_3738709 := by exact prefixLift 3738709
  have htrace : WordTrace (prefixWord ++ tailWord_3738709) baseStart_3738709 baseEnd_3738709 := by
    simpa [prefixWord, tailWord_3738709, baseEnd_3738709] using wordTrace_append hprefix tailTrace_3738709
  have hstable : (prefixWord ++ tailWord_3738709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738709).length < 2 ^ (prefixWord ++ tailWord_3738709).sum := by decide
  have hdescent : baseEnd_3738709 < baseStart_3738709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738722 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3738722 : Nat := 118140960795 + 3738722 * 2 ^ 59
def prefixEnd_3738722 : Nat := 4983230072969 + 3 ^ 40 * 3738722 * 2
def baseEnd_3738722 : Nat := 426613648786450325929097

theorem tailTrace_3738722 : CollatzResearch.WordTrace tailWord_3738722 prefixEnd_3738722 426613648786450325929097 := by
  unfold tailWord_3738722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090598490314047931826605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90908262640837461151537613 34090598490314047931826605)
  ·
    refine ⟨12783974433867767974434977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34090598490314047931826605 12783974433867767974434977)
    ·
      refine ⟨9587980825400825980826233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12783974433867767974434977 9587980825400825980826233)
      ·
        refine ⟨7190985619050619485619675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9587980825400825980826233 7190985619050619485619675)
        ·
          refine ⟨10786478428575929228429513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190985619050619485619675 10786478428575929228429513)
          ·
            refine ⟨8089858821431946921322135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786478428575929228429513 8089858821431946921322135)
            ·
              refine ⟨12134788232147920381983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8089858821431946921322135 12134788232147920381983203)
              ·
                refine ⟨18202182348221880572974805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12134788232147920381983203 18202182348221880572974805)
                ·
                  refine ⟨426613648786450325929097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18202182348221880572974805 426613648786450325929097)
                  ·
                    rfl

theorem cell22_3738722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3738722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738722 prefixEnd_3738722 := by exact prefixLift 3738722
  have htrace : WordTrace (prefixWord ++ tailWord_3738722) baseStart_3738722 baseEnd_3738722 := by
    simpa [prefixWord, tailWord_3738722, baseEnd_3738722] using wordTrace_append hprefix tailTrace_3738722
  have hstable : (prefixWord ++ tailWord_3738722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738722).length < 2 ^ (prefixWord ++ tailWord_3738722).sum := by decide
  have hdescent : baseEnd_3738722 < baseStart_3738722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738784 : List Nat := [2, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_3738784 : Nat := 118140960795 + 3738784 * 2 ^ 59
def prefixEnd_3738784 : Nat := 4983230072969 + 3 ^ 40 * 3738784 * 2
def baseEnd_3738784 : Nat := 426620723408801160912367

theorem tailTrace_3738784 : CollatzResearch.WordTrace tailWord_3738784 prefixEnd_3738784 426620723408801160912367 := by
  unfold tailWord_3738784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68182327643515788158031703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90909770191354384210708937 68182327643515788158031703)
  ·
    refine ⟨102273491465273682237047555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68182327643515788158031703 102273491465273682237047555)
    ·
      refine ⟨153410237197910523355571333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102273491465273682237047555 153410237197910523355571333)
      ·
        refine ⟨28764419474608223129169625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153410237197910523355571333 28764419474608223129169625)
        ·
          refine ⟨21573314605956167346877219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28764419474608223129169625 21573314605956167346877219)
          ·
            refine ⟨32359971908934251020315829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21573314605956167346877219 32359971908934251020315829)
            ·
              refine ⟨3033747366462586033154609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32359971908934251020315829 3033747366462586033154609)
              ·
                refine ⟨2275310524846939524865957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033747366462586033154609 2275310524846939524865957)
                ·
                  refine ⟨426620723408801160912367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275310524846939524865957 426620723408801160912367)
                  ·
                    rfl

theorem cell22_3738784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_3738784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738784 prefixEnd_3738784 := by exact prefixLift 3738784
  have htrace : WordTrace (prefixWord ++ tailWord_3738784) baseStart_3738784 baseEnd_3738784 := by
    simpa [prefixWord, tailWord_3738784, baseEnd_3738784] using wordTrace_append hprefix tailTrace_3738784
  have hstable : (prefixWord ++ tailWord_3738784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738784).length < 2 ^ (prefixWord ++ tailWord_3738784).sum := by decide
  have hdescent : baseEnd_3738784 < baseStart_3738784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738799 : List Nat := [1, 1, 2, 1, 2, 3, 6, 1, 2, 3]
def baseStart_3738799 : Nat := 118140960795 + 3738799 * 2 ^ 59
def prefixEnd_3738799 : Nat := 4983230072969 + 3 ^ 40 * 3738799 * 2
def baseEnd_3738799 : Nat := 1279867305032948443612055

theorem tailTrace_3738799 : CollatzResearch.WordTrace tailWord_3738799 prefixEnd_3738799 1279867305032948443612055 := by
  unfold tailWord_3738799
  simp only [CollatzResearch.WordTrace]
  refine ⟨136365202381977233877859451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90910134921318155918572967 136365202381977233877859451)
  ·
    refine ⟨204547803572965850816789177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136365202381977233877859451 204547803572965850816789177)
    ·
      refine ⟨153410852679724388112591883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204547803572965850816789177 153410852679724388112591883)
      ·
        refine ⟨230116279019586582168887825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153410852679724388112591883 230116279019586582168887825)
        ·
          refine ⟨172587209264689936626665869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230116279019586582168887825 172587209264689936626665869)
          ·
            refine ⟨64720203474258726234999701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172587209264689936626665869 64720203474258726234999701)
            ·
              refine ⟨3033759537855877792265611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64720203474258726234999701 3033759537855877792265611)
              ·
                refine ⟨4550639306783816688398417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033759537855877792265611 4550639306783816688398417)
                ·
                  refine ⟨3412979480087862516298813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4550639306783816688398417 3412979480087862516298813)
                  ·
                    refine ⟨1279867305032948443612055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3412979480087862516298813 1279867305032948443612055)
                    ·
                      rfl

theorem cell22_3738799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_3738799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738799 prefixEnd_3738799 := by exact prefixLift 3738799
  have htrace : WordTrace (prefixWord ++ tailWord_3738799) baseStart_3738799 baseEnd_3738799 := by
    simpa [prefixWord, tailWord_3738799, baseEnd_3738799] using wordTrace_append hprefix tailTrace_3738799
  have hstable : (prefixWord ++ tailWord_3738799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738799).length < 2 ^ (prefixWord ++ tailWord_3738799).sum := by decide
  have hdescent : baseEnd_3738799 < baseStart_3738799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738814 : List Nat := [4, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3738814 : Nat := 118140960795 + 3738814 * 2 ^ 59
def prefixEnd_3738814 : Nat := 4983230072969 + 3 ^ 40 * 3738814 * 2
def baseEnd_3738814 : Nat := 1279872439839493404487009

theorem tailTrace_3738814 : CollatzResearch.WordTrace tailWord_3738814 prefixEnd_3738814 1279872439839493404487009 := by
  unfold tailWord_3738814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17045718684615361429956937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90910499651281927626436997 17045718684615361429956937)
  ·
    refine ⟨12784289013461521072467703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17045718684615361429956937 12784289013461521072467703)
    ·
      refine ⟨19176433520192281608701555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12784289013461521072467703 19176433520192281608701555)
      ·
        refine ⟨28764650280288422413052333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19176433520192281608701555 28764650280288422413052333)
        ·
          refine ⟨10786743855108158404894625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28764650280288422413052333 10786743855108158404894625)
          ·
            refine ⟨8090057891331118803670969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10786743855108158404894625 8090057891331118803670969)
            ·
              refine ⟨6067543418498339102753227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090057891331118803670969 6067543418498339102753227)
              ·
                refine ⟨9101315127747508654129841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6067543418498339102753227 9101315127747508654129841)
                ·
                  refine ⟨6825986345810631490597381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9101315127747508654129841 6825986345810631490597381)
                  ·
                    refine ⟨1279872439839493404487009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6825986345810631490597381 1279872439839493404487009)
                    ·
                      rfl

theorem cell22_3738814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3738814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738814 prefixEnd_3738814 := by exact prefixLift 3738814
  have htrace : WordTrace (prefixWord ++ tailWord_3738814) baseStart_3738814 baseEnd_3738814 := by
    simpa [prefixWord, tailWord_3738814, baseEnd_3738814] using wordTrace_append hprefix tailTrace_3738814
  have hstable : (prefixWord ++ tailWord_3738814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738814).length < 2 ^ (prefixWord ++ tailWord_3738814).sum := by decide
  have hdescent : baseEnd_3738814 < baseStart_3738814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738829 : List Nat := [1, 6, 2, 2, 1, 10]
def baseStart_3738829 : Nat := 118140960795 + 3738829 * 2 ^ 59
def prefixEnd_3738829 : Nat := 4983230072969 + 3 ^ 40 * 3738829 * 2
def baseEnd_3738829 : Nat := 15800957711679485992123

theorem tailTrace_3738829 : CollatzResearch.WordTrace tailWord_3738829 prefixEnd_3738829 15800957711679485992123 := by
  unfold tailWord_3738829
  simp only [CollatzResearch.WordTrace]
  refine ⟨136366296571868549001451541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90910864381245699334301027 136366296571868549001451541)
  ·
    refine ⟨6392170151806338234443041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136366296571868549001451541 6392170151806338234443041)
    ·
      refine ⟨4794127613854753675832281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392170151806338234443041 4794127613854753675832281)
      ·
        refine ⟨3595595710391065256874211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4794127613854753675832281 3595595710391065256874211)
        ·
          refine ⟨5393393565586597885311317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595595710391065256874211 5393393565586597885311317)
          ·
            refine ⟨15800957711679485992123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5393393565586597885311317 15800957711679485992123)
            ·
              rfl

theorem cell22_3738829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 10].length) (baseStart_3738829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738829 prefixEnd_3738829 := by exact prefixLift 3738829
  have htrace : WordTrace (prefixWord ++ tailWord_3738829) baseStart_3738829 baseEnd_3738829 := by
    simpa [prefixWord, tailWord_3738829, baseEnd_3738829] using wordTrace_append hprefix tailTrace_3738829
  have hstable : (prefixWord ++ tailWord_3738829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738829).length < 2 ^ (prefixWord ++ tailWord_3738829).sum := by decide
  have hdescent : baseEnd_3738829 < baseStart_3738829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738878 : List Nat := [4, 2, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3738878 : Nat := 118140960795 + 3738878 * 2 ^ 59
def prefixEnd_3738878 : Nat := 4983230072969 + 3 ^ 40 * 3738878 * 2
def baseEnd_3738878 : Nat := 1279894348347418570886813

theorem tailTrace_3738878 : CollatzResearch.WordTrace tailWord_3738878 prefixEnd_3738878 1279894348347418570886813 := by
  unfold tailWord_3738878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046010468586378796248161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90912055832460686913323525 17046010468586378796248161)
  ·
    refine ⟨12784507851439784097186121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17046010468586378796248161 12784507851439784097186121)
    ·
      refine ⟨9588380888579838072889591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12784507851439784097186121 9588380888579838072889591)
      ·
        refine ⟨14382571332869757109334387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588380888579838072889591 14382571332869757109334387)
        ·
          refine ⟨21573856999304635664001581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382571332869757109334387 21573856999304635664001581)
          ·
            refine ⟨8090196374739238374000593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21573856999304635664001581 8090196374739238374000593)
            ·
              refine ⟨6067647281054428780500445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090196374739238374000593 6067647281054428780500445)
              ·
                refine ⟨2275367730395410792687667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6067647281054428780500445 2275367730395410792687667)
                ·
                  refine ⟨3413051595593116189031501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275367730395410792687667 3413051595593116189031501)
                  ·
                    refine ⟨1279894348347418570886813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413051595593116189031501 1279894348347418570886813)
                    ·
                      rfl

theorem cell22_3738878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3738878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738878 prefixEnd_3738878 := by exact prefixLift 3738878
  have htrace : WordTrace (prefixWord ++ tailWord_3738878) baseStart_3738878 baseEnd_3738878 := by
    simpa [prefixWord, tailWord_3738878, baseEnd_3738878] using wordTrace_append hprefix tailTrace_3738878
  have hstable : (prefixWord ++ tailWord_3738878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738878).length < 2 ^ (prefixWord ++ tailWord_3738878).sum := by decide
  have hdescent : baseEnd_3738878 < baseStart_3738878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3738885 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 8]
def baseStart_3738885 : Nat := 118140960795 + 3738885 * 2 ^ 59
def prefixEnd_3738885 : Nat := 4983230072969 + 3 ^ 40 * 3738885 * 2
def baseEnd_3738885 : Nat := 426632248196824295320597

theorem tailTrace_3738885 : CollatzResearch.WordTrace tailWord_3738885 prefixEnd_3738885 426632248196824295320597 := by
  unfold tailWord_3738885
  simp only [CollatzResearch.WordTrace]
  refine ⟨136368339059665670565490109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90912226039777113710326739 136368339059665670565490109)
  ·
    refine ⟨51138127147374626462058791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136368339059665670565490109 51138127147374626462058791)
    ·
      refine ⟨76707190721061939693088187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51138127147374626462058791 76707190721061939693088187)
      ·
        refine ⟨115060786081592909539632281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76707190721061939693088187 115060786081592909539632281)
        ·
          refine ⟨86295589561194682154724211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115060786081592909539632281 86295589561194682154724211)
          ·
            refine ⟨129443384341792023232086317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86295589561194682154724211 129443384341792023232086317)
            ·
              refine ⟨48541269128172008712032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129443384341792023232086317 48541269128172008712032369)
              ·
                refine ⟨36405951846129006534024277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48541269128172008712032369 36405951846129006534024277)
                ·
                  refine ⟨426632248196824295320597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36405951846129006534024277 426632248196824295320597)
                  ·
                    rfl

theorem cell22_3738885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_3738885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3738885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3738885 prefixEnd_3738885 := by exact prefixLift 3738885
  have htrace : WordTrace (prefixWord ++ tailWord_3738885) baseStart_3738885 baseEnd_3738885 := by
    simpa [prefixWord, tailWord_3738885, baseEnd_3738885] using wordTrace_append hprefix tailTrace_3738885
  have hstable : (prefixWord ++ tailWord_3738885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3738885).length < 2 ^ (prefixWord ++ tailWord_3738885).sum := by decide
  have hdescent : baseEnd_3738885 < baseStart_3738885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3738885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739013 : List Nat := [1, 3, 1, 1, 3, 1, 6, 2, 1, 3]
def baseStart_3739013 : Nat := 118140960795 + 3739013 * 2 ^ 59
def prefixEnd_3739013 : Nat := 4983230072969 + 3 ^ 40 * 3739013 * 2
def baseEnd_3739013 : Nat := 1279940561606323218761399

theorem tailTrace_3739013 : CollatzResearch.WordTrace tailWord_3739013 prefixEnd_3739013 1279940561606323218761399 := by
  unfold tailWord_3739013
  simp only [CollatzResearch.WordTrace]
  refine ⟨136373007603201948426149693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90915338402134632284099795 136373007603201948426149693)
  ·
    refine ⟨51139877851200730659806135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136373007603201948426149693 51139877851200730659806135)
    ·
      refine ⟨76709816776801095989709203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51139877851200730659806135 76709816776801095989709203)
      ·
        refine ⟨115064725165201643984563805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76709816776801095989709203 115064725165201643984563805)
        ·
          refine ⟨43149271936950616494211427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115064725165201643984563805 43149271936950616494211427)
          ·
            refine ⟨64723907905425924741317141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43149271936950616494211427 64723907905425924741317141)
            ·
              refine ⟨3033933183066840222249241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64723907905425924741317141 3033933183066840222249241)
              ·
                refine ⟨2275449887300130166686931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3033933183066840222249241 2275449887300130166686931)
                ·
                  refine ⟨3413174830950195250030397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275449887300130166686931 3413174830950195250030397)
                  ·
                    refine ⟨1279940561606323218761399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413174830950195250030397 1279940561606323218761399)
                    ·
                      rfl

theorem cell22_3739013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_3739013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739013 prefixEnd_3739013 := by exact prefixLift 3739013
  have htrace : WordTrace (prefixWord ++ tailWord_3739013) baseStart_3739013 baseEnd_3739013 := by
    simpa [prefixWord, tailWord_3739013, baseEnd_3739013] using wordTrace_append hprefix tailTrace_3739013
  have hstable : (prefixWord ++ tailWord_3739013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739013).length < 2 ^ (prefixWord ++ tailWord_3739013).sum := by decide
  have hdescent : baseEnd_3739013 < baseStart_3739013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739039 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_3739039 : Nat := 118140960795 + 3739039 * 2 ^ 59
def prefixEnd_3739039 : Nat := 4983230072969 + 3 ^ 40 * 3739039 * 2
def baseEnd_3739039 : Nat := 1279949461937667817611319

theorem tailTrace_3739039 : CollatzResearch.WordTrace tailWord_3739039 prefixEnd_3739039 1279949461937667817611319 := by
  unfold tailWord_3739039
  simp only [CollatzResearch.WordTrace]
  refine ⟨136373955901107754866596171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90915970600738503244397447 136373955901107754866596171)
  ·
    refine ⟨204560933851661632299894257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136373955901107754866596171 204560933851661632299894257)
    ·
      refine ⟨153420700388746224224920693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204560933851661632299894257 153420700388746224224920693)
      ·
        refine ⟨14383190661444958521086315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153420700388746224224920693 14383190661444958521086315)
        ·
          refine ⟨21574785992167437781629473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14383190661444958521086315 21574785992167437781629473)
          ·
            refine ⟨16181089494125578336222105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21574785992167437781629473 16181089494125578336222105)
            ·
              refine ⟨12135817120594183752166579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16181089494125578336222105 12135817120594183752166579)
              ·
                refine ⟨18203725680891275628249869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12135817120594183752166579 18203725680891275628249869)
                ·
                  refine ⟨6826397130334228360593701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18203725680891275628249869 6826397130334228360593701)
                  ·
                    refine ⟨1279949461937667817611319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6826397130334228360593701 1279949461937667817611319)
                    ·
                      rfl

theorem cell22_3739039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_3739039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739039 prefixEnd_3739039 := by exact prefixLift 3739039
  have htrace : WordTrace (prefixWord ++ tailWord_3739039) baseStart_3739039 baseEnd_3739039 := by
    simpa [prefixWord, tailWord_3739039, baseEnd_3739039] using wordTrace_append hprefix tailTrace_3739039
  have hstable : (prefixWord ++ tailWord_3739039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739039).length < 2 ^ (prefixWord ++ tailWord_3739039).sum := by decide
  have hdescent : baseEnd_3739039 < baseStart_3739039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739084 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_3739084 : Nat := 118140960795 + 3739084 * 2 ^ 59
def prefixEnd_3739084 : Nat := 4983230072969 + 3 ^ 40 * 3739084 * 2
def baseEnd_3739084 : Nat := 1279964866357302700236181

theorem tailTrace_3739084 : CollatzResearch.WordTrace tailWord_3739084 prefixEnd_3739084 1279964866357302700236181 := by
  unfold tailWord_3739084
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187798592972363775992153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90917064790629818367989537 68187798592972363775992153)
  ·
    refine ⟨51140848944729272831994115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68187798592972363775992153 51140848944729272831994115)
    ·
      refine ⟨76711273417093909247991173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51140848944729272831994115 76711273417093909247991173)
      ·
        refine ⟨14383363765705107983998345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76711273417093909247991173 14383363765705107983998345)
        ·
          refine ⟨10787522824278830987998759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14383363765705107983998345 10787522824278830987998759)
          ·
            refine ⟨16181284236418246481998139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787522824278830987998759 16181284236418246481998139)
            ·
              refine ⟨24271926354627369722997209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16181284236418246481998139 24271926354627369722997209)
              ·
                refine ⟨18203944765970527292247907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24271926354627369722997209 18203944765970527292247907)
                ·
                  refine ⟨27305917148955790938371861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18203944765970527292247907 27305917148955790938371861)
                  ·
                    refine ⟨1279964866357302700236181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27305917148955790938371861 1279964866357302700236181)
                    ·
                      rfl

theorem cell22_3739084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_3739084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739084 prefixEnd_3739084 := by exact prefixLift 3739084
  have htrace : WordTrace (prefixWord ++ tailWord_3739084) baseStart_3739084 baseEnd_3739084 := by
    simpa [prefixWord, tailWord_3739084, baseEnd_3739084] using wordTrace_append hprefix tailTrace_3739084
  have hstable : (prefixWord ++ tailWord_3739084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739084).length < 2 ^ (prefixWord ++ tailWord_3739084).sum := by decide
  have hdescent : baseEnd_3739084 < baseStart_3739084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739086 : List Nat := [4, 1, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_3739086 : Nat := 118140960795 + 3739086 * 2 ^ 59
def prefixEnd_3739086 : Nat := 4983230072969 + 3 ^ 40 * 3739086 * 2
def baseEnd_3739086 : Nat := 1279965550998175361686175

theorem tailTrace_3739086 : CollatzResearch.WordTrace tailWord_3739086 prefixEnd_3739086 1279965550998175361686175 := by
  unfold tailWord_3739086
  simp only [CollatzResearch.WordTrace]
  refine ⟨17046958766492185236694639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90917113421291654595704741 17046958766492185236694639)
  ·
    refine ⟨25570438149738277855041959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17046958766492185236694639 25570438149738277855041959)
    ·
      refine ⟨38355657224607416782562939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25570438149738277855041959 38355657224607416782562939)
      ·
        refine ⟨57533485836911125173844409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38355657224607416782562939 57533485836911125173844409)
        ·
          refine ⟨43150114377683343880383307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57533485836911125173844409 43150114377683343880383307)
          ·
            refine ⟨64725171566525015820574961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43150114377683343880383307 64725171566525015820574961)
            ·
              refine ⟨48543878674893761865431221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64725171566525015820574961 48543878674893761865431221)
              ·
                refine ⟨4550988625771290174884177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48543878674893761865431221 4550988625771290174884177)
                ·
                  refine ⟨3413241469328467631163133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4550988625771290174884177 3413241469328467631163133)
                  ·
                    refine ⟨1279965550998175361686175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413241469328467631163133 1279965550998175361686175)
                    ·
                      rfl

theorem cell22_3739086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_3739086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739086 prefixEnd_3739086 := by exact prefixLift 3739086
  have htrace : WordTrace (prefixWord ++ tailWord_3739086) baseStart_3739086 baseEnd_3739086 := by
    simpa [prefixWord, tailWord_3739086, baseEnd_3739086] using wordTrace_append hprefix tailTrace_3739086
  have hstable : (prefixWord ++ tailWord_3739086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739086).length < 2 ^ (prefixWord ++ tailWord_3739086).sum := by decide
  have hdescent : baseEnd_3739086 < baseStart_3739086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739137 : List Nat := [1, 2, 4, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3739137 : Nat := 118140960795 + 3739137 * 2 ^ 59
def prefixEnd_3739137 : Nat := 4983230072969 + 3 ^ 40 * 3739137 * 2
def baseEnd_3739137 : Nat := 1279983009340428228661019

theorem tailTrace_3739137 : CollatzResearch.WordTrace tailWord_3739137 prefixEnd_3739137 1279983009340428228661019 := by
  unfold tailWord_3739137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136377530254752717603663665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90918353503168478402442443 136377530254752717603663665)
  ·
    refine ⟨102283147691064538202747749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136377530254752717603663665 102283147691064538202747749)
    ·
      refine ⟨19178090192074600913015203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102283147691064538202747749 19178090192074600913015203)
      ·
        refine ⟨28767135288111901369522805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19178090192074600913015203 28767135288111901369522805)
        ·
          refine ⟨2696918933260490753392763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28767135288111901369522805 2696918933260490753392763)
          ·
            refine ⟨4045378399890736130089145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696918933260490753392763 4045378399890736130089145)
            ·
              refine ⟨3034033799918052097566859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045378399890736130089145 3034033799918052097566859)
              ·
                refine ⟨4551050699877078146350289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034033799918052097566859 4551050699877078146350289)
                ·
                  refine ⟨3413288024907808609762717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551050699877078146350289 3413288024907808609762717)
                  ·
                    refine ⟨1279983009340428228661019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413288024907808609762717 1279983009340428228661019)
                    ·
                      rfl

theorem cell22_3739137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3739137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739137 prefixEnd_3739137 := by exact prefixLift 3739137
  have htrace : WordTrace (prefixWord ++ tailWord_3739137) baseStart_3739137 baseEnd_3739137 := by
    simpa [prefixWord, tailWord_3739137, baseEnd_3739137] using wordTrace_append hprefix tailTrace_3739137
  have hstable : (prefixWord ++ tailWord_3739137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739137).length < 2 ^ (prefixWord ++ tailWord_3739137).sum := by decide
  have hdescent : baseEnd_3739137 < baseStart_3739137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739182 : List Nat := [4, 1, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3739182 : Nat := 118140960795 + 3739182 * 2 ^ 59
def prefixEnd_3739182 : Nat := 4983230072969 + 3 ^ 40 * 3739182 * 2
def baseEnd_3739182 : Nat := 1279998413760063111285881

theorem tailTrace_3739182 : CollatzResearch.WordTrace tailWord_3739182 prefixEnd_3739182 1279998413760063111285881 := by
  unfold tailWord_3739182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17047396442448711286131475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90919447693059793526034533 17047396442448711286131475)
  ·
    refine ⟨25571094663673066929197213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17047396442448711286131475 25571094663673066929197213)
    ·
      refine ⟨9589160498877400098448955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25571094663673066929197213 9589160498877400098448955)
      ·
        refine ⟨14383740748316100147673433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9589160498877400098448955 14383740748316100147673433)
        ·
          refine ⟨10787805561237075110755075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14383740748316100147673433 10787805561237075110755075)
          ·
            refine ⟨16181708341855612666132613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787805561237075110755075 16181708341855612666132613)
            ·
              refine ⟨3034070314097927374899865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16181708341855612666132613 3034070314097927374899865)
              ·
                refine ⟨2275552735573445531174899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034070314097927374899865 2275552735573445531174899)
                ·
                  refine ⟨3413329103360168296762349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275552735573445531174899 3413329103360168296762349)
                  ·
                    refine ⟨1279998413760063111285881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413329103360168296762349 1279998413760063111285881)
                    ·
                      rfl

theorem cell22_3739182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3739182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739182 prefixEnd_3739182 := by exact prefixLift 3739182
  have htrace : WordTrace (prefixWord ++ tailWord_3739182) baseStart_3739182 baseEnd_3739182 := by
    simpa [prefixWord, tailWord_3739182, baseEnd_3739182] using wordTrace_append hprefix tailTrace_3739182
  have hstable : (prefixWord ++ tailWord_3739182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739182).length < 2 ^ (prefixWord ++ tailWord_3739182).sum := by decide
  have hdescent : baseEnd_3739182 < baseStart_3739182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739219 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_3739219 : Nat := 118140960795 + 3739219 * 2 ^ 59
def prefixEnd_3739219 : Nat := 4983230072969 + 3 ^ 40 * 3739219 * 2
def baseEnd_3739219 : Nat := 1280011079616207348110767

theorem tailTrace_3739219 : CollatzResearch.WordTrace tailWord_3739219 prefixEnd_3739219 1280011079616207348110767 := by
  unfold tailWord_3739219
  simp only [CollatzResearch.WordTrace]
  refine ⟨136380521040455645608148711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90920347360303763738765807 136380521040455645608148711)
  ·
    refine ⟨204570781560683468412223067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136380521040455645608148711 204570781560683468412223067)
    ·
      refine ⟨306856172341025202618334601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204570781560683468412223067 306856172341025202618334601)
      ·
        refine ⟨230142129255768901963750951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306856172341025202618334601 230142129255768901963750951)
        ·
          refine ⟨345213193883653352945626427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230142129255768901963750951 345213193883653352945626427)
          ·
            refine ⟨517819790825480029418439641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345213193883653352945626427 517819790825480029418439641)
            ·
              refine ⟨388364843119110022063829731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517819790825480029418439641 388364843119110022063829731)
              ·
                refine ⟨582547264678665033095744597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388364843119110022063829731 582547264678665033095744597)
                ·
                  refine ⟨6826725757953105856590757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 582547264678665033095744597 6826725757953105856590757)
                  ·
                    refine ⟨1280011079616207348110767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6826725757953105856590757 1280011079616207348110767)
                    ·
                      rfl

theorem cell22_3739219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_3739219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739219 prefixEnd_3739219 := by exact prefixLift 3739219
  have htrace : WordTrace (prefixWord ++ tailWord_3739219) baseStart_3739219 baseEnd_3739219 := by
    simpa [prefixWord, tailWord_3739219, baseEnd_3739219] using wordTrace_append hprefix tailTrace_3739219
  have hstable : (prefixWord ++ tailWord_3739219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739219).length < 2 ^ (prefixWord ++ tailWord_3739219).sum := by decide
  have hdescent : baseEnd_3739219 < baseStart_3739219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739221 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3739221 : Nat := 118140960795 + 3739221 * 2 ^ 59
def prefixEnd_3739221 : Nat := 4983230072969 + 3 ^ 40 * 3739221 * 2
def baseEnd_3739221 : Nat := 1280011764257080009560761

theorem tailTrace_3739221 : CollatzResearch.WordTrace tailWord_3739221 prefixEnd_3739221 1280011764257080009560761 := by
  unfold tailWord_3739221
  simp only [CollatzResearch.WordTrace]
  refine ⟨136380593986448399949721517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90920395990965599966481011 136380593986448399949721517)
  ·
    refine ⟨51142722744918149981145569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136380593986448399949721517 51142722744918149981145569)
    ·
      refine ⟨38357042058688612485859177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51142722744918149981145569 38357042058688612485859177)
      ·
        refine ⟨28767781544016459364394383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38357042058688612485859177 28767781544016459364394383)
        ·
          refine ⟨43151672316024689046591575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28767781544016459364394383 43151672316024689046591575)
          ·
            refine ⟨64727508474037033569887363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43151672316024689046591575 64727508474037033569887363)
            ·
              refine ⟨97091262711055550354831045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64727508474037033569887363 97091262711055550354831045)
              ·
                refine ⟨18204611758322915691530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97091262711055550354831045 18204611758322915691530821)
                ·
                  refine ⟨3413364704685546692162029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18204611758322915691530821 3413364704685546692162029)
                  ·
                    refine ⟨1280011764257080009560761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413364704685546692162029 1280011764257080009560761)
                    ·
                      rfl

theorem cell22_3739221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3739221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739221 prefixEnd_3739221 := by exact prefixLift 3739221
  have htrace : WordTrace (prefixWord ++ tailWord_3739221) baseStart_3739221 baseEnd_3739221 := by
    simpa [prefixWord, tailWord_3739221, baseEnd_3739221] using wordTrace_append hprefix tailTrace_3739221
  have hstable : (prefixWord ++ tailWord_3739221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739221).length < 2 ^ (prefixWord ++ tailWord_3739221).sum := by decide
  have hdescent : baseEnd_3739221 < baseStart_3739221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739223 : List Nat := [1, 1, 3, 2, 2, 4, 2, 3, 4]
def baseStart_3739223 : Nat := 118140960795 + 3739223 * 2 ^ 59
def prefixEnd_3739223 : Nat := 4983230072969 + 3 ^ 40 * 3739223 * 2
def baseEnd_3739223 : Nat := 426670816299317557003585

theorem tailTrace_3739223 : CollatzResearch.WordTrace tailWord_3739223 prefixEnd_3739223 426670816299317557003585 := by
  unfold tailWord_3739223
  simp only [CollatzResearch.WordTrace]
  refine ⟨136380666932441154291294323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90920444621627436194196215 136380666932441154291294323)
  ·
    refine ⟨204571000398661731436941485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136380666932441154291294323 204571000398661731436941485)
    ·
      refine ⟨76714125149498149288853057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204571000398661731436941485 76714125149498149288853057)
      ·
        refine ⟨57535593862123611966639793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76714125149498149288853057 57535593862123611966639793)
        ·
          refine ⟨43151695396592708974979845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57535593862123611966639793 43151695396592708974979845)
          ·
            refine ⟨8090942886861132932808721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43151695396592708974979845 8090942886861132932808721)
            ·
              refine ⟨6068207165145849699606541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090942886861132932808721 6068207165145849699606541)
              ·
                refine ⟨2275577686929693637352453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6068207165145849699606541 2275577686929693637352453)
                ·
                  refine ⟨426670816299317557003585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275577686929693637352453 426670816299317557003585)
                  ·
                    rfl

theorem cell22_3739223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3, 4].length) (baseStart_3739223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739223 prefixEnd_3739223 := by exact prefixLift 3739223
  have htrace : WordTrace (prefixWord ++ tailWord_3739223) baseStart_3739223 baseEnd_3739223 := by
    simpa [prefixWord, tailWord_3739223, baseEnd_3739223] using wordTrace_append hprefix tailTrace_3739223
  have hstable : (prefixWord ++ tailWord_3739223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739223).length < 2 ^ (prefixWord ++ tailWord_3739223).sum := by decide
  have hdescent : baseEnd_3739223 < baseStart_3739223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739296 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 7]
def baseStart_3739296 : Nat := 118140960795 + 3739296 * 2 ^ 59
def prefixEnd_3739296 : Nat := 4983230072969 + 3 ^ 40 * 3739296 * 2
def baseEnd_3739296 : Nat := 426679146096601604645177

theorem tailTrace_3739296 : CollatzResearch.WordTrace tailWord_3739296 prefixEnd_3739296 426679146096601604645177 := by
  unfold tailWord_3739296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191664730588343879350871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90922219640784458505801161 68191664730588343879350871)
  ·
    refine ⟨102287497095882515819026307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68191664730588343879350871 102287497095882515819026307)
    ·
      refine ⟨153431245643823773728539461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102287497095882515819026307 153431245643823773728539461)
      ·
        refine ⟨28768358558216957574101149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153431245643823773728539461 28768358558216957574101149)
        ·
          refine ⟨10788134459331359090287931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28768358558216957574101149 10788134459331359090287931)
          ·
            refine ⟨16182201688997038635431897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10788134459331359090287931 16182201688997038635431897)
            ·
              refine ⟨12136651266747778976573923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16182201688997038635431897 12136651266747778976573923)
              ·
                refine ⟨18204976900121668464860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12136651266747778976573923 18204976900121668464860885)
                ·
                  refine ⟨426679146096601604645177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18204976900121668464860885 426679146096601604645177)
                  ·
                    rfl

theorem cell22_3739296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_3739296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739296 prefixEnd_3739296 := by exact prefixLift 3739296
  have htrace : WordTrace (prefixWord ++ tailWord_3739296) baseStart_3739296 baseEnd_3739296 := by
    simpa [prefixWord, tailWord_3739296, baseEnd_3739296] using wordTrace_append hprefix tailTrace_3739296
  have hstable : (prefixWord ++ tailWord_3739296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739296).length < 2 ^ (prefixWord ++ tailWord_3739296).sum := by decide
  have hdescent : baseEnd_3739296 < baseStart_3739296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739300 : List Nat := [2, 3, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_3739300 : Nat := 118140960795 + 3739300 * 2 ^ 59
def prefixEnd_3739300 : Nat := 4983230072969 + 3 ^ 40 * 3739300 * 2
def baseEnd_3739300 : Nat := 1280038807571550136835519

theorem tailTrace_3739300 : CollatzResearch.WordTrace tailWord_3739300 prefixEnd_3739300 1280038807571550136835519 := by
  unfold tailWord_3739300
  simp only [CollatzResearch.WordTrace]
  refine ⟨68191737676581098220923677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90922316902108130961231569 68191737676581098220923677)
  ·
    refine ⟨25571901628717911832846379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68191737676581098220923677 25571901628717911832846379)
    ·
      refine ⟨38357852443076867749269569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25571901628717911832846379 38357852443076867749269569)
      ·
        refine ⟨28768389332307650811952177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38357852443076867749269569 28768389332307650811952177)
        ·
          refine ⟨21576291999230738108964133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28768389332307650811952177 21576291999230738108964133)
          ·
            refine ⟨4045554749855763395430775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21576291999230738108964133 4045554749855763395430775)
            ·
              refine ⟨6068332124783645093146163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045554749855763395430775 6068332124783645093146163)
              ·
                refine ⟨9102498187175467639719245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068332124783645093146163 9102498187175467639719245)
                ·
                  refine ⟨3413436820190800364894717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9102498187175467639719245 3413436820190800364894717)
                  ·
                    refine ⟨1280038807571550136835519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413436820190800364894717 1280038807571550136835519)
                    ·
                      rfl

theorem cell22_3739300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_3739300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739300 prefixEnd_3739300 := by exact prefixLift 3739300
  have htrace : WordTrace (prefixWord ++ tailWord_3739300) baseStart_3739300 baseEnd_3739300 := by
    simpa [prefixWord, tailWord_3739300, baseEnd_3739300] using wordTrace_append hprefix tailTrace_3739300
  have hstable : (prefixWord ++ tailWord_3739300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739300).length < 2 ^ (prefixWord ++ tailWord_3739300).sum := by decide
  have hdescent : baseEnd_3739300 < baseStart_3739300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739371 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 4, 4]
def baseStart_3739371 : Nat := 118140960795 + 3739371 * 2 ^ 59
def prefixEnd_3739371 : Nat := 4983230072969 + 3 ^ 40 * 3739371 * 2
def baseEnd_3739371 : Nat := 1280063112322529618310301

theorem tailTrace_3739371 : CollatzResearch.WordTrace tailWord_3739371 prefixEnd_3739371 1280063112322529618310301 := by
  unfold tailWord_3739371
  simp only [CollatzResearch.WordTrace]
  refine ⟨136386064935904975567681967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90924043290603317045121311 136386064935904975567681967)
  ·
    refine ⟨204579097403857463351522951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136386064935904975567681967 204579097403857463351522951)
    ·
      refine ⟨306868646105786195027284427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204579097403857463351522951 306868646105786195027284427)
      ·
        refine ⟨460302969158679292540926641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306868646105786195027284427 460302969158679292540926641)
        ·
          refine ⟨345227226869009469405694981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460302969158679292540926641 345227226869009469405694981)
          ·
            refine ⟨64730105037939275513567809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345227226869009469405694981 64730105037939275513567809)
            ·
              refine ⟨48547578778454456635175857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64730105037939275513567809 48547578778454456635175857)
              ·
                refine ⟨36410684083840842476381893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48547578778454456635175857 36410684083840842476381893)
                ·
                  refine ⟨6827003265720157964321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36410684083840842476381893 6827003265720157964321605)
                  ·
                    refine ⟨1280063112322529618310301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827003265720157964321605 1280063112322529618310301)
                    ·
                      rfl

theorem cell22_3739371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 4].length) (baseStart_3739371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739371 prefixEnd_3739371 := by exact prefixLift 3739371
  have htrace : WordTrace (prefixWord ++ tailWord_3739371) baseStart_3739371 baseEnd_3739371 := by
    simpa [prefixWord, tailWord_3739371, baseEnd_3739371] using wordTrace_append hprefix tailTrace_3739371
  have hstable : (prefixWord ++ tailWord_3739371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739371).length < 2 ^ (prefixWord ++ tailWord_3739371).sum := by decide
  have hdescent : baseEnd_3739371 < baseStart_3739371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739373 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3739373 : Nat := 118140960795 + 3739373 * 2 ^ 59
def prefixEnd_3739373 : Nat := 4983230072969 + 3 ^ 40 * 3739373 * 2
def baseEnd_3739373 : Nat := 1280063796963402279760295

theorem tailTrace_3739373 : CollatzResearch.WordTrace tailWord_3739373 prefixEnd_3739373 1280063796963402279760295 := by
  unfold tailWord_3739373
  simp only [CollatzResearch.WordTrace]
  refine ⟨136386137881897729909254773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90924091921265153272836515 136386137881897729909254773)
  ·
    refine ⟨12786200426427912178992635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136386137881897729909254773 12786200426427912178992635)
    ·
      refine ⟨19179300639641868268488953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786200426427912178992635 19179300639641868268488953)
      ·
        refine ⟨14384475479731401201366715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19179300639641868268488953 14384475479731401201366715)
        ·
          refine ⟨21576713219597101802050073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14384475479731401201366715 21576713219597101802050073)
          ·
            refine ⟨16182534914697826351537555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21576713219597101802050073 16182534914697826351537555)
            ·
              refine ⟨24273802372046739527306333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16182534914697826351537555 24273802372046739527306333)
              ·
                refine ⟨9102675889517527322739875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24273802372046739527306333 9102675889517527322739875)
                ·
                  refine ⟨13654013834276290984109813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9102675889517527322739875 13654013834276290984109813)
                  ·
                    refine ⟨1280063796963402279760295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13654013834276290984109813 1280063796963402279760295)
                    ·
                      rfl

theorem cell22_3739373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3739373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739373 prefixEnd_3739373 := by exact prefixLift 3739373
  have htrace : WordTrace (prefixWord ++ tailWord_3739373) baseStart_3739373 baseEnd_3739373 := by
    simpa [prefixWord, tailWord_3739373, baseEnd_3739373] using wordTrace_append hprefix tailTrace_3739373
  have hstable : (prefixWord ++ tailWord_3739373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739373).length < 2 ^ (prefixWord ++ tailWord_3739373).sum := by decide
  have hdescent : baseEnd_3739373 < baseStart_3739373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739398 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3739398 : Nat := 118140960795 + 3739398 * 2 ^ 59
def prefixEnd_3739398 : Nat := 4983230072969 + 3 ^ 40 * 3739398 * 2
def baseEnd_3739398 : Nat := 426690784991436849295073

theorem tailTrace_3739398 : CollatzResearch.WordTrace tailWord_3739398 prefixEnd_3739398 426690784991436849295073 := by
  unfold tailWord_3739398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262095303337723724341089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 90924699804538106119276565 4262095303337723724341089)
  ·
    refine ⟨3196571477503292793255817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4262095303337723724341089 3196571477503292793255817)
    ·
      refine ⟨2397428608127469594941863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196571477503292793255817 2397428608127469594941863)
      ·
        refine ⟨3596142912191204392412795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397428608127469594941863 3596142912191204392412795)
        ·
          refine ⟨5394214368286806588619193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596142912191204392412795 5394214368286806588619193)
          ·
            refine ⟨4045660776215104941464395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5394214368286806588619193 4045660776215104941464395)
            ·
              refine ⟨6068491164322657412196593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045660776215104941464395 6068491164322657412196593)
              ·
                refine ⟨4551368373241993059147445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6068491164322657412196593 4551368373241993059147445)
                ·
                  refine ⟨426690784991436849295073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4551368373241993059147445 426690784991436849295073)
                  ·
                    rfl

theorem cell22_3739398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3739398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739398 prefixEnd_3739398 := by exact prefixLift 3739398
  have htrace : WordTrace (prefixWord ++ tailWord_3739398) baseStart_3739398 baseEnd_3739398 := by
    simpa [prefixWord, tailWord_3739398, baseEnd_3739398] using wordTrace_append hprefix tailTrace_3739398
  have hstable : (prefixWord ++ tailWord_3739398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739398).length < 2 ^ (prefixWord ++ tailWord_3739398).sum := by decide
  have hdescent : baseEnd_3739398 < baseStart_3739398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739416 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3739416 : Nat := 118140960795 + 3739416 * 2 ^ 59
def prefixEnd_3739416 : Nat := 4983230072969 + 3 ^ 40 * 3739416 * 2
def baseEnd_3739416 : Nat := 1280078516742164500935163

theorem tailTrace_3739416 : CollatzResearch.WordTrace tailWord_3739416 prefixEnd_3739416 1280078516742164500935163 := by
  unfold tailWord_3739416
  simp only [CollatzResearch.WordTrace]
  refine ⟨68193853110370974126535051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90925137480494632168713401 68193853110370974126535051)
  ·
    refine ⟨102290779665556461189802577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68193853110370974126535051 102290779665556461189802577)
    ·
      refine ⟨76718084749167345892351933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102290779665556461189802577 76718084749167345892351933)
      ·
        refine ⟨28769281780937754709631975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76718084749167345892351933 28769281780937754709631975)
        ·
          refine ⟨43153922671406632064447963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28769281780937754709631975 43153922671406632064447963)
          ·
            refine ⟨64730884007109948096671945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43153922671406632064447963 64730884007109948096671945)
            ·
              refine ⟨48548163005332461072503959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64730884007109948096671945 48548163005332461072503959)
              ·
                refine ⟨72822244507998691608755939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48548163005332461072503959 72822244507998691608755939)
                ·
                  refine ⟨109233366761998037413133909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72822244507998691608755939 109233366761998037413133909)
                  ·
                    refine ⟨1280078516742164500935163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109233366761998037413133909 1280078516742164500935163)
                    ·
                      rfl

theorem cell22_3739416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3739416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739416 prefixEnd_3739416 := by exact prefixLift 3739416
  have htrace : WordTrace (prefixWord ++ tailWord_3739416) baseStart_3739416 baseEnd_3739416 := by
    simpa [prefixWord, tailWord_3739416, baseEnd_3739416] using wordTrace_append hprefix tailTrace_3739416
  have hstable : (prefixWord ++ tailWord_3739416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739416).length < 2 ^ (prefixWord ++ tailWord_3739416).sum := by decide
  have hdescent : baseEnd_3739416 < baseStart_3739416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739452 : List Nat := [2, 2, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_3739452 : Nat := 118140960795 + 3739452 * 2 ^ 59
def prefixEnd_3739452 : Nat := 4983230072969 + 3 ^ 40 * 3739452 * 2
def baseEnd_3739452 : Nat := 1280090840277872407035053

theorem tailTrace_3739452 : CollatzResearch.WordTrace tailWord_3739452 prefixEnd_3739452 1280090840277872407035053 := by
  unfold tailWord_3739452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68194509624305763200690305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90926012832407684267587073 68194509624305763200690305)
  ·
    refine ⟨51145882218229322400517729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68194509624305763200690305 51145882218229322400517729)
    ·
      refine ⟨38359411663671991800388297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51145882218229322400517729 38359411663671991800388297)
      ·
        refine ⟨28769558747753993850291223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38359411663671991800388297 28769558747753993850291223)
        ·
          refine ⟨43154338121630990775436835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28769558747753993850291223 43154338121630990775436835)
          ·
            refine ⟨64731507182446486163155253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43154338121630990775436835 64731507182446486163155253)
            ·
              refine ⟨6068578798354358077795805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64731507182446486163155253 6068578798354358077795805)
              ·
                refine ⟨2275717049382884279173427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6068578798354358077795805 2275717049382884279173427)
                ·
                  refine ⟨3413575574074326418760141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275717049382884279173427 3413575574074326418760141)
                  ·
                    refine ⟨1280090840277872407035053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413575574074326418760141 1280090840277872407035053)
                    ·
                      rfl

theorem cell22_3739452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3739452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739452 prefixEnd_3739452 := by exact prefixLift 3739452
  have htrace : WordTrace (prefixWord ++ tailWord_3739452) baseStart_3739452 baseEnd_3739452 := by
    simpa [prefixWord, tailWord_3739452, baseEnd_3739452] using wordTrace_append hprefix tailTrace_3739452
  have hstable : (prefixWord ++ tailWord_3739452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739452).length < 2 ^ (prefixWord ++ tailWord_3739452).sum := by decide
  have hdescent : baseEnd_3739452 < baseStart_3739452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739469 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_3739469 : Nat := 118140960795 + 3739469 * 2 ^ 59
def prefixEnd_3739469 : Nat := 4983230072969 + 3 ^ 40 * 3739469 * 2
def baseEnd_3739469 : Nat := 1280096659725290029360001

theorem tailTrace_3739469 : CollatzResearch.WordTrace tailWord_3739469 prefixEnd_3739469 1280096659725290029360001 := by
  unfold tailWord_3739469
  simp only [CollatzResearch.WordTrace]
  refine ⟨136389639289549938304749461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90926426193033292203166307 136389639289549938304749461)
  ·
    refine ⟨6393264341697653358035131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136389639289549938304749461 6393264341697653358035131)
    ·
      refine ⟨9589896512546480037052697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393264341697653358035131 9589896512546480037052697)
      ·
        refine ⟨7192422384409860027789523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9589896512546480037052697 7192422384409860027789523)
        ·
          refine ⟨10788633576614790041684285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192422384409860027789523 10788633576614790041684285)
          ·
            refine ⟨4045737591230546265631607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10788633576614790041684285 4045737591230546265631607)
            ·
              refine ⟨6068606386845819398447411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045737591230546265631607 6068606386845819398447411)
              ·
                refine ⟨9102909580268729097671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068606386845819398447411 9102909580268729097671117)
                ·
                  refine ⟨3413591092600773411626669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9102909580268729097671117 3413591092600773411626669)
                  ·
                    refine ⟨1280096659725290029360001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413591092600773411626669 1280096659725290029360001)
                    ·
                      rfl

theorem cell22_3739469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_3739469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739469 prefixEnd_3739469 := by exact prefixLift 3739469
  have htrace : WordTrace (prefixWord ++ tailWord_3739469) baseStart_3739469 baseEnd_3739469 := by
    simpa [prefixWord, tailWord_3739469, baseEnd_3739469] using wordTrace_append hprefix tailTrace_3739469
  have hstable : (prefixWord ++ tailWord_3739469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739469).length < 2 ^ (prefixWord ++ tailWord_3739469).sum := by decide
  have hdescent : baseEnd_3739469 < baseStart_3739469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739527 : List Nat := [1, 1, 4, 2, 4, 1, 1, 4, 4]
def baseStart_3739527 : Nat := 118140960795 + 3739527 * 2 ^ 59
def prefixEnd_3739527 : Nat := 4983230072969 + 3 ^ 40 * 3739527 * 2
def baseEnd_3739527 : Nat := 426705504770199070469941

theorem tailTrace_3739527 : CollatzResearch.WordTrace tailWord_3739527 prefixEnd_3739527 426705504770199070469941 := by
  unfold tailWord_3739527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136391754723339814210360835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90927836482226542806907223 136391754723339814210360835)
  ·
    refine ⟨204587632085009721315541253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136391754723339814210360835 204587632085009721315541253)
    ·
      refine ⟨38360181015939322746663985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204587632085009721315541253 38360181015939322746663985)
      ·
        refine ⟨28770135761954492059997989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38360181015939322746663985 28770135761954492059997989)
        ·
          refine ⟨5394400455366467261249623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28770135761954492059997989 5394400455366467261249623)
          ·
            refine ⟨8091600683049700891874435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394400455366467261249623 8091600683049700891874435)
            ·
              refine ⟨12137401024574551337811653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091600683049700891874435 12137401024574551337811653)
              ·
                refine ⟨2275762692107728375839685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12137401024574551337811653 2275762692107728375839685)
                ·
                  refine ⟨426705504770199070469941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275762692107728375839685 426705504770199070469941)
                  ·
                    rfl

theorem cell22_3739527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 4, 4].length) (baseStart_3739527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739527 prefixEnd_3739527 := by exact prefixLift 3739527
  have htrace : WordTrace (prefixWord ++ tailWord_3739527) baseStart_3739527 baseEnd_3739527 := by
    simpa [prefixWord, tailWord_3739527, baseEnd_3739527] using wordTrace_append hprefix tailTrace_3739527
  have hstable : (prefixWord ++ tailWord_3739527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739527).length < 2 ^ (prefixWord ++ tailWord_3739527).sum := by decide
  have hdescent : baseEnd_3739527 < baseStart_3739527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739572 : List Nat := [2, 5, 2, 1, 2, 1, 9]
def baseStart_3739572 : Nat := 118140960795 + 3739572 * 2 ^ 59
def prefixEnd_3739572 : Nat := 4983230072969 + 3 ^ 40 * 3739572 * 2
def baseEnd_3739572 : Nat := 47412293286304892371655

theorem tailTrace_3739572 : CollatzResearch.WordTrace tailWord_3739572 prefixEnd_3739572 47412293286304892371655 := by
  unfold tailWord_3739572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68196698004088393447874485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90928930672117857930499313 68196698004088393447874485)
  ·
    refine ⟨6393440437883286885738233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68196698004088393447874485 6393440437883286885738233)
    ·
      refine ⟨4795080328412465164303675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6393440437883286885738233 4795080328412465164303675)
      ·
        refine ⟨7192620492618697746455513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795080328412465164303675 7192620492618697746455513)
        ·
          refine ⟨5394465369464023309841635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7192620492618697746455513 5394465369464023309841635)
          ·
            refine ⟨8091698054196034964762453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394465369464023309841635 8091698054196034964762453)
            ·
              refine ⟨47412293286304892371655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8091698054196034964762453 47412293286304892371655)
              ·
                rfl

theorem cell22_3739572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 9].length) (baseStart_3739572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739572 prefixEnd_3739572 := by exact prefixLift 3739572
  have htrace : WordTrace (prefixWord ++ tailWord_3739572) baseStart_3739572 baseEnd_3739572 := by
    simpa [prefixWord, tailWord_3739572, baseEnd_3739572] using wordTrace_append hprefix tailTrace_3739572
  have hstable : (prefixWord ++ tailWord_3739572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739572).length < 2 ^ (prefixWord ++ tailWord_3739572).sum := by decide
  have hdescent : baseEnd_3739572 < baseStart_3739572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739583 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 7]
def baseStart_3739583 : Nat := 118140960795 + 3739583 * 2 ^ 59
def prefixEnd_3739583 : Nat := 4983230072969 + 3 ^ 40 * 3739583 * 2
def baseEnd_3739583 : Nat := 426711894751677244003217

theorem tailTrace_3739583 : CollatzResearch.WordTrace tailWord_3739583 prefixEnd_3739583 426711894751677244003217 := by
  unfold tailWord_3739583
  simp only [CollatzResearch.WordTrace]
  refine ⟨136393797211136935774399403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90929198140757957182932935 136393797211136935774399403)
  ·
    refine ⟨204590695816705403661599105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136393797211136935774399403 204590695816705403661599105)
    ·
      refine ⟨153443021862529052746199329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204590695816705403661599105 153443021862529052746199329)
      ·
        refine ⟨115082266396896789559649497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153443021862529052746199329 115082266396896789559649497)
        ·
          refine ⟨86311699797672592169737123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115082266396896789559649497 86311699797672592169737123)
          ·
            refine ⟨129467549696508888254605685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86311699797672592169737123 129467549696508888254605685)
            ·
              refine ⟨12137582784047708273869283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129467549696508888254605685 12137582784047708273869283)
              ·
                refine ⟨18206374176071562410803925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12137582784047708273869283 18206374176071562410803925)
                ·
                  refine ⟨426711894751677244003217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18206374176071562410803925 426711894751677244003217)
                  ·
                    rfl

theorem cell22_3739583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_3739583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739583 prefixEnd_3739583 := by exact prefixLift 3739583
  have htrace : WordTrace (prefixWord ++ tailWord_3739583) baseStart_3739583 baseEnd_3739583 := by
    simpa [prefixWord, tailWord_3739583, baseEnd_3739583] using wordTrace_append hprefix tailTrace_3739583
  have hstable : (prefixWord ++ tailWord_3739583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739583).length < 2 ^ (prefixWord ++ tailWord_3739583).sum := by decide
  have hdescent : baseEnd_3739583 < baseStart_3739583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739606 : List Nat := [5, 2, 1, 1, 4, 1, 2, 6]
def baseStart_3739606 : Nat := 118140960795 + 3739606 * 2 ^ 59
def prefixEnd_3739606 : Nat := 4983230072969 + 3 ^ 40 * 3739606 * 2
def baseEnd_3739606 : Nat := 142238173069451926520509

theorem tailTrace_3739606 : CollatzResearch.WordTrace tailWord_3739606 prefixEnd_3739606 142238173069451926520509 := by
  unfold tailWord_3739606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524664755628350668905417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90929757393369073801657781 8524664755628350668905417)
  ·
    refine ⟨6393498566721263001679063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8524664755628350668905417 6393498566721263001679063)
    ·
      refine ⟨9590247850081894502518595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6393498566721263001679063 9590247850081894502518595)
      ·
        refine ⟨14385371775122841753777893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590247850081894502518595 14385371775122841753777893)
        ·
          refine ⟨2697257207835532828833355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14385371775122841753777893 2697257207835532828833355)
          ·
            refine ⟨4045885811753299243250033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697257207835532828833355 4045885811753299243250033)
            ·
              refine ⟨3034414358814974432437525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4045885811753299243250033 3034414358814974432437525)
              ·
                refine ⟨142238173069451926520509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034414358814974432437525 142238173069451926520509)
                ·
                  rfl

theorem cell22_3739606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_3739606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739606 prefixEnd_3739606 := by exact prefixLift 3739606
  have htrace : WordTrace (prefixWord ++ tailWord_3739606) baseStart_3739606 baseEnd_3739606 := by
    simpa [prefixWord, tailWord_3739606, baseEnd_3739606] using wordTrace_append hprefix tailTrace_3739606
  have hstable : (prefixWord ++ tailWord_3739606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739606).length < 2 ^ (prefixWord ++ tailWord_3739606).sum := by decide
  have hdescent : baseEnd_3739606 < baseStart_3739606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739628 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 8]
def baseStart_3739628 : Nat := 118140960795 + 3739628 * 2 ^ 59
def prefixEnd_3739628 : Nat := 4983230072969 + 3 ^ 40 * 3739628 * 2
def baseEnd_3739628 : Nat := 426717029558222204878171

theorem tailTrace_3739628 : CollatzResearch.WordTrace tailWord_3739628 prefixEnd_3739628 426717029558222204878171 := by
  unfold tailWord_3739628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68197719247986954229893769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90930292330649272306525025 68197719247986954229893769)
  ·
    refine ⟨51148289435990215672420327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68197719247986954229893769 51148289435990215672420327)
    ·
      refine ⟨76722434153985323508630491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51148289435990215672420327 76722434153985323508630491)
      ·
        refine ⟨115083651230977985262945737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76722434153985323508630491 115083651230977985262945737)
        ·
          refine ⟨86312738423233488947209303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115083651230977985262945737 86312738423233488947209303)
          ·
            refine ⟨129469107634850233420813955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86312738423233488947209303 129469107634850233420813955)
            ·
              refine ⟨194203661452275350131220933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129469107634850233420813955 194203661452275350131220933)
              ·
                refine ⟨36413186522301628149603925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194203661452275350131220933 36413186522301628149603925)
                ·
                  refine ⟨426717029558222204878171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36413186522301628149603925 426717029558222204878171)
                  ·
                    rfl

theorem cell22_3739628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 8].length) (baseStart_3739628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739628 prefixEnd_3739628 := by exact prefixLift 3739628
  have htrace : WordTrace (prefixWord ++ tailWord_3739628) baseStart_3739628 baseEnd_3739628 := by
    simpa [prefixWord, tailWord_3739628, baseEnd_3739628] using wordTrace_append hprefix tailTrace_3739628
  have hstable : (prefixWord ++ tailWord_3739628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739628).length < 2 ^ (prefixWord ++ tailWord_3739628).sum := by decide
  have hdescent : baseEnd_3739628 < baseStart_3739628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739638 : List Nat := [5, 1, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_3739638 : Nat := 118140960795 + 3739638 * 2 ^ 59
def prefixEnd_3739638 : Nat := 4983230072969 + 3 ^ 40 * 3739638 * 2
def baseEnd_3739638 : Nat := 1280154511879029921884483

theorem tailTrace_3739638 : CollatzResearch.WordTrace tailWord_3739638 prefixEnd_3739638 1280154511879029921884483 := by
  unfold tailWord_3739638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524737701621105010478223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90930535483958453445101045 8524737701621105010478223)
  ·
    refine ⟨12787106552431657515717335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8524737701621105010478223 12787106552431657515717335)
    ·
      refine ⟨19180659828647486273576003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12787106552431657515717335 19180659828647486273576003)
      ·
        refine ⟨28770989742971229410364005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19180659828647486273576003 28770989742971229410364005)
        ·
          refine ⟨5394560576807105514443251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28770989742971229410364005 5394560576807105514443251)
          ·
            refine ⟨8091840865210658271664877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394560576807105514443251 8091840865210658271664877)
            ·
              refine ⟨3034440324453996851874329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8091840865210658271664877 3034440324453996851874329)
              ·
                refine ⟨2275830243340497638905747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034440324453996851874329 2275830243340497638905747)
                ·
                  refine ⟨3413745365010746458358621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275830243340497638905747 3413745365010746458358621)
                  ·
                    refine ⟨1280154511879029921884483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413745365010746458358621 1280154511879029921884483)
                    ·
                      rfl

theorem cell22_3739638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_3739638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739638 prefixEnd_3739638 := by exact prefixLift 3739638
  have htrace : WordTrace (prefixWord ++ tailWord_3739638) baseStart_3739638 baseEnd_3739638 := by
    simpa [prefixWord, tailWord_3739638, baseEnd_3739638] using wordTrace_append hprefix tailTrace_3739638
  have hstable : (prefixWord ++ tailWord_3739638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739638).length < 2 ^ (prefixWord ++ tailWord_3739638).sum := by decide
  have hdescent : baseEnd_3739638 < baseStart_3739638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739645 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 6]
def baseStart_3739645 : Nat := 118140960795 + 3739645 * 2 ^ 59
def prefixEnd_3739645 : Nat := 4983230072969 + 3 ^ 40 * 3739645 * 2
def baseEnd_3739645 : Nat := 426718969374028078986487

theorem tailTrace_3739645 : CollatzResearch.WordTrace tailWord_3739645 prefixEnd_3739645 426718969374028078986487 := by
  unfold tailWord_3739645
  simp only [CollatzResearch.WordTrace]
  refine ⟨136396058536912320363156389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90930705691274880242104259 136396058536912320363156389)
  ·
    refine ⟨25574260975671060068091823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136396058536912320363156389 25574260975671060068091823)
    ·
      refine ⟨38361391463506590102137735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25574260975671060068091823 38361391463506590102137735)
      ·
        refine ⟨57542087195259885153206603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38361391463506590102137735 57542087195259885153206603)
        ·
          refine ⟨86313130792889827729809905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57542087195259885153206603 86313130792889827729809905)
          ·
            refine ⟨64734848094667370797357429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86313130792889827729809905 64734848094667370797357429)
            ·
              refine ⟨6068892008875066012252259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64734848094667370797357429 6068892008875066012252259)
              ·
                refine ⟨9103338013312599018378389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6068892008875066012252259 9103338013312599018378389)
                ·
                  refine ⟨426718969374028078986487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9103338013312599018378389 426718969374028078986487)
                  ·
                    rfl

theorem cell22_3739645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_3739645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739645 prefixEnd_3739645 := by exact prefixLift 3739645
  have htrace : WordTrace (prefixWord ++ tailWord_3739645) baseStart_3739645 baseEnd_3739645 := by
    simpa [prefixWord, tailWord_3739645, baseEnd_3739645] using wordTrace_append hprefix tailTrace_3739645
  have hstable : (prefixWord ++ tailWord_3739645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739645).length < 2 ^ (prefixWord ++ tailWord_3739645).sum := by decide
  have hdescent : baseEnd_3739645 < baseStart_3739645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739660 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_3739660 : Nat := 118140960795 + 3739660 * 2 ^ 59
def prefixEnd_3739660 : Nat := 4983230072969 + 3 ^ 40 * 3739660 * 2
def baseEnd_3739660 : Nat := 1280162042928629197834415

theorem tailTrace_3739660 : CollatzResearch.WordTrace tailWord_3739660 prefixEnd_3739660 1280162042928629197834415 := by
  unfold tailWord_3739660
  simp only [CollatzResearch.WordTrace]
  refine ⟨68198302815928988962476217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90931070421238651949968289 68198302815928988962476217)
  ·
    refine ⟨51148727111946741721857163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68198302815928988962476217 51148727111946741721857163)
    ·
      refine ⟨76723090667920112582785745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51148727111946741721857163 76723090667920112582785745)
      ·
        refine ⟨57542318000940084437089309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76723090667920112582785745 57542318000940084437089309)
        ·
          refine ⟨21578369250352531663908491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57542318000940084437089309 21578369250352531663908491)
          ·
            refine ⟨32367553875528797495862737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21578369250352531663908491 32367553875528797495862737)
            ·
              refine ⟨24275665406646598121897053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32367553875528797495862737 24275665406646598121897053)
              ·
                refine ⟨9103374527492474295711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24275665406646598121897053 9103374527492474295711395)
                ·
                  refine ⟨13655061791238711443567093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103374527492474295711395 13655061791238711443567093)
                  ·
                    refine ⟨1280162042928629197834415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13655061791238711443567093 1280162042928629197834415)
                    ·
                      rfl

theorem cell22_3739660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_3739660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739660 prefixEnd_3739660 := by exact prefixLift 3739660
  have htrace : WordTrace (prefixWord ++ tailWord_3739660) baseStart_3739660 baseEnd_3739660 := by
    simpa [prefixWord, tailWord_3739660, baseEnd_3739660] using wordTrace_append hprefix tailTrace_3739660
  have hstable : (prefixWord ++ tailWord_3739660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739660).length < 2 ^ (prefixWord ++ tailWord_3739660).sum := by decide
  have hdescent : baseEnd_3739660 < baseStart_3739660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739677 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3739677 : Nat := 118140960795 + 3739677 * 2 ^ 59
def prefixEnd_3739677 : Nat := 4983230072969 + 3 ^ 40 * 3739677 * 2
def baseEnd_3739677 : Nat := 1280167862376046820159363

theorem tailTrace_3739677 : CollatzResearch.WordTrace tailWord_3739677 prefixEnd_3739677 1280167862376046820159363 := by
  unfold tailWord_3739677
  simp only [CollatzResearch.WordTrace]
  refine ⟨136397225672796389828321285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90931483781864259885547523 136397225672796389828321285)
  ·
    refine ⟨25574479813649323092810241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136397225672796389828321285 25574479813649323092810241)
    ·
      refine ⟨19180859860236992319607681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25574479813649323092810241 19180859860236992319607681)
      ·
        refine ⟨14385644895177744239705761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19180859860236992319607681 14385644895177744239705761)
        ·
          refine ⟨10789233671383308179779321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14385644895177744239705761 10789233671383308179779321)
          ·
            refine ⟨8091925253537481134834491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10789233671383308179779321 8091925253537481134834491)
            ·
              refine ⟨12137887880306221702251737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8091925253537481134834491 12137887880306221702251737)
              ·
                refine ⟨9103415910229666276688803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12137887880306221702251737 9103415910229666276688803)
                ·
                  refine ⟨13655123865344499415033205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9103415910229666276688803 13655123865344499415033205)
                  ·
                    refine ⟨1280167862376046820159363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13655123865344499415033205 1280167862376046820159363)
                    ·
                      rfl

theorem cell22_3739677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3739677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739677 prefixEnd_3739677 := by exact prefixLift 3739677
  have htrace : WordTrace (prefixWord ++ tailWord_3739677) baseStart_3739677 baseEnd_3739677 := by
    simpa [prefixWord, tailWord_3739677, baseEnd_3739677] using wordTrace_append hprefix tailTrace_3739677
  have hstable : (prefixWord ++ tailWord_3739677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739677).length < 2 ^ (prefixWord ++ tailWord_3739677).sum := by decide
  have hdescent : baseEnd_3739677 < baseStart_3739677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739690 : List Nat := [3, 1, 4, 1, 2, 11]
def baseStart_3739690 : Nat := 118140960795 + 3739690 * 2 ^ 59
def prefixEnd_3739690 : Nat := 4983230072969 + 3 ^ 40 * 3739690 * 2
def baseEnd_3739690 : Nat := 15804596451132334809683

theorem tailTrace_3739690 : CollatzResearch.WordTrace tailWord_3739690 prefixEnd_3739690 15804596451132334809683 := by
  unfold tailWord_3739690
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099424955437323262136131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90931799881166195365696349 34099424955437323262136131)
  ·
    refine ⟨51149137433155984893204197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34099424955437323262136131 51149137433155984893204197)
    ·
      refine ⟨9590463268716747167475787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51149137433155984893204197 9590463268716747167475787)
      ·
        refine ⟨14385694903075120751213681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590463268716747167475787 14385694903075120751213681)
        ·
          refine ⟨10789271177306340563410261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14385694903075120751213681 10789271177306340563410261)
          ·
            refine ⟨15804596451132334809683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10789271177306340563410261 15804596451132334809683)
            ·
              rfl

theorem cell22_3739690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 11].length) (baseStart_3739690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739690 prefixEnd_3739690 := by exact prefixLift 3739690
  have htrace : WordTrace (prefixWord ++ tailWord_3739690) baseStart_3739690 baseEnd_3739690 := by
    simpa [prefixWord, tailWord_3739690, baseEnd_3739690] using wordTrace_append hprefix tailTrace_3739690
  have hstable : (prefixWord ++ tailWord_3739690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739690).length < 2 ^ (prefixWord ++ tailWord_3739690).sum := by decide
  have hdescent : baseEnd_3739690 < baseStart_3739690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739694 : List Nat := [4, 1, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3739694 : Nat := 118140960795 + 3739694 * 2 ^ 59
def prefixEnd_3739694 : Nat := 4983230072969 + 3 ^ 40 * 3739694 * 2
def baseEnd_3739694 : Nat := 1280173681823464442484311

theorem tailTrace_3739694 : CollatzResearch.WordTrace tailWord_3739694 prefixEnd_3739694 1280173681823464442484311 := by
  unfold tailWord_3739694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17049730714216850216461267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90931897142489867821126757 17049730714216850216461267)
  ·
    refine ⟨25574596071325275324691901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17049730714216850216461267 25574596071325275324691901)
    ·
      refine ⟨9590473526746978246759463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25574596071325275324691901 9590473526746978246759463)
      ·
        refine ⟨14385710290120467370139195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590473526746978246759463 14385710290120467370139195)
        ·
          refine ⟨21578565435180701055208793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14385710290120467370139195 21578565435180701055208793)
          ·
            refine ⟨16183924076385525791406595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21578565435180701055208793 16183924076385525791406595)
            ·
              refine ⟨24275886114578288687109893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16183924076385525791406595 24275886114578288687109893)
              ·
                refine ⟨4551728646483429128833105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24275886114578288687109893 4551728646483429128833105)
                ·
                  refine ⟨3413796484862571846624829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4551728646483429128833105 3413796484862571846624829)
                  ·
                    refine ⟨1280173681823464442484311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413796484862571846624829 1280173681823464442484311)
                    ·
                      rfl

theorem cell22_3739694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3739694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739694 prefixEnd_3739694 := by exact prefixLift 3739694
  have htrace : WordTrace (prefixWord ++ tailWord_3739694) baseStart_3739694 baseEnd_3739694 := by
    simpa [prefixWord, tailWord_3739694, baseEnd_3739694] using wordTrace_append hprefix tailTrace_3739694
  have hstable : (prefixWord ++ tailWord_3739694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739694).length < 2 ^ (prefixWord ++ tailWord_3739694).sum := by decide
  have hdescent : baseEnd_3739694 < baseStart_3739694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739769 : List Nat := [1, 2, 1, 3, 4, 2, 3, 1, 5]
def baseStart_3739769 : Nat := 118140960795 + 3739769 * 2 ^ 59
def prefixEnd_3739769 : Nat := 4983230072969 + 3 ^ 40 * 3739769 * 2
def baseEnd_3739769 : Nat := 426733118618729748953027

theorem tailTrace_3739769 : CollatzResearch.WordTrace tailWord_3739769 prefixEnd_3739769 426733118618729748953027 := by
  unfold tailWord_3739769
  simp only [CollatzResearch.WordTrace]
  refine ⟨136400581188463089540670361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90933720792308726360446907 136400581188463089540670361)
  ·
    refine ⟨102300435891347317155502771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136400581188463089540670361 102300435891347317155502771)
    ·
      refine ⟨153450653837020975733254157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102300435891347317155502771 153450653837020975733254157)
      ·
        refine ⟨57543995188882865899970309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153450653837020975733254157 57543995188882865899970309)
        ·
          refine ⟨10789499097915537356244433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57543995188882865899970309 10789499097915537356244433)
          ·
            refine ⟨8092124323436653017183325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10789499097915537356244433 8092124323436653017183325)
            ·
              refine ⟨3034546621288744881443747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8092124323436653017183325 3034546621288744881443747)
              ·
                refine ⟨4551819931933117322165621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034546621288744881443747 4551819931933117322165621)
                ·
                  refine ⟨426733118618729748953027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4551819931933117322165621 426733118618729748953027)
                  ·
                    rfl

theorem cell22_3739769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 1, 5].length) (baseStart_3739769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739769 prefixEnd_3739769 := by exact prefixLift 3739769
  have htrace : WordTrace (prefixWord ++ tailWord_3739769) baseStart_3739769 baseEnd_3739769 := by
    simpa [prefixWord, tailWord_3739769, baseEnd_3739769] using wordTrace_append hprefix tailTrace_3739769
  have hstable : (prefixWord ++ tailWord_3739769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739769).length < 2 ^ (prefixWord ++ tailWord_3739769).sum := by decide
  have hdescent : baseEnd_3739769 < baseStart_3739769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739790 : List Nat := [4, 1, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3739790 : Nat := 118140960795 + 3739790 * 2 ^ 59
def prefixEnd_3739790 : Nat := 4983230072969 + 3 ^ 40 * 3739790 * 2
def baseEnd_3739790 : Nat := 1280206544585352192084017

theorem tailTrace_3739790 : CollatzResearch.WordTrace tailWord_3739790 prefixEnd_3739790 1280206544585352192084017 := by
  unfold tailWord_3739790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050168390173376265898103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90934231414258006751456549 17050168390173376265898103)
  ·
    refine ⟨25575252585260064398847155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17050168390173376265898103 25575252585260064398847155)
    ·
      refine ⟨38362878877890096598270733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25575252585260064398847155 38362878877890096598270733)
      ·
        refine ⟨14386079579208786224351525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38362878877890096598270733 14386079579208786224351525)
        ·
          refine ⟨2697389921101647417065911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14386079579208786224351525 2697389921101647417065911)
          ·
            refine ⟨4046084881652471125598867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697389921101647417065911 4046084881652471125598867)
            ·
              refine ⟨6069127322478706688398301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046084881652471125598867 6069127322478706688398301)
              ·
                refine ⟨2275922745929515008149363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6069127322478706688398301 2275922745929515008149363)
                ·
                  refine ⟨3413884118894272512224045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2275922745929515008149363 3413884118894272512224045)
                  ·
                    refine ⟨1280206544585352192084017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3413884118894272512224045 1280206544585352192084017)
                    ·
                      rfl

theorem cell22_3739790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3739790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739790 prefixEnd_3739790 := by exact prefixLift 3739790
  have htrace : WordTrace (prefixWord ++ tailWord_3739790) baseStart_3739790 baseEnd_3739790 := by
    simpa [prefixWord, tailWord_3739790, baseEnd_3739790] using wordTrace_append hprefix tailTrace_3739790
  have hstable : (prefixWord ++ tailWord_3739790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739790).length < 2 ^ (prefixWord ++ tailWord_3739790).sum := by decide
  have hdescent : baseEnd_3739790 < baseStart_3739790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739795 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_3739795 : Nat := 118140960795 + 3739795 * 2 ^ 59
def prefixEnd_3739795 : Nat := 4983230072969 + 3 ^ 40 * 3739795 * 2
def baseEnd_3739795 : Nat := 1280208256187533845709001

theorem tailTrace_3739795 : CollatzResearch.WordTrace tailWord_3739795 prefixEnd_3739795 1280208256187533845709001 := by
  unfold tailWord_3739795
  simp only [CollatzResearch.WordTrace]
  refine ⟨136401529486368895981116839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90934352990912597320744559 136401529486368895981116839)
  ·
    refine ⟨204602294229553343971675259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136401529486368895981116839 204602294229553343971675259)
    ·
      refine ⟨306903441344330015957512889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204602294229553343971675259 306903441344330015957512889)
      ·
        refine ⟨230177581008247511968134667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306903441344330015957512889 230177581008247511968134667)
        ·
          refine ⟨345266371512371267952202001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230177581008247511968134667 345266371512371267952202001)
          ·
            refine ⟨258949778634278450964151501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345266371512371267952202001 258949778634278450964151501)
            ·
              refine ⟨97106166987854419111556813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258949778634278450964151501 97106166987854419111556813)
              ·
                refine ⟨36414812620445407166833805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97106166987854419111556813 36414812620445407166833805)
                ·
                  refine ⟨13655554732667027687562677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36414812620445407166833805 13655554732667027687562677)
                  ·
                    refine ⟨1280208256187533845709001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13655554732667027687562677 1280208256187533845709001)
                    ·
                      rfl

theorem cell22_3739795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_3739795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739795 prefixEnd_3739795 := by exact prefixLift 3739795
  have htrace : WordTrace (prefixWord ++ tailWord_3739795) baseStart_3739795 baseEnd_3739795 := by
    simpa [prefixWord, tailWord_3739795, baseEnd_3739795] using wordTrace_append hprefix tailTrace_3739795
  have hstable : (prefixWord ++ tailWord_3739795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739795).length < 2 ^ (prefixWord ++ tailWord_3739795).sum := by decide
  have hdescent : baseEnd_3739795 < baseStart_3739795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739844 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3739844 : Nat := 118140960795 + 3739844 * 2 ^ 59
def prefixEnd_3739844 : Nat := 4983230072969 + 3 ^ 40 * 3739844 * 2
def baseEnd_3739844 : Nat := 1280225029888914051233851

theorem tailTrace_3739844 : CollatzResearch.WordTrace tailWord_3739844 prefixEnd_3739844 1280225029888914051233851 := by
  unfold tailWord_3739844
  simp only [CollatzResearch.WordTrace]
  refine ⟨68201658331595688674825293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90935544442127584899767057 68201658331595688674825293)
  ·
    refine ⟨25575621874348383253059485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68201658331595688674825293 25575621874348383253059485)
    ·
      refine ⟨9590858202880643719897307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25575621874348383253059485 9590858202880643719897307)
      ·
        refine ⟨14386287304320965579845961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9590858202880643719897307 14386287304320965579845961)
        ·
          refine ⟨10789715478240724184884471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14386287304320965579845961 10789715478240724184884471)
          ·
            refine ⟨16184573217361086277326707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10789715478240724184884471 16184573217361086277326707)
            ·
              refine ⟨24276859826041629415990061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16184573217361086277326707 24276859826041629415990061)
              ·
                refine ⟨9103822434765611030996273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24276859826041629415990061 9103822434765611030996273)
                ·
                  refine ⟨6827866826074208273247205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9103822434765611030996273 6827866826074208273247205)
                  ·
                    refine ⟨1280225029888914051233851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6827866826074208273247205 1280225029888914051233851)
                    ·
                      rfl

theorem cell22_3739844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3739844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739844 prefixEnd_3739844 := by exact prefixLift 3739844
  have htrace : WordTrace (prefixWord ++ tailWord_3739844) baseStart_3739844 baseEnd_3739844 := by
    simpa [prefixWord, tailWord_3739844, baseEnd_3739844] using wordTrace_append hprefix tailTrace_3739844
  have hstable : (prefixWord ++ tailWord_3739844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739844).length < 2 ^ (prefixWord ++ tailWord_3739844).sum := by decide
  have hdescent : baseEnd_3739844 < baseStart_3739844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739964 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 6, 3]
def baseStart_3739964 : Nat := 118140960795 + 3739964 * 2 ^ 59
def prefixEnd_3739964 : Nat := 4983230072969 + 3 ^ 40 * 3739964 * 2
def baseEnd_3739964 : Nat := 1280266108341273738233483

theorem tailTrace_3739964 : CollatzResearch.WordTrace tailWord_3739964 prefixEnd_3739964 1280266108341273738233483 := by
  unfold tailWord_3739964
  simp only [CollatzResearch.WordTrace]
  refine ⟨68203846711378318922009473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90938462281837758562679297 68203846711378318922009473)
  ·
    refine ⟨51152885033533739191507105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68203846711378318922009473 51152885033533739191507105)
    ·
      refine ⟨38364663775150304393630329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51152885033533739191507105 38364663775150304393630329)
      ·
        refine ⟨28773497831362728295222747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38364663775150304393630329 28773497831362728295222747)
        ·
          refine ⟨43160246747044092442834121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28773497831362728295222747 43160246747044092442834121)
          ·
            refine ⟨32370185060283069332125591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43160246747044092442834121 32370185060283069332125591)
            ·
              refine ⟨48555277590424603998188387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32370185060283069332125591 48555277590424603998188387)
              ·
                refine ⟨72832916385636905997282581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48555277590424603998188387 72832916385636905997282581)
                ·
                  refine ⟨3414042955576729968622621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72832916385636905997282581 3414042955576729968622621)
                  ·
                    refine ⟨1280266108341273738233483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414042955576729968622621 1280266108341273738233483)
                    ·
                      rfl

theorem cell22_3739964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_3739964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739964 prefixEnd_3739964 := by exact prefixLift 3739964
  have htrace : WordTrace (prefixWord ++ tailWord_3739964) baseStart_3739964 baseEnd_3739964 := by
    simpa [prefixWord, tailWord_3739964, baseEnd_3739964] using wordTrace_append hprefix tailTrace_3739964
  have hstable : (prefixWord ++ tailWord_3739964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739964).length < 2 ^ (prefixWord ++ tailWord_3739964).sum := by decide
  have hdescent : baseEnd_3739964 < baseStart_3739964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3739992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3739992 : Nat := 118140960795 + 3739992 * 2 ^ 59
def prefixEnd_3739992 : Nat := 4983230072969 + 3 ^ 40 * 3739992 * 2
def baseEnd_3739992 : Nat := 1280275693313490998533397

theorem tailTrace_3739992 : CollatzResearch.WordTrace tailWord_3739992 prefixEnd_3739992 1280275693313490998533397 := by
  unfold tailWord_3739992
  simp only [CollatzResearch.WordTrace]
  refine ⟨68204357333327599313019115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90939143111103465750692153 68204357333327599313019115)
  ·
    refine ⟨102306535999991398969528673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68204357333327599313019115 102306535999991398969528673)
    ·
      refine ⟨76729901999993549227146505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102306535999991398969528673 76729901999993549227146505)
      ·
        refine ⟨57547426499995161920359879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76729901999993549227146505 57547426499995161920359879)
        ·
          refine ⟨86321139749992742880539819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57547426499995161920359879 86321139749992742880539819)
          ·
            refine ⟨129481709624989114320809729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86321139749992742880539819 129481709624989114320809729)
            ·
              refine ⟨97111282218741835740607297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129481709624989114320809729 97111282218741835740607297)
              ·
                refine ⟨72833461664056376805455473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97111282218741835740607297 72833461664056376805455473)
                ·
                  refine ⟨54625096248042282604091605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72833461664056376805455473 54625096248042282604091605)
                  ·
                    refine ⟨1280275693313490998533397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54625096248042282604091605 1280275693313490998533397)
                    ·
                      rfl

theorem cell22_3739992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3739992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3739992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3739992 prefixEnd_3739992 := by exact prefixLift 3739992
  have htrace : WordTrace (prefixWord ++ tailWord_3739992) baseStart_3739992 baseEnd_3739992 := by
    simpa [prefixWord, tailWord_3739992, baseEnd_3739992] using wordTrace_append hprefix tailTrace_3739992
  have hstable : (prefixWord ++ tailWord_3739992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3739992).length < 2 ^ (prefixWord ++ tailWord_3739992).sum := by decide
  have hdescent : baseEnd_3739992 < baseStart_3739992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3739992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740009 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 5, 3]
def baseStart_3740009 : Nat := 118140960795 + 3740009 * 2 ^ 59
def prefixEnd_3740009 : Nat := 4983230072969 + 3 ^ 40 * 3740009 * 2
def baseEnd_3740009 : Nat := 1280281512760908620858345

theorem tailTrace_3740009 : CollatzResearch.WordTrace tailWord_3740009 prefixEnd_3740009 1280281512760908620858345 := by
  unfold tailWord_3740009
  simp only [CollatzResearch.WordTrace]
  refine ⟨136409334707593610529407081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90939556471729073686271387 136409334707593610529407081)
  ·
    refine ⟨102307001030695207897055311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136409334707593610529407081 102307001030695207897055311)
    ·
      refine ⟨153460501546042811845582967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102307001030695207897055311 153460501546042811845582967)
      ·
        refine ⟨230190752319064217768374451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153460501546042811845582967 230190752319064217768374451)
        ·
          refine ⟨345286128478596326652561677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230190752319064217768374451 345286128478596326652561677)
          ·
            refine ⟨129482298179473622494710629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345286128478596326652561677 129482298179473622494710629)
            ·
              refine ⟨24277930908651304217758243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129482298179473622494710629 24277930908651304217758243)
              ·
                refine ⟨36416896362976956326637365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24277930908651304217758243 36416896362976956326637365)
                ·
                  refine ⟨3414084034029089655622253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36416896362976956326637365 3414084034029089655622253)
                  ·
                    refine ⟨1280281512760908620858345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414084034029089655622253 1280281512760908620858345)
                    ·
                      rfl

theorem cell22_3740009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_3740009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740009 prefixEnd_3740009 := by exact prefixLift 3740009
  have htrace : WordTrace (prefixWord ++ tailWord_3740009) baseStart_3740009 baseEnd_3740009 := by
    simpa [prefixWord, tailWord_3740009, baseEnd_3740009] using wordTrace_append hprefix tailTrace_3740009
  have hstable : (prefixWord ++ tailWord_3740009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740009).length < 2 ^ (prefixWord ++ tailWord_3740009).sum := by decide
  have hdescent : baseEnd_3740009 < baseStart_3740009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740034 : List Nat := [3, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3740034 : Nat := 118140960795 + 3740034 * 2 ^ 59
def prefixEnd_3740034 : Nat := 4983230072969 + 3 ^ 40 * 3740034 * 2
def baseEnd_3740034 : Nat := 426763356923938962994423

theorem tailTrace_3740034 : CollatzResearch.WordTrace tailWord_3740034 prefixEnd_3740034 426763356923938962994423 := by
  unfold tailWord_3740034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34102561633125759949766789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90940164355002026532711437 34102561633125759949766789)
  ·
    refine ⟨6394230306211079990581273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34102561633125759949766789 6394230306211079990581273)
    ·
      refine ⟨4795672729658309992935955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6394230306211079990581273 4795672729658309992935955)
      ·
        refine ⟨7193509094487464989403933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795672729658309992935955 7193509094487464989403933)
        ·
          refine ⟨2697565910432799371026475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7193509094487464989403933 2697565910432799371026475)
          ·
            refine ⟨4046348865649199056539713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697565910432799371026475 4046348865649199056539713)
            ·
              refine ⟨3034761649236899292404785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046348865649199056539713 3034761649236899292404785)
              ·
                refine ⟨2276071236927674469303589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034761649236899292404785 2276071236927674469303589)
                ·
                  refine ⟨426763356923938962994423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276071236927674469303589 426763356923938962994423)
                  ·
                    rfl

theorem cell22_3740034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3740034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740034 prefixEnd_3740034 := by exact prefixLift 3740034
  have htrace : WordTrace (prefixWord ++ tailWord_3740034) baseStart_3740034 baseEnd_3740034 := by
    simpa [prefixWord, tailWord_3740034, baseEnd_3740034] using wordTrace_append hprefix tailTrace_3740034
  have hstable : (prefixWord ++ tailWord_3740034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740034).length < 2 ^ (prefixWord ++ tailWord_3740034).sum := by decide
  have hdescent : baseEnd_3740034 < baseStart_3740034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740043 : List Nat := [1, 1, 1, 1, 4, 5, 1, 4, 1, 3]
def baseStart_3740043 : Nat := 118140960795 + 3740043 * 2 ^ 59
def prefixEnd_3740043 : Nat := 4983230072969 + 3 ^ 40 * 3740043 * 2
def baseEnd_3740043 : Nat := 1280293151655743865508241

theorem tailTrace_3740043 : CollatzResearch.WordTrace tailWord_3740043 prefixEnd_3740043 1280293151655743865508241 := by
  unfold tailWord_3740043
  simp only [CollatzResearch.WordTrace]
  refine ⟨136410574789470434336144783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90940383192980289557429855 136410574789470434336144783)
  ·
    refine ⟨204615862184205651504217175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136410574789470434336144783 204615862184205651504217175)
    ·
      refine ⟨306923793276308477256325763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204615862184205651504217175 306923793276308477256325763)
      ·
        refine ⟨460385689914462715884488645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306923793276308477256325763 460385689914462715884488645)
        ·
          refine ⟨86322316858961759228341621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460385689914462715884488645 86322316858961759228341621)
          ·
            refine ⟨8092717205527664927657027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86322316858961759228341621 8092717205527664927657027)
            ·
              refine ⟨12139075808291497391485541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8092717205527664927657027 12139075808291497391485541)
              ·
                refine ⟨2276076714054655760903539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12139075808291497391485541 2276076714054655760903539)
                ·
                  refine ⟨3414115071081983641355309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276076714054655760903539 3414115071081983641355309)
                  ·
                    refine ⟨1280293151655743865508241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414115071081983641355309 1280293151655743865508241)
                    ·
                      rfl

theorem cell22_3740043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 4, 1, 3].length) (baseStart_3740043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740043 prefixEnd_3740043 := by exact prefixLift 3740043
  have htrace : WordTrace (prefixWord ++ tailWord_3740043) baseStart_3740043 baseEnd_3740043 := by
    simpa [prefixWord, tailWord_3740043, baseEnd_3740043] using wordTrace_append hprefix tailTrace_3740043
  have hstable : (prefixWord ++ tailWord_3740043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740043).length < 2 ^ (prefixWord ++ tailWord_3740043).sum := by decide
  have hdescent : baseEnd_3740043 < baseStart_3740043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740056 : List Nat := [2, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_3740056 : Nat := 118140960795 + 3740056 * 2 ^ 59
def prefixEnd_3740056 : Nat := 4983230072969 + 3 ^ 40 * 3740056 * 2
def baseEnd_3740056 : Nat := 426765867273805388311067

theorem tailTrace_3740056 : CollatzResearch.WordTrace tailWord_3740056 prefixEnd_3740056 426765867273805388311067 := by
  unfold tailWord_3740056
  simp only [CollatzResearch.WordTrace]
  refine ⟨68205524469211668778184011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90940699292282225037578681 68205524469211668778184011)
  ·
    refine ⟨102308286703817503167276017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68205524469211668778184011 102308286703817503167276017)
    ·
      refine ⟨76731215027863127375457013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102308286703817503167276017 76731215027863127375457013)
      ·
        refine ⟨7193551408862168191449095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76731215027863127375457013 7193551408862168191449095)
        ·
          refine ⟨10790327113293252287173643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193551408862168191449095 10790327113293252287173643)
          ·
            refine ⟨16185490669939878430760465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790327113293252287173643 16185490669939878430760465)
            ·
              refine ⟨12139118002454908823070349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16185490669939878430760465 12139118002454908823070349)
              ·
                refine ⟨4552169250920590808651381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12139118002454908823070349 4552169250920590808651381)
                ·
                  refine ⟨426765867273805388311067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4552169250920590808651381 426765867273805388311067)
                  ·
                    rfl

theorem cell22_3740056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_3740056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740056 prefixEnd_3740056 := by exact prefixLift 3740056
  have htrace : WordTrace (prefixWord ++ tailWord_3740056) baseStart_3740056 baseEnd_3740056 := by
    simpa [prefixWord, tailWord_3740056, baseEnd_3740056] using wordTrace_append hprefix tailTrace_3740056
  have hstable : (prefixWord ++ tailWord_3740056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740056).length < 2 ^ (prefixWord ++ tailWord_3740056).sum := by decide
  have hdescent : baseEnd_3740056 < baseStart_3740056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740069 : List Nat := [1, 3, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3740069 : Nat := 118140960795 + 3740069 * 2 ^ 59
def prefixEnd_3740069 : Nat := 4983230072969 + 3 ^ 40 * 3740069 * 2
def baseEnd_3740069 : Nat := 1280302051987088464358161

theorem tailTrace_3740069 : CollatzResearch.WordTrace tailWord_3740069 prefixEnd_3740069 1280302051987088464358161 := by
  unfold tailWord_3740069
  simp only [CollatzResearch.WordTrace]
  refine ⟨136411523087376240776591261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90941015391584160517727507 136411523087376240776591261)
  ·
    refine ⟨51154321157766090291221723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136411523087376240776591261 51154321157766090291221723)
    ·
      refine ⟨76731481736649135436832585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51154321157766090291221723 76731481736649135436832585)
      ·
        refine ⟨57548611302486851577624439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76731481736649135436832585 57548611302486851577624439)
        ·
          refine ⟨86322916953730277366436659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57548611302486851577624439 86322916953730277366436659)
          ·
            refine ⟨129484375430595416049654989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86322916953730277366436659 129484375430595416049654989)
            ·
              refine ⟨48556640786473281018620621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129484375430595416049654989 48556640786473281018620621)
              ·
                refine ⟨18208740294927480381982733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48556640786473281018620621 18208740294927480381982733)
                ·
                  refine ⟨6828277610597805143243525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18208740294927480381982733 6828277610597805143243525)
                  ·
                    refine ⟨1280302051987088464358161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6828277610597805143243525 1280302051987088464358161)
                    ·
                      rfl

theorem cell22_3740069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3740069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740069 prefixEnd_3740069 := by exact prefixLift 3740069
  have htrace : WordTrace (prefixWord ++ tailWord_3740069) baseStart_3740069 baseEnd_3740069 := by
    simpa [prefixWord, tailWord_3740069, baseEnd_3740069] using wordTrace_append hprefix tailTrace_3740069
  have hstable : (prefixWord ++ tailWord_3740069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740069).length < 2 ^ (prefixWord ++ tailWord_3740069).sum := by decide
  have hdescent : baseEnd_3740069 < baseStart_3740069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740077 : List Nat := [1, 5, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3740077 : Nat := 118140960795 + 3740077 * 2 ^ 59
def prefixEnd_3740077 : Nat := 4983230072969 + 3 ^ 40 * 3740077 * 2
def baseEnd_3740077 : Nat := 1280304790550579110158137

theorem tailTrace_3740077 : CollatzResearch.WordTrace tailWord_3740077 prefixEnd_3740077 1280304790550579110158137 := by
  unfold tailWord_3740077
  simp only [CollatzResearch.WordTrace]
  refine ⟨136411814871347258142882485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90941209914231505428588323 136411814871347258142882485)
  ·
    refine ⟨12788607644188805450895233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136411814871347258142882485 12788607644188805450895233)
    ·
      refine ⟨9591455733141604088171425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12788607644188805450895233 9591455733141604088171425)
      ·
        refine ⟨7193591799856203066128569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9591455733141604088171425 7193591799856203066128569)
        ·
          refine ⟨5395193849892152299596427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193591799856203066128569 5395193849892152299596427)
          ·
            refine ⟨8092790774838228449394641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395193849892152299596427 8092790774838228449394641)
            ·
              refine ⟨6069593081128671337045981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092790774838228449394641 6069593081128671337045981)
              ·
                refine ⟨2276097405423251751392243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6069593081128671337045981 2276097405423251751392243)
                ·
                  refine ⟨3414146108134877627088365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276097405423251751392243 3414146108134877627088365)
                  ·
                    refine ⟨1280304790550579110158137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414146108134877627088365 1280304790550579110158137)
                    ·
                      rfl

theorem cell22_3740077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3740077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740077 prefixEnd_3740077 := by exact prefixLift 3740077
  have htrace : WordTrace (prefixWord ++ tailWord_3740077) baseStart_3740077 baseEnd_3740077 := by
    simpa [prefixWord, tailWord_3740077, baseEnd_3740077] using wordTrace_append hprefix tailTrace_3740077
  have hstable : (prefixWord ++ tailWord_3740077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740077).length < 2 ^ (prefixWord ++ tailWord_3740077).sum := by decide
  have hdescent : baseEnd_3740077 < baseStart_3740077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740129 : List Nat := [1, 2, 3, 1, 2, 2, 3, 8]
def baseStart_3740129 : Nat := 118140960795 + 3740129 * 2 ^ 59
def prefixEnd_3740129 : Nat := 4983230072969 + 3 ^ 40 * 3740129 * 2
def baseEnd_3740129 : Nat := 142258065690363145317553

theorem tailTrace_3740129 : CollatzResearch.WordTrace tailWord_3740129 prefixEnd_3740129 142258065690363145317553 := by
  unfold tailWord_3740129
  simp only [CollatzResearch.WordTrace]
  refine ⟨136413711467158871023775441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90942474311439247349183627 136413711467158871023775441)
  ·
    refine ⟨102310283600369153267831581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136413711467158871023775441 102310283600369153267831581)
    ·
      refine ⟨38366356350138432475436843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102310283600369153267831581 38366356350138432475436843)
      ·
        refine ⟨57549534525207648713155265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38366356350138432475436843 57549534525207648713155265)
        ·
          refine ⟨43162150893905736534866449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57549534525207648713155265 43162150893905736534866449)
          ·
            refine ⟨32371613170429302401149837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43162150893905736534866449 32371613170429302401149837)
            ·
              refine ⟨12139354938910988400431189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32371613170429302401149837 12139354938910988400431189)
              ·
                refine ⟨142258065690363145317553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12139354938910988400431189 142258065690363145317553)
                ·
                  rfl

theorem cell22_3740129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 8].length) (baseStart_3740129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740129 prefixEnd_3740129 := by exact prefixLift 3740129
  have htrace : WordTrace (prefixWord ++ tailWord_3740129) baseStart_3740129 baseEnd_3740129 := by
    simpa [prefixWord, tailWord_3740129, baseEnd_3740129] using wordTrace_append hprefix tailTrace_3740129
  have hstable : (prefixWord ++ tailWord_3740129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740129).length < 2 ^ (prefixWord ++ tailWord_3740129).sum := by decide
  have hdescent : baseEnd_3740129 < baseStart_3740129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740159 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_3740159 : Nat := 118140960795 + 3740159 * 2 ^ 59
def prefixEnd_3740159 : Nat := 4983230072969 + 3 ^ 40 * 3740159 * 2
def baseEnd_3740159 : Nat := 1280332860826358229607885

theorem tailTrace_3740159 : CollatzResearch.WordTrace tailWord_3740159 prefixEnd_3740159 1280332860826358229607885 := by
  unfold tailWord_3740159
  simp only [CollatzResearch.WordTrace]
  refine ⟨136414805657050186147367531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90943203771366790764911687 136414805657050186147367531)
  ·
    refine ⟨204622208485575279221051297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136414805657050186147367531 204622208485575279221051297)
    ·
      refine ⟨153466656364181459415788473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204622208485575279221051297 153466656364181459415788473)
      ·
        refine ⟨115099992273136094561841355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153466656364181459415788473 115099992273136094561841355)
        ·
          refine ⟨172649988409704141842762033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115099992273136094561841355 172649988409704141842762033)
          ·
            refine ⟨129487491307278106382071525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172649988409704141842762033 129487491307278106382071525)
            ·
              refine ⟨24278904620114644946638411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129487491307278106382071525 24278904620114644946638411)
              ·
                refine ⟨36418356930171967419957617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24278904620114644946638411 36418356930171967419957617)
                ·
                  refine ⟨27313767697628975564968213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36418356930171967419957617 27313767697628975564968213)
                  ·
                    refine ⟨1280332860826358229607885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27313767697628975564968213 1280332860826358229607885)
                    ·
                      rfl

theorem cell22_3740159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_3740159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740159 prefixEnd_3740159 := by exact prefixLift 3740159
  have htrace : WordTrace (prefixWord ++ tailWord_3740159) baseStart_3740159 baseEnd_3740159 := by
    simpa [prefixWord, tailWord_3740159, baseEnd_3740159] using wordTrace_append hprefix tailTrace_3740159
  have hstable : (prefixWord ++ tailWord_3740159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740159).length < 2 ^ (prefixWord ++ tailWord_3740159).sum := by decide
  have hdescent : baseEnd_3740159 < baseStart_3740159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740167 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 2, 3]
def baseStart_3740167 : Nat := 118140960795 + 3740167 * 2 ^ 59
def prefixEnd_3740167 : Nat := 4983230072969 + 3 ^ 40 * 3740167 * 2
def baseEnd_3740167 : Nat := 1280335599389848875407861

theorem tailTrace_3740167 : CollatzResearch.WordTrace tailWord_3740167 prefixEnd_3740167 1280335599389848875407861 := by
  unfold tailWord_3740167
  simp only [CollatzResearch.WordTrace]
  refine ⟨136415097441021203513658755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90943398294014135675772503 136415097441021203513658755)
  ·
    refine ⟨204622646161531805270488133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136415097441021203513658755 204622646161531805270488133)
    ·
      refine ⟨38366746155287213488216525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204622646161531805270488133 38366746155287213488216525)
      ·
        refine ⟨14387529808232705058081197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38366746155287213488216525 14387529808232705058081197)
        ·
          refine ⟨5395323678087264396780449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14387529808232705058081197 5395323678087264396780449)
          ·
            refine ⟨4046492758565448297585337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395323678087264396780449 4046492758565448297585337)
            ·
              refine ⟨3034869568924086223189003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046492758565448297585337 3034869568924086223189003)
              ·
                refine ⟨4552304353386129334783505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034869568924086223189003 4552304353386129334783505)
                ·
                  refine ⟨3414228265039597001087629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4552304353386129334783505 3414228265039597001087629)
                  ·
                    refine ⟨1280335599389848875407861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414228265039597001087629 1280335599389848875407861)
                    ·
                      rfl

theorem cell22_3740167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_3740167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740167 prefixEnd_3740167 := by exact prefixLift 3740167
  have htrace : WordTrace (prefixWord ++ tailWord_3740167) baseStart_3740167 baseEnd_3740167 := by
    simpa [prefixWord, tailWord_3740167, baseEnd_3740167] using wordTrace_append hprefix tailTrace_3740167
  have hstable : (prefixWord ++ tailWord_3740167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740167).length < 2 ^ (prefixWord ++ tailWord_3740167).sum := by decide
  have hdescent : baseEnd_3740167 < baseStart_3740167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740236 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_3740236 : Nat := 118140960795 + 3740236 * 2 ^ 59
def prefixEnd_3740236 : Nat := 4983230072969 + 3 ^ 40 * 3740236 * 2
def baseEnd_3740236 : Nat := 426786406499985231810883

theorem tailTrace_3740236 : CollatzResearch.WordTrace tailWord_3740236 prefixEnd_3740236 426786406499985231810883 := by
  unfold tailWord_3740236
  simp only [CollatzResearch.WordTrace]
  refine ⟨68208807038885614148960281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90945076051847485531947041 68208807038885614148960281)
  ·
    refine ⟨51156605279164210611720211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68208807038885614148960281 51156605279164210611720211)
    ·
      refine ⟨76734907918746315917580317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51156605279164210611720211 76734907918746315917580317)
      ·
        refine ⟨28775590469529868469092619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76734907918746315917580317 28775590469529868469092619)
        ·
          refine ⟨43163385704294802703638929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28775590469529868469092619 43163385704294802703638929)
          ·
            refine ⟨32372539278221102027729197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43163385704294802703638929 32372539278221102027729197)
            ·
              refine ⟨12139702229332913260398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32372539278221102027729197 12139702229332913260398449)
              ·
                refine ⟨9104776671999684945298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12139702229332913260398449 9104776671999684945298837)
                ·
                  refine ⟨426786406499985231810883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9104776671999684945298837 426786406499985231810883)
                  ·
                    rfl

theorem cell22_3740236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_3740236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740236 prefixEnd_3740236 := by exact prefixLift 3740236
  have htrace : WordTrace (prefixWord ++ tailWord_3740236) baseStart_3740236 baseEnd_3740236 := by
    simpa [prefixWord, tailWord_3740236, baseEnd_3740236] using wordTrace_append hprefix tailTrace_3740236
  have hstable : (prefixWord ++ tailWord_3740236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740236).length < 2 ^ (prefixWord ++ tailWord_3740236).sum := by decide
  have hdescent : baseEnd_3740236 < baseStart_3740236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740270 : List Nat := [4, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_3740270 : Nat := 118140960795 + 3740270 * 2 ^ 59
def prefixEnd_3740270 : Nat := 4983230072969 + 3 ^ 40 * 3740270 * 2
def baseEnd_3740270 : Nat := 426790286131596980027515

theorem tailTrace_3740270 : CollatzResearch.WordTrace tailWord_3740270 prefixEnd_3740270 426790286131596980027515 := by
  unfold tailWord_3740270
  simp only [CollatzResearch.WordTrace]
  refine ⟨17052356769956006513082283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90945902773098701403105509 17052356769956006513082283)
  ·
    refine ⟨25578535154934009769623425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17052356769956006513082283 25578535154934009769623425)
    ·
      refine ⟨19183901366200507327217569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25578535154934009769623425 19183901366200507327217569)
      ·
        refine ⟨14387926024650380495413177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19183901366200507327217569 14387926024650380495413177)
        ·
          refine ⟨10790944518487785371559883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14387926024650380495413177 10790944518487785371559883)
          ·
            refine ⟨16186416777731678057339825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790944518487785371559883 16186416777731678057339825)
            ·
              refine ⟨12139812583298758543004869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16186416777731678057339825 12139812583298758543004869)
              ·
                refine ⟨2276214859368517226813413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12139812583298758543004869 2276214859368517226813413)
                ·
                  refine ⟨426790286131596980027515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276214859368517226813413 426790286131596980027515)
                  ·
                    rfl

theorem cell22_3740270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_3740270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740270 prefixEnd_3740270 := by exact prefixLift 3740270
  have htrace : WordTrace (prefixWord ++ tailWord_3740270) baseStart_3740270 baseEnd_3740270 := by
    simpa [prefixWord, tailWord_3740270, baseEnd_3740270] using wordTrace_append hprefix tailTrace_3740270
  have hstable : (prefixWord ++ tailWord_3740270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740270).length < 2 ^ (prefixWord ++ tailWord_3740270).sum := by decide
  have hdescent : baseEnd_3740270 < baseStart_3740270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740285 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_3740285 : Nat := 118140960795 + 3740285 * 2 ^ 59
def prefixEnd_3740285 : Nat := 4983230072969 + 3 ^ 40 * 3740285 * 2
def baseEnd_3740285 : Nat := 1280375993201335900957499

theorem tailTrace_3740285 : CollatzResearch.WordTrace tailWord_3740285 prefixEnd_3740285 1280375993201335900957499 := by
  unfold tailWord_3740285
  simp only [CollatzResearch.WordTrace]
  refine ⟨136419401254593709666454309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90946267503062473110969539 136419401254593709666454309)
  ·
    refine ⟨25578637735236320562460183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136419401254593709666454309 25578637735236320562460183)
    ·
      refine ⟨38367956602854480843690275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25578637735236320562460183 38367956602854480843690275)
      ·
        refine ⟨57551934904281721265535413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38367956602854480843690275 57551934904281721265535413)
        ·
          refine ⟨5395493897276411368643945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57551934904281721265535413 5395493897276411368643945)
          ·
            refine ⟨4046620422957308526482959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5395493897276411368643945 4046620422957308526482959)
            ·
              refine ⟨6069930634435962789724439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046620422957308526482959 6069930634435962789724439)
              ·
                refine ⟨9104895951653944184586659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069930634435962789724439 9104895951653944184586659)
                ·
                  refine ⟨13657343927480916276879989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9104895951653944184586659 13657343927480916276879989)
                  ·
                    refine ⟨1280375993201335900957499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13657343927480916276879989 1280375993201335900957499)
                    ·
                      rfl

theorem cell22_3740285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_3740285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740285 prefixEnd_3740285 := by exact prefixLift 3740285
  have htrace : WordTrace (prefixWord ++ tailWord_3740285) baseStart_3740285 baseEnd_3740285 := by
    simpa [prefixWord, tailWord_3740285, baseEnd_3740285] using wordTrace_append hprefix tailTrace_3740285
  have hstable : (prefixWord ++ tailWord_3740285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740285).length < 2 ^ (prefixWord ++ tailWord_3740285).sum := by decide
  have hdescent : baseEnd_3740285 < baseStart_3740285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740298 : List Nat := [3, 1, 2, 3, 3, 1, 1, 8]
def baseStart_3740298 : Nat := 118140960795 + 3740298 * 2 ^ 59
def prefixEnd_3740298 : Nat := 4983230072969 + 3 ^ 40 * 3740298 * 2
def baseEnd_3740298 : Nat := 142264493707445355598051

theorem tailTrace_3740298 : CollatzResearch.WordTrace tailWord_3740298 prefixEnd_3740298 142264493707445355598051 := by
  unfold tailWord_3740298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34104968850886653221669387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90946583602364408591118365 34104968850886653221669387)
  ·
    refine ⟨51157453276329979832504081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34104968850886653221669387 51157453276329979832504081)
    ·
      refine ⟨38368089957247484874378061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51157453276329979832504081 38368089957247484874378061)
      ·
        refine ⟨14388033733967806827891773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38368089957247484874378061 14388033733967806827891773)
        ·
          refine ⟨5395512650237927560459415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14388033733967806827891773 5395512650237927560459415)
          ·
            refine ⟨8093268975356891340689123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395512650237927560459415 8093268975356891340689123)
            ·
              refine ⟨12139903463035337011033685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8093268975356891340689123 12139903463035337011033685)
              ·
                refine ⟨142264493707445355598051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12139903463035337011033685 142264493707445355598051)
                ·
                  rfl

theorem cell22_3740298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_3740298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740298 prefixEnd_3740298 := by exact prefixLift 3740298
  have htrace : WordTrace (prefixWord ++ tailWord_3740298) baseStart_3740298 baseEnd_3740298 := by
    simpa [prefixWord, tailWord_3740298, baseEnd_3740298] using wordTrace_append hprefix tailTrace_3740298
  have hstable : (prefixWord ++ tailWord_3740298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740298).length < 2 ^ (prefixWord ++ tailWord_3740298).sum := by decide
  have hdescent : baseEnd_3740298 < baseStart_3740298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740403 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 6, 3]
def baseStart_3740403 : Nat := 118140960795 + 3740403 * 2 ^ 59
def prefixEnd_3740403 : Nat := 4983230072969 + 3 ^ 40 * 3740403 * 2
def baseEnd_3740403 : Nat := 1280416387012822926507137

theorem tailTrace_3740403 : CollatzResearch.WordTrace tailWord_3740403 prefixEnd_3740403 1280416387012822926507137 := by
  unfold tailWord_3740403
  simp only [CollatzResearch.WordTrace]
  refine ⟨136423705068166215819249863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90949136712110810546166575 136423705068166215819249863)
  ·
    refine ⟨204635557602249323728874795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136423705068166215819249863 204635557602249323728874795)
    ·
      refine ⟨306953336403373985593312193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204635557602249323728874795 306953336403373985593312193)
      ·
        refine ⟨230215002302530489194984145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306953336403373985593312193 230215002302530489194984145)
        ·
          refine ⟨172661251726897866896238109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230215002302530489194984145 172661251726897866896238109)
          ·
            refine ⟨64747969397586700086089291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172661251726897866896238109 64747969397586700086089291)
            ·
              refine ⟨97121954096380050129133937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64747969397586700086089291 97121954096380050129133937)
              ·
                refine ⟨72841465572285037596850453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97121954096380050129133937 72841465572285037596850453)
                ·
                  refine ⟨3414443698700861137352365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72841465572285037596850453 3414443698700861137352365)
                  ·
                    refine ⟨1280416387012822926507137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414443698700861137352365 1280416387012822926507137)
                    ·
                      rfl

theorem cell22_3740403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 6, 3].length) (baseStart_3740403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740403 prefixEnd_3740403 := by exact prefixLift 3740403
  have htrace : WordTrace (prefixWord ++ tailWord_3740403) baseStart_3740403 baseEnd_3740403 := by
    simpa [prefixWord, tailWord_3740403, baseEnd_3740403] using wordTrace_append hprefix tailTrace_3740403
  have hstable : (prefixWord ++ tailWord_3740403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740403).length < 2 ^ (prefixWord ++ tailWord_3740403).sum := by decide
  have hdescent : baseEnd_3740403 < baseStart_3740403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740420 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3740420 : Nat := 118140960795 + 3740420 * 2 ^ 59
def prefixEnd_3740420 : Nat := 4983230072969 + 3 ^ 40 * 3740420 * 2
def baseEnd_3740420 : Nat := 1280422206460240548832085

theorem tailTrace_3740420 : CollatzResearch.WordTrace tailWord_3740420 prefixEnd_3740420 1280422206460240548832085 := by
  unfold tailWord_3740420
  simp only [CollatzResearch.WordTrace]
  refine ⟨68212162554552313861309357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90949550072736418481745809 68212162554552313861309357)
  ·
    refine ⟨25579560957957117697991009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68212162554552313861309357 25579560957957117697991009)
    ·
      refine ⟨19184670718467838273493257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25579560957957117697991009 19184670718467838273493257)
      ·
        refine ⟨14388503038850878705119943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19184670718467838273493257 14388503038850878705119943)
        ·
          refine ⟨21582754558276318057679915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14388503038850878705119943 21582754558276318057679915)
          ·
            refine ⟨32374131837414477086519873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21582754558276318057679915 32374131837414477086519873)
            ·
              refine ⟨24280598878060857814889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32374131837414477086519873 24280598878060857814889905)
              ·
                refine ⟨18210449158545643361167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24280598878060857814889905 18210449158545643361167429)
                ·
                  refine ⟨3414459217227308130218893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18210449158545643361167429 3414459217227308130218893)
                  ·
                    refine ⟨1280422206460240548832085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414459217227308130218893 1280422206460240548832085)
                    ·
                      rfl

theorem cell22_3740420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3740420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740420 prefixEnd_3740420 := by exact prefixLift 3740420
  have htrace : WordTrace (prefixWord ++ tailWord_3740420) baseStart_3740420 baseEnd_3740420 := by
    simpa [prefixWord, tailWord_3740420, baseEnd_3740420] using wordTrace_append hprefix tailTrace_3740420
  have hstable : (prefixWord ++ tailWord_3740420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740420).length < 2 ^ (prefixWord ++ tailWord_3740420).sum := by decide
  have hdescent : baseEnd_3740420 < baseStart_3740420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740465 : List Nat := [1, 2, 2, 3, 2, 1, 1, 4, 3, 3]
def baseStart_3740465 : Nat := 118140960795 + 3740465 * 2 ^ 59
def prefixEnd_3740465 : Nat := 4983230072969 + 3 ^ 40 * 3740465 * 2
def baseEnd_3740465 : Nat := 1280437610879875431456947

theorem tailTrace_3740465 : CollatzResearch.WordTrace tailWord_3740465 prefixEnd_3740465 1280437610879875431456947 := by
  unfold tailWord_3740465
  simp only [CollatzResearch.WordTrace]
  refine ⟨136425966393941600408006849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90950644262627733605337899 136425966393941600408006849)
  ·
    refine ⟨102319474795456200306005137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136425966393941600408006849 102319474795456200306005137)
    ·
      refine ⟨76739606096592150229503853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102319474795456200306005137 76739606096592150229503853)
      ·
        refine ⟨28777352286222056336063945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76739606096592150229503853 28777352286222056336063945)
        ·
          refine ⟨21583014214666542252047959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28777352286222056336063945 21583014214666542252047959)
          ·
            refine ⟨32374521321999813378071939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21583014214666542252047959 32374521321999813378071939)
            ·
              refine ⟨48561781982999720067107909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32374521321999813378071939 48561781982999720067107909)
              ·
                refine ⟨9105334121812447512582733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48561781982999720067107909 9105334121812447512582733)
                ·
                  refine ⟨3414500295679667817218525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9105334121812447512582733 3414500295679667817218525)
                  ·
                    refine ⟨1280437610879875431456947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414500295679667817218525 1280437610879875431456947)
                    ·
                      rfl

theorem cell22_3740465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_3740465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740465 prefixEnd_3740465 := by exact prefixLift 3740465
  have htrace : WordTrace (prefixWord ++ tailWord_3740465) baseStart_3740465 baseEnd_3740465 := by
    simpa [prefixWord, tailWord_3740465, baseEnd_3740465] using wordTrace_append hprefix tailTrace_3740465
  have hstable : (prefixWord ++ tailWord_3740465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740465).length < 2 ^ (prefixWord ++ tailWord_3740465).sum := by decide
  have hdescent : baseEnd_3740465 < baseStart_3740465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740484 : List Nat := [2, 3, 4, 2, 2, 1, 8]
def baseStart_3740484 : Nat := 118140960795 + 3740484 * 2 ^ 59
def prefixEnd_3740484 : Nat := 4983230072969 + 3 ^ 40 * 3740484 * 2
def baseEnd_3740484 : Nat := 47423856109932063527107

theorem tailTrace_3740484 : CollatzResearch.WordTrace tailWord_3740484 prefixEnd_3740484 47423856109932063527107 := by
  unfold tailWord_3740484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68213329690436383326474253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90951106253915177768632337 68213329690436383326474253)
  ·
    refine ⟨25579998633913643747427845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68213329690436383326474253 25579998633913643747427845)
    ·
      refine ⟨4796249743858808202642721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25579998633913643747427845 4796249743858808202642721)
      ·
        refine ⟨3597187307894106151982041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796249743858808202642721 3597187307894106151982041)
        ·
          refine ⟨2697890480920579613986531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3597187307894106151982041 2697890480920579613986531)
          ·
            refine ⟨4046835721380869420979797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697890480920579613986531 4046835721380869420979797)
            ·
              refine ⟨47423856109932063527107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4046835721380869420979797 47423856109932063527107)
              ·
                rfl

theorem cell22_3740484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 8].length) (baseStart_3740484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740484 prefixEnd_3740484 := by exact prefixLift 3740484
  have htrace : WordTrace (prefixWord ++ tailWord_3740484) baseStart_3740484 baseEnd_3740484 := by
    simpa [prefixWord, tailWord_3740484, baseEnd_3740484] using wordTrace_append hprefix tailTrace_3740484
  have hstable : (prefixWord ++ tailWord_3740484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740484).length < 2 ^ (prefixWord ++ tailWord_3740484).sum := by decide
  have hdescent : baseEnd_3740484 < baseStart_3740484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740523 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 6]
def baseStart_3740523 : Nat := 118140960795 + 3740523 * 2 ^ 59
def prefixEnd_3740523 : Nat := 4983230072969 + 3 ^ 40 * 3740523 * 2
def baseEnd_3740523 : Nat := 426819155155060871168923

theorem tailTrace_3740523 : CollatzResearch.WordTrace tailWord_3740523 prefixEnd_3740523 426819155155060871168923 := by
  unfold tailWord_3740523
  simp only [CollatzResearch.WordTrace]
  refine ⟨136428081827731476313618223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90952054551820984209078815 136428081827731476313618223)
  ·
    refine ⟨204642122741597214470427335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136428081827731476313618223 204642122741597214470427335)
    ·
      refine ⟨306963184112395821705641003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204642122741597214470427335 306963184112395821705641003)
      ·
        refine ⟨460444776168593732558461505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306963184112395821705641003 460444776168593732558461505)
        ·
          refine ⟨345333582126445299418846129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460444776168593732558461505 345333582126445299418846129)
          ·
            refine ⟨259000186594833974564134597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345333582126445299418846129 259000186594833974564134597)
            ·
              refine ⟨48562534986531370230775237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259000186594833974564134597 48562534986531370230775237)
              ·
                refine ⟨9105475309974631918270357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48562534986531370230775237 9105475309974631918270357)
                ·
                  refine ⟨426819155155060871168923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9105475309974631918270357 426819155155060871168923)
                  ·
                    rfl

theorem cell22_3740523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_3740523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740523 prefixEnd_3740523 := by exact prefixLift 3740523
  have htrace : WordTrace (prefixWord ++ tailWord_3740523) baseStart_3740523 baseEnd_3740523 := by
    simpa [prefixWord, tailWord_3740523, baseEnd_3740523] using wordTrace_append hprefix tailTrace_3740523
  have hstable : (prefixWord ++ tailWord_3740523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740523).length < 2 ^ (prefixWord ++ tailWord_3740523).sum := by decide
  have hdescent : baseEnd_3740523 < baseStart_3740523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740546 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3740546 : Nat := 118140960795 + 3740546 * 2 ^ 59
def prefixEnd_3740546 : Nat := 4983230072969 + 3 ^ 40 * 3740546 * 2
def baseEnd_3740546 : Nat := 426821779611739406727233

theorem tailTrace_3740546 : CollatzResearch.WordTrace tailWord_3740546 prefixEnd_3740546 426821779611739406727233 := by
  unfold tailWord_3740546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34107230176662037810426373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90952613804432100827803661 34107230176662037810426373)
  ·
    refine ⟨6395105658124132089454945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34107230176662037810426373 6395105658124132089454945)
    ·
      refine ⟨4796329243593099067091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6395105658124132089454945 4796329243593099067091209)
      ·
        refine ⟨3597246932694824300318407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796329243593099067091209 3597246932694824300318407)
        ·
          refine ⟨5395870399042236450477611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597246932694824300318407 5395870399042236450477611)
          ·
            refine ⟨8093805598563354675716417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395870399042236450477611 8093805598563354675716417)
            ·
              refine ⟨6070354198922516006787313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8093805598563354675716417 6070354198922516006787313)
              ·
                refine ⟨4552765649191887005090485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6070354198922516006787313 4552765649191887005090485)
                ·
                  refine ⟨426821779611739406727233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4552765649191887005090485 426821779611739406727233)
                  ·
                    rfl

theorem cell22_3740546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3740546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740546 prefixEnd_3740546 := by exact prefixLift 3740546
  have htrace : WordTrace (prefixWord ++ tailWord_3740546) baseStart_3740546 baseEnd_3740546 := by
    simpa [prefixWord, tailWord_3740546, baseEnd_3740546] using wordTrace_append hprefix tailTrace_3740546
  have hstable : (prefixWord ++ tailWord_3740546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740546).length < 2 ^ (prefixWord ++ tailWord_3740546).sum := by decide
  have hdescent : baseEnd_3740546 < baseStart_3740546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740555 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 4, 3]
def baseStart_3740555 : Nat := 118140960795 + 3740555 * 2 ^ 59
def prefixEnd_3740555 : Nat := 4983230072969 + 3 ^ 40 * 3740555 * 2
def baseEnd_3740555 : Nat := 1280468419719145196706671

theorem tailTrace_3740555 : CollatzResearch.WordTrace tailWord_3740555 prefixEnd_3740555 1280468419719145196706671 := by
  unfold tailWord_3740555
  simp only [CollatzResearch.WordTrace]
  refine ⟨136429248963615545778783119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90952832642410363852522079 136429248963615545778783119)
  ·
    refine ⟨204643873445423318668174679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136429248963615545778783119 204643873445423318668174679)
    ·
      refine ⟨306965810168134978002262019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204643873445423318668174679 306965810168134978002262019)
      ·
        refine ⟨460448715252202467003393029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306965810168134978002262019 460448715252202467003393029)
        ·
          refine ⟨86334134109787962563136193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460448715252202467003393029 86334134109787962563136193)
          ·
            refine ⟨64750600582340971922352145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86334134109787962563136193 64750600582340971922352145)
            ·
              refine ⟨48562950436755728941764109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64750600582340971922352145 48562950436755728941764109)
              ·
                refine ⟨18211106413783398353161541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48562950436755728941764109 18211106413783398353161541)
                ·
                  refine ⟨3414582452584387191217789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18211106413783398353161541 3414582452584387191217789)
                  ·
                    refine ⟨1280468419719145196706671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414582452584387191217789 1280468419719145196706671)
                    ·
                      rfl

theorem cell22_3740555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 3].length) (baseStart_3740555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740555 prefixEnd_3740555 := by exact prefixLift 3740555
  have htrace : WordTrace (prefixWord ++ tailWord_3740555) baseStart_3740555 baseEnd_3740555 := by
    simpa [prefixWord, tailWord_3740555, baseEnd_3740555] using wordTrace_append hprefix tailTrace_3740555
  have hstable : (prefixWord ++ tailWord_3740555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740555).length < 2 ^ (prefixWord ++ tailWord_3740555).sum := by decide
  have hdescent : baseEnd_3740555 < baseStart_3740555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740585 : List Nat := [1, 2, 1, 1, 1, 1, 9, 6]
def baseStart_3740585 : Nat := 118140960795 + 3740585 * 2 ^ 59
def prefixEnd_3740585 : Nat := 4983230072969 + 3 ^ 40 * 3740585 * 2
def baseEnd_3740585 : Nat := 142275409925803902050731

theorem tailTrace_3740585 : CollatzResearch.WordTrace tailWord_3740585 prefixEnd_3740585 142275409925803902050731 := by
  unfold tailWord_3740585
  simp only [CollatzResearch.WordTrace]
  refine ⟨136430343153506860902375209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90953562102337907268250139 136430343153506860902375209)
  ·
    refine ⟨102322757365130145676781407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136430343153506860902375209 102322757365130145676781407)
    ·
      refine ⟨153484136047695218515172111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102322757365130145676781407 153484136047695218515172111)
      ·
        refine ⟨230226204071542827772758167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153484136047695218515172111 230226204071542827772758167)
        ·
          refine ⟨345339306107314241659137251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230226204071542827772758167 345339306107314241659137251)
          ·
            refine ⟨518008959160971362488705877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345339306107314241659137251 518008959160971362488705877)
            ·
              refine ⟨3035208745083816577082261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 518008959160971362488705877 3035208745083816577082261)
              ·
                refine ⟨142275409925803902050731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3035208745083816577082261 142275409925803902050731)
                ·
                  rfl

theorem cell22_3740585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 6].length) (baseStart_3740585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740585 prefixEnd_3740585 := by exact prefixLift 3740585
  have htrace : WordTrace (prefixWord ++ tailWord_3740585) baseStart_3740585 baseEnd_3740585 := by
    simpa [prefixWord, tailWord_3740585, baseEnd_3740585] using wordTrace_append hprefix tailTrace_3740585
  have hstable : (prefixWord ++ tailWord_3740585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740585).length < 2 ^ (prefixWord ++ tailWord_3740585).sum := by decide
  have hdescent : baseEnd_3740585 < baseStart_3740585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740707 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_3740707 : Nat := 118140960795 + 3740707 * 2 ^ 59
def prefixEnd_3740707 : Nat := 4983230072969 + 3 ^ 40 * 3740707 * 2
def baseEnd_3740707 : Nat := 1280520452425467466906205

theorem tailTrace_3740707 : CollatzResearch.WordTrace tailWord_3740707 prefixEnd_3740707 1280520452425467466906205 := by
  unfold tailWord_3740707
  simp only [CollatzResearch.WordTrace]
  refine ⟨136434792859064875738316375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90956528572709917158877583 136434792859064875738316375)
  ·
    refine ⟨204652189288597313607474563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136434792859064875738316375 204652189288597313607474563)
    ·
      refine ⟨306978283932895970411211845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204652189288597313607474563 306978283932895970411211845)
      ·
        refine ⟨57558428237417994452102221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 306978283932895970411211845 57558428237417994452102221)
        ·
          refine ⟨21584410589031747919538333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57558428237417994452102221 21584410589031747919538333)
          ·
            refine ⟨8094153970886905469826875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21584410589031747919538333 8094153970886905469826875)
            ·
              refine ⟨12141230956330358204740313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094153970886905469826875 12141230956330358204740313)
              ·
                refine ⟨9105923217247768653555235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12141230956330358204740313 9105923217247768653555235)
                ·
                  refine ⟨13658884825871652980332853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9105923217247768653555235 13658884825871652980332853)
                  ·
                    refine ⟨1280520452425467466906205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13658884825871652980332853 1280520452425467466906205)
                    ·
                      rfl

theorem cell22_3740707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_3740707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740707 prefixEnd_3740707 := by exact prefixLift 3740707
  have htrace : WordTrace (prefixWord ++ tailWord_3740707) baseStart_3740707 baseEnd_3740707 := by
    simpa [prefixWord, tailWord_3740707, baseEnd_3740707] using wordTrace_append hprefix tailTrace_3740707
  have hstable : (prefixWord ++ tailWord_3740707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740707).length < 2 ^ (prefixWord ++ tailWord_3740707).sum := by decide
  have hdescent : baseEnd_3740707 < baseStart_3740707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740722 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3740722 : Nat := 118140960795 + 3740722 * 2 ^ 59
def prefixEnd_3740722 : Nat := 4983230072969 + 3 ^ 40 * 3740722 * 2
def baseEnd_3740722 : Nat := 1280525587232012427781159

theorem tailTrace_3740722 : CollatzResearch.WordTrace tailWord_3740722 prefixEnd_3740722 1280525587232012427781159 := by
  unfold tailWord_3740722
  simp only [CollatzResearch.WordTrace]
  refine ⟨34108834988502633325028105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90956893302673688866741613 34108834988502633325028105)
  ·
    refine ⟨25581626241376974993771079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34108834988502633325028105 25581626241376974993771079)
    ·
      refine ⟨38372439362065462490656619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25581626241376974993771079 38372439362065462490656619)
      ·
        refine ⟨57558659043098193735984929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38372439362065462490656619 57558659043098193735984929)
        ·
          refine ⟨43168994282323645301988697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57558659043098193735984929 43168994282323645301988697)
          ·
            refine ⟨32376745711742733976491523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43168994282323645301988697 32376745711742733976491523)
            ·
              refine ⟨48565118567614100964737285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32376745711742733976491523 48565118567614100964737285)
              ·
                refine ⟨9105959731427643930888241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48565118567614100964737285 9105959731427643930888241)
                ·
                  refine ⟨6829469798570732948166181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9105959731427643930888241 6829469798570732948166181)
                  ·
                    refine ⟨1280525587232012427781159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829469798570732948166181 1280525587232012427781159)
                    ·
                      rfl

theorem cell22_3740722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3740722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740722 prefixEnd_3740722 := by exact prefixLift 3740722
  have htrace : WordTrace (prefixWord ++ tailWord_3740722) baseStart_3740722 baseEnd_3740722 := by
    simpa [prefixWord, tailWord_3740722, baseEnd_3740722] using wordTrace_append hprefix tailTrace_3740722
  have hstable : (prefixWord ++ tailWord_3740722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740722).length < 2 ^ (prefixWord ++ tailWord_3740722).sum := by decide
  have hdescent : baseEnd_3740722 < baseStart_3740722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740726 : List Nat := [5, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_3740726 : Nat := 118140960795 + 3740726 * 2 ^ 59
def prefixEnd_3740726 : Nat := 4983230072969 + 3 ^ 40 * 3740726 * 2
def baseEnd_3740726 : Nat := 426842318837919250227049

theorem tailTrace_3740726 : CollatzResearch.WordTrace tailWord_3740726 prefixEnd_3740726 426842318837919250227049 := by
  unfold tailWord_3740726
  simp only [CollatzResearch.WordTrace]
  refine ⟨8527217865374752623953627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90956990563997361322172021 8527217865374752623953627)
  ·
    refine ⟨12790826798062128935930441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8527217865374752623953627 12790826798062128935930441)
    ·
      refine ⟨9593120098546596701947831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12790826798062128935930441 9593120098546596701947831)
      ·
        refine ⟨14389680147819895052921747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593120098546596701947831 14389680147819895052921747)
        ·
          refine ⟨21584520221729842579382621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14389680147819895052921747 21584520221729842579382621)
          ·
            refine ⟨8094195083148690967268483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21584520221729842579382621 8094195083148690967268483)
            ·
              refine ⟨12141292624723036450902725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094195083148690967268483 12141292624723036450902725)
              ·
                refine ⟨2276492367135569334544261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12141292624723036450902725 2276492367135569334544261)
                ·
                  refine ⟨426842318837919250227049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276492367135569334544261 426842318837919250227049)
                  ·
                    rfl

theorem cell22_3740726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_3740726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740726 prefixEnd_3740726 := by exact prefixLift 3740726
  have htrace : WordTrace (prefixWord ++ tailWord_3740726) baseStart_3740726 baseEnd_3740726 := by
    simpa [prefixWord, tailWord_3740726, baseEnd_3740726] using wordTrace_append hprefix tailTrace_3740726
  have hstable : (prefixWord ++ tailWord_3740726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740726).length < 2 ^ (prefixWord ++ tailWord_3740726).sum := by decide
  have hdescent : baseEnd_3740726 < baseStart_3740726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740735 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_3740735 : Nat := 118140960795 + 3740735 * 2 ^ 59
def prefixEnd_3740735 : Nat := 4983230072969 + 3 ^ 40 * 3740735 * 2
def baseEnd_3740735 : Nat := 1280530037397684727206119

theorem tailTrace_3740735 : CollatzResearch.WordTrace tailWord_3740735 prefixEnd_3740735 1280530037397684727206119 := by
  unfold tailWord_3740735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136435814102963436520335659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90957209401975624346890439 136435814102963436520335659)
  ·
    refine ⟨204653721154445154780503489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136435814102963436520335659 204653721154445154780503489)
    ·
      refine ⟨153490290865833866085377617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204653721154445154780503489 153490290865833866085377617)
      ·
        refine ⟨115117718149375399564033213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153490290865833866085377617 115117718149375399564033213)
        ·
          refine ⟨43169144306015774836512455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115117718149375399564033213 43169144306015774836512455)
          ·
            refine ⟨64753716459023662254768683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43169144306015774836512455 64753716459023662254768683)
            ·
              refine ⟨97130574688535493382153025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64753716459023662254768683 97130574688535493382153025)
              ·
                refine ⟨72847931016401620036614769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97130574688535493382153025 72847931016401620036614769)
                ·
                  refine ⟨54635948262301215027461077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72847931016401620036614769 54635948262301215027461077)
                  ·
                    refine ⟨1280530037397684727206119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54635948262301215027461077 1280530037397684727206119)
                    ·
                      rfl

theorem cell22_3740735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_3740735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740735 prefixEnd_3740735 := by exact prefixLift 3740735
  have htrace : WordTrace (prefixWord ++ tailWord_3740735) baseStart_3740735 baseEnd_3740735 := by
    simpa [prefixWord, tailWord_3740735, baseEnd_3740735] using wordTrace_append hprefix tailTrace_3740735
  have hstable : (prefixWord ++ tailWord_3740735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740735).length < 2 ^ (prefixWord ++ tailWord_3740735).sum := by decide
  have hdescent : baseEnd_3740735 < baseStart_3740735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740754 : List Nat := [3, 2, 2, 1, 3, 2, 3, 6]
def baseStart_3740754 : Nat := 118140960795 + 3740754 * 2 ^ 59
def prefixEnd_3740754 : Nat := 4983230072969 + 3 ^ 40 * 3740754 * 2
def baseEnd_3740754 : Nat := 142281837942886112331229

theorem tailTrace_3740754 : CollatzResearch.WordTrace tailWord_3740754 prefixEnd_3740754 142281837942886112331229 := by
  unfold tailWord_3740754
  simp only [CollatzResearch.WordTrace]
  refine ⟨34109126772473650691319329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90957671393263068510184877 34109126772473650691319329)
  ·
    refine ⟨25581845079355238018489497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34109126772473650691319329 25581845079355238018489497)
    ·
      refine ⟨19186383809516428513867123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25581845079355238018489497 19186383809516428513867123)
      ·
        refine ⟨28779575714274642770800685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19186383809516428513867123 28779575714274642770800685)
        ·
          refine ⟨10792340892852991039050257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28779575714274642770800685 10792340892852991039050257)
          ·
            refine ⟨8094255669639743279287693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10792340892852991039050257 8094255669639743279287693)
            ·
              refine ⟨3035345876114903729732885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8094255669639743279287693 3035345876114903729732885)
              ·
                refine ⟨142281837942886112331229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3035345876114903729732885 142281837942886112331229)
                ·
                  rfl

theorem cell22_3740754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_3740754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740754 prefixEnd_3740754 := by exact prefixLift 3740754
  have htrace : WordTrace (prefixWord ++ tailWord_3740754) baseStart_3740754 baseEnd_3740754 := by
    simpa [prefixWord, tailWord_3740754, baseEnd_3740754] using wordTrace_append hprefix tailTrace_3740754
  have hstable : (prefixWord ++ tailWord_3740754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740754).length < 2 ^ (prefixWord ++ tailWord_3740754).sum := by decide
  have hdescent : baseEnd_3740754 < baseStart_3740754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740786 : List Nat := [3, 2, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_3740786 : Nat := 118140960795 + 3740786 * 2 ^ 59
def prefixEnd_3740786 : Nat := 4983230072969 + 3 ^ 40 * 3740786 * 2
def baseEnd_3740786 : Nat := 1280547495739937594180963

theorem tailTrace_3740786 : CollatzResearch.WordTrace tailWord_3740786 prefixEnd_3740786 1280547495739937594180963 := by
  unfold tailWord_3740786
  simp only [CollatzResearch.WordTrace]
  refine ⟨34109418556444668057610553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90958449483852448153628141 34109418556444668057610553)
  ·
    refine ⟨25582063917333501043207915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34109418556444668057610553 25582063917333501043207915)
    ·
      refine ⟨38373095876000251564811873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25582063917333501043207915 38373095876000251564811873)
      ·
        refine ⟨28779821907000188673608905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38373095876000251564811873 28779821907000188673608905)
        ·
          refine ⟨21584866430250141505206679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28779821907000188673608905 21584866430250141505206679)
          ·
            refine ⟨32377299645375212257810019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21584866430250141505206679 32377299645375212257810019)
            ·
              refine ⟨48565949468062818386715029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32377299645375212257810019 48565949468062818386715029)
              ·
                refine ⟨2276528881315444611877267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48565949468062818386715029 2276528881315444611877267)
                ·
                  refine ⟨3414793321973166917815901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276528881315444611877267 3414793321973166917815901)
                  ·
                    refine ⟨1280547495739937594180963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414793321973166917815901 1280547495739937594180963)
                    ·
                      rfl

theorem cell22_3740786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_3740786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740786 prefixEnd_3740786 := by exact prefixLift 3740786
  have htrace : WordTrace (prefixWord ++ tailWord_3740786) baseStart_3740786 baseEnd_3740786 := by
    simpa [prefixWord, tailWord_3740786, baseEnd_3740786] using wordTrace_append hprefix tailTrace_3740786
  have hstable : (prefixWord ++ tailWord_3740786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740786).length < 2 ^ (prefixWord ++ tailWord_3740786).sum := by decide
  have hdescent : baseEnd_3740786 < baseStart_3740786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740797 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3740797 : Nat := 118140960795 + 3740797 * 2 ^ 59
def prefixEnd_3740797 : Nat := 4983230072969 + 3 ^ 40 * 3740797 * 2
def baseEnd_3740797 : Nat := 1280551261264737232155929

theorem tailTrace_3740797 : CollatzResearch.WordTrace tailWord_3740797 prefixEnd_3740797 1280551261264737232155929 := by
  unfold tailWord_3740797
  simp only [CollatzResearch.WordTrace]
  refine ⟨136438075428738821109092645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90958716952492547406061763 136438075428738821109092645)
  ·
    refine ⟨25582139142888528957954871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136438075428738821109092645 25582139142888528957954871)
    ·
      refine ⟨38373208714332793436932307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25582139142888528957954871 38373208714332793436932307)
      ·
        refine ⟨57559813071499190155398461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38373208714332793436932307 57559813071499190155398461)
        ·
          refine ⟨21584929901812196308274423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57559813071499190155398461 21584929901812196308274423)
          ·
            refine ⟨32377394852718294462411635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21584929901812196308274423 32377394852718294462411635)
            ·
              refine ⟨48566092279077441693617453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32377394852718294462411635 48566092279077441693617453)
              ·
                refine ⟨18212284604654040635106545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48566092279077441693617453 18212284604654040635106545)
                ·
                  refine ⟨13659213453490530476329909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18212284604654040635106545 13659213453490530476329909)
                  ·
                    refine ⟨1280551261264737232155929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13659213453490530476329909 1280551261264737232155929)
                    ·
                      rfl

theorem cell22_3740797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3740797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740797 prefixEnd_3740797 := by exact prefixLift 3740797
  have htrace : WordTrace (prefixWord ++ tailWord_3740797) baseStart_3740797 baseEnd_3740797 := by
    simpa [prefixWord, tailWord_3740797, baseEnd_3740797] using wordTrace_append hprefix tailTrace_3740797
  have hstable : (prefixWord ++ tailWord_3740797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740797).length < 2 ^ (prefixWord ++ tailWord_3740797).sum := by decide
  have hdescent : baseEnd_3740797 < baseStart_3740797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740812 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_3740812 : Nat := 118140960795 + 3740812 * 2 ^ 59
def prefixEnd_3740812 : Nat := 4983230072969 + 3 ^ 40 * 3740812 * 2
def baseEnd_3740812 : Nat := 1280556396071282193030883

theorem tailTrace_3740812 : CollatzResearch.WordTrace tailWord_3740812 prefixEnd_3740812 1280556396071282193030883 := by
  unfold tailWord_3740812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68219311261842239335444345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90959081682456319113925793 68219311261842239335444345)
  ·
    refine ⟨51164483446381679501583259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68219311261842239335444345 51164483446381679501583259)
    ·
      refine ⟨76746725169572519252374889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51164483446381679501583259 76746725169572519252374889)
      ·
        refine ⟨57560043877179389439281167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76746725169572519252374889 57560043877179389439281167)
        ·
          refine ⟨86340065815769084158921751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57560043877179389439281167 86340065815769084158921751)
          ·
            refine ⟨129510098723653626238382627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86340065815769084158921751 129510098723653626238382627)
            ·
              refine ⟨194265148085480439357573941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129510098723653626238382627 194265148085480439357573941)
              ·
                refine ⟨18212357633013791189772557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194265148085480439357573941 18212357633013791189772557)
                ·
                  refine ⟨6829634112380171696164709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18212357633013791189772557 6829634112380171696164709)
                  ·
                    refine ⟨1280556396071282193030883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829634112380171696164709 1280556396071282193030883)
                    ·
                      rfl

theorem cell22_3740812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_3740812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740812 prefixEnd_3740812 := by exact prefixLift 3740812
  have htrace : WordTrace (prefixWord ++ tailWord_3740812) baseStart_3740812 baseEnd_3740812 := by
    simpa [prefixWord, tailWord_3740812, baseEnd_3740812] using wordTrace_append hprefix tailTrace_3740812
  have hstable : (prefixWord ++ tailWord_3740812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740812).length < 2 ^ (prefixWord ++ tailWord_3740812).sum := by decide
  have hdescent : baseEnd_3740812 < baseStart_3740812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740829 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3740829 : Nat := 118140960795 + 3740829 * 2 ^ 59
def prefixEnd_3740829 : Nat := 4983230072969 + 3 ^ 40 * 3740829 * 2
def baseEnd_3740829 : Nat := 1280562215518699815355831

theorem tailTrace_3740829 : CollatzResearch.WordTrace tailWord_3740829 prefixEnd_3740829 1280562215518699815355831 := by
  unfold tailWord_3740829
  simp only [CollatzResearch.WordTrace]
  refine ⟨136439242564622890574257541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90959495043081927049505027 136439242564622890574257541)
  ·
    refine ⟨25582357980866791982673289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136439242564622890574257541 25582357980866791982673289)
    ·
      refine ⟨19186768485650093987004967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25582357980866791982673289 19186768485650093987004967)
      ·
        refine ⟨28780152728475140980507451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19186768485650093987004967 28780152728475140980507451)
        ·
          refine ⟨43170229092712711470761177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28780152728475140980507451 43170229092712711470761177)
          ·
            refine ⟨32377671819534533603070883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43170229092712711470761177 32377671819534533603070883)
            ·
              refine ⟨48566507729301800404606325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32377671819534533603070883 48566507729301800404606325)
              ·
                refine ⟨4553110099622043787931843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48566507729301800404606325 4553110099622043787931843)
                ·
                  refine ⟨6829665149433065681897765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553110099622043787931843 6829665149433065681897765)
                  ·
                    refine ⟨1280562215518699815355831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829665149433065681897765 1280562215518699815355831)
                    ·
                      rfl

theorem cell22_3740829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3740829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740829 prefixEnd_3740829 := by exact prefixLift 3740829
  have htrace : WordTrace (prefixWord ++ tailWord_3740829) baseStart_3740829 baseEnd_3740829 := by
    simpa [prefixWord, tailWord_3740829, baseEnd_3740829] using wordTrace_append hprefix tailTrace_3740829
  have hstable : (prefixWord ++ tailWord_3740829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740829).length < 2 ^ (prefixWord ++ tailWord_3740829).sum := by decide
  have hdescent : baseEnd_3740829 < baseStart_3740829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740872 : List Nat := [2, 1, 3, 1, 2, 1, 4, 8]
def baseStart_3740872 : Nat := 118140960795 + 3740872 * 2 ^ 59
def prefixEnd_3740872 : Nat := 4983230072969 + 3 ^ 40 * 3740872 * 2
def baseEnd_3740872 : Nat := 142286326144162448503411

theorem tailTrace_3740872 : CollatzResearch.WordTrace tailWord_3740872 prefixEnd_3740872 142286326144162448503411 := by
  unfold tailWord_3740872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68220405451733554459036435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90960540602311405945381913 68220405451733554459036435)
  ·
    refine ⟨102330608177600331688554653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68220405451733554459036435 102330608177600331688554653)
    ·
      refine ⟨38373978066600124383207995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102330608177600331688554653 38373978066600124383207995)
      ·
        refine ⟨57560967099900186574811993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38373978066600124383207995 57560967099900186574811993)
        ·
          refine ⟨43170725324925139931108995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57560967099900186574811993 43170725324925139931108995)
          ·
            refine ⟨64756087987387709896663493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43170725324925139931108995 64756087987387709896663493)
            ·
              refine ⟨12141766497635195605624405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64756087987387709896663493 12141766497635195605624405)
              ·
                refine ⟨142286326144162448503411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12141766497635195605624405 142286326144162448503411)
                ·
                  rfl

theorem cell22_3740872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_3740872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740872 prefixEnd_3740872 := by exact prefixLift 3740872
  have htrace : WordTrace (prefixWord ++ tailWord_3740872) baseStart_3740872 baseEnd_3740872 := by
    simpa [prefixWord, tailWord_3740872, baseEnd_3740872] using wordTrace_append hprefix tailTrace_3740872
  have hstable : (prefixWord ++ tailWord_3740872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740872).length < 2 ^ (prefixWord ++ tailWord_3740872).sum := by decide
  have hdescent : baseEnd_3740872 < baseStart_3740872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740874 : List Nat := [3, 1, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3740874 : Nat := 118140960795 + 3740874 * 2 ^ 59
def prefixEnd_3740874 : Nat := 4983230072969 + 3 ^ 40 * 3740874 * 2
def baseEnd_3740874 : Nat := 1280577619938334697980693

theorem tailTrace_3740874 : CollatzResearch.WordTrace tailWord_3740874 prefixEnd_3740874 1280577619938334697980693 := by
  unfold tailWord_3740874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34110220962364965814911419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90960589232973242173097117 34110220962364965814911419)
  ·
    refine ⟨51165331443547448722367129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34110220962364965814911419 51165331443547448722367129)
    ·
      refine ⟨38373998582660586541775347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51165331443547448722367129 38373998582660586541775347)
      ·
        refine ⟨57560997873990879812663021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38373998582660586541775347 57560997873990879812663021)
        ·
          refine ⟨21585374202746579929748633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57560997873990879812663021 21585374202746579929748633)
          ·
            refine ⟨16189030652059934947311475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21585374202746579929748633 16189030652059934947311475)
            ·
              refine ⟨24283545978089902420967213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16189030652059934947311475 24283545978089902420967213)
              ·
                refine ⟨9106329741783713407862705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24283545978089902420967213 9106329741783713407862705)
                ·
                  refine ⟨6829747306337785055897029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9106329741783713407862705 6829747306337785055897029)
                  ·
                    refine ⟨1280577619938334697980693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829747306337785055897029 1280577619938334697980693)
                    ·
                      rfl

theorem cell22_3740874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3740874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740874 prefixEnd_3740874 := by exact prefixLift 3740874
  have htrace : WordTrace (prefixWord ++ tailWord_3740874) baseStart_3740874 baseEnd_3740874 := by
    simpa [prefixWord, tailWord_3740874, baseEnd_3740874] using wordTrace_append hprefix tailTrace_3740874
  have hstable : (prefixWord ++ tailWord_3740874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740874).length < 2 ^ (prefixWord ++ tailWord_3740874).sum := by decide
  have hdescent : baseEnd_3740874 < baseStart_3740874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740968 : List Nat := [2, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_3740968 : Nat := 118140960795 + 3740968 * 2 ^ 59
def prefixEnd_3740968 : Nat := 4983230072969 + 3 ^ 40 * 3740968 * 2
def baseEnd_3740968 : Nat := 426869932686449928710135

theorem tailTrace_3740968 : CollatzResearch.WordTrace tailWord_3740968 prefixEnd_3740968 426869932686449928710135 := by
  unfold tailWord_3740968
  simp only [CollatzResearch.WordTrace]
  refine ⟨68222156155559658656783779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90962874874079544875711705 68222156155559658656783779)
  ·
    refine ⟨102333234233339487985175669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68222156155559658656783779 102333234233339487985175669)
    ·
      refine ⟨9593740709375576998610219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102333234233339487985175669 9593740709375576998610219)
      ·
        refine ⟨14390611064063365497915329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593740709375576998610219 14390611064063365497915329)
        ·
          refine ⟨10792958298047524123436497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14390611064063365497915329 10792958298047524123436497)
          ·
            refine ⟨8094718723535643092577373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10792958298047524123436497 8094718723535643092577373)
            ·
              refine ⟨3035519521325866159716515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8094718723535643092577373 3035519521325866159716515)
              ·
                refine ⟨4553279281988799239574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035519521325866159716515 4553279281988799239574773)
                ·
                  refine ⟨426869932686449928710135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4553279281988799239574773 426869932686449928710135)
                  ·
                    rfl

theorem cell22_3740968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_3740968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740968 prefixEnd_3740968 := by exact prefixLift 3740968
  have htrace : WordTrace (prefixWord ++ tailWord_3740968) baseStart_3740968 baseEnd_3740968 := by
    simpa [prefixWord, tailWord_3740968, baseEnd_3740968] using wordTrace_append hprefix tailTrace_3740968
  have hstable : (prefixWord ++ tailWord_3740968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740968).length < 2 ^ (prefixWord ++ tailWord_3740968).sum := by decide
  have hdescent : baseEnd_3740968 < baseStart_3740968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740979 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 6]
def baseStart_3740979 : Nat := 118140960795 + 3740979 * 2 ^ 59
def prefixEnd_3740979 : Nat := 4983230072969 + 3 ^ 40 * 3740979 * 2
def baseEnd_3740979 : Nat := 426871187861383141368457

theorem tailTrace_3740979 : CollatzResearch.WordTrace tailWord_3740979 prefixEnd_3740979 426871187861383141368457 := by
  unfold tailWord_3740979
  simp only [CollatzResearch.WordTrace]
  refine ⟨136444713514079466192217991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90963142342719644128145327 136444713514079466192217991)
  ·
    refine ⟨204667070271119199288326987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136444713514079466192217991 204667070271119199288326987)
    ·
      refine ⟨307000605406678798932490481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204667070271119199288326987 307000605406678798932490481)
      ·
        refine ⟨230250454055009099199367861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307000605406678798932490481 230250454055009099199367861)
        ·
          refine ⟨21585980067657103049940737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230250454055009099199367861 21585980067657103049940737)
          ·
            refine ⟨16189485050742827287455553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21585980067657103049940737 16189485050742827287455553)
            ·
              refine ⟨12142113788057120465591665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16189485050742827287455553 12142113788057120465591665)
              ·
                refine ⟨9106585341042840349193749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142113788057120465591665 9106585341042840349193749)
                ·
                  refine ⟨426871187861383141368457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9106585341042840349193749 426871187861383141368457)
                  ·
                    rfl

theorem cell22_3740979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_3740979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740979 prefixEnd_3740979 := by exact prefixLift 3740979
  have htrace : WordTrace (prefixWord ++ tailWord_3740979) baseStart_3740979 baseEnd_3740979 := by
    simpa [prefixWord, tailWord_3740979, baseEnd_3740979] using wordTrace_append hprefix tailTrace_3740979
  have hstable : (prefixWord ++ tailWord_3740979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740979).length < 2 ^ (prefixWord ++ tailWord_3740979).sum := by decide
  have hdescent : baseEnd_3740979 < baseStart_3740979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740981 : List Nat := [1, 3, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3740981 : Nat := 118140960795 + 3740981 * 2 ^ 59
def prefixEnd_3740981 : Nat := 4983230072969 + 3 ^ 40 * 3740981 * 2
def baseEnd_3740981 : Nat := 1280614248225022085555365

theorem tailTrace_3740981 : CollatzResearch.WordTrace tailWord_3740981 prefixEnd_3740981 1280614248225022085555365 := by
  unfold tailWord_3740981
  simp only [CollatzResearch.WordTrace]
  refine ⟨136444786460072220533790797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90963190973381480355860531 136444786460072220533790797)
  ·
    refine ⟨51166794922527082700171549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136444786460072220533790797 51166794922527082700171549)
    ·
      refine ⟨19187548095947656012564331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51166794922527082700171549 19187548095947656012564331)
      ·
        refine ⟨28781322143921484018846497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19187548095947656012564331 28781322143921484018846497)
        ·
          refine ⟨21585991607941113014134873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28781322143921484018846497 21585991607941113014134873)
          ·
            refine ⟨16189493705955834760601155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21585991607941113014134873 16189493705955834760601155)
            ·
              refine ⟨24284240558933752140901733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16189493705955834760601155 24284240558933752140901733)
              ·
                refine ⟨4553295104800078526419075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24284240558933752140901733 4553295104800078526419075)
                ·
                  refine ⟨6829942657200117789628613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553295104800078526419075 6829942657200117789628613)
                  ·
                    refine ⟨1280614248225022085555365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6829942657200117789628613 1280614248225022085555365)
                    ·
                      rfl

theorem cell22_3740981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3740981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740981 prefixEnd_3740981 := by exact prefixLift 3740981
  have htrace : WordTrace (prefixWord ++ tailWord_3740981) baseStart_3740981 baseEnd_3740981 := by
    simpa [prefixWord, tailWord_3740981, baseEnd_3740981] using wordTrace_append hprefix tailTrace_3740981
  have hstable : (prefixWord ++ tailWord_3740981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740981).length < 2 ^ (prefixWord ++ tailWord_3740981).sum := by decide
  have hdescent : baseEnd_3740981 < baseStart_3740981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3740989 : List Nat := [1, 4, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3740989 : Nat := 118140960795 + 3740989 * 2 ^ 59
def prefixEnd_3740989 : Nat := 4983230072969 + 3 ^ 40 * 3740989 * 2
def baseEnd_3740989 : Nat := 1280616986788512731355341

theorem tailTrace_3740989 : CollatzResearch.WordTrace tailWord_3740989 prefixEnd_3740989 1280616986788512731355341 := by
  unfold tailWord_3740989
  simp only [CollatzResearch.WordTrace]
  refine ⟨136445078244043237900082021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90963385496028825266721347 136445078244043237900082021)
  ·
    refine ⟨25583452170758107106265379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136445078244043237900082021 25583452170758107106265379)
    ·
      refine ⟨38375178256137160659398069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25583452170758107106265379 38375178256137160659398069)
      ·
        refine ⟨3597672961512858811818569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38375178256137160659398069 3597672961512858811818569)
        ·
          refine ⟨2698254721134644108863927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3597672961512858811818569 2698254721134644108863927)
          ·
            refine ⟨4047382081701966163295891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698254721134644108863927 4047382081701966163295891)
            ·
              refine ⟨6071073122552949244943837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047382081701966163295891 6071073122552949244943837)
              ·
                refine ⟨2276652420957355966853939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6071073122552949244943837 2276652420957355966853939)
                ·
                  refine ⟨3414978631436033950280909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276652420957355966853939 3414978631436033950280909)
                  ·
                    refine ⟨1280616986788512731355341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414978631436033950280909 1280616986788512731355341)
                    ·
                      rfl

theorem cell22_3740989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3740989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3740989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3740989 prefixEnd_3740989 := by exact prefixLift 3740989
  have htrace : WordTrace (prefixWord ++ tailWord_3740989) baseStart_3740989 baseEnd_3740989 := by
    simpa [prefixWord, tailWord_3740989, baseEnd_3740989] using wordTrace_append hprefix tailTrace_3740989
  have hstable : (prefixWord ++ tailWord_3740989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3740989).length < 2 ^ (prefixWord ++ tailWord_3740989).sum := by decide
  have hdescent : baseEnd_3740989 < baseStart_3740989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3740989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741011 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 2, 3]
def baseStart_3741011 : Nat := 118140960795 + 3741011 * 2 ^ 59
def prefixEnd_3741011 : Nat := 4983230072969 + 3 ^ 40 * 3741011 * 2
def baseEnd_3741011 : Nat := 1280624517838112007305273

theorem tailTrace_3741011 : CollatzResearch.WordTrace tailWord_3741011 prefixEnd_3741011 1280624517838112007305273 := by
  unfold tailWord_3741011
  simp only [CollatzResearch.WordTrace]
  refine ⟨136445880649963535657382887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90963920433309023771588591 136445880649963535657382887)
  ·
    refine ⟨204668820974945303486074331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136445880649963535657382887 204668820974945303486074331)
    ·
      refine ⟨307003231462417955229111497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204668820974945303486074331 307003231462417955229111497)
      ·
        refine ⟨230252423596813466421833623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307003231462417955229111497 230252423596813466421833623)
        ·
          refine ⟨345378635395220199632750435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230252423596813466421833623 345378635395220199632750435)
          ·
            refine ⟨518067953092830299449125653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345378635395220199632750435 518067953092830299449125653)
            ·
              refine ⟨24284435301226420286677765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 518067953092830299449125653 24284435301226420286677765)
              ·
                refine ⟨4553331618979953803752081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24284435301226420286677765 4553331618979953803752081)
                ·
                  refine ⟨3414998714234965352814061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553331618979953803752081 3414998714234965352814061)
                  ·
                    refine ⟨1280624517838112007305273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3414998714234965352814061 1280624517838112007305273)
                    ·
                      rfl

theorem cell22_3741011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 2, 3].length) (baseStart_3741011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741011 prefixEnd_3741011 := by exact prefixLift 3741011
  have htrace : WordTrace (prefixWord ++ tailWord_3741011) baseStart_3741011 baseEnd_3741011 := by
    simpa [prefixWord, tailWord_3741011, baseEnd_3741011] using wordTrace_append hprefix tailTrace_3741011
  have hstable : (prefixWord ++ tailWord_3741011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741011).length < 2 ^ (prefixWord ++ tailWord_3741011).sum := by decide
  have hdescent : baseEnd_3741011 < baseStart_3741011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741024 : List Nat := [2, 1, 1, 3, 4, 1, 1, 9]
def baseStart_3741024 : Nat := 118140960795 + 3741024 * 2 ^ 59
def prefixEnd_3741024 : Nat := 4983230072969 + 3 ^ 40 * 3741024 * 2
def baseEnd_3741024 : Nat := 142292107555976034081137

theorem tailTrace_3741024 : CollatzResearch.WordTrace tailWord_3741024 prefixEnd_3741024 142292107555976034081137 := by
  unfold tailWord_3741024
  simp only [CollatzResearch.WordTrace]
  refine ⟨68223177399458219438803063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90964236532610959251737417 68223177399458219438803063)
  ·
    refine ⟨102334766099187329158204595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68223177399458219438803063 102334766099187329158204595)
    ·
      refine ⟨153502149148780993737306893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102334766099187329158204595 153502149148780993737306893)
      ·
        refine ⟨57563305930792872651490085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153502149148780993737306893 57563305930792872651490085)
        ·
          refine ⟨10793119862023663622154391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57563305930792872651490085 10793119862023663622154391)
          ·
            refine ⟨16189679793035495433231587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10793119862023663622154391 16189679793035495433231587)
            ·
              refine ⟨24284519689553243149847381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16189679793035495433231587 24284519689553243149847381)
              ·
                refine ⟨142292107555976034081137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24284519689553243149847381 142292107555976034081137)
                ·
                  rfl

theorem cell22_3741024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_3741024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741024 prefixEnd_3741024 := by exact prefixLift 3741024
  have htrace : WordTrace (prefixWord ++ tailWord_3741024) baseStart_3741024 baseEnd_3741024 := by
    simpa [prefixWord, tailWord_3741024, baseEnd_3741024] using wordTrace_append hprefix tailTrace_3741024
  have hstable : (prefixWord ++ tailWord_3741024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741024).length < 2 ^ (prefixWord ++ tailWord_3741024).sum := by decide
  have hdescent : baseEnd_3741024 < baseStart_3741024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741026 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3741026 : Nat := 118140960795 + 3741026 * 2 ^ 59
def prefixEnd_3741026 : Nat := 4983230072969 + 3 ^ 40 * 3741026 * 2
def baseEnd_3741026 : Nat := 1280629652644656968180227

theorem tailTrace_3741026 : CollatzResearch.WordTrace tailWord_3741026 prefixEnd_3741026 1280629652644656968180227 := by
  unfold tailWord_3741026
  simp only [CollatzResearch.WordTrace]
  refine ⟨34111606936227298304794733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90964285163272795479452621 34111606936227298304794733)
  ·
    refine ⟨12791852601085236864298025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34111606936227298304794733 12791852601085236864298025)
    ·
      refine ⟨9593889450813927648223519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12791852601085236864298025 9593889450813927648223519)
      ·
        refine ⟨14390834176220891472335279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9593889450813927648223519 14390834176220891472335279)
        ·
          refine ⟨21586251264331337208502919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14390834176220891472335279 21586251264331337208502919)
          ·
            refine ⟨32379376896497005812754379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21586251264331337208502919 32379376896497005812754379)
            ·
              refine ⟨48569065344745508719131569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32379376896497005812754379 48569065344745508719131569)
              ·
                refine ⟨36426799008559131539348677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48569065344745508719131569 36426799008559131539348677)
                ·
                  refine ⟨6830024814104837163627877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36426799008559131539348677 6830024814104837163627877)
                  ·
                    refine ⟨1280629652644656968180227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830024814104837163627877 1280629652644656968180227)
                    ·
                      rfl

theorem cell22_3741026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3741026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741026 prefixEnd_3741026 := by exact prefixLift 3741026
  have htrace : WordTrace (prefixWord ++ tailWord_3741026) baseStart_3741026 baseEnd_3741026 := by
    simpa [prefixWord, tailWord_3741026, baseEnd_3741026] using wordTrace_append hprefix tailTrace_3741026
  have hstable : (prefixWord ++ tailWord_3741026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741026).length < 2 ^ (prefixWord ++ tailWord_3741026).sum := by decide
  have hdescent : baseEnd_3741026 < baseStart_3741026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741028 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3741028 : Nat := 118140960795 + 3741028 * 2 ^ 59
def prefixEnd_3741028 : Nat := 4983230072969 + 3 ^ 40 * 3741028 * 2
def baseEnd_3741028 : Nat := 1280630337285529629630221

theorem tailTrace_3741028 : CollatzResearch.WordTrace tailWord_3741028 prefixEnd_3741028 1280630337285529629630221 := by
  unfold tailWord_3741028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68223250345450973780375869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90964333793934631707167825 68223250345450973780375869)
  ·
    refine ⟨25583718879544115167640951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68223250345450973780375869 25583718879544115167640951)
    ·
      refine ⟨38375578319316172751461427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25583718879544115167640951 38375578319316172751461427)
      ·
        refine ⟨57563367478974259127192141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38375578319316172751461427 57563367478974259127192141)
        ·
          refine ⟨21586262804615347172697053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57563367478974259127192141 21586262804615347172697053)
          ·
            refine ⟨8094848551730755189761395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21586262804615347172697053 8094848551730755189761395)
            ·
              refine ⟨12142272827596132784642093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8094848551730755189761395 12142272827596132784642093)
              ·
                refine ⟨4553352310348549794240785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12142272827596132784642093 4553352310348549794240785)
                ·
                  refine ⟨3415014232761412345680589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553352310348549794240785 3415014232761412345680589)
                  ·
                    refine ⟨1280630337285529629630221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415014232761412345680589 1280630337285529629630221)
                    ·
                      rfl

theorem cell22_3741028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3741028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741028 prefixEnd_3741028 := by exact prefixLift 3741028
  have htrace : WordTrace (prefixWord ++ tailWord_3741028) baseStart_3741028 baseEnd_3741028 := by
    simpa [prefixWord, tailWord_3741028, baseEnd_3741028] using wordTrace_append hprefix tailTrace_3741028
  have hstable : (prefixWord ++ tailWord_3741028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741028).length < 2 ^ (prefixWord ++ tailWord_3741028).sum := by decide
  have hdescent : baseEnd_3741028 < baseStart_3741028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741073 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_3741073 : Nat := 118140960795 + 3741073 * 2 ^ 59
def prefixEnd_3741073 : Nat := 4983230072969 + 3 ^ 40 * 3741073 * 2
def baseEnd_3741073 : Nat := 1280645741705164512255083

theorem tailTrace_3741073 : CollatzResearch.WordTrace tailWord_3741073 prefixEnd_3741073 1280645741705164512255083 := by
  unfold tailWord_3741073
  simp only [CollatzResearch.WordTrace]
  refine ⟨136448141975738920246139873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90965427983825946830759915 136448141975738920246139873)
  ·
    refine ⟨102336106481804190184604905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136448141975738920246139873 102336106481804190184604905)
    ·
      refine ⟨76752079861353142638453679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102336106481804190184604905 76752079861353142638453679)
      ·
        refine ⟨115128119792029713957680519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76752079861353142638453679 115128119792029713957680519)
        ·
          refine ⟨172692179688044570936520779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115128119792029713957680519 172692179688044570936520779)
          ·
            refine ⟨259038269532066856404781169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172692179688044570936520779 259038269532066856404781169)
            ·
              refine ⟨194278702149050142303585877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259038269532066856404781169 194278702149050142303585877)
              ·
                refine ⟨2276703540809181355120147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194278702149050142303585877 2276703540809181355120147)
                ·
                  refine ⟨3415055311213772032680221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2276703540809181355120147 3415055311213772032680221)
                  ·
                    refine ⟨1280645741705164512255083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415055311213772032680221 1280645741705164512255083)
                    ·
                      rfl

theorem cell22_3741073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_3741073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741073 prefixEnd_3741073 := by exact prefixLift 3741073
  have htrace : WordTrace (prefixWord ++ tailWord_3741073) baseStart_3741073 baseEnd_3741073 := by
    simpa [prefixWord, tailWord_3741073, baseEnd_3741073] using wordTrace_append hprefix tailTrace_3741073
  have hstable : (prefixWord ++ tailWord_3741073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741073).length < 2 ^ (prefixWord ++ tailWord_3741073).sum := by decide
  have hdescent : baseEnd_3741073 < baseStart_3741073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741176 : List Nat := [2, 1, 2, 1, 1, 7, 8]
def baseStart_3741176 : Nat := 118140960795 + 3741176 * 2 ^ 59
def prefixEnd_3741176 : Nat := 4983230072969 + 3 ^ 40 * 3741176 * 2
def baseEnd_3741176 : Nat := 47432629655929873219621

theorem tailTrace_3741176 : CollatzResearch.WordTrace tailWord_3741176 prefixEnd_3741176 47432629655929873219621 := by
  unfold tailWord_3741176
  simp only [CollatzResearch.WordTrace]
  refine ⟨68225949347182884418569691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90967932462910512558092921 68225949347182884418569691)
  ·
    refine ⟨102338924020774326627854537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68225949347182884418569691 102338924020774326627854537)
    ·
      refine ⟨76754193015580744970890903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102338924020774326627854537 76754193015580744970890903)
      ·
        refine ⟨115131289523371117456336355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76754193015580744970890903 115131289523371117456336355)
        ·
          refine ⟨172696934285056676184504533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115131289523371117456336355 172696934285056676184504533)
          ·
            refine ⟨4047584397306015848074325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 172696934285056676184504533 4047584397306015848074325)
            ·
              refine ⟨47432629655929873219621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4047584397306015848074325 47432629655929873219621)
              ·
                rfl

theorem cell22_3741176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 8].length) (baseStart_3741176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741176 prefixEnd_3741176 := by exact prefixLift 3741176
  have htrace : WordTrace (prefixWord ++ tailWord_3741176) baseStart_3741176 baseEnd_3741176 := by
    simpa [prefixWord, tailWord_3741176, baseEnd_3741176] using wordTrace_append hprefix tailTrace_3741176
  have hstable : (prefixWord ++ tailWord_3741176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741176).length < 2 ^ (prefixWord ++ tailWord_3741176).sum := by decide
  have hdescent : baseEnd_3741176 < baseStart_3741176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741182 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_3741182 : Nat := 118140960795 + 3741182 * 2 ^ 59
def prefixEnd_3741182 : Nat := 4983230072969 + 3 ^ 40 * 3741182 * 2
def baseEnd_3741182 : Nat := 426894351544241520426583

theorem tailTrace_3741182 : CollatzResearch.WordTrace tailWord_3741182 prefixEnd_3741182 426894351544241520426583 := by
  unfold tailWord_3741182
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056514691543003982732225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90968078354896021241238533 17056514691543003982732225)
  ·
    refine ⟨12792386018657252987049169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17056514691543003982732225 12792386018657252987049169)
    ·
      refine ⟨9594289513992939740286877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12792386018657252987049169 9594289513992939740286877)
      ·
        refine ⟨3597858567747352402607579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9594289513992939740286877 3597858567747352402607579)
        ·
          refine ⟨5396787851621028603911369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597858567747352402607579 5396787851621028603911369)
          ·
            refine ⟨4047590888715771452933527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396787851621028603911369 4047590888715771452933527)
            ·
              refine ⟨6071386333073657179400291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047590888715771452933527 6071386333073657179400291)
              ·
                refine ⟨9107079499610485769100437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071386333073657179400291 9107079499610485769100437)
                ·
                  refine ⟨426894351544241520426583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9107079499610485769100437 426894351544241520426583)
                  ·
                    rfl

theorem cell22_3741182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_3741182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741182 prefixEnd_3741182 := by exact prefixLift 3741182
  have htrace : WordTrace (prefixWord ++ tailWord_3741182) baseStart_3741182 baseEnd_3741182 := by
    simpa [prefixWord, tailWord_3741182, baseEnd_3741182] using wordTrace_append hprefix tailTrace_3741182
  have hstable : (prefixWord ++ tailWord_3741182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741182).length < 2 ^ (prefixWord ++ tailWord_3741182).sum := by decide
  have hdescent : baseEnd_3741182 < baseStart_3741182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741214 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3741214 : Nat := 118140960795 + 3741214 * 2 ^ 59
def prefixEnd_3741214 : Nat := 4983230072969 + 3 ^ 40 * 3741214 * 2
def baseEnd_3741214 : Nat := 1280694008886687144479651

theorem tailTrace_3741214 : CollatzResearch.WordTrace tailWord_3741214 prefixEnd_3741214 1280694008886687144479651 := by
  unfold tailWord_3741214
  simp only [CollatzResearch.WordTrace]
  refine ⟨17056660583528512665877837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90968856445485400884681797 17056660583528512665877837)
  ·
    refine ⟨6396247718823192249704189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17056660583528512665877837 6396247718823192249704189)
    ·
      refine ⟨2398592894558697093639071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6396247718823192249704189 2398592894558697093639071)
      ·
        refine ⟨3597889341838045640458607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398592894558697093639071 3597889341838045640458607)
        ·
          refine ⟨5396834012757068460687911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597889341838045640458607 5396834012757068460687911)
          ·
            refine ⟨8095251019135602691031867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396834012757068460687911 8095251019135602691031867)
            ·
              refine ⟨12142876528703404036547801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095251019135602691031867 12142876528703404036547801)
              ·
                refine ⟨9107157396527553027410851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12142876528703404036547801 9107157396527553027410851)
                ·
                  refine ⟨13660736094791329541116277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107157396527553027410851 13660736094791329541116277)
                  ·
                    refine ⟨1280694008886687144479651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13660736094791329541116277 1280694008886687144479651)
                    ·
                      rfl

theorem cell22_3741214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3741214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741214 prefixEnd_3741214 := by exact prefixLift 3741214
  have htrace : WordTrace (prefixWord ++ tailWord_3741214) baseStart_3741214 baseEnd_3741214 := by
    simpa [prefixWord, tailWord_3741214, baseEnd_3741214] using wordTrace_append hprefix tailTrace_3741214
  have hstable : (prefixWord ++ tailWord_3741214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741214).length < 2 ^ (prefixWord ++ tailWord_3741214).sum := by decide
  have hdescent : baseEnd_3741214 < baseStart_3741214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741268 : List Nat := [2, 4, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_3741268 : Nat := 118140960795 + 3741268 * 2 ^ 59
def prefixEnd_3741268 : Nat := 4983230072969 + 3 ^ 40 * 3741268 * 2
def baseEnd_3741268 : Nat := 1280712494190249003629485

theorem tailTrace_3741268 : CollatzResearch.WordTrace tailWord_3741268 prefixEnd_3741268 1280712494190249003629485 := by
  unfold tailWord_3741268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68227627105016234274744229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90970169473354979032992305 68227627105016234274744229)
  ·
    refine ⟨12792680082190543926514543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68227627105016234274744229 12792680082190543926514543)
    ·
      refine ⟨19189020123285815889771815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12792680082190543926514543 19189020123285815889771815)
      ·
        refine ⟨28783530184928723834657723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19189020123285815889771815 28783530184928723834657723)
        ·
          refine ⟨43175295277393085751986585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28783530184928723834657723 43175295277393085751986585)
          ·
            refine ⟨32381471458044814313989939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43175295277393085751986585 32381471458044814313989939)
            ·
              refine ⟨48572207187067221470984909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381471458044814313989939 48572207187067221470984909)
              ·
                refine ⟨18214577695150208051619341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48572207187067221470984909 18214577695150208051619341)
                ·
                  refine ⟨6830466635681328019357253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18214577695150208051619341 6830466635681328019357253)
                  ·
                    refine ⟨1280712494190249003629485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830466635681328019357253 1280712494190249003629485)
                    ·
                      rfl

theorem cell22_3741268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_3741268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741268 prefixEnd_3741268 := by exact prefixLift 3741268
  have htrace : WordTrace (prefixWord ++ tailWord_3741268) baseStart_3741268 baseEnd_3741268 := by
    simpa [prefixWord, tailWord_3741268, baseEnd_3741268] using wordTrace_append hprefix tailTrace_3741268
  have hstable : (prefixWord ++ tailWord_3741268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741268).length < 2 ^ (prefixWord ++ tailWord_3741268).sum := by decide
  have hdescent : baseEnd_3741268 < baseStart_3741268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741285 : List Nat := [1, 3, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3741285 : Nat := 118140960795 + 3741285 * 2 ^ 59
def prefixEnd_3741285 : Nat := 4983230072969 + 3 ^ 40 * 3741285 * 2
def baseEnd_3741285 : Nat := 1280718313637666625954433

theorem tailTrace_3741285 : CollatzResearch.WordTrace tailWord_3741285 prefixEnd_3741285 1280718313637666625954433 := by
  unfold tailWord_3741285
  simp only [CollatzResearch.WordTrace]
  refine ⟨136455874250970880452857309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90970582833980586968571539 136455874250970880452857309)
  ·
    refine ⟨51170952844114080169821491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136455874250970880452857309 51170952844114080169821491)
    ·
      refine ⟨76756429266171120254732237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51170952844114080169821491 76756429266171120254732237)
      ·
        refine ⟨28783660974814170095524589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76756429266171120254732237 28783660974814170095524589)
        ·
          refine ⟨10793872865555313785821721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28783660974814170095524589 10793872865555313785821721)
          ·
            refine ⟨8095404649166485339366291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793872865555313785821721 8095404649166485339366291)
            ·
              refine ⟨12143106973749728009049437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095404649166485339366291 12143106973749728009049437)
              ·
                refine ⟨4553665115156148003393539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12143106973749728009049437 4553665115156148003393539)
                ·
                  refine ⟨6830497672734222005090309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4553665115156148003393539 6830497672734222005090309)
                  ·
                    refine ⟨1280718313637666625954433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6830497672734222005090309 1280718313637666625954433)
                    ·
                      rfl

theorem cell22_3741285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3741285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741285 prefixEnd_3741285 := by exact prefixLift 3741285
  have htrace : WordTrace (prefixWord ++ tailWord_3741285) baseStart_3741285 baseEnd_3741285 := by
    simpa [prefixWord, tailWord_3741285, baseEnd_3741285] using wordTrace_append hprefix tailTrace_3741285
  have hstable : (prefixWord ++ tailWord_3741285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741285).length < 2 ^ (prefixWord ++ tailWord_3741285).sum := by decide
  have hdescent : baseEnd_3741285 < baseStart_3741285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741313 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3741313 : Nat := 118140960795 + 3741313 * 2 ^ 59
def prefixEnd_3741313 : Nat := 4983230072969 + 3 ^ 40 * 3741313 * 2
def baseEnd_3741313 : Nat := 1280727898609883886254347

theorem tailTrace_3741313 : CollatzResearch.WordTrace tailWord_3741313 prefixEnd_3741313 1280727898609883886254347 := by
  unfold tailWord_3741313
  simp only [CollatzResearch.WordTrace]
  refine ⟨136456895494869441234876593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90971263663246294156584395 136456895494869441234876593)
  ·
    refine ⟨102342671621152080926157445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136456895494869441234876593 102342671621152080926157445)
    ·
      refine ⟨19189250928966015173654521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102342671621152080926157445 19189250928966015173654521)
      ·
        refine ⟨14391938196724511380240891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19189250928966015173654521 14391938196724511380240891)
        ·
          refine ⟨21587907295086767070361337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391938196724511380240891 21587907295086767070361337)
          ·
            refine ⟨16190930471315075302771003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21587907295086767070361337 16190930471315075302771003)
            ·
              refine ⟨24286395706972612954156505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16190930471315075302771003 24286395706972612954156505)
              ·
                refine ⟨18214796780229459715617379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24286395706972612954156505 18214796780229459715617379)
                ·
                  refine ⟨27322195170344189573426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18214796780229459715617379 27322195170344189573426069)
                  ·
                    refine ⟨1280727898609883886254347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27322195170344189573426069 1280727898609883886254347)
                    ·
                      rfl

theorem cell22_3741313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3741313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741313 prefixEnd_3741313 := by exact prefixLift 3741313
  have htrace : WordTrace (prefixWord ++ tailWord_3741313) baseStart_3741313 baseEnd_3741313 := by
    simpa [prefixWord, tailWord_3741313, baseEnd_3741313] using wordTrace_append hprefix tailTrace_3741313
  have hstable : (prefixWord ++ tailWord_3741313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741313).length < 2 ^ (prefixWord ++ tailWord_3741313).sum := by decide
  have hdescent : baseEnd_3741313 < baseStart_3741313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741360 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_3741360 : Nat := 118140960795 + 3741360 * 2 ^ 59
def prefixEnd_3741360 : Nat := 4983230072969 + 3 ^ 40 * 3741360 * 2
def baseEnd_3741360 : Nat := 1280743987670391430329203

theorem tailTrace_3741360 : CollatzResearch.WordTrace tailWord_3741360 prefixEnd_3741360 1280743987670391430329203 := by
  unfold tailWord_3741360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68229304862849584130918767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90972406483799445507891689 68229304862849584130918767)
  ·
    refine ⟨102343957294274376196378151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68229304862849584130918767 102343957294274376196378151)
    ·
      refine ⟨153515935941411564294567227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102343957294274376196378151 153515935941411564294567227)
      ·
        refine ⟨230273903912117346441850841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153515935941411564294567227 230273903912117346441850841)
        ·
          refine ⟨172705427934088009831388131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230273903912117346441850841 172705427934088009831388131)
          ·
            refine ⟨259058141901132014747082197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172705427934088009831388131 259058141901132014747082197)
            ·
              refine ⟨6071675200807781595634739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259058141901132014747082197 6071675200807781595634739)
              ·
                refine ⟨9107512801211672393452109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6071675200807781595634739 9107512801211672393452109)
                ·
                  refine ⟨3415317300454377147544541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9107512801211672393452109 3415317300454377147544541)
                  ·
                    refine ⟨1280743987670391430329203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415317300454377147544541 1280743987670391430329203)
                    ·
                      rfl

theorem cell22_3741360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_3741360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741360 prefixEnd_3741360 := by exact prefixLift 3741360
  have htrace : WordTrace (prefixWord ++ tailWord_3741360) baseStart_3741360 baseEnd_3741360 := by
    simpa [prefixWord, tailWord_3741360, baseEnd_3741360] using wordTrace_append hprefix tailTrace_3741360
  have hstable : (prefixWord ++ tailWord_3741360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741360).length < 2 ^ (prefixWord ++ tailWord_3741360).sum := by decide
  have hdescent : baseEnd_3741360 < baseStart_3741360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741366 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3741366 : Nat := 118140960795 + 3741366 * 2 ^ 59
def prefixEnd_3741366 : Nat := 4983230072969 + 3 ^ 40 * 3741366 * 2
def baseEnd_3741366 : Nat := 1280746041593009414679185

theorem tailTrace_3741366 : CollatzResearch.WordTrace tailWord_3741366 prefixEnd_3741366 1280746041593009414679185 := by
  unfold tailWord_3741366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8528676785229839455409747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 90972552375784954191037301 8528676785229839455409747)
  ·
    refine ⟨12793015177844759183114621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8528676785229839455409747 12793015177844759183114621)
    ·
      refine ⟨4797380691691784693667983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12793015177844759183114621 4797380691691784693667983)
      ·
        refine ⟨7196071037537677040501975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4797380691691784693667983 7196071037537677040501975)
        ·
          refine ⟨10794106556306515560752963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196071037537677040501975 10794106556306515560752963)
          ·
            refine ⟨16191159834459773341129445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10794106556306515560752963 16191159834459773341129445)
            ·
              refine ⟨3035842468961207501461771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16191159834459773341129445 3035842468961207501461771)
              ·
                refine ⟨4553763703441811252192657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035842468961207501461771 4553763703441811252192657)
                ·
                  refine ⟨3415322777581358439144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553763703441811252192657 3415322777581358439144493)
                  ·
                    refine ⟨1280746041593009414679185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415322777581358439144493 1280746041593009414679185)
                    ·
                      rfl

theorem cell22_3741366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3741366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741366 prefixEnd_3741366 := by exact prefixLift 3741366
  have htrace : WordTrace (prefixWord ++ tailWord_3741366) baseStart_3741366 baseEnd_3741366 := by
    simpa [prefixWord, tailWord_3741366, baseEnd_3741366] using wordTrace_append hprefix tailTrace_3741366
  have hstable : (prefixWord ++ tailWord_3741366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741366).length < 2 ^ (prefixWord ++ tailWord_3741366).sum := by decide
  have hdescent : baseEnd_3741366 < baseStart_3741366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741450 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3741450 : Nat := 118140960795 + 3741450 * 2 ^ 59
def prefixEnd_3741450 : Nat := 4983230072969 + 3 ^ 40 * 3741450 * 2
def baseEnd_3741450 : Nat := 1280774796509661195578927

theorem tailTrace_3741450 : CollatzResearch.WordTrace tailWord_3741450 prefixEnd_3741450 1280774796509661195578927 := by
  unfold tailWord_3741450
  simp only [CollatzResearch.WordTrace]
  refine ⟨34115473073843278408153451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90974594863582075755075869 34115473073843278408153451)
  ·
    refine ⟨51173209610764917612230177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34115473073843278408153451 51173209610764917612230177)
    ·
      refine ⟨38379907208073688209172633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51173209610764917612230177 38379907208073688209172633)
      ·
        refine ⟨28784930406055266156879475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38379907208073688209172633 28784930406055266156879475)
        ·
          refine ⟨43177395609082899235319213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28784930406055266156879475 43177395609082899235319213)
          ·
            refine ⟨16191523353406087213244705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43177395609082899235319213 16191523353406087213244705)
            ·
              refine ⟨12143642515054565409933529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16191523353406087213244705 12143642515054565409933529)
              ·
                refine ⟨9107731886290924057450147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12143642515054565409933529 9107731886290924057450147)
                ·
                  refine ⟨13661597829436386086175221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9107731886290924057450147 13661597829436386086175221)
                  ·
                    refine ⟨1280774796509661195578927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13661597829436386086175221 1280774796509661195578927)
                    ·
                      rfl

theorem cell22_3741450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3741450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741450 prefixEnd_3741450 := by exact prefixLift 3741450
  have htrace : WordTrace (prefixWord ++ tailWord_3741450) baseStart_3741450 baseEnd_3741450 := by
    simpa [prefixWord, tailWord_3741450, baseEnd_3741450] using wordTrace_append hprefix tailTrace_3741450
  have hstable : (prefixWord ++ tailWord_3741450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741450).length < 2 ^ (prefixWord ++ tailWord_3741450).sum := by decide
  have hdescent : baseEnd_3741450 < baseStart_3741450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741484 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_3741484 : Nat := 118140960795 + 3741484 * 2 ^ 59
def prefixEnd_3741484 : Nat := 4983230072969 + 3 ^ 40 * 3741484 * 2
def baseEnd_3741484 : Nat := 1280786435404496440228823

theorem tailTrace_3741484 : CollatzResearch.WordTrace tailWord_3741484 prefixEnd_3741484 1280786435404496440228823 := by
  unfold tailWord_3741484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68231566188624968719675753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90975421584833291626234337 68231566188624968719675753)
  ·
    refine ⟨51173674641468726539756815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68231566188624968719675753 51173674641468726539756815)
    ·
      refine ⟨76760511962203089809635223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51173674641468726539756815 76760511962203089809635223)
      ·
        refine ⟨115140767943304634714452835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76760511962203089809635223 115140767943304634714452835)
        ·
          refine ⟨172711151914956952071679253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115140767943304634714452835 172711151914956952071679253)
          ·
            refine ⟨8095835246013607128359965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 172711151914956952071679253 8095835246013607128359965)
            ·
              refine ⟨3035938217255102673134987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8095835246013607128359965 3035938217255102673134987)
              ·
                refine ⟨4553907325882654009702481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035938217255102673134987 4553907325882654009702481)
                ·
                  refine ⟨3415430494411990507276861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4553907325882654009702481 3415430494411990507276861)
                  ·
                    refine ⟨1280786435404496440228823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415430494411990507276861 1280786435404496440228823)
                    ·
                      rfl

theorem cell22_3741484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_3741484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741484 prefixEnd_3741484 := by exact prefixLift 3741484
  have htrace : WordTrace (prefixWord ++ tailWord_3741484) baseStart_3741484 baseEnd_3741484 := by
    simpa [prefixWord, tailWord_3741484, baseEnd_3741484] using wordTrace_append hprefix tailTrace_3741484
  have hstable : (prefixWord ++ tailWord_3741484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741484).length < 2 ^ (prefixWord ++ tailWord_3741484).sum := by decide
  have hdescent : baseEnd_3741484 < baseStart_3741484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741495 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 5, 3]
def baseStart_3741495 : Nat := 118140960795 + 3741495 * 2 ^ 59
def prefixEnd_3741495 : Nat := 4983230072969 + 3 ^ 40 * 3741495 * 2
def baseEnd_3741495 : Nat := 1280790200929296078203789

theorem tailTrace_3741495 : CollatzResearch.WordTrace tailWord_3741495 prefixEnd_3741495 1280790200929296078203789 := by
  unfold tailWord_3741495
  simp only [CollatzResearch.WordTrace]
  refine ⟨136463533580210086318001939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90975689053473390878667959 136463533580210086318001939)
  ·
    refine ⟨204695300370315129477002909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136463533580210086318001939 204695300370315129477002909)
    ·
      refine ⟨76760737638868173553876091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204695300370315129477002909 76760737638868173553876091)
      ·
        refine ⟨115141106458302260330814137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76760737638868173553876091 115141106458302260330814137)
        ·
          refine ⟨86355829843726695248110603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115141106458302260330814137 86355829843726695248110603)
          ·
            refine ⟨129533744765590042872165905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86355829843726695248110603 129533744765590042872165905)
            ·
              refine ⟨97150308574192532154124429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129533744765590042872165905 97150308574192532154124429)
              ·
                refine ⟨36431365715322199557796661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97150308574192532154124429 36431365715322199557796661)
                ·
                  refine ⟨3415440535811456208543437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36431365715322199557796661 3415440535811456208543437)
                  ·
                    refine ⟨1280790200929296078203789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415440535811456208543437 1280790200929296078203789)
                    ·
                      rfl

theorem cell22_3741495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_3741495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741495 prefixEnd_3741495 := by exact prefixLift 3741495
  have htrace : WordTrace (prefixWord ++ tailWord_3741495) baseStart_3741495 baseEnd_3741495 := by
    simpa [prefixWord, tailWord_3741495, baseEnd_3741495] using wordTrace_append hprefix tailTrace_3741495
  have hstable : (prefixWord ++ tailWord_3741495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741495).length < 2 ^ (prefixWord ++ tailWord_3741495).sum := by decide
  have hdescent : baseEnd_3741495 < baseStart_3741495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741497 : List Nat := [1, 2, 1, 7, 1, 1, 1, 8]
def baseStart_3741497 : Nat := 118140960795 + 3741497 * 2 ^ 59
def prefixEnd_3741497 : Nat := 4983230072969 + 3 ^ 40 * 3741497 * 2
def baseEnd_3741497 : Nat := 142310098396685415517087

theorem tailTrace_3741497 : CollatzResearch.WordTrace tailWord_3741497 prefixEnd_3741497 142310098396685415517087 := by
  unfold tailWord_3741497
  simp only [CollatzResearch.WordTrace]
  refine ⟨136463606526202840659574745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90975737684135227106383163 136463606526202840659574745)
  ·
    refine ⟨102347704894652130494681059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136463606526202840659574745 102347704894652130494681059)
    ·
      refine ⟨153521557341978195742021589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102347704894652130494681059 153521557341978195742021589)
      ·
        refine ⟨3598161500202613962703631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 153521557341978195742021589 3598161500202613962703631)
        ·
          refine ⟨5397242250303920944055447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598161500202613962703631 5397242250303920944055447)
          ·
            refine ⟨8095863375455881416083171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397242250303920944055447 8095863375455881416083171)
            ·
              refine ⟨12143795063183822124124757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8095863375455881416083171 12143795063183822124124757)
              ·
                refine ⟨142310098396685415517087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12143795063183822124124757 142310098396685415517087)
                ·
                  rfl

theorem cell22_3741497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 8].length) (baseStart_3741497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741497 prefixEnd_3741497 := by exact prefixLift 3741497
  have htrace : WordTrace (prefixWord ++ tailWord_3741497) baseStart_3741497 baseEnd_3741497 := by
    simpa [prefixWord, tailWord_3741497, baseEnd_3741497] using wordTrace_append hprefix tailTrace_3741497
  have hstable : (prefixWord ++ tailWord_3741497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741497).length < 2 ^ (prefixWord ++ tailWord_3741497).sum := by decide
  have hdescent : baseEnd_3741497 < baseStart_3741497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741525 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3741525 : Nat := 118140960795 + 3741525 * 2 ^ 59
def prefixEnd_3741525 : Nat := 4983230072969 + 3 ^ 40 * 3741525 * 2
def baseEnd_3741525 : Nat := 426933490180795333317899

theorem tailTrace_3741525 : CollatzResearch.WordTrace tailWord_3741525 prefixEnd_3741525 426933490180795333317899 := by
  unfold tailWord_3741525
  simp only [CollatzResearch.WordTrace]
  refine ⟨136464627770101401441594029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90976418513400934294396019 136464627770101401441594029)
  ·
    refine ⟨51174235413788025540597761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136464627770101401441594029 51174235413788025540597761)
    ·
      refine ⟨38380676560341019155448321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51174235413788025540597761 38380676560341019155448321)
      ·
        refine ⟨28785507420255764366586241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38380676560341019155448321 28785507420255764366586241)
        ·
          refine ⟨21589130565191823274939681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28785507420255764366586241 21589130565191823274939681)
          ·
            refine ⟨16191847923893867456204761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21589130565191823274939681 16191847923893867456204761)
            ·
              refine ⟨12143885942920400592153571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16191847923893867456204761 12143885942920400592153571)
              ·
                refine ⟨18215828914380600888230357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12143885942920400592153571 18215828914380600888230357)
                ·
                  refine ⟨426933490180795333317899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18215828914380600888230357 426933490180795333317899)
                  ·
                    rfl

theorem cell22_3741525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3741525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741525 prefixEnd_3741525 := by exact prefixLift 3741525
  have htrace : WordTrace (prefixWord ++ tailWord_3741525) baseStart_3741525 baseEnd_3741525 := by
    simpa [prefixWord, tailWord_3741525, baseEnd_3741525] using wordTrace_append hprefix tailTrace_3741525
  have hstable : (prefixWord ++ tailWord_3741525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741525).length < 2 ^ (prefixWord ++ tailWord_3741525).sum := by decide
  have hdescent : baseEnd_3741525 < baseStart_3741525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741572 : List Nat := [2, 3, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3741572 : Nat := 118140960795 + 3741572 * 2 ^ 59
def prefixEnd_3741572 : Nat := 4983230072969 + 3 ^ 40 * 3741572 * 2
def baseEnd_3741572 : Nat := 1280816559602893544028553

theorem tailTrace_3741572 : CollatzResearch.WordTrace tailWord_3741572 prefixEnd_3741572 1280816559602893544028553 := by
  unfold tailWord_3741572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68233171000465564234277485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90977561333954085645703313 68233171000465564234277485)
  ·
    refine ⟨25587439125174586587854057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68233171000465564234277485 25587439125174586587854057)
    ·
      refine ⟨19190579343880939940890543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25587439125174586587854057 19190579343880939940890543)
      ·
        refine ⟨28785869015821409911335815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19190579343880939940890543 28785869015821409911335815)
        ·
          refine ⟨43178803523732114867003723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28785869015821409911335815 43178803523732114867003723)
          ·
            refine ⟨64768205285598172300505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43178803523732114867003723 64768205285598172300505585)
            ·
              refine ⟨48576153964198629225379189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64768205285598172300505585 48576153964198629225379189)
              ·
                refine ⟨4554014434143621489879299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48576153964198629225379189 4554014434143621489879299)
                ·
                  refine ⟨6831021651215432234818949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4554014434143621489879299 6831021651215432234818949)
                  ·
                    refine ⟨1280816559602893544028553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831021651215432234818949 1280816559602893544028553)
                    ·
                      rfl

theorem cell22_3741572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3741572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741572 prefixEnd_3741572 := by exact prefixLift 3741572
  have htrace : WordTrace (prefixWord ++ tailWord_3741572) baseStart_3741572 baseEnd_3741572 := by
    simpa [prefixWord, tailWord_3741572, baseEnd_3741572] using wordTrace_append hprefix tailTrace_3741572
  have hstable : (prefixWord ++ tailWord_3741572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741572).length < 2 ^ (prefixWord ++ tailWord_3741572).sum := by decide
  have hdescent : baseEnd_3741572 < baseStart_3741572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741600 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_3741600 : Nat := 118140960795 + 3741600 * 2 ^ 59
def prefixEnd_3741600 : Nat := 4983230072969 + 3 ^ 40 * 3741600 * 2
def baseEnd_3741600 : Nat := 1280826144575110804328467

theorem tailTrace_3741600 : CollatzResearch.WordTrace tailWord_3741600 prefixEnd_3741600 1280826144575110804328467 := by
  unfold tailWord_3741600
  simp only [CollatzResearch.WordTrace]
  refine ⟨68233681622414844625287127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90978242163219792833716169 68233681622414844625287127)
  ·
    refine ⟨102350522433622266937930691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68233681622414844625287127 102350522433622266937930691)
    ·
      refine ⟨153525783650433400406896037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102350522433622266937930691 153525783650433400406896037)
      ·
        refine ⟨28786084434456262576293007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153525783650433400406896037 28786084434456262576293007)
        ·
          refine ⟨43179126651684393864439511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28786084434456262576293007 43179126651684393864439511)
          ·
            refine ⟨64768689977526590796659267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43179126651684393864439511 64768689977526590796659267)
            ·
              refine ⟨97153034966289886194988901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64768689977526590796659267 97153034966289886194988901)
              ·
                refine ⟨18216194056179353661560419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97153034966289886194988901 18216194056179353661560419)
                ·
                  refine ⟨27324291084269030492340629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216194056179353661560419 27324291084269030492340629)
                  ·
                    refine ⟨1280826144575110804328467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27324291084269030492340629 1280826144575110804328467)
                    ·
                      rfl

theorem cell22_3741600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_3741600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741600 prefixEnd_3741600 := by exact prefixLift 3741600
  have htrace : WordTrace (prefixWord ++ tailWord_3741600) baseStart_3741600 baseEnd_3741600 := by
    simpa [prefixWord, tailWord_3741600, baseEnd_3741600] using wordTrace_append hprefix tailTrace_3741600
  have hstable : (prefixWord ++ tailWord_3741600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741600).length < 2 ^ (prefixWord ++ tailWord_3741600).sum := by decide
  have hdescent : baseEnd_3741600 < baseStart_3741600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741617 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3741617 : Nat := 118140960795 + 3741617 * 2 ^ 59
def prefixEnd_3741617 : Nat := 4983230072969 + 3 ^ 40 * 3741617 * 2
def baseEnd_3741617 : Nat := 1280831964022528426653415

theorem tailTrace_3741617 : CollatzResearch.WordTrace tailWord_3741617 prefixEnd_3741617 1280831964022528426653415 := by
  unfold tailWord_3741617
  simp only [CollatzResearch.WordTrace]
  refine ⟨136467983285768101153943105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90978655523845400769295403 136467983285768101153943105)
  ·
    refine ⟨102350987464326075865457329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136467983285768101153943105 102350987464326075865457329)
    ·
      refine ⟨76763240598244556899092997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102350987464326075865457329 76763240598244556899092997)
      ·
        refine ⟨14393107612170854418579937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76763240598244556899092997 14393107612170854418579937)
        ·
          refine ⟨10794830709128140813934953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14393107612170854418579937 10794830709128140813934953)
          ·
            refine ⟨8096123031846105610451215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10794830709128140813934953 8096123031846105610451215)
            ·
              refine ⟨12144184547769158415676823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096123031846105610451215 12144184547769158415676823)
              ·
                refine ⟨18216276821653737623515235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144184547769158415676823 18216276821653737623515235)
                ·
                  refine ⟨27324415232480606435272853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18216276821653737623515235 27324415232480606435272853)
                  ·
                    refine ⟨1280831964022528426653415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27324415232480606435272853 1280831964022528426653415)
                    ·
                      rfl

theorem cell22_3741617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3741617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741617 prefixEnd_3741617 := by exact prefixLift 3741617
  have htrace : WordTrace (prefixWord ++ tailWord_3741617) baseStart_3741617 baseEnd_3741617 := by
    simpa [prefixWord, tailWord_3741617, baseEnd_3741617] using wordTrace_append hprefix tailTrace_3741617
  have hstable : (prefixWord ++ tailWord_3741617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741617).length < 2 ^ (prefixWord ++ tailWord_3741617).sum := by decide
  have hdescent : baseEnd_3741617 < baseStart_3741617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741675 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_3741675 : Nat := 118140960795 + 3741675 * 2 ^ 59
def prefixEnd_3741675 : Nat := 4983230072969 + 3 ^ 40 * 3741675 * 2
def baseEnd_3741675 : Nat := 1280851818607835608703237

theorem tailTrace_3741675 : CollatzResearch.WordTrace tailWord_3741675 prefixEnd_3741675 1280851818607835608703237 := by
  unfold tailWord_3741675
  simp only [CollatzResearch.WordTrace]
  refine ⟨136470098719557977059554479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90980065813038651373036319 136470098719557977059554479)
  ·
    refine ⟨204705148079336965589331719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136470098719557977059554479 204705148079336965589331719)
    ·
      refine ⟨307057722119005448383997579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204705148079336965589331719 307057722119005448383997579)
      ·
        refine ⟨460586583178508172575996369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307057722119005448383997579 460586583178508172575996369)
        ·
          refine ⟨345439937383881129431997277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460586583178508172575996369 345439937383881129431997277)
          ·
            refine ⟨129539976518955423536998979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345439937383881129431997277 129539976518955423536998979)
            ·
              refine ⟨194309964778433135305498469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129539976518955423536998979 194309964778433135305498469)
              ·
                refine ⟨36433118395956212869780963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194309964778433135305498469 36433118395956212869780963)
                ·
                  refine ⟨54649677593934319304671445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36433118395956212869780963 54649677593934319304671445)
                  ·
                    refine ⟨1280851818607835608703237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54649677593934319304671445 1280851818607835608703237)
                    ·
                      rfl

theorem cell22_3741675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_3741675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741675 prefixEnd_3741675 := by exact prefixLift 3741675
  have htrace : WordTrace (prefixWord ++ tailWord_3741675) baseStart_3741675 baseEnd_3741675 := by
    simpa [prefixWord, tailWord_3741675, baseEnd_3741675] using wordTrace_append hprefix tailTrace_3741675
  have hstable : (prefixWord ++ tailWord_3741675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741675).length < 2 ^ (prefixWord ++ tailWord_3741675).sum := by decide
  have hdescent : baseEnd_3741675 < baseStart_3741675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741694 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3741694 : Nat := 118140960795 + 3741694 * 2 ^ 59
def prefixEnd_3741694 : Nat := 4983230072969 + 3 ^ 40 * 3741694 * 2
def baseEnd_3741694 : Nat := 426952774232041964159393

theorem tailTrace_3741694 : CollatzResearch.WordTrace tailWord_3741694 prefixEnd_3741694 426952774232041964159393 := by
  unfold tailWord_3741694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058848963311142913062017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90980527804326095536330757 17058848963311142913062017)
  ·
    refine ⟨12794136722483357184796513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17058848963311142913062017 12794136722483357184796513)
    ·
      refine ⟨9595602541862517888597385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12794136722483357184796513 9595602541862517888597385)
      ·
        refine ⟨7196701906396888416448039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9595602541862517888597385 7196701906396888416448039)
        ·
          refine ⟨10795052859595332624672059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7196701906396888416448039 10795052859595332624672059)
          ·
            refine ⟨16192579289392998937008089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10795052859595332624672059 16192579289392998937008089)
            ·
              refine ⟨12144434467044749202756067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16192579289392998937008089 12144434467044749202756067)
              ·
                refine ⟨18216651700567123804134101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144434467044749202756067 18216651700567123804134101)
                ·
                  refine ⟨426952774232041964159393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18216651700567123804134101 426952774232041964159393)
                  ·
                    rfl

theorem cell22_3741694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3741694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741694 prefixEnd_3741694 := by exact prefixLift 3741694
  have htrace : WordTrace (prefixWord ++ tailWord_3741694) baseStart_3741694 baseEnd_3741694 := by
    simpa [prefixWord, tailWord_3741694, baseEnd_3741694] using wordTrace_append hprefix tailTrace_3741694
  have hstable : (prefixWord ++ tailWord_3741694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741694).length < 2 ^ (prefixWord ++ tailWord_3741694).sum := by decide
  have hdescent : baseEnd_3741694 < baseStart_3741694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741707 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_3741707 : Nat := 118140960795 + 3741707 * 2 ^ 59
def prefixEnd_3741707 : Nat := 4983230072969 + 3 ^ 40 * 3741707 * 2
def baseEnd_3741707 : Nat := 1280862772861798191903139

theorem tailTrace_3741707 : CollatzResearch.WordTrace tailWord_3741707 prefixEnd_3741707 1280862772861798191903139 := by
  unfold tailWord_3741707
  simp only [CollatzResearch.WordTrace]
  refine ⟨136471265855442046524719375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90980843903628031016479583 136471265855442046524719375)
  ·
    refine ⟨204706898783163069787079063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136471265855442046524719375 204706898783163069787079063)
    ·
      refine ⟨307060348174744604680618595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204706898783163069787079063 307060348174744604680618595)
      ·
        refine ⟨460590522262116907020927893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307060348174744604680618595 460590522262116907020927893)
        ·
          refine ⟨21590180731036730016605995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460590522262116907020927893 21590180731036730016605995)
          ·
            refine ⟨32385271096555095024908993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21590180731036730016605995 32385271096555095024908993)
            ·
              refine ⟨24288953322416321268681745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32385271096555095024908993 24288953322416321268681745)
              ·
                refine ⟨18216714991812240951511309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24288953322416321268681745 18216714991812240951511309)
                ·
                  refine ⟨6831268121929590356816741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18216714991812240951511309 6831268121929590356816741)
                  ·
                    refine ⟨1280862772861798191903139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831268121929590356816741 1280862772861798191903139)
                    ·
                      rfl

theorem cell22_3741707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_3741707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741707 prefixEnd_3741707 := by exact prefixLift 3741707
  have htrace : WordTrace (prefixWord ++ tailWord_3741707) baseStart_3741707 baseEnd_3741707 := by
    simpa [prefixWord, tailWord_3741707, baseEnd_3741707] using wordTrace_append hprefix tailTrace_3741707
  have hstable : (prefixWord ++ tailWord_3741707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741707).length < 2 ^ (prefixWord ++ tailWord_3741707).sum := by decide
  have hdescent : baseEnd_3741707 < baseStart_3741707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741724 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 3, 4]
def baseStart_3741724 : Nat := 118140960795 + 3741724 * 2 ^ 59
def prefixEnd_3741724 : Nat := 4983230072969 + 3 ^ 40 * 3741724 * 2
def baseEnd_3741724 : Nat := 1280868592309215814228087

theorem tailTrace_3741724 : CollatzResearch.WordTrace tailWord_3741724 prefixEnd_3741724 1280868592309215814228087 := by
  unfold tailWord_3741724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68235942948190229214044113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90981257264253638952058817 68235942948190229214044113)
  ·
    refine ⟨51176957211142671910533085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68235942948190229214044113 51176957211142671910533085)
    ·
      refine ⟨19191358954178501966449907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51176957211142671910533085 19191358954178501966449907)
      ·
        refine ⟨28787038431267752949674861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191358954178501966449907 28787038431267752949674861)
        ·
          refine ⟨10795139411725407356128073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28787038431267752949674861 10795139411725407356128073)
          ·
            refine ⟨8096354558794055517096055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10795139411725407356128073 8096354558794055517096055)
            ·
              refine ⟨12144531838191083275644083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096354558794055517096055 12144531838191083275644083)
              ·
                refine ⟨18216797757286624913466125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12144531838191083275644083 18216797757286624913466125)
                ·
                  refine ⟨6831299158982484342549797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18216797757286624913466125 6831299158982484342549797)
                  ·
                    refine ⟨1280868592309215814228087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6831299158982484342549797 1280868592309215814228087)
                    ·
                      rfl

theorem cell22_3741724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_3741724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741724 prefixEnd_3741724 := by exact prefixLift 3741724
  have htrace : WordTrace (prefixWord ++ tailWord_3741724) baseStart_3741724 baseEnd_3741724 := by
    simpa [prefixWord, tailWord_3741724, baseEnd_3741724] using wordTrace_append hprefix tailTrace_3741724
  have hstable : (prefixWord ++ tailWord_3741724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741724).length < 2 ^ (prefixWord ++ tailWord_3741724).sum := by decide
  have hdescent : baseEnd_3741724 < baseStart_3741724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741784 : List Nat := [2, 1, 2, 2, 1, 5, 3, 6]
def baseStart_3741784 : Nat := 118140960795 + 3741784 * 2 ^ 59
def prefixEnd_3741784 : Nat := 4983230072969 + 3 ^ 40 * 3741784 * 2
def baseEnd_3741784 : Nat := 142321014615043961969767

theorem tailTrace_3741784 : CollatzResearch.WordTrace tailWord_3741784 prefixEnd_3741784 142321014615043961969767 := by
  unfold tailWord_3741784
  simp only [CollatzResearch.WordTrace]
  refine ⟨68237037138081544337636203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90982716184108725783514937 68237037138081544337636203)
  ·
    refine ⟨102355555707122316506454305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68237037138081544337636203 102355555707122316506454305)
    ·
      refine ⟨76766666780341737379840729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102355555707122316506454305 76766666780341737379840729)
      ·
        refine ⟨57575000085256303034880547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76766666780341737379840729 57575000085256303034880547)
        ·
          refine ⟨86362500127884454552320821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57575000085256303034880547 86362500127884454552320821)
          ·
            refine ⟨8096484386989167614280077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86362500127884454552320821 8096484386989167614280077)
            ·
              refine ⟨3036181645120937855355029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8096484386989167614280077 3036181645120937855355029)
              ·
                refine ⟨142321014615043961969767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3036181645120937855355029 142321014615043961969767)
                ·
                  rfl

theorem cell22_3741784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_3741784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741784 prefixEnd_3741784 := by exact prefixLift 3741784
  have htrace : WordTrace (prefixWord ++ tailWord_3741784) baseStart_3741784 baseEnd_3741784 := by
    simpa [prefixWord, tailWord_3741784, baseEnd_3741784] using wordTrace_append hprefix tailTrace_3741784
  have hstable : (prefixWord ++ tailWord_3741784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741784).length < 2 ^ (prefixWord ++ tailWord_3741784).sum := by decide
  have hdescent : baseEnd_3741784 < baseStart_3741784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741799 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3741799 : Nat := 118140960795 + 3741799 * 2 ^ 59
def prefixEnd_3741799 : Nat := 4983230072969 + 3 ^ 40 * 3741799 * 2
def baseEnd_3741799 : Nat := 1280894266341940618602857

theorem tailTrace_3741799 : CollatzResearch.WordTrace tailWord_3741799 prefixEnd_3741799 1280894266341940618602857 := by
  unfold tailWord_3741799
  simp only [CollatzResearch.WordTrace]
  refine ⟨136474621371108746237068451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90983080914072497491378967 136474621371108746237068451)
  ·
    refine ⟨204711932056663119355602677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136474621371108746237068451 204711932056663119355602677)
    ·
      refine ⟨19191743630312167439587751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204711932056663119355602677 19191743630312167439587751)
      ·
        refine ⟨28787615445468251159381627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191743630312167439587751 28787615445468251159381627)
        ·
          refine ⟨43181423168202376739072441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28787615445468251159381627 43181423168202376739072441)
          ·
            refine ⟨32386067376151782554304331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43181423168202376739072441 32386067376151782554304331)
            ·
              refine ⟨48579101064227673831456497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32386067376151782554304331 48579101064227673831456497)
              ·
                refine ⟨36434325798170755373592373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48579101064227673831456497 36434325798170755373592373)
                ·
                  refine ⟨3415718043578508316274285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36434325798170755373592373 3415718043578508316274285)
                  ·
                    refine ⟨1280894266341940618602857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415718043578508316274285 1280894266341940618602857)
                    ·
                      rfl

theorem cell22_3741799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3741799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741799 prefixEnd_3741799 := by exact prefixLift 3741799
  have htrace : WordTrace (prefixWord ++ tailWord_3741799) baseStart_3741799 baseEnd_3741799 := by
    simpa [prefixWord, tailWord_3741799, baseEnd_3741799] using wordTrace_append hprefix tailTrace_3741799
  have hstable : (prefixWord ++ tailWord_3741799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741799).length < 2 ^ (prefixWord ++ tailWord_3741799).sum := by decide
  have hdescent : baseEnd_3741799 < baseStart_3741799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741872 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_3741872 : Nat := 118140960795 + 3741872 * 2 ^ 59
def prefixEnd_3741872 : Nat := 4983230072969 + 3 ^ 40 * 3741872 * 2
def baseEnd_3741872 : Nat := 1280919255733792761527633

theorem tailTrace_3741872 : CollatzResearch.WordTrace tailWord_3741872 prefixEnd_3741872 1280919255733792761527633 := by
  unfold tailWord_3741872
  simp only [CollatzResearch.WordTrace]
  refine ⟨68238641949922139852237935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90984855933229519802983913 68238641949922139852237935)
  ·
    refine ⟨102357962924883209778356903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68238641949922139852237935 102357962924883209778356903)
    ·
      refine ⟨153536944387324814667535355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102357962924883209778356903 153536944387324814667535355)
      ·
        refine ⟨230305416580987222001303033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153536944387324814667535355 230305416580987222001303033)
        ·
          refine ⟨172729062435740416500977275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230305416580987222001303033 172729062435740416500977275)
          ·
            refine ⟨259093593653610624751465913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172729062435740416500977275 259093593653610624751465913)
            ·
              refine ⟨194320195240207968563599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259093593653610624751465913 194320195240207968563599435)
              ·
                refine ⟨291480292860311952845399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194320195240207968563599435 291480292860311952845399153)
                ·
                  refine ⟨218610219645233964634049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291480292860311952845399153 218610219645233964634049365)
                  ·
                    refine ⟨1280919255733792761527633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 218610219645233964634049365 1280919255733792761527633)
                    ·
                      rfl

theorem cell22_3741872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_3741872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741872 prefixEnd_3741872 := by exact prefixLift 3741872
  have htrace : WordTrace (prefixWord ++ tailWord_3741872) baseStart_3741872 baseEnd_3741872 := by
    simpa [prefixWord, tailWord_3741872, baseEnd_3741872] using wordTrace_append hprefix tailTrace_3741872
  have hstable : (prefixWord ++ tailWord_3741872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741872).length < 2 ^ (prefixWord ++ tailWord_3741872).sum := by decide
  have hdescent : baseEnd_3741872 < baseStart_3741872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741906 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_3741906 : Nat := 118140960795 + 3741906 * 2 ^ 59
def prefixEnd_3741906 : Nat := 4983230072969 + 3 ^ 40 * 3741906 * 2
def baseEnd_3741906 : Nat := 1280930894628628006177529

theorem tailTrace_3741906 : CollatzResearch.WordTrace tailWord_3741906 prefixEnd_3741906 1280930894628628006177529 := by
  unfold tailWord_3741906
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119630995430275877803393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 90985682654480735674142381 34119630995430275877803393)
  ·
    refine ⟨25589723246572706908352545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34119630995430275877803393 25589723246572706908352545)
    ·
      refine ⟨19192292434929530181264409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589723246572706908352545 19192292434929530181264409)
      ·
        refine ⟨14394219326197147635948307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19192292434929530181264409 14394219326197147635948307)
        ·
          refine ⟨21591328989295721453922461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14394219326197147635948307 21591328989295721453922461)
          ·
            refine ⟨8096748370985895545220923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21591328989295721453922461 8096748370985895545220923)
            ·
              refine ⟨12145122556478843317831385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096748370985895545220923 12145122556478843317831385)
              ·
                refine ⟨9108841917359132488373539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145122556478843317831385 9108841917359132488373539)
                ·
                  refine ⟨13663262876038698732560309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9108841917359132488373539 13663262876038698732560309)
                  ·
                    refine ⟨1280930894628628006177529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13663262876038698732560309 1280930894628628006177529)
                    ·
                      rfl

theorem cell22_3741906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_3741906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741906 prefixEnd_3741906 := by exact prefixLift 3741906
  have htrace : WordTrace (prefixWord ++ tailWord_3741906) baseStart_3741906 baseEnd_3741906 := by
    simpa [prefixWord, tailWord_3741906, baseEnd_3741906] using wordTrace_append hprefix tailTrace_3741906
  have hstable : (prefixWord ++ tailWord_3741906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741906).length < 2 ^ (prefixWord ++ tailWord_3741906).sum := by decide
  have hdescent : baseEnd_3741906 < baseStart_3741906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741925 : List Nat := [1, 3, 1, 4, 2, 3, 2, 2, 4]
def baseStart_3741925 : Nat := 118140960795 + 3741925 * 2 ^ 59
def prefixEnd_3741925 : Nat := 4983230072969 + 3 ^ 40 * 3741925 * 2
def baseEnd_3741925 : Nat := 426979132905639429984157

theorem tailTrace_3741925 : CollatzResearch.WordTrace tailWord_3741925 prefixEnd_3741925 426979132905639429984157 := by
  unfold tailWord_3741925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136479216968652269756155229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90986144645768179837436819 136479216968652269756155229)
  ·
    refine ⟨51179706363244601158558211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136479216968652269756155229 51179706363244601158558211)
    ·
      refine ⟨76769559544866901737837317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51179706363244601158558211 76769559544866901737837317)
      ·
        refine ⟨14394292414662544075844497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76769559544866901737837317 14394292414662544075844497)
        ·
          refine ⟨10795719310996908056883373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14394292414662544075844497 10795719310996908056883373)
          ·
            refine ⟨4048394741623840521331265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10795719310996908056883373 4048394741623840521331265)
            ·
              refine ⟨3036296056217880390998449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048394741623840521331265 3036296056217880390998449)
              ·
                refine ⟨2277222042163410293248837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3036296056217880390998449 2277222042163410293248837)
                ·
                  refine ⟨426979132905639429984157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277222042163410293248837 426979132905639429984157)
                  ·
                    rfl

theorem cell22_3741925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_3741925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741925 prefixEnd_3741925 := by exact prefixLift 3741925
  have htrace : WordTrace (prefixWord ++ tailWord_3741925) baseStart_3741925 baseEnd_3741925 := by
    simpa [prefixWord, tailWord_3741925, baseEnd_3741925] using wordTrace_append hprefix tailTrace_3741925
  have hstable : (prefixWord ++ tailWord_3741925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741925).length < 2 ^ (prefixWord ++ tailWord_3741925).sum := by decide
  have hdescent : baseEnd_3741925 < baseStart_3741925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741934 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3741934 : Nat := 118140960795 + 3741934 * 2 ^ 59
def prefixEnd_3741934 : Nat := 4983230072969 + 3 ^ 40 * 3741934 * 2
def baseEnd_3741934 : Nat := 1280940479600845266477443

theorem tailTrace_3741934 : CollatzResearch.WordTrace tailWord_3741934 prefixEnd_3741934 1280940479600845266477443 := by
  unfold tailWord_3741934
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059943153202458036654107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 90986363483746442862155237 17059943153202458036654107)
  ·
    refine ⟨25589914729803687054981161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059943153202458036654107 25589914729803687054981161)
    ·
      refine ⟨19192436047352765291235871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25589914729803687054981161 19192436047352765291235871)
      ·
        refine ⟨28788654071029147936853807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19192436047352765291235871 28788654071029147936853807)
        ·
          refine ⟨43182981106543721905280711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28788654071029147936853807 43182981106543721905280711)
          ·
            refine ⟨64774471659815582857921067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43182981106543721905280711 64774471659815582857921067)
            ·
              refine ⟨97161707489723374286881601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64774471659815582857921067 97161707489723374286881601)
              ·
                refine ⟨72871280617292530715161201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97161707489723374286881601 72871280617292530715161201)
                ·
                  refine ⟨54653460462969398036370901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72871280617292530715161201 54653460462969398036370901)
                  ·
                    refine ⟨1280940479600845266477443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54653460462969398036370901 1280940479600845266477443)
                    ·
                      rfl

theorem cell22_3741934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3741934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741934 prefixEnd_3741934 := by exact prefixLift 3741934
  have htrace : WordTrace (prefixWord ++ tailWord_3741934) baseStart_3741934 baseEnd_3741934 := by
    simpa [prefixWord, tailWord_3741934, baseEnd_3741934] using wordTrace_append hprefix tailTrace_3741934
  have hstable : (prefixWord ++ tailWord_3741934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741934).length < 2 ^ (prefixWord ++ tailWord_3741934).sum := by decide
  have hdescent : baseEnd_3741934 < baseStart_3741934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741951 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 3, 3]
def baseStart_3741951 : Nat := 118140960795 + 3741951 * 2 ^ 59
def prefixEnd_3741951 : Nat := 4983230072969 + 3 ^ 40 * 3741951 * 2
def baseEnd_3741951 : Nat := 1280946299048262888802391

theorem tailTrace_3741951 : CollatzResearch.WordTrace tailWord_3741951 prefixEnd_3741951 1280946299048262888802391 := by
  unfold tailWord_3741951
  simp only [CollatzResearch.WordTrace]
  refine ⟨136480165266558076196601707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90986776844372050797734471 136480165266558076196601707)
  ·
    refine ⟨204720247899837114294902561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136480165266558076196601707 204720247899837114294902561)
    ·
      refine ⟨153540185924877835721176921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204720247899837114294902561 153540185924877835721176921)
      ·
        refine ⟨115155139443658376790882691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153540185924877835721176921 115155139443658376790882691)
        ·
          refine ⟨172732709165487565186324037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115155139443658376790882691 172732709165487565186324037)
          ·
            refine ⟨32387382968528918472435757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172732709165487565186324037 32387382968528918472435757)
            ·
              refine ⟨12145268613198344427163409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32387382968528918472435757 12145268613198344427163409)
              ·
                refine ⟨9108951459898758320372557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12145268613198344427163409 9108951459898758320372557)
                ·
                  refine ⟨3415856797462034370139709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9108951459898758320372557 3415856797462034370139709)
                  ·
                    refine ⟨1280946299048262888802391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3415856797462034370139709 1280946299048262888802391)
                    ·
                      rfl

theorem cell22_3741951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_3741951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741951 prefixEnd_3741951 := by exact prefixLift 3741951
  have htrace : WordTrace (prefixWord ++ tailWord_3741951) baseStart_3741951 baseEnd_3741951 := by
    simpa [prefixWord, tailWord_3741951, baseEnd_3741951] using wordTrace_append hprefix tailTrace_3741951
  have hstable : (prefixWord ++ tailWord_3741951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741951).length < 2 ^ (prefixWord ++ tailWord_3741951).sum := by decide
  have hdescent : baseEnd_3741951 < baseStart_3741951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741964 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_3741964 : Nat := 118140960795 + 3741964 * 2 ^ 59
def prefixEnd_3741964 : Nat := 4983230072969 + 3 ^ 40 * 3741964 * 2
def baseEnd_3741964 : Nat := 426983583071311729409117

theorem tailTrace_3741964 : CollatzResearch.WordTrace tailWord_3741964 prefixEnd_3741964 426983583071311729409117 := by
  unfold tailWord_3741964
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240319707755489708412473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90987092943673986277883297 68240319707755489708412473)
  ·
    refine ⟨51180239780816617281309355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68240319707755489708412473 51180239780816617281309355)
    ·
      refine ⟨76770359671224925921964033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51180239780816617281309355 76770359671224925921964033)
      ·
        refine ⟨57577769753418694441473025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76770359671224925921964033 57577769753418694441473025)
        ·
          refine ⟨43183327315064020831104769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57577769753418694441473025 43183327315064020831104769)
          ·
            refine ⟨32387495486298015623328577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43183327315064020831104769 32387495486298015623328577)
            ·
              refine ⟨24290621614723511717496433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32387495486298015623328577 24290621614723511717496433)
              ·
                refine ⟨18217966211042633788122325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24290621614723511717496433 18217966211042633788122325)
                ·
                  refine ⟨426983583071311729409117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18217966211042633788122325 426983583071311729409117)
                  ·
                    rfl

theorem cell22_3741964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_3741964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741964 prefixEnd_3741964 := by exact prefixLift 3741964
  have htrace : WordTrace (prefixWord ++ tailWord_3741964) baseStart_3741964 baseEnd_3741964 := by
    simpa [prefixWord, tailWord_3741964, baseEnd_3741964] using wordTrace_append hprefix tailTrace_3741964
  have hstable : (prefixWord ++ tailWord_3741964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741964).length < 2 ^ (prefixWord ++ tailWord_3741964).sum := by decide
  have hdescent : baseEnd_3741964 < baseStart_3741964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3741979 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_3741979 : Nat := 118140960795 + 3741979 * 2 ^ 59
def prefixEnd_3741979 : Nat := 4983230072969 + 3 ^ 40 * 3741979 * 2
def baseEnd_3741979 : Nat := 1280955884020480149102305

theorem tailTrace_3741979 : CollatzResearch.WordTrace tailWord_3741979 prefixEnd_3741979 1280955884020480149102305 := by
  unfold tailWord_3741979
  simp only [CollatzResearch.WordTrace]
  refine ⟨136481186510456636978620991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90987457673637757985747327 136481186510456636978620991)
  ·
    refine ⟨204721779765684955467931487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136481186510456636978620991 204721779765684955467931487)
    ·
      refine ⟨307082669648527433201897231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204721779765684955467931487 307082669648527433201897231)
      ·
        refine ⟨460624004472791149802845847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307082669648527433201897231 460624004472791149802845847)
        ·
          refine ⟨690936006709186724704268771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460624004472791149802845847 690936006709186724704268771)
          ·
            refine ⟨1036404010063780087056403157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690936006709186724704268771 1036404010063780087056403157)
            ·
              refine ⟨24290718985869845790384449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1036404010063780087056403157 24290718985869845790384449)
              ·
                refine ⟨18218039239402384342788337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24290718985869845790384449 18218039239402384342788337)
                ·
                  refine ⟨13663529429551788257091253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18218039239402384342788337 13663529429551788257091253)
                  ·
                    refine ⟨1280955884020480149102305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13663529429551788257091253 1280955884020480149102305)
                    ·
                      rfl

theorem cell22_3741979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_3741979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3741979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3741979 prefixEnd_3741979 := by exact prefixLift 3741979
  have htrace : WordTrace (prefixWord ++ tailWord_3741979) baseStart_3741979 baseEnd_3741979 := by
    simpa [prefixWord, tailWord_3741979, baseEnd_3741979] using wordTrace_append hprefix tailTrace_3741979
  have hstable : (prefixWord ++ tailWord_3741979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3741979).length < 2 ^ (prefixWord ++ tailWord_3741979).sum := by decide
  have hdescent : baseEnd_3741979 < baseStart_3741979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3741979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742120 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3742120 : Nat := 118140960795 + 3742120 * 2 ^ 59
def prefixEnd_3742120 : Nat := 4983230072969 + 3 ^ 40 * 3742120 * 2
def baseEnd_3742120 : Nat := 1281004151202002781326873

theorem tailTrace_3742120 : CollatzResearch.WordTrace tailWord_3742120 prefixEnd_3742120 1281004151202002781326873 := by
  unfold tailWord_3742120
  simp only [CollatzResearch.WordTrace]
  refine ⟨68243164601472909029751907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90990886135297212039669209 68243164601472909029751907)
  ·
    refine ⟨102364746902209363544627861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68243164601472909029751907 102364746902209363544627861)
    ·
      refine ⟨4798347511041063916154431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102364746902209363544627861 4798347511041063916154431)
      ·
        refine ⟨7197521266561595874231647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798347511041063916154431 7197521266561595874231647)
        ·
          refine ⟨10796281899842393811347471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7197521266561595874231647 10796281899842393811347471)
          ·
            refine ⟨16194422849763590717021207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10796281899842393811347471 16194422849763590717021207)
            ·
              refine ⟨24291634274645386075531811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16194422849763590717021207 24291634274645386075531811)
              ·
                refine ⟨36437451411968079113297717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24291634274645386075531811 36437451411968079113297717)
                ·
                  refine ⟨3416011069872007416871661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36437451411968079113297717 3416011069872007416871661)
                  ·
                    refine ⟨1281004151202002781326873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416011069872007416871661 1281004151202002781326873)
                    ·
                      rfl

theorem cell22_3742120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3742120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742120 prefixEnd_3742120 := by exact prefixLift 3742120
  have htrace : WordTrace (prefixWord ++ tailWord_3742120) baseStart_3742120 baseEnd_3742120 := by
    simpa [prefixWord, tailWord_3742120, baseEnd_3742120] using wordTrace_append hprefix tailTrace_3742120
  have hstable : (prefixWord ++ tailWord_3742120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742120).length < 2 ^ (prefixWord ++ tailWord_3742120).sum := by decide
  have hdescent : baseEnd_3742120 < baseStart_3742120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742137 : List Nat := [1, 2, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_3742137 : Nat := 118140960795 + 3742137 * 2 ^ 59
def prefixEnd_3742137 : Nat := 4983230072969 + 3 ^ 40 * 3742137 * 2
def baseEnd_3742137 : Nat := 1281009970649420403651821

theorem tailTrace_3742137 : CollatzResearch.WordTrace tailWord_3742137 prefixEnd_3742137 1281009970649420403651821 := by
  unfold tailWord_3742137
  simp only [CollatzResearch.WordTrace]
  refine ⟨136486949243884229962872665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90991299495922819975248443 136486949243884229962872665)
  ·
    refine ⟨102365211932913172472154499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136486949243884229962872665 102365211932913172472154499)
    ·
      refine ⟨153547817899369758708231749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102365211932913172472154499 153547817899369758708231749)
      ·
        refine ⟨28790215856131829757793453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153547817899369758708231749 28790215856131829757793453)
        ·
          refine ⟨10796330946049436159172545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28790215856131829757793453 10796330946049436159172545)
          ·
            refine ⟨8097248209537077119379409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10796330946049436159172545 8097248209537077119379409)
            ·
              refine ⟨6072936157152807839534557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097248209537077119379409 6072936157152807839534557)
              ·
                refine ⟨2277351058932302939825459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6072936157152807839534557 2277351058932302939825459)
                ·
                  refine ⟨3416026588398454409738189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277351058932302939825459 3416026588398454409738189)
                  ·
                    refine ⟨1281009970649420403651821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416026588398454409738189 1281009970649420403651821)
                    ·
                      rfl

theorem cell22_3742137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_3742137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742137 prefixEnd_3742137 := by exact prefixLift 3742137
  have htrace : WordTrace (prefixWord ++ tailWord_3742137) baseStart_3742137 baseEnd_3742137 := by
    simpa [prefixWord, tailWord_3742137, baseEnd_3742137] using wordTrace_append hprefix tailTrace_3742137
  have hstable : (prefixWord ++ tailWord_3742137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742137).length < 2 ^ (prefixWord ++ tailWord_3742137).sum := by decide
  have hdescent : baseEnd_3742137 < baseStart_3742137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742193 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 6, 3]
def baseStart_3742193 : Nat := 118140960795 + 3742193 * 2 ^ 59
def prefixEnd_3742193 : Nat := 4983230072969 + 3 ^ 40 * 3742193 * 2
def baseEnd_3742193 : Nat := 1281029140593854924251649

theorem tailTrace_3742193 : CollatzResearch.WordTrace tailWord_3742193 prefixEnd_3742193 1281029140593854924251649 := by
  unfold tailWord_3742193
  simp only [CollatzResearch.WordTrace]
  refine ⟨136488991731681351526911233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90992661154454234351274155 136488991731681351526911233)
  ·
    refine ⟨102366743798761013645183425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136488991731681351526911233 102366743798761013645183425)
    ·
      refine ⟨76775057849070760233887569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102366743798761013645183425 76775057849070760233887569)
      ·
        refine ⟨57581293386803070175415677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76775057849070760233887569 57581293386803070175415677)
        ·
          refine ⟨21592985020051151315780879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57581293386803070175415677 21592985020051151315780879)
          ·
            refine ⟨32389477530076726973671319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21592985020051151315780879 32389477530076726973671319)
            ·
              refine ⟨48584216295115090460506979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32389477530076726973671319 48584216295115090460506979)
              ·
                refine ⟨72876324442672635690760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48584216295115090460506979 72876324442672635690760469)
                ·
                  refine ⟨3416077708250279798004397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72876324442672635690760469 3416077708250279798004397)
                  ·
                    refine ⟨1281029140593854924251649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416077708250279798004397 1281029140593854924251649)
                    ·
                      rfl

theorem cell22_3742193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_3742193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742193 prefixEnd_3742193 := by exact prefixLift 3742193
  have htrace : WordTrace (prefixWord ++ tailWord_3742193) baseStart_3742193 baseEnd_3742193 := by
    simpa [prefixWord, tailWord_3742193, baseEnd_3742193] using wordTrace_append hprefix tailTrace_3742193
  have hstable : (prefixWord ++ tailWord_3742193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742193).length < 2 ^ (prefixWord ++ tailWord_3742193).sum := by decide
  have hdescent : baseEnd_3742193 < baseStart_3742193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742251 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 9]
def baseStart_3742251 : Nat := 118140960795 + 3742251 * 2 ^ 59
def prefixEnd_3742251 : Nat := 4983230072969 + 3 ^ 40 * 3742251 * 2
def baseEnd_3742251 : Nat := 427016331726387368767157

theorem tailTrace_3742251 : CollatzResearch.WordTrace tailWord_3742251 prefixEnd_3742251 427016331726387368767157 := by
  unfold tailWord_3742251
  simp only [CollatzResearch.WordTrace]
  refine ⟨136491107165471227432522607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90994071443647484955015071 136491107165471227432522607)
  ·
    refine ⟨204736660748206841148783911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136491107165471227432522607 204736660748206841148783911)
    ·
      refine ⟨307104991122310261723175867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204736660748206841148783911 307104991122310261723175867)
      ·
        refine ⟨460657486683465392584763801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307104991122310261723175867 460657486683465392584763801)
        ·
          refine ⟨345493115012599044438572851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460657486683465392584763801 345493115012599044438572851)
          ·
            refine ⟨518239672518898566657859277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345493115012599044438572851 518239672518898566657859277)
            ·
              refine ⟨194339877194586962496697229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518239672518898566657859277 194339877194586962496697229)
              ·
                refine ⟨72877453947970110936261461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194339877194586962496697229 72877453947970110936261461)
                ·
                  refine ⟨427016331726387368767157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72877453947970110936261461 427016331726387368767157)
                  ·
                    rfl

theorem cell22_3742251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_3742251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742251 prefixEnd_3742251 := by exact prefixLift 3742251
  have htrace : WordTrace (prefixWord ++ tailWord_3742251) baseStart_3742251 baseEnd_3742251 := by
    simpa [prefixWord, tailWord_3742251, baseEnd_3742251] using wordTrace_append hprefix tailTrace_3742251
  have hstable : (prefixWord ++ tailWord_3742251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742251).length < 2 ^ (prefixWord ++ tailWord_3742251).sum := by decide
  have hdescent : baseEnd_3742251 < baseStart_3742251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742343 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 6]
def baseStart_3742343 : Nat := 118140960795 + 3742343 * 2 ^ 59
def prefixEnd_3742343 : Nat := 4983230072969 + 3 ^ 40 * 3742343 * 2
def baseEnd_3742343 : Nat := 1281080488659304533001189

theorem tailTrace_3742343 : CollatzResearch.WordTrace tailWord_3742343 prefixEnd_3742343 1281080488659304533001189 := by
  unfold tailWord_3742343
  simp only [CollatzResearch.WordTrace]
  refine ⟨136494462681137927144871683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90996308454091951429914455 136494462681137927144871683)
  ·
    refine ⟨204741694021706890717307525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136494462681137927144871683 204741694021706890717307525)
    ·
      refine ⟨38389067629070042009495161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204741694021706890717307525 38389067629070042009495161)
      ·
        refine ⟨28791800721802531507121371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38389067629070042009495161 28791800721802531507121371)
        ·
          refine ⟨43187701082703797260682057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28791800721802531507121371 43187701082703797260682057)
          ·
            refine ⟨32390775812027847945511543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43187701082703797260682057 32390775812027847945511543)
            ·
              refine ⟨48586163718041771918267315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32390775812027847945511543 48586163718041771918267315)
              ·
                refine ⟨72879245577062657877400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48586163718041771918267315 72879245577062657877400973)
                ·
                  refine ⟨27329717091398496704025365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72879245577062657877400973 27329717091398496704025365)
                  ·
                    refine ⟨1281080488659304533001189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27329717091398496704025365 1281080488659304533001189)
                    ·
                      rfl

theorem cell22_3742343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_3742343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742343 prefixEnd_3742343 := by exact prefixLift 3742343
  have htrace : WordTrace (prefixWord ++ tailWord_3742343) baseStart_3742343 baseEnd_3742343 := by
    simpa [prefixWord, tailWord_3742343, baseEnd_3742343] using wordTrace_append hprefix tailTrace_3742343
  have hstable : (prefixWord ++ tailWord_3742343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742343).length < 2 ^ (prefixWord ++ tailWord_3742343).sum := by decide
  have hdescent : baseEnd_3742343 < baseStart_3742343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742360 : List Nat := [2, 1, 2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_3742360 : Nat := 118140960795 + 3742360 * 2 ^ 59
def prefixEnd_3742360 : Nat := 4983230072969 + 3 ^ 40 * 3742360 * 2
def baseEnd_3742360 : Nat := 1281086308106722155326137

theorem tailTrace_3742360 : CollatzResearch.WordTrace tailWord_3742360 prefixEnd_3742360 1281086308106722155326137 := by
  unfold tailWord_3742360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68247541361038169524120267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90996721814717559365493689 68247541361038169524120267)
  ·
    refine ⟨102371312041557254286180401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68247541361038169524120267 102371312041557254286180401)
    ·
      refine ⟨76778484031167940714635301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102371312041557254286180401 76778484031167940714635301)
      ·
        refine ⟨14395965755843988883994119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76778484031167940714635301 14395965755843988883994119)
        ·
          refine ⟨21593948633765983325991179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14395965755843988883994119 21593948633765983325991179)
          ·
            refine ⟨32390922950648974988986769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21593948633765983325991179 32390922950648974988986769)
            ·
              refine ⟨24293192212986731241740077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32390922950648974988986769 24293192212986731241740077)
              ·
                refine ⟨9109947079870024215652529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24293192212986731241740077 9109947079870024215652529)
                ·
                  refine ⟨6832460309902518161739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9109947079870024215652529 6832460309902518161739397)
                  ·
                    refine ⟨1281086308106722155326137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6832460309902518161739397 1281086308106722155326137)
                    ·
                      rfl

theorem cell22_3742360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_3742360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742360 prefixEnd_3742360 := by exact prefixLift 3742360
  have htrace : WordTrace (prefixWord ++ tailWord_3742360) baseStart_3742360 baseEnd_3742360 := by
    simpa [prefixWord, tailWord_3742360, baseEnd_3742360] using wordTrace_append hprefix tailTrace_3742360
  have hstable : (prefixWord ++ tailWord_3742360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742360).length < 2 ^ (prefixWord ++ tailWord_3742360).sum := by decide
  have hdescent : baseEnd_3742360 < baseStart_3742360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742364 : List Nat := [2, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_3742364 : Nat := 118140960795 + 3742364 * 2 ^ 59
def prefixEnd_3742364 : Nat := 4983230072969 + 3 ^ 40 * 3742364 * 2
def baseEnd_3742364 : Nat := 427029225796155826075375

theorem tailTrace_3742364 : CollatzResearch.WordTrace tailWord_3742364 prefixEnd_3742364 427029225796155826075375 := by
  unfold tailWord_3742364
  simp only [CollatzResearch.WordTrace]
  refine ⟨68247614307030923865693073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 90996819076041231820924097 68247614307030923865693073)
  ·
    refine ⟨51185710730273192899269805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68247614307030923865693073 51185710730273192899269805)
    ·
      refine ⟨19194641523852447337226177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51185710730273192899269805 19194641523852447337226177)
      ·
        refine ⟨14395981142889335502919633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19194641523852447337226177 14395981142889335502919633)
        ·
          refine ⟨10796985857167001627189725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14395981142889335502919633 10796985857167001627189725)
          ·
            refine ⟨4048869696437625610196147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10796985857167001627189725 4048869696437625610196147)
            ·
              refine ⟨6073304544656438415294221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048869696437625610196147 6073304544656438415294221)
              ·
                refine ⟨2277489204246164405735333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6073304544656438415294221 2277489204246164405735333)
                ·
                  refine ⟨427029225796155826075375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277489204246164405735333 427029225796155826075375)
                  ·
                    rfl

theorem cell22_3742364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_3742364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742364 prefixEnd_3742364 := by exact prefixLift 3742364
  have htrace : WordTrace (prefixWord ++ tailWord_3742364) baseStart_3742364 baseEnd_3742364 := by
    simpa [prefixWord, tailWord_3742364, baseEnd_3742364] using wordTrace_append hprefix tailTrace_3742364
  have hstable : (prefixWord ++ tailWord_3742364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742364).length < 2 ^ (prefixWord ++ tailWord_3742364).sum := by decide
  have hdescent : baseEnd_3742364 < baseStart_3742364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742437 : List Nat := [1, 3, 1, 4, 1, 3, 2, 2, 5]
def baseStart_3742437 : Nat := 118140960795 + 3742437 * 2 ^ 59
def prefixEnd_3742437 : Nat := 4983230072969 + 3 ^ 40 * 3742437 * 2
def baseEnd_3742437 : Nat := 427037555593439873716967

theorem tailTrace_3742437 : CollatzResearch.WordTrace tailWord_3742437 prefixEnd_3742437 427037555593439873716967 := by
  unfold tailWord_3742437
  simp only [CollatzResearch.WordTrace]
  refine ⟨136497891142797381198793565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 90998594095198254132529043 136497891142797381198793565)
  ·
    refine ⟨51186709178549017949547587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136497891142797381198793565 51186709178549017949547587)
    ·
      refine ⟨76780063767823526924321381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51186709178549017949547587 76780063767823526924321381)
      ·
        refine ⟨14396261956466911298310259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76780063767823526924321381 14396261956466911298310259)
        ·
          refine ⟨21594392934700366947465389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396261956466911298310259 21594392934700366947465389)
          ·
            refine ⟨8097897350512637605299521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21594392934700366947465389 8097897350512637605299521)
            ·
              refine ⟨6073423012884478203974641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097897350512637605299521 6073423012884478203974641)
              ·
                refine ⟨4555067259663358652980981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073423012884478203974641 4555067259663358652980981)
                ·
                  refine ⟨427037555593439873716967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555067259663358652980981 427037555593439873716967)
                  ·
                    rfl

theorem cell22_3742437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_3742437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742437 prefixEnd_3742437 := by exact prefixLift 3742437
  have htrace : WordTrace (prefixWord ++ tailWord_3742437) baseStart_3742437 baseEnd_3742437 := by
    simpa [prefixWord, tailWord_3742437, baseEnd_3742437] using wordTrace_append hprefix tailTrace_3742437
  have hstable : (prefixWord ++ tailWord_3742437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742437).length < 2 ^ (prefixWord ++ tailWord_3742437).sum := by decide
  have hdescent : baseEnd_3742437 < baseStart_3742437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742497 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3742497 : Nat := 118140960795 + 3742497 * 2 ^ 59
def prefixEnd_3742497 : Nat := 4983230072969 + 3 ^ 40 * 3742497 * 2
def baseEnd_3742497 : Nat := 1281133206006499464650717

theorem tailTrace_3742497 : CollatzResearch.WordTrace tailWord_3742497 prefixEnd_3742497 1281133206006499464650717 := by
  unfold tailWord_3742497
  simp only [CollatzResearch.WordTrace]
  refine ⟨136500079522580011445977745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91000053015053340963985163 136500079522580011445977745)
  ·
    refine ⟨102375059641935008584483309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136500079522580011445977745 102375059641935008584483309)
    ·
      refine ⟨38390647365725628219181241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102375059641935008584483309 38390647365725628219181241)
      ·
        refine ⟨28792985524294221164385931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38390647365725628219181241 28792985524294221164385931)
        ·
          refine ⟨43189478286441331746578897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28792985524294221164385931 43189478286441331746578897)
          ·
            refine ⟨32392108714830998809934173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43189478286441331746578897 32392108714830998809934173)
            ·
              refine ⟨12147040768061624553725315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32392108714830998809934173 12147040768061624553725315)
              ·
                refine ⟨18220561152092436830587973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12147040768061624553725315 18220561152092436830587973)
                ·
                  refine ⟨3416355216017331905735245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18220561152092436830587973 3416355216017331905735245)
                  ·
                    refine ⟨1281133206006499464650717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416355216017331905735245 1281133206006499464650717)
                    ·
                      rfl

theorem cell22_3742497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3742497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742497 prefixEnd_3742497 := by exact prefixLift 3742497
  have htrace : WordTrace (prefixWord ++ tailWord_3742497) baseStart_3742497 baseEnd_3742497 := by
    simpa [prefixWord, tailWord_3742497, baseEnd_3742497] using wordTrace_append hprefix tailTrace_3742497
  have hstable : (prefixWord ++ tailWord_3742497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742497).length < 2 ^ (prefixWord ++ tailWord_3742497).sum := by decide
  have hdescent : baseEnd_3742497 < baseStart_3742497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742527 : List Nat := [1, 1, 2, 2, 5, 1, 4, 6]
def baseStart_3742527 : Nat := 118140960795 + 3742527 * 2 ^ 59
def prefixEnd_3742527 : Nat := 4983230072969 + 3 ^ 40 * 3742527 * 2
def baseEnd_3742527 : Nat := 142349275068843265155625

theorem tailTrace_3742527 : CollatzResearch.WordTrace tailWord_3742527 prefixEnd_3742527 142349275068843265155625 := by
  unfold tailWord_3742527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136501173712471326569569835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91000782474980884379713223 136501173712471326569569835)
  ·
    refine ⟨204751760568706989854354753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136501173712471326569569835 204751760568706989854354753)
    ·
      refine ⟨153563820426530242390766065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204751760568706989854354753 153563820426530242390766065)
      ·
        refine ⟨115172865319897681793074549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153563820426530242390766065 115172865319897681793074549)
        ·
          refine ⟨10797456123740407668100739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115172865319897681793074549 10797456123740407668100739)
          ·
            refine ⟨16196184185610611502151109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797456123740407668100739 16196184185610611502151109)
            ·
              refine ⟨3036784534801989656653333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16196184185610611502151109 3036784534801989656653333)
              ·
                refine ⟨142349275068843265155625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3036784534801989656653333 142349275068843265155625)
                ·
                  rfl

theorem cell22_3742527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 6].length) (baseStart_3742527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742527 prefixEnd_3742527 := by exact prefixLift 3742527
  have htrace : WordTrace (prefixWord ++ tailWord_3742527) baseStart_3742527 baseEnd_3742527 := by
    simpa [prefixWord, tailWord_3742527, baseEnd_3742527] using wordTrace_append hprefix tailTrace_3742527
  have hstable : (prefixWord ++ tailWord_3742527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742527).length < 2 ^ (prefixWord ++ tailWord_3742527).sum := by decide
  have hdescent : baseEnd_3742527 < baseStart_3742527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742542 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_3742542 : Nat := 118140960795 + 3742542 * 2 ^ 59
def prefixEnd_3742542 : Nat := 4983230072969 + 3 ^ 40 * 3742542 * 2
def baseEnd_3742542 : Nat := 1281148610426134347275579

theorem tailTrace_3742542 : CollatzResearch.WordTrace tailWord_3742542 prefixEnd_3742542 1281148610426134347275579 := by
  unfold tailWord_3742542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17062715100927123016420735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91001147204944656087577253 17062715100927123016420735)
  ·
    refine ⟨25594072651390684524631103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17062715100927123016420735 25594072651390684524631103)
    ·
      refine ⟨38391108977086026786946655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594072651390684524631103 38391108977086026786946655)
      ·
        refine ⟨57586663465629040180419983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38391108977086026786946655 57586663465629040180419983)
        ·
          refine ⟨86379995198443560270629975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57586663465629040180419983 86379995198443560270629975)
          ·
            refine ⟨129569992797665340405944963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86379995198443560270629975 129569992797665340405944963)
            ·
              refine ⟨194354989196498010608917445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129569992797665340405944963 194354989196498010608917445)
              ·
                refine ⟨36441560474343376989172021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194354989196498010608917445 36441560474343376989172021)
                ·
                  refine ⟨3416396294469691592734877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36441560474343376989172021 3416396294469691592734877)
                  ·
                    refine ⟨1281148610426134347275579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416396294469691592734877 1281148610426134347275579)
                    ·
                      rfl

theorem cell22_3742542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_3742542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742542 prefixEnd_3742542 := by exact prefixLift 3742542
  have htrace : WordTrace (prefixWord ++ tailWord_3742542) baseStart_3742542 baseEnd_3742542 := by
    simpa [prefixWord, tailWord_3742542, baseEnd_3742542] using wordTrace_append hprefix tailTrace_3742542
  have hstable : (prefixWord ++ tailWord_3742542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742542).length < 2 ^ (prefixWord ++ tailWord_3742542).sum := by decide
  have hdescent : baseEnd_3742542 < baseStart_3742542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742572 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_3742572 : Nat := 118140960795 + 3742572 * 2 ^ 59
def prefixEnd_3742572 : Nat := 4983230072969 + 3 ^ 40 * 3742572 * 2
def baseEnd_3742572 : Nat := 427052960013074756341829

theorem tailTrace_3742572 : CollatzResearch.WordTrace tailWord_3742572 prefixEnd_3742572 427052960013074756341829 := by
  unfold tailWord_3742572
  simp only [CollatzResearch.WordTrace]
  refine ⟨68251407498654149627478985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91001876664872199503305313 68251407498654149627478985)
  ·
    refine ⟨51188555623990612220609239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68251407498654149627478985 51188555623990612220609239)
    ·
      refine ⟨76782833435985918330913859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51188555623990612220609239 76782833435985918330913859)
      ·
        refine ⟨115174250153978877496370789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76782833435985918330913859 115174250153978877496370789)
        ·
          refine ⟨21595171903871039530569523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115174250153978877496370789 21595171903871039530569523)
          ·
            refine ⟨32392757855806559295854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21595171903871039530569523 32392757855806559295854285)
            ·
              refine ⟨12147284195927459735945357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32392757855806559295854285 12147284195927459735945357)
              ·
                refine ⟨4555231573472797400979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12147284195927459735945357 4555231573472797400979509)
                ·
                  refine ⟨427052960013074756341829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555231573472797400979509 427052960013074756341829)
                  ·
                    rfl

theorem cell22_3742572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_3742572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742572 prefixEnd_3742572 := by exact prefixLift 3742572
  have htrace : WordTrace (prefixWord ++ tailWord_3742572) baseStart_3742572 baseEnd_3742572 := by
    simpa [prefixWord, tailWord_3742572, baseEnd_3742572] using wordTrace_append hprefix tailTrace_3742572
  have hstable : (prefixWord ++ tailWord_3742572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742572).length < 2 ^ (prefixWord ++ tailWord_3742572).sum := by decide
  have hdescent : baseEnd_3742572 < baseStart_3742572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742653 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3742653 : Nat := 118140960795 + 3742653 * 2 ^ 59
def prefixEnd_3742653 : Nat := 4983230072969 + 3 ^ 40 * 3742653 * 2
def baseEnd_3742653 : Nat := 1281186607994567057750239

theorem tailTrace_3742653 : CollatzResearch.WordTrace tailWord_3742653 prefixEnd_3742653 1281186607994567057750239 := by
  unfold tailWord_3742653
  simp only [CollatzResearch.WordTrace]
  refine ⟨136505769310014850088656613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91003846206676566725771075 136505769310014850088656613)
  ·
    refine ⟨25594831745627784391623115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136505769310014850088656613 25594831745627784391623115)
    ·
      refine ⟨38392247618441676587434673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25594831745627784391623115 38392247618441676587434673)
      ·
        refine ⟨28794185713831257440576005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38392247618441676587434673 28794185713831257440576005)
        ·
          refine ⟨5398909821343360770108001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28794185713831257440576005 5398909821343360770108001)
          ·
            refine ⟨4049182366007520577581001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5398909821343360770108001 4049182366007520577581001)
            ·
              refine ⟨3036886774505640433185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049182366007520577581001 3036886774505640433185751)
              ·
                refine ⟨4555330161758460649778627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036886774505640433185751 4555330161758460649778627)
                ·
                  refine ⟨6832995242637690974667941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4555330161758460649778627 6832995242637690974667941)
                  ·
                    refine ⟨1281186607994567057750239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6832995242637690974667941 1281186607994567057750239)
                    ·
                      rfl

theorem cell22_3742653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3742653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742653 prefixEnd_3742653 := by exact prefixLift 3742653
  have htrace : WordTrace (prefixWord ++ tailWord_3742653) baseStart_3742653 baseEnd_3742653 := by
    simpa [prefixWord, tailWord_3742653, baseEnd_3742653] using wordTrace_append hprefix tailTrace_3742653
  have hstable : (prefixWord ++ tailWord_3742653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742653).length < 2 ^ (prefixWord ++ tailWord_3742653).sum := by decide
  have hdescent : baseEnd_3742653 < baseStart_3742653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742741 : List Nat := [1, 3, 2, 1, 4, 1, 4, 1, 5]
def baseStart_3742741 : Nat := 118140960795 + 3742741 * 2 ^ 59
def prefixEnd_3742741 : Nat := 4983230072969 + 3 ^ 40 * 3742741 * 2
def baseEnd_3742741 : Nat := 427072244064321387183323

theorem tailTrace_3742741 : CollatzResearch.WordTrace tailWord_3742741 prefixEnd_3742741 427072244064321387183323 := by
  unfold tailWord_3742741
  simp only [CollatzResearch.WordTrace]
  refine ⟨136508978933696041117860077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91005985955797360745240051 136508978933696041117860077)
  ·
    refine ⟨51190867100136015419197529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136508978933696041117860077 51190867100136015419197529)
    ·
      refine ⟨38393150325102011564398147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51190867100136015419197529 38393150325102011564398147)
      ·
        refine ⟨57589725487653017346597221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38393150325102011564398147 57589725487653017346597221)
        ·
          refine ⟨10798073528934940752486979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57589725487653017346597221 10798073528934940752486979)
          ·
            refine ⟨16197110293402411128730469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10798073528934940752486979 16197110293402411128730469)
            ·
              refine ⟨3036958180012952086636963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16197110293402411128730469 3036958180012952086636963)
              ·
                refine ⟨4555437270019428129955445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036958180012952086636963 4555437270019428129955445)
                ·
                  refine ⟨427072244064321387183323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555437270019428129955445 427072244064321387183323)
                  ·
                    rfl

theorem cell22_3742741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_3742741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742741 prefixEnd_3742741 := by exact prefixLift 3742741
  have htrace : WordTrace (prefixWord ++ tailWord_3742741) baseStart_3742741 baseEnd_3742741 := by
    simpa [prefixWord, tailWord_3742741, baseEnd_3742741] using wordTrace_append hprefix tailTrace_3742741
  have hstable : (prefixWord ++ tailWord_3742741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742741).length < 2 ^ (prefixWord ++ tailWord_3742741).sum := by decide
  have hdescent : baseEnd_3742741 < baseStart_3742741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742801 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 2, 3]
def baseStart_3742801 : Nat := 118140960795 + 3742801 * 2 ^ 59
def prefixEnd_3742801 : Nat := 4983230072969 + 3 ^ 40 * 3742801 * 2
def baseEnd_3742801 : Nat := 1281237271419144005049785

theorem tailTrace_3742801 : CollatzResearch.WordTrace tailWord_3742801 prefixEnd_3742801 1281237271419144005049785 := by
  unfold tailWord_3742801
  simp only [CollatzResearch.WordTrace]
  refine ⟨136511167313478671365044257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91007444875652447576696171 136511167313478671365044257)
  ·
    refine ⟨102383375485109003523783193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136511167313478671365044257 102383375485109003523783193)
    ·
      refine ⟨76787531613831752642837395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102383375485109003523783193 76787531613831752642837395)
      ·
        refine ⟨115181297420747628964256093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76787531613831752642837395 115181297420747628964256093)
        ·
          refine ⟨43192986532780360861596035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115181297420747628964256093 43192986532780360861596035)
          ·
            refine ⟨64789479799170541292394053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43192986532780360861596035 64789479799170541292394053)
            ·
              refine ⟨12148027462344476492323885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64789479799170541292394053 12148027462344476492323885)
              ·
                refine ⟨4555510298379178684621457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12148027462344476492323885 4555510298379178684621457)
                ·
                  refine ⟨3416632723784384013466093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4555510298379178684621457 3416632723784384013466093)
                  ·
                    refine ⟨1281237271419144005049785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416632723784384013466093 1281237271419144005049785)
                    ·
                      rfl

theorem cell22_3742801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_3742801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742801 prefixEnd_3742801 := by exact prefixLift 3742801
  have htrace : WordTrace (prefixWord ++ tailWord_3742801) baseStart_3742801 baseEnd_3742801 := by
    simpa [prefixWord, tailWord_3742801, baseEnd_3742801] using wordTrace_append hprefix tailTrace_3742801
  have hstable : (prefixWord ++ tailWord_3742801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742801).length < 2 ^ (prefixWord ++ tailWord_3742801).sum := by decide
  have hdescent : baseEnd_3742801 < baseStart_3742801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742859 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 5]
def baseStart_3742859 : Nat := 118140960795 + 3742859 * 2 ^ 59
def prefixEnd_3742859 : Nat := 4983230072969 + 3 ^ 40 * 3742859 * 2
def baseEnd_3742859 : Nat := 427085708668150395699869

theorem tailTrace_3742859 : CollatzResearch.WordTrace tailWord_3742859 prefixEnd_3742859 427085708668150395699869 := by
  unfold tailWord_3742859
  simp only [CollatzResearch.WordTrace]
  refine ⟨136513282747268547270655631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91008855164845698180437087 136513282747268547270655631)
  ·
    refine ⟨204769924120902820905983447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136513282747268547270655631 204769924120902820905983447)
    ·
      refine ⟨307154886181354231358975171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204769924120902820905983447 307154886181354231358975171)
      ·
        refine ⟨460732329272031347038462757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307154886181354231358975171 460732329272031347038462757)
        ·
          refine ⟨86387311738505877569711767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 460732329272031347038462757 86387311738505877569711767)
          ·
            refine ⟨129580967607758816354567651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86387311738505877569711767 129580967607758816354567651)
            ·
              refine ⟨194371451411638224531851477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129580967607758816354567651 194371451411638224531851477)
              ·
                refine ⟨4555580892460270887465269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194371451411638224531851477 4555580892460270887465269)
                ·
                  refine ⟨427085708668150395699869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555580892460270887465269 427085708668150395699869)
                  ·
                    rfl

theorem cell22_3742859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 5].length) (baseStart_3742859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742859 prefixEnd_3742859 := by exact prefixLift 3742859
  have htrace : WordTrace (prefixWord ++ tailWord_3742859) baseStart_3742859 baseEnd_3742859 := by
    simpa [prefixWord, tailWord_3742859, baseEnd_3742859] using wordTrace_append hprefix tailTrace_3742859
  have hstable : (prefixWord ++ tailWord_3742859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742859).length < 2 ^ (prefixWord ++ tailWord_3742859).sum := by decide
  have hdescent : baseEnd_3742859 < baseStart_3742859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742897 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 1, 3]
def baseStart_3742897 : Nat := 118140960795 + 3742897 * 2 ^ 59
def prefixEnd_3742897 : Nat := 4983230072969 + 3 ^ 40 * 3742897 * 2
def baseEnd_3742897 : Nat := 1281270134181031754649491

theorem tailTrace_3742897 : CollatzResearch.WordTrace tailWord_3742897 prefixEnd_3742897 1281270134181031754649491 := by
  unfold tailWord_3742897
  simp only [CollatzResearch.WordTrace]
  refine ⟨136514668721130879760538945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91009779147420586507025963 136514668721130879760538945)
  ·
    refine ⟨102386001540848159820404209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136514668721130879760538945 102386001540848159820404209)
    ·
      refine ⟨76789501155636119865303157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102386001540848159820404209 76789501155636119865303157)
      ·
        refine ⟨7199015733340886237372171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76789501155636119865303157 7199015733340886237372171)
        ·
          refine ⟨10798523600011329356058257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199015733340886237372171 10798523600011329356058257)
          ·
            refine ⟨8098892700008497017043693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10798523600011329356058257 8098892700008497017043693)
            ·
              refine ⟨3037084762503186381391385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8098892700008497017043693 3037084762503186381391385)
              ·
                refine ⟨2277813571877389786043539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037084762503186381391385 2277813571877389786043539)
                ·
                  refine ⟨3416720357816084679065309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2277813571877389786043539 3416720357816084679065309)
                  ·
                    refine ⟨1281270134181031754649491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3416720357816084679065309 1281270134181031754649491)
                    ·
                      rfl

theorem cell22_3742897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_3742897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742897 prefixEnd_3742897 := by exact prefixLift 3742897
  have htrace : WordTrace (prefixWord ++ tailWord_3742897) baseStart_3742897 baseEnd_3742897 := by
    simpa [prefixWord, tailWord_3742897, baseEnd_3742897] using wordTrace_append hprefix tailTrace_3742897
  have hstable : (prefixWord ++ tailWord_3742897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742897).length < 2 ^ (prefixWord ++ tailWord_3742897).sum := by decide
  have hdescent : baseEnd_3742897 < baseStart_3742897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742904 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_3742904 : Nat := 118140960795 + 3742904 * 2 ^ 59
def prefixEnd_3742904 : Nat := 4983230072969 + 3 ^ 40 * 3742904 * 2
def baseEnd_3742904 : Nat := 427090843474695356574823

theorem tailTrace_3742904 : CollatzResearch.WordTrace tailWord_3742904 prefixEnd_3742904 427090843474695356574823 := by
  unfold tailWord_3742904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68257462016052759978021883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91009949354737013304029177 68257462016052759978021883)
  ·
    refine ⟨102386193024079139967032825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68257462016052759978021883 102386193024079139967032825)
    ·
      refine ⟨76789644768059354975274619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102386193024079139967032825 76789644768059354975274619)
      ·
        refine ⟨115184467152089032462911929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76789644768059354975274619 115184467152089032462911929)
        ·
          refine ⟨86388350364066774347183947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115184467152089032462911929 86388350364066774347183947)
          ·
            refine ⟨129582525546100161520775921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86388350364066774347183947 129582525546100161520775921)
            ·
              refine ⟨97186894159575121140581941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129582525546100161520775921 97186894159575121140581941)
              ·
                refine ⟨9111271327460167606929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97186894159575121140581941 9111271327460167606929557)
                ·
                  refine ⟨427090843474695356574823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9111271327460167606929557 427090843474695356574823)
                  ·
                    rfl

theorem cell22_3742904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_3742904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742904 prefixEnd_3742904 := by exact prefixLift 3742904
  have htrace : WordTrace (prefixWord ++ tailWord_3742904) baseStart_3742904 baseEnd_3742904 := by
    simpa [prefixWord, tailWord_3742904, baseEnd_3742904] using wordTrace_append hprefix tailTrace_3742904
  have hstable : (prefixWord ++ tailWord_3742904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742904).length < 2 ^ (prefixWord ++ tailWord_3742904).sum := by decide
  have hdescent : baseEnd_3742904 < baseStart_3742904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742910 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_3742910 : Nat := 118140960795 + 3742910 * 2 ^ 59
def prefixEnd_3742910 : Nat := 4983230072969 + 3 ^ 40 * 3742910 * 2
def baseEnd_3742910 : Nat := 427091528115568018024817

theorem tailTrace_3742910 : CollatzResearch.WordTrace tailWord_3742910 prefixEnd_3742910 427091528115568018024817 := by
  unfold tailWord_3742910
  simp only [CollatzResearch.WordTrace]
  refine ⟨17064392858760472872595273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91010095246722521987174789 17064392858760472872595273)
  ·
    refine ⟨12798294644070354654446455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17064392858760472872595273 12798294644070354654446455)
    ·
      refine ⟨19197441966105531981669683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12798294644070354654446455 19197441966105531981669683)
      ·
        refine ⟨28796162949158297972504525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19197441966105531981669683 28796162949158297972504525)
        ·
          refine ⟨10798561105934361739689197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28796162949158297972504525 10798561105934361739689197)
          ·
            refine ⟨4049460414725385652383449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10798561105934361739689197 4049460414725385652383449)
            ·
              refine ⟨3037095311044039239287587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049460414725385652383449 3037095311044039239287587)
              ·
                refine ⟨4555642966566058858931381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037095311044039239287587 4555642966566058858931381)
                ·
                  refine ⟨427091528115568018024817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555642966566058858931381 427091528115568018024817)
                  ·
                    rfl

theorem cell22_3742910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_3742910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742910 prefixEnd_3742910 := by exact prefixLift 3742910
  have htrace : WordTrace (prefixWord ++ tailWord_3742910) baseStart_3742910 baseEnd_3742910 := by
    simpa [prefixWord, tailWord_3742910, baseEnd_3742910] using wordTrace_append hprefix tailTrace_3742910
  have hstable : (prefixWord ++ tailWord_3742910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742910).length < 2 ^ (prefixWord ++ tailWord_3742910).sum := by decide
  have hdescent : baseEnd_3742910 < baseStart_3742910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742919 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3742919 : Nat := 118140960795 + 3742919 * 2 ^ 59
def prefixEnd_3742919 : Nat := 4983230072969 + 3 ^ 40 * 3742919 * 2
def baseEnd_3742919 : Nat := 1281277665230631030599423

theorem tailTrace_3742919 : CollatzResearch.WordTrace tailWord_3742919 prefixEnd_3742919 1281277665230631030599423 := by
  unfold tailWord_3742919
  simp only [CollatzResearch.WordTrace]
  refine ⟨136515471127051177517839811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91010314084700785011893207 136515471127051177517839811)
  ·
    refine ⟨204773206690576766276759717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136515471127051177517839811 204773206690576766276759717)
    ·
      refine ⟨38394976254483143676892447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204773206690576766276759717 38394976254483143676892447)
      ·
        refine ⟨57592464381724715515338671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38394976254483143676892447 57592464381724715515338671)
        ·
          refine ⟨86388696572587073273008007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57592464381724715515338671 86388696572587073273008007)
          ·
            refine ⟨129583044858880609909512011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86388696572587073273008007 129583044858880609909512011)
            ·
              refine ⟨194374567288320914864268017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129583044858880609909512011 194374567288320914864268017)
              ·
                refine ⟨145780925466240686148201013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194374567288320914864268017 145780925466240686148201013)
                ·
                  refine ⟨13666961762460064326393845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145780925466240686148201013 13666961762460064326393845)
                  ·
                    refine ⟨1281277665230631030599423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13666961762460064326393845 1281277665230631030599423)
                    ·
                      rfl

theorem cell22_3742919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3742919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742919 prefixEnd_3742919 := by exact prefixLift 3742919
  have htrace : WordTrace (prefixWord ++ tailWord_3742919) baseStart_3742919 baseEnd_3742919 := by
    simpa [prefixWord, tailWord_3742919, baseEnd_3742919] using wordTrace_append hprefix tailTrace_3742919
  have hstable : (prefixWord ++ tailWord_3742919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742919).length < 2 ^ (prefixWord ++ tailWord_3742919).sum := by decide
  have hdescent : baseEnd_3742919 < baseStart_3742919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742949 : List Nat := [1, 3, 1, 4, 13]
def baseStart_3742949 : Nat := 118140960795 + 3742949 * 2 ^ 59
def prefixEnd_3742949 : Nat := 4983230072969 + 3 ^ 40 * 3742949 * 2
def baseEnd_3742949 : Nat := 5272789855323954536417

theorem tailTrace_3742949 : CollatzResearch.WordTrace tailWord_3742949 prefixEnd_3742949 5272789855323954536417 := by
  unfold tailWord_3742949
  simp only [CollatzResearch.WordTrace]
  refine ⟨136516565316942492641431901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91011043544628328427621267 136516565316942492641431901)
  ·
    refine ⟨51193711993853434740536963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136516565316942492641431901 51193711993853434740536963)
    ·
      refine ⟨76790567990780152110805445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51193711993853434740536963 76790567990780152110805445)
      ·
        refine ⟨14398231498271278520776021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76790567990780152110805445 14398231498271278520776021)
        ·
          refine ⟨5272789855323954536417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 14398231498271278520776021 5272789855323954536417)
          ·
            rfl

theorem cell22_3742949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 13].length) (baseStart_3742949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742949 prefixEnd_3742949 := by exact prefixLift 3742949
  have htrace : WordTrace (prefixWord ++ tailWord_3742949) baseStart_3742949 baseEnd_3742949 := by
    simpa [prefixWord, tailWord_3742949, baseEnd_3742949] using wordTrace_append hprefix tailTrace_3742949
  have hstable : (prefixWord ++ tailWord_3742949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742949).length < 2 ^ (prefixWord ++ tailWord_3742949).sum := by decide
  have hdescent : baseEnd_3742949 < baseStart_3742949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3742955 : List Nat := [1, 1, 1, 1, 2, 8, 2, 2, 4]
def baseStart_3742955 : Nat := 118140960795 + 3742955 * 2 ^ 59
def prefixEnd_3742955 : Nat := 4983230072969 + 3 ^ 40 * 3742955 * 2
def baseEnd_3742955 : Nat := 427096662922112978899771

theorem tailTrace_3742955 : CollatzResearch.WordTrace tailWord_3742955 prefixEnd_3742955 427096662922112978899771 := by
  unfold tailWord_3742955
  simp only [CollatzResearch.WordTrace]
  refine ⟨136516784154920755666150319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91011189436613837110766879 136516784154920755666150319)
  ·
    refine ⟨204775176232381133499225479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136516784154920755666150319 204775176232381133499225479)
    ·
      refine ⟨307162764348571700248838219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204775176232381133499225479 307162764348571700248838219)
      ·
        refine ⟨460744146522857550373257329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307162764348571700248838219 460744146522857550373257329)
        ·
          refine ⟨345558109892143162779942997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460744146522857550373257329 345558109892143162779942997)
          ·
            refine ⟨4049509100298552688827457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 345558109892143162779942997 4049509100298552688827457)
            ·
              refine ⟨3037131825223914516620593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049509100298552688827457 3037131825223914516620593)
              ·
                refine ⟨2277848868917935887465445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037131825223914516620593 2277848868917935887465445)
                ·
                  refine ⟨427096662922112978899771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277848868917935887465445 427096662922112978899771)
                  ·
                    rfl

theorem cell22_3742955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 2, 4].length) (baseStart_3742955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3742955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3742955 prefixEnd_3742955 := by exact prefixLift 3742955
  have htrace : WordTrace (prefixWord ++ tailWord_3742955) baseStart_3742955 baseEnd_3742955 := by
    simpa [prefixWord, tailWord_3742955, baseEnd_3742955] using wordTrace_append hprefix tailTrace_3742955
  have hstable : (prefixWord ++ tailWord_3742955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3742955).length < 2 ^ (prefixWord ++ tailWord_3742955).sum := by decide
  have hdescent : baseEnd_3742955 < baseStart_3742955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3742955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743011 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 7]
def baseStart_3743011 : Nat := 118140960795 + 3743011 * 2 ^ 59
def prefixEnd_3743011 : Nat := 4983230072969 + 3 ^ 40 * 3743011 * 2
def baseEnd_3743011 : Nat := 427103052903591152433047

theorem tailTrace_3743011 : CollatzResearch.WordTrace tailWord_3743011 prefixEnd_3743011 427103052903591152433047 := by
  unfold tailWord_3743011
  simp only [CollatzResearch.WordTrace]
  refine ⟨136518826642717877230188887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91012551095145251486792591 136518826642717877230188887)
  ·
    refine ⟨204778239964076815845283331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136518826642717877230188887 204778239964076815845283331)
    ·
      refine ⟨307167359946115223767924997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204778239964076815845283331 307167359946115223767924997)
      ·
        refine ⟨57593879989896604456485937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307167359946115223767924997 57593879989896604456485937)
        ·
          refine ⟨43195409992422453342364453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57593879989896604456485937 43195409992422453342364453)
          ·
            refine ⟨8099139373579210001693335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43195409992422453342364453 8099139373579210001693335)
            ·
              refine ⟨12148709060368815002540003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099139373579210001693335 12148709060368815002540003)
              ·
                refine ⟨18223063590553222503810005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148709060368815002540003 18223063590553222503810005)
                ·
                  refine ⟨427103052903591152433047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18223063590553222503810005 427103052903591152433047)
                  ·
                    rfl

theorem cell22_3743011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 7].length) (baseStart_3743011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743011 prefixEnd_3743011 := by exact prefixLift 3743011
  have htrace : WordTrace (prefixWord ++ tailWord_3743011) baseStart_3743011 baseEnd_3743011 := by
    simpa [prefixWord, tailWord_3743011, baseEnd_3743011] using wordTrace_append hprefix tailTrace_3743011
  have hstable : (prefixWord ++ tailWord_3743011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743011).length < 2 ^ (prefixWord ++ tailWord_3743011).sum := by decide
  have hdescent : baseEnd_3743011 < baseStart_3743011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743073 : List Nat := [1, 2, 3, 1, 1, 1, 1, 8, 4]
def baseStart_3743073 : Nat := 118140960795 + 3743073 * 2 ^ 59
def prefixEnd_3743073 : Nat := 4983230072969 + 3 ^ 40 * 3743073 * 2
def baseEnd_3743073 : Nat := 427110127525941987416317

theorem tailTrace_3743073 : CollatzResearch.WordTrace tailWord_3743073 prefixEnd_3743073 427110127525941987416317 := by
  unfold tailWord_3743073
  simp only [CollatzResearch.WordTrace]
  refine ⟨136521087968493261818945873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91014058645662174545963915 136521087968493261818945873)
  ·
    refine ⟨102390815976369946364209405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136521087968493261818945873 102390815976369946364209405)
    ·
      refine ⟨38396555991138729886578527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102390815976369946364209405 38396555991138729886578527)
      ·
        refine ⟨57594833986708094829867791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38396555991138729886578527 57594833986708094829867791)
        ·
          refine ⟨86392250980062142244801687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57594833986708094829867791 86392250980062142244801687)
          ·
            refine ⟨129588376470093213367202531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86392250980062142244801687 129588376470093213367202531)
            ·
              refine ⟨194382564705139820050803797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129588376470093213367202531 194382564705139820050803797)
              ·
                refine ⟨2277920680138357266220357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 194382564705139820050803797 2277920680138357266220357)
                ·
                  refine ⟨427110127525941987416317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277920680138357266220357 427110127525941987416317)
                  ·
                    rfl

theorem cell22_3743073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_3743073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743073 prefixEnd_3743073 := by exact prefixLift 3743073
  have htrace : WordTrace (prefixWord ++ tailWord_3743073) baseStart_3743073 baseEnd_3743073 := by
    simpa [prefixWord, tailWord_3743073, baseEnd_3743073] using wordTrace_append hprefix tailTrace_3743073
  have hstable : (prefixWord ++ tailWord_3743073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743073).length < 2 ^ (prefixWord ++ tailWord_3743073).sum := by decide
  have hdescent : baseEnd_3743073 < baseStart_3743073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743101 : List Nat := [1, 4, 1, 1, 2, 2, 1, 10]
def baseStart_3743101 : Nat := 118140960795 + 3743101 * 2 ^ 59
def prefixEnd_3743101 : Nat := 4983230072969 + 3 ^ 40 * 3743101 * 2
def baseEnd_3743101 : Nat := 142371107505560358060985

theorem tailTrace_3743101 : CollatzResearch.WordTrace tailWord_3743101 prefixEnd_3743101 142371107505560358060985 := by
  unfold tailWord_3743101
  simp only [CollatzResearch.WordTrace]
  refine ⟨136522109212391822600965157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91014739474927881733976771 136522109212391822600965157)
  ·
    refine ⟨25597895477323466737680967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136522109212391822600965157 25597895477323466737680967)
    ·
      refine ⟨38396843215985200106521451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25597895477323466737680967 38396843215985200106521451)
      ·
        refine ⟨57595264823977800159782177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38396843215985200106521451 57595264823977800159782177)
        ·
          refine ⟨43196448617983350119836633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57595264823977800159782177 43196448617983350119836633)
          ·
            refine ⟨32397336463487512589877475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43196448617983350119836633 32397336463487512589877475)
            ·
              refine ⟨48596004695231268884816213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32397336463487512589877475 48596004695231268884816213)
              ·
                refine ⟨142371107505560358060985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48596004695231268884816213 142371107505560358060985)
                ·
                  rfl

theorem cell22_3743101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 10].length) (baseStart_3743101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743101 prefixEnd_3743101 := by exact prefixLift 3743101
  have htrace : WordTrace (prefixWord ++ tailWord_3743101) baseStart_3743101 baseEnd_3743101 := by
    simpa [prefixWord, tailWord_3743101, baseEnd_3743101] using wordTrace_append hprefix tailTrace_3743101
  have hstable : (prefixWord ++ tailWord_3743101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743101).length < 2 ^ (prefixWord ++ tailWord_3743101).sum := by decide
  have hdescent : baseEnd_3743101 < baseStart_3743101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743105 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3743105 : Nat := 118140960795 + 3743105 * 2 ^ 59
def prefixEnd_3743105 : Nat := 4983230072969 + 3 ^ 40 * 3743105 * 2
def baseEnd_3743105 : Nat := 1281341336831788545448853

theorem tailTrace_3743105 : CollatzResearch.WordTrace tailWord_3743105 prefixEnd_3743105 1281341336831788545448853 := by
  unfold tailWord_3743105
  simp only [CollatzResearch.WordTrace]
  refine ⟨136522255104377331284110769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91014836736251554189407179 136522255104377331284110769)
  ·
    refine ⟨102391691328282998463083077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136522255104377331284110769 102391691328282998463083077)
    ·
      refine ⟨19198442124053062211828077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102391691328282998463083077 19198442124053062211828077)
      ·
        refine ⟨7199415796519898329435529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19198442124053062211828077 7199415796519898329435529)
        ·
          refine ⟨5399561847389923747076647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199415796519898329435529 5399561847389923747076647)
          ·
            refine ⟨8099342771084885620614971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399561847389923747076647 8099342771084885620614971)
            ·
              refine ⟨12149014156627328430922457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099342771084885620614971 12149014156627328430922457)
              ·
                refine ⟨9111760617470496323191843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12149014156627328430922457 9111760617470496323191843)
                ·
                  refine ⟨13667640926205744484787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9111760617470496323191843 13667640926205744484787765)
                  ·
                    refine ⟨1281341336831788545448853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13667640926205744484787765 1281341336831788545448853)
                    ·
                      rfl

theorem cell22_3743105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3743105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743105 prefixEnd_3743105 := by exact prefixLift 3743105
  have htrace : WordTrace (prefixWord ++ tailWord_3743105) baseStart_3743105 baseEnd_3743105 := by
    simpa [prefixWord, tailWord_3743105, baseEnd_3743105] using wordTrace_append hprefix tailTrace_3743105
  have hstable : (prefixWord ++ tailWord_3743105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743105).length < 2 ^ (prefixWord ++ tailWord_3743105).sum := by decide
  have hdescent : baseEnd_3743105 < baseStart_3743105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743118 : List Nat := [4, 1, 1, 4, 2, 10]
def baseStart_3743118 : Nat := 118140960795 + 3743118 * 2 ^ 59
def prefixEnd_3743118 : Nat := 4983230072969 + 3 ^ 40 * 3743118 * 2
def baseEnd_3743118 : Nat := 15819083790092109195973

theorem tailTrace_3743118 : CollatzResearch.WordTrace tailWord_3743118 prefixEnd_3743118 15819083790092109195973 := by
  unfold tailWord_3743118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17065341156666279313041751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91015152835553489669556005 17065341156666279313041751)
  ·
    refine ⟨25598011734999418969562627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17065341156666279313041751 25598011734999418969562627)
    ·
      refine ⟨38397017602499128454343941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25598011734999418969562627 38397017602499128454343941)
      ·
        refine ⟨7199440800468586585189489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38397017602499128454343941 7199440800468586585189489)
        ·
          refine ⟨5399580600351439938892117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199440800468586585189489 5399580600351439938892117)
          ·
            refine ⟨15819083790092109195973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5399580600351439938892117 15819083790092109195973)
            ·
              rfl

theorem cell22_3743118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 10].length) (baseStart_3743118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743118 prefixEnd_3743118 := by exact prefixLift 3743118
  have htrace : WordTrace (prefixWord ++ tailWord_3743118) baseStart_3743118 baseEnd_3743118 := by
    simpa [prefixWord, tailWord_3743118, baseEnd_3743118] using wordTrace_append hprefix tailTrace_3743118
  have hstable : (prefixWord ++ tailWord_3743118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743118).length < 2 ^ (prefixWord ++ tailWord_3743118).sum := by decide
  have hdescent : baseEnd_3743118 < baseStart_3743118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743124 : List Nat := [2, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3743124 : Nat := 118140960795 + 3743124 * 2 ^ 59
def prefixEnd_3743124 : Nat := 4983230072969 + 3 ^ 40 * 3743124 * 2
def baseEnd_3743124 : Nat := 427115946973359609741265

theorem tailTrace_3743124 : CollatzResearch.WordTrace tailWord_3743124 prefixEnd_3743124 427115946973359609741265 := by
  unfold tailWord_3743124
  simp only [CollatzResearch.WordTrace]
  refine ⟨68261474045654248764526213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91015298727538998352701617 68261474045654248764526213)
  ·
    refine ⟨12799026383560171643348665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68261474045654248764526213 12799026383560171643348665)
    ·
      refine ⟨9599269787670128732511499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12799026383560171643348665 9599269787670128732511499)
      ·
        refine ⟨14398904681505193098767249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599269787670128732511499 14398904681505193098767249)
        ·
          refine ⟨10799178511128894824075437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14398904681505193098767249 10799178511128894824075437)
          ·
            refine ⟨4049691941673335559028289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10799178511128894824075437 4049691941673335559028289)
            ·
              refine ⟨3037268956255001669271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049691941673335559028289 3037268956255001669271217)
              ·
                refine ⟨2277951717191251251953413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037268956255001669271217 2277951717191251251953413)
                ·
                  refine ⟨427115946973359609741265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277951717191251251953413 427115946973359609741265)
                  ·
                    rfl

theorem cell22_3743124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3743124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743124 prefixEnd_3743124 := by exact prefixLift 3743124
  have htrace : WordTrace (prefixWord ++ tailWord_3743124) baseStart_3743124 baseEnd_3743124 := by
    simpa [prefixWord, tailWord_3743124, baseEnd_3743124] using wordTrace_append hprefix tailTrace_3743124
  have hstable : (prefixWord ++ tailWord_3743124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743124).length < 2 ^ (prefixWord ++ tailWord_3743124).sum := by decide
  have hdescent : baseEnd_3743124 < baseStart_3743124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743178 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3743178 : Nat := 118140960795 + 3743178 * 2 ^ 59
def prefixEnd_3743178 : Nat := 4983230072969 + 3 ^ 40 * 3743178 * 2
def baseEnd_3743178 : Nat := 1281366326223640688373629

theorem tailTrace_3743178 : CollatzResearch.WordTrace tailWord_3743178 prefixEnd_3743178 1281366326223640688373629 := by
  unfold tailWord_3743178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34131229408278216187879547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91016611755408576501012125 34131229408278216187879547)
  ·
    refine ⟨51196844112417324281819321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34131229408278216187879547 51196844112417324281819321)
    ·
      refine ⟨38397633084312993211364491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51196844112417324281819321 38397633084312993211364491)
      ·
        refine ⟨57596449626469489817046737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38397633084312993211364491 57596449626469489817046737)
        ·
          refine ⟨43197337219852117362785053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57596449626469489817046737 43197337219852117362785053)
          ·
            refine ⟨16199001457444544011044395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43197337219852117362785053 16199001457444544011044395)
            ·
              refine ⟨24298502186166816016566593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199001457444544011044395 24298502186166816016566593)
              ·
                refine ⟨18223876639625112012424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24298502186166816016566593 18223876639625112012424945)
                ·
                  refine ⟨13667907479718834009318709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18223876639625112012424945 13667907479718834009318709)
                  ·
                    refine ⟨1281366326223640688373629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13667907479718834009318709 1281366326223640688373629)
                    ·
                      rfl

theorem cell22_3743178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3743178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743178 prefixEnd_3743178 := by exact prefixLift 3743178
  have htrace : WordTrace (prefixWord ++ tailWord_3743178) baseStart_3743178 baseEnd_3743178 := by
    simpa [prefixWord, tailWord_3743178, baseEnd_3743178] using wordTrace_append hprefix tailTrace_3743178
  have hstable : (prefixWord ++ tailWord_3743178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743178).length < 2 ^ (prefixWord ++ tailWord_3743178).sum := by decide
  have hdescent : baseEnd_3743178 < baseStart_3743178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743180 : List Nat := [2, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_3743180 : Nat := 118140960795 + 3743180 * 2 ^ 59
def prefixEnd_3743180 : Nat := 4983230072969 + 3 ^ 40 * 3743180 * 2
def baseEnd_3743180 : Nat := 427122336954837783274541

theorem tailTrace_3743180 : CollatzResearch.WordTrace tailWord_3743180 prefixEnd_3743180 427122336954837783274541 := by
  unfold tailWord_3743180
  simp only [CollatzResearch.WordTrace]
  refine ⟨68262495289552809546545497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91016660386070412728727329 68262495289552809546545497)
  ·
    refine ⟨51196871467164607159909123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68262495289552809546545497 51196871467164607159909123)
    ·
      refine ⟨76795307200746910739863685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51196871467164607159909123 76795307200746910739863685)
      ·
        refine ⟨14399120100140045763724441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76795307200746910739863685 14399120100140045763724441)
        ·
          refine ⟨10799340075105034322793331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399120100140045763724441 10799340075105034322793331)
          ·
            refine ⟨16199010112657551484189997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799340075105034322793331 16199010112657551484189997)
            ·
              refine ⟨6074628792246581806571249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16199010112657551484189997 6074628792246581806571249)
              ·
                refine ⟨4555971594184936354928437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074628792246581806571249 4555971594184936354928437)
                ·
                  refine ⟨427122336954837783274541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555971594184936354928437 427122336954837783274541)
                  ·
                    rfl

theorem cell22_3743180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_3743180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743180 prefixEnd_3743180 := by exact prefixLift 3743180
  have htrace : WordTrace (prefixWord ++ tailWord_3743180) baseStart_3743180 baseEnd_3743180 := by
    simpa [prefixWord, tailWord_3743180, baseEnd_3743180] using wordTrace_append hprefix tailTrace_3743180
  have hstable : (prefixWord ++ tailWord_3743180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743180).length < 2 ^ (prefixWord ++ tailWord_3743180).sum := by decide
  have hdescent : baseEnd_3743180 < baseStart_3743180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743197 : List Nat := [1, 4, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3743197 : Nat := 118140960795 + 3743197 * 2 ^ 59
def prefixEnd_3743197 : Nat := 4983230072969 + 3 ^ 40 * 3743197 * 2
def baseEnd_3743197 : Nat := 427124276770643657382857

theorem tailTrace_3743197 : CollatzResearch.WordTrace tailWord_3743197 prefixEnd_3743197 427124276770643657382857 := by
  unfold tailWord_3743197
  simp only [CollatzResearch.WordTrace]
  refine ⟨136525610620044030996459845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91017073746696020664306563 136525610620044030996459845)
  ·
    refine ⟨25598551991258255811836221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136525610620044030996459845 25598551991258255811836221)
    ·
      refine ⟨9599456996721845929438583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25598551991258255811836221 9599456996721845929438583)
      ·
        refine ⟨14399185495082768894157875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599456996721845929438583 14399185495082768894157875)
        ·
          refine ⟨21598778242624153341236813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399185495082768894157875 21598778242624153341236813)
          ·
            refine ⟨8099541840984057502963805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21598778242624153341236813 8099541840984057502963805)
            ·
              refine ⟨3037328190369021563611427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8099541840984057502963805 3037328190369021563611427)
              ·
                refine ⟨4555992285553532345417141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037328190369021563611427 4555992285553532345417141)
                ·
                  refine ⟨427124276770643657382857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555992285553532345417141 427124276770643657382857)
                  ·
                    rfl

theorem cell22_3743197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3743197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743197 prefixEnd_3743197 := by exact prefixLift 3743197
  have htrace : WordTrace (prefixWord ++ tailWord_3743197) baseStart_3743197 baseEnd_3743197 := by
    simpa [prefixWord, tailWord_3743197, baseEnd_3743197] using wordTrace_append hprefix tailTrace_3743197
  have hstable : (prefixWord ++ tailWord_3743197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743197).length < 2 ^ (prefixWord ++ tailWord_3743197).sum := by decide
  have hdescent : baseEnd_3743197 < baseStart_3743197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743208 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_3743208 : Nat := 118140960795 + 3743208 * 2 ^ 59
def prefixEnd_3743208 : Nat := 4983230072969 + 3 ^ 40 * 3743208 * 2
def baseEnd_3743208 : Nat := 427125531945576870041179

theorem tailTrace_3743208 : CollatzResearch.WordTrace tailWord_3743208 prefixEnd_3743208 427125531945576870041179 := by
  unfold tailWord_3743208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263005911502089937555139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91017341215336119916740185 68263005911502089937555139)
  ·
    refine ⟨102394508867253134906332709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68263005911502089937555139 102394508867253134906332709)
    ·
      refine ⟨19198970412609962794937383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102394508867253134906332709 19198970412609962794937383)
      ·
        refine ⟨28798455618914944192406075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19198970412609962794937383 28798455618914944192406075)
        ·
          refine ⟨43197683428372416288609113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28798455618914944192406075 43197683428372416288609113)
          ·
            refine ⟨32398262571279312216456835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43197683428372416288609113 32398262571279312216456835)
            ·
              refine ⟨48597393856918968324685253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32398262571279312216456835 48597393856918968324685253)
              ·
                refine ⟨9112011348172306560878485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48597393856918968324685253 9112011348172306560878485)
                ·
                  refine ⟨427125531945576870041179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9112011348172306560878485 427125531945576870041179)
                  ·
                    rfl

theorem cell22_3743208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_3743208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743208 prefixEnd_3743208 := by exact prefixLift 3743208
  have htrace : WordTrace (prefixWord ++ tailWord_3743208) baseStart_3743208 baseEnd_3743208 := by
    simpa [prefixWord, tailWord_3743208, baseEnd_3743208] using wordTrace_append hprefix tailTrace_3743208
  have hstable : (prefixWord ++ tailWord_3743208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743208).length < 2 ^ (prefixWord ++ tailWord_3743208).sum := by decide
  have hdescent : baseEnd_3743208 < baseStart_3743208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743240 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_3743240 : Nat := 118140960795 + 3743240 * 2 ^ 59
def prefixEnd_3743240 : Nat := 4983230072969 + 3 ^ 40 * 3743240 * 2
def baseEnd_3743240 : Nat := 1281387550090693193323439

theorem tailTrace_3743240 : CollatzResearch.WordTrace tailWord_3743240 prefixEnd_3743240 1281387550090693193323439 := by
  unfold tailWord_3743240
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263589479444124670137587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91018119305925499560183449 68263589479444124670137587)
  ·
    refine ⟨102395384219166187005206381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68263589479444124670137587 102395384219166187005206381)
    ·
      refine ⟨38398269082187320126952393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102395384219166187005206381 38398269082187320126952393)
      ·
        refine ⟨28798701811640490095214295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38398269082187320126952393 28798701811640490095214295)
        ·
          refine ⟨43198052717460735142821443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28798701811640490095214295 43198052717460735142821443)
          ·
            refine ⟨64797079076191102714232165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43198052717460735142821443 64797079076191102714232165)
            ·
              refine ⟨12149452326785831758918531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64797079076191102714232165 12149452326785831758918531)
              ·
                refine ⟨18224178490178747638377797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12149452326785831758918531 18224178490178747638377797)
                ·
                  refine ⟨3417033466908515182195837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18224178490178747638377797 3417033466908515182195837)
                  ·
                    refine ⟨1281387550090693193323439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417033466908515182195837 1281387550090693193323439)
                    ·
                      rfl

theorem cell22_3743240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_3743240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743240 prefixEnd_3743240 := by exact prefixLift 3743240
  have htrace : WordTrace (prefixWord ++ tailWord_3743240) baseStart_3743240 baseEnd_3743240 := by
    simpa [prefixWord, tailWord_3743240, baseEnd_3743240] using wordTrace_append hprefix tailTrace_3743240
  have hstable : (prefixWord ++ tailWord_3743240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743240).length < 2 ^ (prefixWord ++ tailWord_3743240).sum := by decide
  have hdescent : baseEnd_3743240 < baseStart_3743240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743253 : List Nat := [1, 3, 2, 1, 3, 2, 1, 9]
def baseStart_3743253 : Nat := 118140960795 + 3743253 * 2 ^ 59
def prefixEnd_3743253 : Nat := 4983230072969 + 3 ^ 40 * 3743253 * 2
def baseEnd_3743253 : Nat := 142376888917373943638711

theorem tailTrace_3743253 : CollatzResearch.WordTrace tailWord_3743253 prefixEnd_3743253 142376888917373943638711 := by
  unfold tailWord_3743253
  simp only [CollatzResearch.WordTrace]
  refine ⟨136527653107841152560498413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91018435405227435040332275 136527653107841152560498413)
  ·
    refine ⟨51197869915440432210186905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136527653107841152560498413 51197869915440432210186905)
    ·
      refine ⟨38398402436580324157640179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51197869915440432210186905 38398402436580324157640179)
      ·
        refine ⟨57597603654870486236460269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38398402436580324157640179 57597603654870486236460269)
        ·
          refine ⟨21599101370576432338672601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57597603654870486236460269 21599101370576432338672601)
          ·
            refine ⟨16199326027932324254004451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21599101370576432338672601 16199326027932324254004451)
            ·
              refine ⟨24298989041898486381006677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199326027932324254004451 24298989041898486381006677)
              ·
                refine ⟨142376888917373943638711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24298989041898486381006677 142376888917373943638711)
                ·
                  rfl

theorem cell22_3743253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 9].length) (baseStart_3743253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743253 prefixEnd_3743253 := by exact prefixLift 3743253
  have htrace : WordTrace (prefixWord ++ tailWord_3743253) baseStart_3743253 baseEnd_3743253 := by
    simpa [prefixWord, tailWord_3743253, baseEnd_3743253] using wordTrace_append hprefix tailTrace_3743253
  have hstable : (prefixWord ++ tailWord_3743253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743253).length < 2 ^ (prefixWord ++ tailWord_3743253).sum := by decide
  have hdescent : baseEnd_3743253 < baseStart_3743253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743336 : List Nat := [2, 1, 4, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3743336 : Nat := 118140960795 + 3743336 * 2 ^ 59
def prefixEnd_3743336 : Nat := 4983230072969 + 3 ^ 40 * 3743336 * 2
def baseEnd_3743336 : Nat := 1281420412852580942923145

theorem tailTrace_3743336 : CollatzResearch.WordTrace tailWord_3743336 prefixEnd_3743336 1281420412852580942923145 := by
  unfold tailWord_3743336
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265340183270228867884931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91020453577693638490513241 68265340183270228867884931)
  ·
    refine ⟨102398010274905343301827397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68265340183270228867884931 102398010274905343301827397)
    ·
      refine ⟨19199626926544751869092637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102398010274905343301827397 19199626926544751869092637)
      ·
        refine ⟨7199860097454281950909739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19199626926544751869092637 7199860097454281950909739)
        ·
          refine ⟨10799790146181422926364609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199860097454281950909739 10799790146181422926364609)
          ·
            refine ⟨8099842609636067194773457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10799790146181422926364609 8099842609636067194773457)
            ·
              refine ⟨6074881957227050396080093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8099842609636067194773457 6074881957227050396080093)
              ·
                refine ⟨2278080733960143898530035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6074881957227050396080093 2278080733960143898530035)
                ·
                  refine ⟨3417121100940215847795053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278080733960143898530035 3417121100940215847795053)
                  ·
                    refine ⟨1281420412852580942923145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417121100940215847795053 1281420412852580942923145)
                    ·
                      rfl

theorem cell22_3743336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3743336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743336 prefixEnd_3743336 := by exact prefixLift 3743336
  have htrace : WordTrace (prefixWord ++ tailWord_3743336) baseStart_3743336 baseEnd_3743336 := by
    simpa [prefixWord, tailWord_3743336, baseEnd_3743336] using wordTrace_append hprefix tailTrace_3743336
  have hstable : (prefixWord ++ tailWord_3743336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743336).length < 2 ^ (prefixWord ++ tailWord_3743336).sum := by decide
  have hdescent : baseEnd_3743336 < baseStart_3743336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743343 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 10]
def baseStart_3743343 : Nat := 118140960795 + 3743343 * 2 ^ 59
def prefixEnd_3743343 : Nat := 4983230072969 + 3 ^ 40 * 3743343 * 2
def baseEnd_3743343 : Nat := 427140936365211752666041

theorem tailTrace_3743343 : CollatzResearch.WordTrace tailWord_3743343 prefixEnd_3743343 427140936365211752666041 := by
  unfold tailWord_3743343
  simp only [CollatzResearch.WordTrace]
  refine ⟨136530935677515097931274683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91020623785010065287516455 136530935677515097931274683)
  ·
    refine ⟨204796403516272646896912025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136530935677515097931274683 204796403516272646896912025)
    ·
      refine ⟨153597302637204485172684019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204796403516272646896912025 153597302637204485172684019)
      ·
        refine ⟨230395953955806727759026029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153597302637204485172684019 230395953955806727759026029)
        ·
          refine ⟨86398482733427522909634761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230395953955806727759026029 86398482733427522909634761)
          ·
            refine ⟨64798862050070642182226071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86398482733427522909634761 64798862050070642182226071)
            ·
              refine ⟨97198293075105963273339107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64798862050070642182226071 97198293075105963273339107)
              ·
                refine ⟨145797439612658944910008661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97198293075105963273339107 145797439612658944910008661)
                ·
                  refine ⟨427140936365211752666041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 145797439612658944910008661 427140936365211752666041)
                  ·
                    rfl

theorem cell22_3743343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_3743343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743343 prefixEnd_3743343 := by exact prefixLift 3743343
  have htrace : WordTrace (prefixWord ++ tailWord_3743343) baseStart_3743343 baseEnd_3743343 := by
    simpa [prefixWord, tailWord_3743343, baseEnd_3743343] using wordTrace_append hprefix tailTrace_3743343
  have hstable : (prefixWord ++ tailWord_3743343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743343).length < 2 ^ (prefixWord ++ tailWord_3743343).sum := by decide
  have hdescent : baseEnd_3743343 < baseStart_3743343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743349 : List Nat := [1, 3, 4, 2, 1, 3, 1, 2, 5]
def baseStart_3743349 : Nat := 118140960795 + 3743349 * 2 ^ 59
def prefixEnd_3743349 : Nat := 4983230072969 + 3 ^ 40 * 3743349 * 2
def baseEnd_3743349 : Nat := 427141621006084414116035

theorem tailTrace_3743349 : CollatzResearch.WordTrace tailWord_3743349 prefixEnd_3743349 427141621006084414116035 := by
  unfold tailWord_3743349
  simp only [CollatzResearch.WordTrace]
  refine ⟨136531154515493360955993101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91020769676995573970662067 136531154515493360955993101)
  ·
    refine ⟨51199182943310010358497413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136531154515493360955993101 51199182943310010358497413)
    ·
      refine ⟨9599846801870626942218265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51199182943310010358497413 9599846801870626942218265)
      ·
        refine ⟨7199885101402970206663699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9599846801870626942218265 7199885101402970206663699)
        ·
          refine ⟨10799827652104455309995549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7199885101402970206663699 10799827652104455309995549)
          ·
            refine ⟨4049935369539170741248331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10799827652104455309995549 4049935369539170741248331)
            ·
              refine ⟨6074903054308756111872497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049935369539170741248331 6074903054308756111872497)
              ·
                refine ⟨4556177290731567083904373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074903054308756111872497 4556177290731567083904373)
                ·
                  refine ⟨427141621006084414116035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556177290731567083904373 427141621006084414116035)
                  ·
                    rfl

theorem cell22_3743349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_3743349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743349 prefixEnd_3743349 := by exact prefixLift 3743349
  have htrace : WordTrace (prefixWord ++ tailWord_3743349) baseStart_3743349 baseEnd_3743349 := by
    simpa [prefixWord, tailWord_3743349, baseEnd_3743349] using wordTrace_append hprefix tailTrace_3743349
  have hstable : (prefixWord ++ tailWord_3743349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743349).length < 2 ^ (prefixWord ++ tailWord_3743349).sum := by decide
  have hdescent : baseEnd_3743349 < baseStart_3743349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743360 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_3743360 : Nat := 118140960795 + 3743360 * 2 ^ 59
def prefixEnd_3743360 : Nat := 4983230072969 + 3 ^ 40 * 3743360 * 2
def baseEnd_3743360 : Nat := 427142876181017626774357

theorem tailTrace_3743360 : CollatzResearch.WordTrace tailWord_3743360 prefixEnd_3743360 427142876181017626774357 := by
  unfold tailWord_3743360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68265777859226754917321767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91021037145635673223095689 68265777859226754917321767)
  ·
    refine ⟨102398666788840132375982651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68265777859226754917321767 102398666788840132375982651)
    ·
      refine ⟨153598000183260198563973977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102398666788840132375982651 153598000183260198563973977)
      ·
        refine ⟨115198500137445148922980483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153598000183260198563973977 115198500137445148922980483)
        ·
          refine ⟨172797750206167723384470725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115198500137445148922980483 172797750206167723384470725)
          ·
            refine ⟨32399578163656448134588261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172797750206167723384470725 32399578163656448134588261)
            ·
              refine ⟨6074920905685584025235299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32399578163656448134588261 6074920905685584025235299)
              ·
                refine ⟨9112381358528376037852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074920905685584025235299 9112381358528376037852949)
                ·
                  refine ⟨427142876181017626774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9112381358528376037852949 427142876181017626774357)
                  ·
                    rfl

theorem cell22_3743360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_3743360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743360 prefixEnd_3743360 := by exact prefixLift 3743360
  have htrace : WordTrace (prefixWord ++ tailWord_3743360) baseStart_3743360 baseEnd_3743360 := by
    simpa [prefixWord, tailWord_3743360, baseEnd_3743360] using wordTrace_append hprefix tailTrace_3743360
  have hstable : (prefixWord ++ tailWord_3743360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743360).length < 2 ^ (prefixWord ++ tailWord_3743360).sum := by decide
  have hdescent : baseEnd_3743360 < baseStart_3743360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 8, 3]
def baseStart_3743375 : Nat := 118140960795 + 3743375 * 2 ^ 59
def prefixEnd_3743375 : Nat := 4983230072969 + 3 ^ 40 * 3743375 * 2
def baseEnd_3743375 : Nat := 1281433763349597841198025

theorem tailTrace_3743375 : CollatzResearch.WordTrace tailWord_3743375 prefixEnd_3743375 1281433763349597841198025 := by
  unfold tailWord_3743375
  simp only [CollatzResearch.WordTrace]
  refine ⟨136532102813399167396439579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91021401875599444930959719 136532102813399167396439579)
  ·
    refine ⟨204798154220098751094659369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136532102813399167396439579 204798154220098751094659369)
    ·
      refine ⟨153598615665074063320994527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204798154220098751094659369 153598615665074063320994527)
      ·
        refine ⟨230397923497611094981491791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153598615665074063320994527 230397923497611094981491791)
        ·
          refine ⟨345596885246416642472237687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230397923497611094981491791 345596885246416642472237687)
          ·
            refine ⟨518395327869624963708356531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345596885246416642472237687 518395327869624963708356531)
            ·
              refine ⟨777592991804437445562534797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518395327869624963708356531 777592991804437445562534797)
              ·
                refine ⟨291597371926664042085950549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 777592991804437445562534797 291597371926664042085950549)
                ·
                  refine ⟨3417156702265594243194733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 291597371926664042085950549 3417156702265594243194733)
                  ·
                    refine ⟨1281433763349597841198025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417156702265594243194733 1281433763349597841198025)
                    ·
                      rfl

theorem cell22_3743375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 3].length) (baseStart_3743375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743375 prefixEnd_3743375 := by exact prefixLift 3743375
  have htrace : WordTrace (prefixWord ++ tailWord_3743375) baseStart_3743375 baseEnd_3743375 := by
    simpa [prefixWord, tailWord_3743375, baseEnd_3743375] using wordTrace_append hprefix tailTrace_3743375
  have hstable : (prefixWord ++ tailWord_3743375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743375).length < 2 ^ (prefixWord ++ tailWord_3743375).sum := by decide
  have hdescent : baseEnd_3743375 < baseStart_3743375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743392 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_3743392 : Nat := 118140960795 + 3743392 * 2 ^ 59
def prefixEnd_3743392 : Nat := 4983230072969 + 3 ^ 40 * 3743392 * 2
def baseEnd_3743392 : Nat := 1281439582797015463522973

theorem tailTrace_3743392 : CollatzResearch.WordTrace tailWord_3743392 prefixEnd_3743392 1281439582797015463522973 := by
  unfold tailWord_3743392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68266361427168789649904215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91021815236225052866538953 68266361427168789649904215)
  ·
    refine ⟨102399542140753184474856323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68266361427168789649904215 102399542140753184474856323)
    ·
      refine ⟨153599313211129776712284485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102399542140753184474856323 153599313211129776712284485)
      ·
        refine ⟨28799871227086833133553341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153599313211129776712284485 28799871227086833133553341)
        ·
          refine ⟨10799951710157562425082503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28799871227086833133553341 10799951710157562425082503)
          ·
            refine ⟨16199927565236343637623755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799951710157562425082503 16199927565236343637623755)
            ·
              refine ⟨24299891347854515456435633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199927565236343637623755 24299891347854515456435633)
              ·
                refine ⟨18224918510890886592326725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24299891347854515456435633 18224918510890886592326725)
                ·
                  refine ⟨3417172220792041236061261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18224918510890886592326725 3417172220792041236061261)
                  ·
                    refine ⟨1281439582797015463522973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417172220792041236061261 1281439582797015463522973)
                    ·
                      rfl

theorem cell22_3743392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_3743392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743392 prefixEnd_3743392 := by exact prefixLift 3743392
  have htrace : WordTrace (prefixWord ++ tailWord_3743392) baseStart_3743392 baseEnd_3743392 := by
    simpa [prefixWord, tailWord_3743392, baseEnd_3743392] using wordTrace_append hprefix tailTrace_3743392
  have hstable : (prefixWord ++ tailWord_3743392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743392).length < 2 ^ (prefixWord ++ tailWord_3743392).sum := by decide
  have hdescent : baseEnd_3743392 < baseStart_3743392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743422 : List Nat := [4, 2, 1, 1, 2, 3, 2, 7]
def baseStart_3743422 : Nat := 118140960795 + 3743422 * 2 ^ 59
def prefixEnd_3743422 : Nat := 4983230072969 + 3 ^ 40 * 3743422 * 2
def baseEnd_3743422 : Nat := 142383316934456153919209

theorem tailTrace_3743422 : CollatzResearch.WordTrace tailWord_3743422 prefixEnd_3743422 142383316934456153919209 := by
  unfold tailWord_3743422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066727130528611802925065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91022544696152596282267013 17066727130528611802925065)
  ·
    refine ⟨12800045347896458852193799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17066727130528611802925065 12800045347896458852193799)
    ·
      refine ⟨19200068021844688278290699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12800045347896458852193799 19200068021844688278290699)
      ·
        refine ⟨28800102032767032417436049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19200068021844688278290699 28800102032767032417436049)
        ·
          refine ⟨21600076524575274313077037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28800102032767032417436049 21600076524575274313077037)
          ·
            refine ⟨8100028696715727867403889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21600076524575274313077037 8100028696715727867403889)
            ·
              refine ⟨6075021522536795900552917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8100028696715727867403889 6075021522536795900552917)
              ·
                refine ⟨142383316934456153919209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6075021522536795900552917 142383316934456153919209)
                ·
                  rfl

theorem cell22_3743422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_3743422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743422 prefixEnd_3743422 := by exact prefixLift 3743422
  have htrace : WordTrace (prefixWord ++ tailWord_3743422) baseStart_3743422 baseEnd_3743422 := by
    simpa [prefixWord, tailWord_3743422, baseEnd_3743422] using wordTrace_append hprefix tailTrace_3743422
  have hstable : (prefixWord ++ tailWord_3743422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743422).length < 2 ^ (prefixWord ++ tailWord_3743422).sum := by decide
  have hdescent : baseEnd_3743422 < baseStart_3743422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743465 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_3743465 : Nat := 118140960795 + 3743465 * 2 ^ 59
def prefixEnd_3743465 : Nat := 4983230072969 + 3 ^ 40 * 3743465 * 2
def baseEnd_3743465 : Nat := 1281464572188867606447749

theorem tailTrace_3743465 : CollatzResearch.WordTrace tailWord_3743465 prefixEnd_3743465 1281464572188867606447749 := by
  unfold tailWord_3743465
  simp only [CollatzResearch.WordTrace]
  refine ⟨136535385383073112767215849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91023590255382075178143899 136535385383073112767215849)
  ·
    refine ⟨102401539037304834575411887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136535385383073112767215849 102401539037304834575411887)
    ·
      refine ⟨153602308555957251863117831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102401539037304834575411887 153602308555957251863117831)
      ·
        refine ⟨230403462833935877794676747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153602308555957251863117831 230403462833935877794676747)
        ·
          refine ⟨345605194250903816692015121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230403462833935877794676747 345605194250903816692015121)
          ·
            refine ⟨259203895688177862519011341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345605194250903816692015121 259203895688177862519011341)
            ·
              refine ⟨97201460883066698444629253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259203895688177862519011341 97201460883066698444629253)
              ·
                refine ⟨18225273915575005958367985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97201460883066698444629253 18225273915575005958367985)
                ·
                  refine ⟨13668955436681254468775989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18225273915575005958367985 13668955436681254468775989)
                  ·
                    refine ⟨1281464572188867606447749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13668955436681254468775989 1281464572188867606447749)
                    ·
                      rfl

theorem cell22_3743465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_3743465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743465 prefixEnd_3743465 := by exact prefixLift 3743465
  have htrace : WordTrace (prefixWord ++ tailWord_3743465) baseStart_3743465 baseEnd_3743465 := by
    simpa [prefixWord, tailWord_3743465, baseEnd_3743465] using wordTrace_append hprefix tailTrace_3743465
  have hstable : (prefixWord ++ tailWord_3743465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743465).length < 2 ^ (prefixWord ++ tailWord_3743465).sum := by decide
  have hdescent : baseEnd_3743465 < baseStart_3743465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743497 : List Nat := [1, 2, 1, 1, 3, 2, 1, 6, 1, 4]
def baseStart_3743497 : Nat := 118140960795 + 3743497 * 2 ^ 59
def prefixEnd_3743497 : Nat := 4983230072969 + 3 ^ 40 * 3743497 * 2
def baseEnd_3743497 : Nat := 1281475526442830189647651

theorem tailTrace_3743497 : CollatzResearch.WordTrace tailWord_3743497 prefixEnd_3743497 1281475526442830189647651 := by
  unfold tailWord_3743497
  simp only [CollatzResearch.WordTrace]
  refine ⟨136536552518957182232380745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91024368345971454821587163 136536552518957182232380745)
  ·
    refine ⟨102402414389217886674285559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136536552518957182232380745 102402414389217886674285559)
    ·
      refine ⟨153603621583826830011428339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102402414389217886674285559 153603621583826830011428339)
      ·
        refine ⟨230405432375740245017142509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153603621583826830011428339 230405432375740245017142509)
        ·
          refine ⟨86402037140902591881428441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230405432375740245017142509 86402037140902591881428441)
          ·
            refine ⟨64801527855676943911071331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86402037140902591881428441 64801527855676943911071331)
            ·
              refine ⟨97202291783515415866606997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64801527855676943911071331 97202291783515415866606997)
              ·
                refine ⟨4556357427352285118747203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97202291783515415866606997 4556357427352285118747203)
                ·
                  refine ⟨6834536141028427678120805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556357427352285118747203 6834536141028427678120805)
                  ·
                    refine ⟨1281475526442830189647651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6834536141028427678120805 1281475526442830189647651)
                    ·
                      rfl

theorem cell22_3743497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_3743497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743497 prefixEnd_3743497 := by exact prefixLift 3743497
  have htrace : WordTrace (prefixWord ++ tailWord_3743497) baseStart_3743497 baseEnd_3743497 := by
    simpa [prefixWord, tailWord_3743497, baseEnd_3743497] using wordTrace_append hprefix tailTrace_3743497
  have hstable : (prefixWord ++ tailWord_3743497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743497).length < 2 ^ (prefixWord ++ tailWord_3743497).sum := by decide
  have hdescent : baseEnd_3743497 < baseStart_3743497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743514 : List Nat := [3, 1, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3743514 : Nat := 118140960795 + 3743514 * 2 ^ 59
def prefixEnd_3743514 : Nat := 4983230072969 + 3 ^ 40 * 3743514 * 2
def baseEnd_3743514 : Nat := 1281481345890247811972599

theorem tailTrace_3743514 : CollatzResearch.WordTrace tailWord_3743514 prefixEnd_3743514 1281481345890247811972599 := by
  unfold tailWord_3743514
  simp only [CollatzResearch.WordTrace]
  refine ⟨34134293139973898533937399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91024781706597062757166397 34134293139973898533937399)
  ·
    refine ⟨51201439709960847800906099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34134293139973898533937399 51201439709960847800906099)
    ·
      refine ⟨76802159564941271701359149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51201439709960847800906099 76802159564941271701359149)
      ·
        refine ⟨28800809836852976888009681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76802159564941271701359149 28800809836852976888009681)
        ·
          refine ⟨21600607377639732666007261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28800809836852976888009681 21600607377639732666007261)
          ·
            refine ⟨8100227766614899749752723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21600607377639732666007261 8100227766614899749752723)
            ·
              refine ⟨12150341649922349624629085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100227766614899749752723 12150341649922349624629085)
              ·
                refine ⟨4556378118720881109235907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12150341649922349624629085 4556378118720881109235907)
                ·
                  refine ⟨6834567178081321663853861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556378118720881109235907 6834567178081321663853861)
                  ·
                    refine ⟨1281481345890247811972599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6834567178081321663853861 1281481345890247811972599)
                    ·
                      rfl

theorem cell22_3743514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3743514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743514 prefixEnd_3743514 := by exact prefixLift 3743514
  have htrace : WordTrace (prefixWord ++ tailWord_3743514) baseStart_3743514 baseEnd_3743514 := by
    simpa [prefixWord, tailWord_3743514, baseEnd_3743514] using wordTrace_append hprefix tailTrace_3743514
  have hstable : (prefixWord ++ tailWord_3743514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743514).length < 2 ^ (prefixWord ++ tailWord_3743514).sum := by decide
  have hdescent : baseEnd_3743514 < baseStart_3743514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743544 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_3743544 : Nat := 118140960795 + 3743544 * 2 ^ 59
def prefixEnd_3743544 : Nat := 4983230072969 + 3 ^ 40 * 3743544 * 2
def baseEnd_3743544 : Nat := 1281491615503337733722507

theorem tailTrace_3743544 : CollatzResearch.WordTrace tailWord_3743544 prefixEnd_3743544 1281491615503337733722507 := by
  unfold tailWord_3743544
  simp only [CollatzResearch.WordTrace]
  refine ⟨68269133374893454629670843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91025511166524606172894457 68269133374893454629670843)
  ·
    refine ⟨102403700062340181944506265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68269133374893454629670843 102403700062340181944506265)
    ·
      refine ⟨76802775046755136458379699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102403700062340181944506265 76802775046755136458379699)
      ·
        refine ⟨115204162570132704687569549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76802775046755136458379699 115204162570132704687569549)
        ·
          refine ⟨43201560963799764257838581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115204162570132704687569549 43201560963799764257838581)
          ·
            refine ⟨4050146340356227899172367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43201560963799764257838581 4050146340356227899172367)
            ·
              refine ⟨6075219510534341848758551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050146340356227899172367 6075219510534341848758551)
              ·
                refine ⟨9112829265801512773137827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075219510534341848758551 9112829265801512773137827)
                ·
                  refine ⟨13669243898702269159706741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9112829265801512773137827 13669243898702269159706741)
                  ·
                    refine ⟨1281491615503337733722507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13669243898702269159706741 1281491615503337733722507)
                    ·
                      rfl

theorem cell22_3743544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_3743544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743544 prefixEnd_3743544 := by exact prefixLift 3743544
  have htrace : WordTrace (prefixWord ++ tailWord_3743544) baseStart_3743544 baseEnd_3743544 := by
    simpa [prefixWord, tailWord_3743544, baseEnd_3743544] using wordTrace_append hprefix tailTrace_3743544
  have hstable : (prefixWord ++ tailWord_3743544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743544).length < 2 ^ (prefixWord ++ tailWord_3743544).sum := by decide
  have hdescent : baseEnd_3743544 < baseStart_3743544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743632 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_3743632 : Nat := 118140960795 + 3743632 * 2 ^ 59
def prefixEnd_3743632 : Nat := 4983230072969 + 3 ^ 40 * 3743632 * 2
def baseEnd_3743632 : Nat := 1281521739701734837522237

theorem tailTrace_3743632 : CollatzResearch.WordTrace tailWord_3743632 prefixEnd_3743632 1281521739701734837522237 := by
  unfold tailWord_3743632
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270738186734050144272575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91027650915645400192363433 68270738186734050144272575)
  ·
    refine ⟨102406107280101075216408863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68270738186734050144272575 102406107280101075216408863)
    ·
      refine ⟨153609160920151612824613295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102406107280101075216408863 153609160920151612824613295)
      ·
        refine ⟨230413741380227419236919943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153609160920151612824613295 230413741380227419236919943)
        ·
          refine ⟨345620612070341128855379915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230413741380227419236919943 345620612070341128855379915)
          ·
            refine ⟨518430918105511693283069873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345620612070341128855379915 518430918105511693283069873)
            ·
              refine ⟨388823188579133769962302405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 518430918105511693283069873 388823188579133769962302405)
              ·
                refine ⟨72904347858587581867931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 388823188579133769962302405 72904347858587581867931701)
                ·
                  refine ⟨6834782611742585800118597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72904347858587581867931701 6834782611742585800118597)
                  ·
                    refine ⟨1281521739701734837522237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6834782611742585800118597 1281521739701734837522237)
                    ·
                      rfl

theorem cell22_3743632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_3743632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743632 prefixEnd_3743632 := by exact prefixLift 3743632
  have htrace : WordTrace (prefixWord ++ tailWord_3743632) baseStart_3743632 baseEnd_3743632 := by
    simpa [prefixWord, tailWord_3743632, baseEnd_3743632] using wordTrace_append hprefix tailTrace_3743632
  have hstable : (prefixWord ++ tailWord_3743632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743632).length < 2 ^ (prefixWord ++ tailWord_3743632).sum := by decide
  have hdescent : baseEnd_3743632 < baseStart_3743632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743636 : List Nat := [2, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_3743636 : Nat := 118140960795 + 3743636 * 2 ^ 59
def prefixEnd_3743636 : Nat := 4983230072969 + 3 ^ 40 * 3743636 * 2
def baseEnd_3743636 : Nat := 427174369661160053474075

theorem tailTrace_3743636 : CollatzResearch.WordTrace tailWord_3743636 prefixEnd_3743636 427174369661160053474075 := by
  unfold tailWord_3743636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270811132726804485845381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91027748176969072647793841 68270811132726804485845381)
  ·
    refine ⟨12800777087386275841096009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68270811132726804485845381 12800777087386275841096009)
    ·
      refine ⟨9600582815539706880822007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12800777087386275841096009 9600582815539706880822007)
      ·
        refine ⟨14400874223309560321233011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600582815539706880822007 14400874223309560321233011)
        ·
          refine ⟨21601311334964340481849517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14400874223309560321233011 21601311334964340481849517)
          ·
            refine ⟨8100491750611627680693569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21601311334964340481849517 8100491750611627680693569)
            ·
              refine ⟨6075368812958720760520177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8100491750611627680693569 6075368812958720760520177)
              ·
                refine ⟨4556526609719040570390133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075368812958720760520177 4556526609719040570390133)
                ·
                  refine ⟨427174369661160053474075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556526609719040570390133 427174369661160053474075)
                  ·
                    rfl

theorem cell22_3743636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_3743636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743636 prefixEnd_3743636 := by exact prefixLift 3743636
  have htrace : WordTrace (prefixWord ++ tailWord_3743636) baseStart_3743636 baseEnd_3743636 := by
    simpa [prefixWord, tailWord_3743636, baseEnd_3743636] using wordTrace_append hprefix tailTrace_3743636
  have hstable : (prefixWord ++ tailWord_3743636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743636).length < 2 ^ (prefixWord ++ tailWord_3743636).sum := by decide
  have hdescent : baseEnd_3743636 < baseStart_3743636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743640 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_3743640 : Nat := 118140960795 + 3743640 * 2 ^ 59
def prefixEnd_3743640 : Nat := 4983230072969 + 3 ^ 40 * 3743640 * 2
def baseEnd_3743640 : Nat := 1281524478265225483322213

theorem tailTrace_3743640 : CollatzResearch.WordTrace tailWord_3743640 prefixEnd_3743640 1281524478265225483322213 := by
  unfold tailWord_3743640
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270884078719558827418187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91027845438292745103224249 68270884078719558827418187)
  ·
    refine ⟨102406326118079338241127281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68270884078719558827418187 102406326118079338241127281)
    ·
      refine ⟨76804744588559503680845461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102406326118079338241127281 76804744588559503680845461)
      ·
        refine ⟨3600222402588726735039631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76804744588559503680845461 3600222402588726735039631)
        ·
          refine ⟨5400333603883090102559447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600222402588726735039631 5400333603883090102559447)
          ·
            refine ⟨8100500405824635153839171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400333603883090102559447 8100500405824635153839171)
            ·
              refine ⟨12150750608736952730758757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8100500405824635153839171 12150750608736952730758757)
              ·
                refine ⟨2278265739138178637017267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12150750608736952730758757 2278265739138178637017267)
                ·
                  refine ⟨3417398608707267955525901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278265739138178637017267 3417398608707267955525901)
                  ·
                    refine ⟨1281524478265225483322213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417398608707267955525901 1281524478265225483322213)
                    ·
                      rfl

theorem cell22_3743640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_3743640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743640 prefixEnd_3743640 := by exact prefixLift 3743640
  have htrace : WordTrace (prefixWord ++ tailWord_3743640) baseStart_3743640 baseEnd_3743640 := by
    simpa [prefixWord, tailWord_3743640, baseEnd_3743640] using wordTrace_append hprefix tailTrace_3743640
  have hstable : (prefixWord ++ tailWord_3743640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743640).length < 2 ^ (prefixWord ++ tailWord_3743640).sum := by decide
  have hdescent : baseEnd_3743640 < baseStart_3743640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743679 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 4, 3]
def baseStart_3743679 : Nat := 118140960795 + 3743679 * 2 ^ 59
def prefixEnd_3743679 : Nat := 4983230072969 + 3 ^ 40 * 3743679 * 2
def baseEnd_3743679 : Nat := 1281537828762242381597093

theorem tailTrace_3743679 : CollatzResearch.WordTrace tailWord_3743679 prefixEnd_3743679 1281537828762242381597093 := by
  unfold tailWord_3743679
  simp only [CollatzResearch.WordTrace]
  refine ⟨136543190604297827315506091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91028793736198551543670727 136543190604297827315506091)
  ·
    refine ⟨204814785906446740973259137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136543190604297827315506091 204814785906446740973259137)
    ·
      refine ⟨153611089429835055729944353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204814785906446740973259137 153611089429835055729944353)
      ·
        refine ⟨115208317072376291797458265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153611089429835055729944353 115208317072376291797458265)
        ·
          refine ⟨86406237804282218848093699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115208317072376291797458265 86406237804282218848093699)
          ·
            refine ⟨129609356706423328272140549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86406237804282218848093699 129609356706423328272140549)
            ·
              refine ⟨24301754382454374051026353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129609356706423328272140549 24301754382454374051026353)
              ·
                refine ⟨18226315786840780538269765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24301754382454374051026353 18226315786840780538269765)
                ·
                  refine ⟨3417434210032646350925581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18226315786840780538269765 3417434210032646350925581)
                  ·
                    refine ⟨1281537828762242381597093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417434210032646350925581 1281537828762242381597093)
                    ·
                      rfl

theorem cell22_3743679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_3743679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743679 prefixEnd_3743679 := by exact prefixLift 3743679
  have htrace : WordTrace (prefixWord ++ tailWord_3743679) baseStart_3743679 baseEnd_3743679 := by
    simpa [prefixWord, tailWord_3743679, baseEnd_3743679] using wordTrace_append hprefix tailTrace_3743679
  have hstable : (prefixWord ++ tailWord_3743679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743679).length < 2 ^ (prefixWord ++ tailWord_3743679).sum := by decide
  have hdescent : baseEnd_3743679 < baseStart_3743679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743694 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_3743694 : Nat := 118140960795 + 3743694 * 2 ^ 59
def prefixEnd_3743694 : Nat := 4983230072969 + 3 ^ 40 * 3743694 * 2
def baseEnd_3743694 : Nat := 1281542963568787342472047

theorem tailTrace_3743694 : CollatzResearch.WordTrace tailWord_3743694 prefixEnd_3743694 1281542963568787342472047 := by
  unfold tailWord_3743694
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067967212405435609662767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91029158466162323251534757 17067967212405435609662767)
  ·
    refine ⟨25601950818608153414494151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17067967212405435609662767 25601950818608153414494151)
    ·
      refine ⟨38402926227912230121741227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25601950818608153414494151 38402926227912230121741227)
      ·
        refine ⟨57604389341868345182611841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38402926227912230121741227 57604389341868345182611841)
        ·
          refine ⟨43203292006401258886958881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57604389341868345182611841 43203292006401258886958881)
          ·
            refine ⟨32402469004800944165219161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43203292006401258886958881 32402469004800944165219161)
            ·
              refine ⟨24301851753600708123914371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32402469004800944165219161 24301851753600708123914371)
              ·
                refine ⟨36452777630401062185871557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24301851753600708123914371 36452777630401062185871557)
                ·
                  refine ⟨6834895805700199159850917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36452777630401062185871557 6834895805700199159850917)
                  ·
                    refine ⟨1281542963568787342472047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6834895805700199159850917 1281542963568787342472047)
                    ·
                      rfl

theorem cell22_3743694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_3743694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743694 prefixEnd_3743694 := by exact prefixLift 3743694
  have htrace : WordTrace (prefixWord ++ tailWord_3743694) baseStart_3743694 baseEnd_3743694 := by
    simpa [prefixWord, tailWord_3743694, baseEnd_3743694] using wordTrace_append hprefix tailTrace_3743694
  have hstable : (prefixWord ++ tailWord_3743694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743694).length < 2 ^ (prefixWord ++ tailWord_3743694).sum := by decide
  have hdescent : baseEnd_3743694 < baseStart_3743694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743696 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_3743696 : Nat := 118140960795 + 3743696 * 2 ^ 59
def prefixEnd_3743696 : Nat := 4983230072969 + 3 ^ 40 * 3743696 * 2
def baseEnd_3743696 : Nat := 1281543648209660003922041

theorem tailTrace_3743696 : CollatzResearch.WordTrace tailWord_3743696 prefixEnd_3743696 1281543648209660003922041 := by
  unfold tailWord_3743696
  simp only [CollatzResearch.WordTrace]
  refine ⟨68271905322618119609437471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91029207096824159479249961 68271905322618119609437471)
  ·
    refine ⟨102407857983927179414156207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68271905322618119609437471 102407857983927179414156207)
    ·
      refine ⟨153611786975890769121234311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102407857983927179414156207 153611786975890769121234311)
      ·
        refine ⟨230417680463836153681851467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153611786975890769121234311 230417680463836153681851467)
        ·
          refine ⟨345626520695754230522777201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230417680463836153681851467 345626520695754230522777201)
          ·
            refine ⟨259219890521815672892082901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345626520695754230522777201 259219890521815672892082901)
            ·
              refine ⟨6075466184105054833408193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259219890521815672892082901 6075466184105054833408193)
              ·
                refine ⟨4556599638078791125056145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075466184105054833408193 4556599638078791125056145)
                ·
                  refine ⟨3417449728559093343792109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556599638078791125056145 3417449728559093343792109)
                  ·
                    refine ⟨1281543648209660003922041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417449728559093343792109 1281543648209660003922041)
                    ·
                      rfl

theorem cell22_3743696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_3743696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743696 prefixEnd_3743696 := by exact prefixLift 3743696
  have htrace : WordTrace (prefixWord ++ tailWord_3743696) baseStart_3743696 baseEnd_3743696 := by
    simpa [prefixWord, tailWord_3743696, baseEnd_3743696] using wordTrace_append hprefix tailTrace_3743696
  have hstable : (prefixWord ++ tailWord_3743696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743696).length < 2 ^ (prefixWord ++ tailWord_3743696).sum := by decide
  have hdescent : baseEnd_3743696 < baseStart_3743696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743726 : List Nat := [4, 1, 2, 1, 3, 1, 4, 6]
def baseStart_3743726 : Nat := 118140960795 + 3743726 * 2 ^ 59
def prefixEnd_3743726 : Nat := 4983230072969 + 3 ^ 40 * 3743726 * 2
def baseEnd_3743726 : Nat := 142394879758083325074661

theorem tailTrace_3743726 : CollatzResearch.WordTrace tailWord_3743726 prefixEnd_3743726 142394879758083325074661 := by
  unfold tailWord_3743726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068113104390944292808379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91029936556751702894978021 17068113104390944292808379)
  ·
    refine ⟨25602169656586416439212569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17068113104390944292808379 25602169656586416439212569)
    ·
      refine ⟨19201627242439812329409427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25602169656586416439212569 19201627242439812329409427)
      ·
        refine ⟨28802440863659718494114141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19201627242439812329409427 28802440863659718494114141)
        ·
          refine ⟨10800915323872394435292803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28802440863659718494114141 10800915323872394435292803)
          ·
            refine ⟨16201372985808591652939205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800915323872394435292803 16201372985808591652939205)
            ·
              refine ⟨3037757434839110934926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16201372985808591652939205 3037757434839110934926101)
              ·
                refine ⟨142394879758083325074661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3037757434839110934926101 142394879758083325074661)
                ·
                  rfl

theorem cell22_3743726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_3743726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743726 prefixEnd_3743726 := by exact prefixLift 3743726
  have htrace : WordTrace (prefixWord ++ tailWord_3743726) baseStart_3743726 baseEnd_3743726 := by
    simpa [prefixWord, tailWord_3743726, baseEnd_3743726] using wordTrace_append hprefix tailTrace_3743726
  have hstable : (prefixWord ++ tailWord_3743726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743726).length < 2 ^ (prefixWord ++ tailWord_3743726).sum := by decide
  have hdescent : baseEnd_3743726 < baseStart_3743726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743764 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3743764 : Nat := 118140960795 + 3743764 * 2 ^ 59
def prefixEnd_3743764 : Nat := 4983230072969 + 3 ^ 40 * 3743764 * 2
def baseEnd_3743764 : Nat := 1281566925999330493221833

theorem tailTrace_3743764 : CollatzResearch.WordTrace tailWord_3743764 prefixEnd_3743764 1281566925999330493221833 := by
  unfold tailWord_3743764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68273145404494943416175173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91030860539326591221566897 68273145404494943416175173)
  ·
    refine ⟨12801214763342801890532845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68273145404494943416175173 12801214763342801890532845)
    ·
      refine ⟨4800455536253550708949817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12801214763342801890532845 4800455536253550708949817)
      ·
        refine ⟨3600341652190163031712363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4800455536253550708949817 3600341652190163031712363)
        ·
          refine ⟨5400512478285244547568545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600341652190163031712363 5400512478285244547568545)
          ·
            refine ⟨4050384358713933410676409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400512478285244547568545 4050384358713933410676409)
            ·
              refine ⟨3037788269035450058007307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050384358713933410676409 3037788269035450058007307)
              ·
                refine ⟨4556682403553175087010961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037788269035450058007307 4556682403553175087010961)
                ·
                  refine ⟨3417511802664881315258221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556682403553175087010961 3417511802664881315258221)
                  ·
                    refine ⟨1281566925999330493221833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417511802664881315258221 1281566925999330493221833)
                    ·
                      rfl

theorem cell22_3743764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3743764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743764 prefixEnd_3743764 := by exact prefixLift 3743764
  have htrace : WordTrace (prefixWord ++ tailWord_3743764) baseStart_3743764 baseEnd_3743764 := by
    simpa [prefixWord, tailWord_3743764, baseEnd_3743764] using wordTrace_append hprefix tailTrace_3743764
  have hstable : (prefixWord ++ tailWord_3743764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743764).length < 2 ^ (prefixWord ++ tailWord_3743764).sum := by decide
  have hdescent : baseEnd_3743764 < baseStart_3743764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743844 : List Nat := [2, 3, 1, 1, 2, 1, 2, 10]
def baseStart_3743844 : Nat := 118140960795 + 3743844 * 2 ^ 59
def prefixEnd_3743844 : Nat := 4983230072969 + 3 ^ 40 * 3743844 * 2
def baseEnd_3743844 : Nat := 142399367959359661246843

theorem tailTrace_3743844 : CollatzResearch.WordTrace tailWord_3743844 prefixEnd_3743844 142399367959359661246843 := by
  unfold tailWord_3743844
  simp only [CollatzResearch.WordTrace]
  refine ⟨68274604324350030247631293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91032805765800040330175057 68274604324350030247631293)
  ·
    refine ⟨25602976621631261342861735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68274604324350030247631293 25602976621631261342861735)
    ·
      refine ⟨38404464932446892014292603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25602976621631261342861735 38404464932446892014292603)
      ·
        refine ⟨57606697398670338021438905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38404464932446892014292603 57606697398670338021438905)
        ·
          refine ⟨43205023049002753516079179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57606697398670338021438905 43205023049002753516079179)
          ·
            refine ⟨64807534573504130274118769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43205023049002753516079179 64807534573504130274118769)
            ·
              refine ⟨48605650930128097705589077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64807534573504130274118769 48605650930128097705589077)
              ·
                refine ⟨142399367959359661246843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48605650930128097705589077 142399367959359661246843)
                ·
                  rfl

theorem cell22_3743844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_3743844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743844 prefixEnd_3743844 := by exact prefixLift 3743844
  have htrace : WordTrace (prefixWord ++ tailWord_3743844) baseStart_3743844 baseEnd_3743844 := by
    simpa [prefixWord, tailWord_3743844, baseEnd_3743844] using wordTrace_append hprefix tailTrace_3743844
  have hstable : (prefixWord ++ tailWord_3743844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743844).length < 2 ^ (prefixWord ++ tailWord_3743844).sum := by decide
  have hdescent : baseEnd_3743844 < baseStart_3743844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743850 : List Nat := [3, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_3743850 : Nat := 118140960795 + 3743850 * 2 ^ 59
def prefixEnd_3743850 : Nat := 4983230072969 + 3 ^ 40 * 3743850 * 2
def baseEnd_3743850 : Nat := 427198788518951645190523

theorem tailTrace_3743850 : CollatzResearch.WordTrace tailWord_3743850 prefixEnd_3743850 427198788518951645190523 := by
  unfold tailWord_3743850
  simp only [CollatzResearch.WordTrace]
  refine ⟨34137356871669580879995251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91032951657785549013320669 34137356871669580879995251)
  ·
    refine ⟨51206035307504371319992877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34137356871669580879995251 51206035307504371319992877)
    ·
      refine ⟨19202263240314139244997329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51206035307504371319992877 19202263240314139244997329)
      ·
        refine ⟨14401697430235604433747997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19202263240314139244997329 14401697430235604433747997)
        ·
          refine ⟨5400636536338351662655499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14401697430235604433747997 5400636536338351662655499)
          ·
            refine ⟨8100954804507527493983249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400636536338351662655499 8100954804507527493983249)
            ·
              refine ⟨6075716103380645620487437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8100954804507527493983249 6075716103380645620487437)
              ·
                refine ⟨2278393538767742107682789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6075716103380645620487437 2278393538767742107682789)
                ·
                  refine ⟨427198788518951645190523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278393538767742107682789 427198788518951645190523)
                  ·
                    rfl

theorem cell22_3743850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_3743850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743850 prefixEnd_3743850 := by exact prefixLift 3743850
  have htrace : WordTrace (prefixWord ++ tailWord_3743850) baseStart_3743850 baseEnd_3743850 := by
    simpa [prefixWord, tailWord_3743850, baseEnd_3743850] using wordTrace_append hprefix tailTrace_3743850
  have hstable : (prefixWord ++ tailWord_3743850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743850).length < 2 ^ (prefixWord ++ tailWord_3743850).sum := by decide
  have hdescent : baseEnd_3743850 < baseStart_3743850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743865 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_3743865 : Nat := 118140960795 + 3743865 * 2 ^ 59
def prefixEnd_3743865 : Nat := 4983230072969 + 3 ^ 40 * 3743865 * 2
def baseEnd_3743865 : Nat := 1281601500363399896446523

theorem tailTrace_3743865 : CollatzResearch.WordTrace tailWord_3743865 prefixEnd_3743865 1281601500363399896446523 := by
  unfold tailWord_3743865
  simp only [CollatzResearch.WordTrace]
  refine ⟨136549974581623981081777049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91033316387749320721184699 136549974581623981081777049)
  ·
    refine ⟨102412480936217985811332787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136549974581623981081777049 102412480936217985811332787)
    ·
      refine ⟨153618721404326978716999181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102412480936217985811332787 153618721404326978716999181)
      ·
        refine ⟨57607020526622617018874693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153618721404326978716999181 57607020526622617018874693)
        ·
          refine ⟨10801316348741740691039005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57607020526622617018874693 10801316348741740691039005)
          ·
            refine ⟨4050493630778152759139627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10801316348741740691039005 4050493630778152759139627)
            ·
              refine ⟨6075740446167229138709441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050493630778152759139627 6075740446167229138709441)
              ·
                refine ⟨4556805334625421854032081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075740446167229138709441 4556805334625421854032081)
                ·
                  refine ⟨3417604000969066390524061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556805334625421854032081 3417604000969066390524061)
                  ·
                    refine ⟨1281601500363399896446523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417604000969066390524061 1281601500363399896446523)
                    ·
                      rfl

theorem cell22_3743865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_3743865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743865 prefixEnd_3743865 := by exact prefixLift 3743865
  have htrace : WordTrace (prefixWord ++ tailWord_3743865) baseStart_3743865 baseEnd_3743865 := by
    simpa [prefixWord, tailWord_3743865, baseEnd_3743865] using wordTrace_append hprefix tailTrace_3743865
  have hstable : (prefixWord ++ tailWord_3743865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743865).length < 2 ^ (prefixWord ++ tailWord_3743865).sum := by decide
  have hdescent : baseEnd_3743865 < baseStart_3743865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743895 : List Nat := [1, 1, 3, 3, 5, 1, 2, 6]
def baseStart_3743895 : Nat := 118140960795 + 3743895 * 2 ^ 59
def prefixEnd_3743895 : Nat := 4983230072969 + 3 ^ 40 * 3743895 * 2
def baseEnd_3743895 : Nat := 142401307775165535355159

theorem tailTrace_3743895 : CollatzResearch.WordTrace tailWord_3743895 prefixEnd_3743895 142401307775165535355159 := by
  unfold tailWord_3743895
  simp only [CollatzResearch.WordTrace]
  refine ⟨136551068771515296205369139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91034045847676864136912759 136551068771515296205369139)
  ·
    refine ⟨204826603157272944308053709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136551068771515296205369139 204826603157272944308053709)
    ·
      refine ⟨76809976183977354115520141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204826603157272944308053709 76809976183977354115520141)
      ·
        refine ⟨28803741068991507793320053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76809976183977354115520141 28803741068991507793320053)
        ·
          refine ⟨2700350725217953855623755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28803741068991507793320053 2700350725217953855623755)
          ·
            refine ⟨4050526087826930783435633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700350725217953855623755 4050526087826930783435633)
            ·
              refine ⟨3037894565870198087576725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050526087826930783435633 3037894565870198087576725)
              ·
                refine ⟨142401307775165535355159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3037894565870198087576725 142401307775165535355159)
                ·
                  rfl

theorem cell22_3743895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 6].length) (baseStart_3743895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743895 prefixEnd_3743895 := by exact prefixLift 3743895
  have htrace : WordTrace (prefixWord ++ tailWord_3743895) baseStart_3743895 baseEnd_3743895 := by
    simpa [prefixWord, tailWord_3743895, baseEnd_3743895] using wordTrace_append hprefix tailTrace_3743895
  have hstable : (prefixWord ++ tailWord_3743895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743895).length < 2 ^ (prefixWord ++ tailWord_3743895).sum := by decide
  have hdescent : baseEnd_3743895 < baseStart_3743895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743927 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 1, 3]
def baseStart_3743927 : Nat := 118140960795 + 3743927 * 2 ^ 59
def prefixEnd_3743927 : Nat := 4983230072969 + 3 ^ 40 * 3743927 * 2
def baseEnd_3743927 : Nat := 1281622724230452401396333

theorem tailTrace_3743927 : CollatzResearch.WordTrace tailWord_3743927 prefixEnd_3743927 1281622724230452401396333 := by
  unfold tailWord_3743927
  simp only [CollatzResearch.WordTrace]
  refine ⟨136552235907399365670534035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91034823938266243780356023 136552235907399365670534035)
  ·
    refine ⟨204828353861099048505801053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136552235907399365670534035 204828353861099048505801053)
    ·
      refine ⟨76810632697912143189675395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204828353861099048505801053 76810632697912143189675395)
      ·
        refine ⟨115215949046868214784513093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76810632697912143189675395 115215949046868214784513093)
        ·
          refine ⟨21602990446287790272096205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115215949046868214784513093 21602990446287790272096205)
          ·
            refine ⟨8101121417357921352036077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21602990446287790272096205 8101121417357921352036077)
            ·
              refine ⟨3037920531509220507013529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8101121417357921352036077 3037920531509220507013529)
              ·
                refine ⟨2278440398631915380260147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037920531509220507013529 2278440398631915380260147)
                ·
                  refine ⟨3417660597947873070390221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278440398631915380260147 3417660597947873070390221)
                  ·
                    refine ⟨1281622724230452401396333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417660597947873070390221 1281622724230452401396333)
                    ·
                      rfl

theorem cell22_3743927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_3743927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743927 prefixEnd_3743927 := by exact prefixLift 3743927
  have htrace : WordTrace (prefixWord ++ tailWord_3743927) baseStart_3743927 baseEnd_3743927 := by
    simpa [prefixWord, tailWord_3743927, baseEnd_3743927] using wordTrace_append hprefix tailTrace_3743927
  have hstable : (prefixWord ++ tailWord_3743927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743927).length < 2 ^ (prefixWord ++ tailWord_3743927).sum := by decide
  have hdescent : baseEnd_3743927 < baseStart_3743927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743940 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3743940 : Nat := 118140960795 + 3743940 * 2 ^ 59
def prefixEnd_3743940 : Nat := 4983230072969 + 3 ^ 40 * 3743940 * 2
def baseEnd_3743940 : Nat := 427209058132041566940431

theorem tailTrace_3743940 : CollatzResearch.WordTrace tailWord_3743940 prefixEnd_3743940 427209058132041566940431 := by
  unfold tailWord_3743940
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276355028176134445378637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91035140037568179260504849 68276355028176134445378637)
  ·
    refine ⟨25603633135566050417016989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68276355028176134445378637 25603633135566050417016989)
    ·
      refine ⟨9601362425837268906381371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25603633135566050417016989 9601362425837268906381371)
      ·
        refine ⟨14402043638755903359572057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601362425837268906381371 14402043638755903359572057)
        ·
          refine ⟨10801532729066927519679043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14402043638755903359572057 10801532729066927519679043)
          ·
            refine ⟨16202299093600391279518565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801532729066927519679043 16202299093600391279518565)
            ·
              refine ⟨3037931080050073364909731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16202299093600391279518565 3037931080050073364909731)
              ·
                refine ⟨4556896620075110047364597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037931080050073364909731 4556896620075110047364597)
                ·
                  refine ⟨427209058132041566940431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556896620075110047364597 427209058132041566940431)
                  ·
                    rfl

theorem cell22_3743940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3743940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743940 prefixEnd_3743940 := by exact prefixLift 3743940
  have htrace : WordTrace (prefixWord ++ tailWord_3743940) baseStart_3743940 baseEnd_3743940 := by
    simpa [prefixWord, tailWord_3743940, baseEnd_3743940] using wordTrace_append hprefix tailTrace_3743940
  have hstable : (prefixWord ++ tailWord_3743940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743940).length < 2 ^ (prefixWord ++ tailWord_3743940).sum := by decide
  have hdescent : baseEnd_3743940 < baseStart_3743940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743953 : List Nat := [1, 2, 2, 1, 2, 2, 5, 2, 1, 4]
def baseStart_3743953 : Nat := 118140960795 + 3743953 * 2 ^ 59
def prefixEnd_3743953 : Nat := 4983230072969 + 3 ^ 40 * 3743953 * 2
def baseEnd_3743953 : Nat := 1281631624561797000246253

theorem tailTrace_3743953 : CollatzResearch.WordTrace tailWord_3743953 prefixEnd_3743953 1281631624561797000246253 := by
  unfold tailWord_3743953
  simp only [CollatzResearch.WordTrace]
  refine ⟨136553184205305172110980513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91035456136870114740653675 136553184205305172110980513)
  ·
    refine ⟨102414888153978879083235385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136553184205305172110980513 102414888153978879083235385)
    ·
      refine ⟨76811166115484159312426539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102414888153978879083235385 76811166115484159312426539)
      ·
        refine ⟨115216749173226238968639809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76811166115484159312426539 115216749173226238968639809)
        ·
          refine ⟨86412561879919679226479857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115216749173226238968639809 86412561879919679226479857)
          ·
            refine ⟨64809421409939759419859893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86412561879919679226479857 64809421409939759419859893)
            ·
              refine ⟨6075883257181852445611865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64809421409939759419859893 6075883257181852445611865)
              ·
                refine ⟨4556912442886389334208899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075883257181852445611865 4556912442886389334208899)
                ·
                  refine ⟨6835368664329584001313349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556912442886389334208899 6835368664329584001313349)
                  ·
                    refine ⟨1281631624561797000246253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6835368664329584001313349 1281631624561797000246253)
                    ·
                      rfl

theorem cell22_3743953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_3743953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743953 prefixEnd_3743953 := by exact prefixLift 3743953
  have htrace : WordTrace (prefixWord ++ tailWord_3743953) baseStart_3743953 baseEnd_3743953 := by
    simpa [prefixWord, tailWord_3743953, baseEnd_3743953] using wordTrace_append hprefix tailTrace_3743953
  have hstable : (prefixWord ++ tailWord_3743953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743953).length < 2 ^ (prefixWord ++ tailWord_3743953).sum := by decide
  have hdescent : baseEnd_3743953 < baseStart_3743953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743968 : List Nat := [2, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_3743968 : Nat := 118140960795 + 3743968 * 2 ^ 59
def prefixEnd_3743968 : Nat := 4983230072969 + 3 ^ 40 * 3743968 * 2
def baseEnd_3743968 : Nat := 427212253122780653707069

theorem tailTrace_3743968 : CollatzResearch.WordTrace tailWord_3743968 prefixEnd_3743968 427212253122780653707069 := by
  unfold tailWord_3743968
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276865650125414836388279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91035820866833886448517705 68276865650125414836388279)
  ·
    refine ⟨102415298475188122254582419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68276865650125414836388279 102415298475188122254582419)
    ·
      refine ⟨153622947712782183381873629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102415298475188122254582419 153622947712782183381873629)
      ·
        refine ⟨57608605392293318768202611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153622947712782183381873629 57608605392293318768202611)
        ·
          refine ⟨86412908088439978152303917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57608605392293318768202611 86412908088439978152303917)
          ·
            refine ⟨32404840533164991807113969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86412908088439978152303917 32404840533164991807113969)
            ·
              refine ⟨24303630399873743855335477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32404840533164991807113969 24303630399873743855335477)
              ·
                refine ⟨2278465349988163486437701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24303630399873743855335477 2278465349988163486437701)
                ·
                  refine ⟨427212253122780653707069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278465349988163486437701 427212253122780653707069)
                  ·
                    rfl

theorem cell22_3743968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_3743968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743968 prefixEnd_3743968 := by exact prefixLift 3743968
  have htrace : WordTrace (prefixWord ++ tailWord_3743968) baseStart_3743968 baseEnd_3743968 := by
    simpa [prefixWord, tailWord_3743968, baseEnd_3743968] using wordTrace_append hprefix tailTrace_3743968
  have hstable : (prefixWord ++ tailWord_3743968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743968).length < 2 ^ (prefixWord ++ tailWord_3743968).sum := by decide
  have hdescent : baseEnd_3743968 < baseStart_3743968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743985 : List Nat := [1, 2, 2, 2, 2, 1, 6, 2, 4]
def baseStart_3743985 : Nat := 118140960795 + 3743985 * 2 ^ 59
def prefixEnd_3743985 : Nat := 4983230072969 + 3 ^ 40 * 3743985 * 2
def baseEnd_3743985 : Nat := 427214192938586527815385

theorem tailTrace_3743985 : CollatzResearch.WordTrace tailWord_3743985 prefixEnd_3743985 427214192938586527815385 := by
  unfold tailWord_3743985
  simp only [CollatzResearch.WordTrace]
  refine ⟨136554351341189241576145409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91036234227459494384096939 136554351341189241576145409)
  ·
    refine ⟨102415763505891931182109057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136554351341189241576145409 102415763505891931182109057)
    ·
      refine ⟨76811822629418948386581793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102415763505891931182109057 76811822629418948386581793)
      ·
        refine ⟨57608866972064211289936345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76811822629418948386581793 57608866972064211289936345)
        ·
          refine ⟨43206650229048158467452259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57608866972064211289936345 43206650229048158467452259)
          ·
            refine ⟨64809975343572237701178389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43206650229048158467452259 64809975343572237701178389)
            ·
              refine ⟨3037967594229948642242737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64809975343572237701178389 3037967594229948642242737)
              ·
                refine ⟨2278475695672461481682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037967594229948642242737 2278475695672461481682053)
                ·
                  refine ⟨427214192938586527815385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278475695672461481682053 427214192938586527815385)
                  ·
                    rfl

theorem cell22_3743985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_3743985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743985 prefixEnd_3743985 := by exact prefixLift 3743985
  have htrace : WordTrace (prefixWord ++ tailWord_3743985) baseStart_3743985 baseEnd_3743985 := by
    simpa [prefixWord, tailWord_3743985, baseEnd_3743985] using wordTrace_append hprefix tailTrace_3743985
  have hstable : (prefixWord ++ tailWord_3743985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743985).length < 2 ^ (prefixWord ++ tailWord_3743985).sum := by decide
  have hdescent : baseEnd_3743985 < baseStart_3743985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743998 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3743998 : Nat := 118140960795 + 3743998 * 2 ^ 59
def prefixEnd_3743998 : Nat := 4983230072969 + 3 ^ 40 * 3743998 * 2
def baseEnd_3743998 : Nat := 1281647028981431882871115

theorem tailTrace_3743998 : CollatzResearch.WordTrace tailWord_3743998 prefixEnd_3743998 1281647028981431882871115 := by
  unfold tailWord_3743998
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069353186267768099546081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91036550326761429864245765 17069353186267768099546081)
  ·
    refine ⟨12802014889700826074659561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17069353186267768099546081 12802014889700826074659561)
    ·
      refine ⟨9601511167275619555994671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12802014889700826074659561 9601511167275619555994671)
      ·
        refine ⟨14402266750913429333992007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601511167275619555994671 14402266750913429333992007)
        ·
          refine ⟨21603400126370144000988011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402266750913429333992007 21603400126370144000988011)
          ·
            refine ⟨32405100189555216001482017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21603400126370144000988011 32405100189555216001482017)
            ·
              refine ⟨24303825142166412001111513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32405100189555216001482017 24303825142166412001111513)
              ·
                refine ⟨18227868856624809000833635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24303825142166412001111513 18227868856624809000833635)
                ·
                  refine ⟨27341803284937213501250453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18227868856624809000833635 27341803284937213501250453)
                  ·
                    refine ⟨1281647028981431882871115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27341803284937213501250453 1281647028981431882871115)
                    ·
                      rfl

theorem cell22_3743998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3743998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3743998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3743998 prefixEnd_3743998 := by exact prefixLift 3743998
  have htrace : WordTrace (prefixWord ++ tailWord_3743998) baseStart_3743998 baseEnd_3743998 := by
    simpa [prefixWord, tailWord_3743998, baseEnd_3743998] using wordTrace_append hprefix tailTrace_3743998
  have hstable : (prefixWord ++ tailWord_3743998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743998).length < 2 ^ (prefixWord ++ tailWord_3743998).sum := by decide
  have hdescent : baseEnd_3743998 < baseStart_3743998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744028 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 7, 3]
def baseStart_3744028 : Nat := 118140960795 + 3744028 * 2 ^ 59
def prefixEnd_3744028 : Nat := 4983230072969 + 3 ^ 40 * 3744028 * 2
def baseEnd_3744028 : Nat := 1281657298594521804621023

theorem tailTrace_3744028 : CollatzResearch.WordTrace tailWord_3744028 prefixEnd_3744028 1281657298594521804621023 := by
  unfold tailWord_3744028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68277959840016729959980369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91037279786688973279973825 68277959840016729959980369)
  ·
    refine ⟨51208469880012547469985277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68277959840016729959980369 51208469880012547469985277)
    ·
      refine ⟨19203176205004705301244479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51208469880012547469985277 19203176205004705301244479)
      ·
        refine ⟨28804764307507057951866719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19203176205004705301244479 28804764307507057951866719)
        ·
          refine ⟨43207146461260586927800079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28804764307507057951866719 43207146461260586927800079)
          ·
            refine ⟨64810719691890880391700119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43207146461260586927800079 64810719691890880391700119)
            ·
              refine ⟨97216079537836320587550179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64810719691890880391700119 97216079537836320587550179)
              ·
                refine ⟨145824119306754480881325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97216079537836320587550179 145824119306754480881325269)
                ·
                  refine ⟨3417752796252058145656061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145824119306754480881325269 3417752796252058145656061)
                  ·
                    refine ⟨1281657298594521804621023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3417752796252058145656061 1281657298594521804621023)
                    ·
                      rfl

theorem cell22_3744028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_3744028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744028 prefixEnd_3744028 := by exact prefixLift 3744028
  have htrace : WordTrace (prefixWord ++ tailWord_3744028) baseStart_3744028 baseEnd_3744028 := by
    simpa [prefixWord, tailWord_3744028, baseEnd_3744028] using wordTrace_append hprefix tailTrace_3744028
  have hstable : (prefixWord ++ tailWord_3744028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744028).length < 2 ^ (prefixWord ++ tailWord_3744028).sum := by decide
  have hdescent : baseEnd_3744028 < baseStart_3744028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744030 : List Nat := [4, 3, 2, 1, 1, 2, 9]
def baseStart_3744030 : Nat := 118140960795 + 3744030 * 2 ^ 59
def prefixEnd_3744030 : Nat := 4983230072969 + 3 ^ 40 * 3744030 * 2
def baseEnd_3744030 : Nat := 47468814193903498743371

theorem tailTrace_3744030 : CollatzResearch.WordTrace tailWord_3744030 prefixEnd_3744030 47468814193903498743371 := by
  unfold tailWord_3744030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069499078253276782691693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91037328417350809507689029 17069499078253276782691693)
  ·
    refine ⟨6401062154344978793509385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17069499078253276782691693 6401062154344978793509385)
    ·
      refine ⟨4800796615758734095132039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6401062154344978793509385 4800796615758734095132039)
      ·
        refine ⟨7201194923638101142698059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800796615758734095132039 7201194923638101142698059)
        ·
          refine ⟨10801792385457151714047089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201194923638101142698059 10801792385457151714047089)
          ·
            refine ⟨8101344289092863785535317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10801792385457151714047089 8101344289092863785535317)
            ·
              refine ⟨47468814193903498743371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8101344289092863785535317 47468814193903498743371)
              ·
                rfl

theorem cell22_3744030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 9].length) (baseStart_3744030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3744030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3744030 prefixEnd_3744030 := by exact prefixLift 3744030
  have htrace : WordTrace (prefixWord ++ tailWord_3744030) baseStart_3744030 baseEnd_3744030 := by
    simpa [prefixWord, tailWord_3744030, baseEnd_3744030] using wordTrace_append hprefix tailTrace_3744030
  have hstable : (prefixWord ++ tailWord_3744030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744030).length < 2 ^ (prefixWord ++ tailWord_3744030).sum := by decide
  have hdescent : baseEnd_3744030 < baseStart_3744030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
