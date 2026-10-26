import V185TrunkScan23Chunk0958

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5678582 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_5678582 : Nat := 118140960795 + 5678582 * 2 ^ 59
def prefixEnd_5678582 : Nat := 4983230072969 + 3 ^ 40 * 5678582 * 2
def baseEnd_5678582 : Nat := 2915842001969806755509683

theorem tailTrace_5678582 : CollatzResearch.WordTrace tailWord_5678582 prefixEnd_5678582 2915842001969806755509683 := by
  unfold tailWord_5678582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12944681294592169589939375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138076600475649808959353333 12944681294592169589939375)
  ·
    refine ⟨19417021941888254384909063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12944681294592169589939375 19417021941888254384909063)
    ·
      refine ⟨29125532912832381577363595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19417021941888254384909063 29125532912832381577363595)
      ·
        refine ⟨43688299369248572366045393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29125532912832381577363595 43688299369248572366045393)
        ·
          refine ⟨32766224526936429274534045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43688299369248572366045393 32766224526936429274534045)
          ·
            refine ⟨12287334197601160977950267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32766224526936429274534045 12287334197601160977950267)
            ·
              refine ⟨18431001296401741466925401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287334197601160977950267 18431001296401741466925401)
              ·
                refine ⟨13823250972301306100194051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18431001296401741466925401 13823250972301306100194051)
                ·
                  refine ⟨20734876458451959150291077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13823250972301306100194051 20734876458451959150291077)
                  ·
                    refine ⟨3887789335959742340679577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20734876458451959150291077 3887789335959742340679577)
                    ·
                      refine ⟨2915842001969806755509683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887789335959742340679577 2915842001969806755509683)
                      ·
                        rfl

theorem cell23_5678582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_5678582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678582 prefixEnd_5678582 := by exact prefixLift 5678582
  have htrace : WordTrace (prefixWord ++ tailWord_5678582) baseStart_5678582 baseEnd_5678582 := by
    simpa [prefixWord, tailWord_5678582, baseEnd_5678582] using wordTrace_append hprefix tailTrace_5678582
  have hstable : (prefixWord ++ tailWord_5678582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678582).length < 2 ^ (prefixWord ++ tailWord_5678582).sum := by decide
  have hdescent : baseEnd_5678582 < baseStart_5678582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678599 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 2, 2, 2]
def baseStart_5678599 : Nat := 118140960795 + 5678599 * 2 ^ 59
def prefixEnd_5678599 : Nat := 4983230072969 + 3 ^ 40 * 5678599 * 2
def baseEnd_5678599 : Nat := 2915850731140933188997105

theorem tailTrace_5678599 : CollatzResearch.WordTrace tailWord_5678599 prefixEnd_5678599 2915850731140933188997105 := by
  unfold tailWord_5678599
  simp only [CollatzResearch.WordTrace]
  refine ⟨207115520754413125342398851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138077013836275416894932567 207115520754413125342398851)
  ·
    refine ⟨310673281131619688013598277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207115520754413125342398851 310673281131619688013598277)
    ·
      refine ⟨58251240212178691502549677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310673281131619688013598277 58251240212178691502549677)
      ·
        refine ⟨21844215079567009313456129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58251240212178691502549677 21844215079567009313456129)
        ·
          refine ⟨16383161309675256985092097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21844215079567009313456129 16383161309675256985092097)
          ·
            refine ⟨12287370982256442738819073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16383161309675256985092097 12287370982256442738819073)
            ·
              refine ⟨9215528236692332054114305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12287370982256442738819073 9215528236692332054114305)
              ·
                refine ⟨6911646177519249040585729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9215528236692332054114305 6911646177519249040585729)
                ·
                  refine ⟨5183734633139436780439297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6911646177519249040585729 5183734633139436780439297)
                  ·
                    refine ⟨3887800974854577585329473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5183734633139436780439297 3887800974854577585329473)
                    ·
                      refine ⟨2915850731140933188997105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887800974854577585329473 2915850731140933188997105)
                      ·
                        rfl

theorem cell23_5678599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_5678599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678599 prefixEnd_5678599 := by exact prefixLift 5678599
  have htrace : WordTrace (prefixWord ++ tailWord_5678599) baseStart_5678599 baseEnd_5678599 := by
    simpa [prefixWord, tailWord_5678599, baseEnd_5678599] using wordTrace_append hprefix tailTrace_5678599
  have hstable : (prefixWord ++ tailWord_5678599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678599).length < 2 ^ (prefixWord ++ tailWord_5678599).sum := by decide
  have hdescent : baseEnd_5678599 < baseStart_5678599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678612 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_5678612 : Nat := 118140960795 + 5678612 * 2 ^ 59
def prefixEnd_5678612 : Nat := 4983230072969 + 3 ^ 40 * 5678612 * 2
def baseEnd_5678612 : Nat := 2915857406389441638134545

theorem tailTrace_5678612 : CollatzResearch.WordTrace tailWord_5678612 prefixEnd_5678612 2915857406389441638134545 := by
  unfold tailWord_5678612
  simp only [CollatzResearch.WordTrace]
  refine ⟨103557997451683014281311045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138077329935577352375081393 103557997451683014281311045)
  ·
    refine ⟨19417124522190565177745821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103557997451683014281311045 19417124522190565177745821)
    ·
      refine ⟨7281421695821461941654683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19417124522190565177745821 7281421695821461941654683)
      ·
        refine ⟨10922132543732192912482025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7281421695821461941654683 10922132543732192912482025)
        ·
          refine ⟨8191599407799144684361519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10922132543732192912482025 8191599407799144684361519)
          ·
            refine ⟨12287399111698717026542279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191599407799144684361519 12287399111698717026542279)
            ·
              refine ⟨18431098667548075539813419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287399111698717026542279 18431098667548075539813419)
              ·
                refine ⟨27646648001322113309720129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18431098667548075539813419 27646648001322113309720129)
                ·
                  refine ⟨20734986000991584982290097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27646648001322113309720129 20734986000991584982290097)
                  ·
                    refine ⟨15551239500743688736717573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20734986000991584982290097 15551239500743688736717573)
                    ·
                      refine ⟨2915857406389441638134545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15551239500743688736717573 2915857406389441638134545)
                      ·
                        rfl

theorem cell23_5678612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_5678612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678612 prefixEnd_5678612 := by exact prefixLift 5678612
  have htrace : WordTrace (prefixWord ++ tailWord_5678612) baseStart_5678612 baseEnd_5678612 := by
    simpa [prefixWord, tailWord_5678612, baseEnd_5678612] using wordTrace_append hprefix tailTrace_5678612
  have hstable : (prefixWord ++ tailWord_5678612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678612).length < 2 ^ (prefixWord ++ tailWord_5678612).sum := by decide
  have hdescent : baseEnd_5678612 < baseStart_5678612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678655 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 2, 4, 2]
def baseStart_5678655 : Nat := 118140960795 + 5678655 * 2 ^ 59
def prefixEnd_5678655 : Nat := 4983230072969 + 3 ^ 40 * 5678655 * 2
def baseEnd_5678655 : Nat := 2915879486057584969896847

theorem tailTrace_5678655 : CollatzResearch.WordTrace tailWord_5678655 prefixEnd_5678655 2915879486057584969896847 := by
  unfold tailWord_5678655
  simp only [CollatzResearch.WordTrace]
  refine ⟨207117563242210246906437419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138078375494806831270958279 207117563242210246906437419)
  ·
    refine ⟨310676344863315370359656129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207117563242210246906437419 310676344863315370359656129)
    ·
      refine ⟨233007258647486527769742097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310676344863315370359656129 233007258647486527769742097)
      ·
        refine ⟨174755443985614895827306573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233007258647486527769742097 174755443985614895827306573)
        ·
          refine ⟨65533291494605585935239965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174755443985614895827306573 65533291494605585935239965)
          ·
            refine ⟨24574984310477094725714987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65533291494605585935239965 24574984310477094725714987)
            ·
              refine ⟨36862476465715642088572481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24574984310477094725714987 36862476465715642088572481)
              ·
                refine ⟨27646857349286731566429361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36862476465715642088572481 27646857349286731566429361)
                ·
                  refine ⟨20735143011965048674822021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27646857349286731566429361 20735143011965048674822021)
                  ·
                    refine ⟨3887839314743446626529129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20735143011965048674822021 3887839314743446626529129)
                    ·
                      refine ⟨2915879486057584969896847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887839314743446626529129 2915879486057584969896847)
                      ·
                        rfl

theorem cell23_5678655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_5678655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678655 prefixEnd_5678655 := by exact prefixLift 5678655
  have htrace : WordTrace (prefixWord ++ tailWord_5678655) baseStart_5678655 baseEnd_5678655 := by
    simpa [prefixWord, tailWord_5678655, baseEnd_5678655] using wordTrace_append hprefix tailTrace_5678655
  have hstable : (prefixWord ++ tailWord_5678655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678655).length < 2 ^ (prefixWord ++ tailWord_5678655).sum := by decide
  have hdescent : baseEnd_5678655 < baseStart_5678655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678688 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_5678688 : Nat := 118140960795 + 5678688 * 2 ^ 59
def prefixEnd_5678688 : Nat := 4983230072969 + 3 ^ 40 * 5678688 * 2
def baseEnd_5678688 : Nat := 2915896430919183340784195

theorem tailTrace_5678688 : CollatzResearch.WordTrace tailWord_5678688 prefixEnd_5678688 2915896430919183340784195 := by
  unfold tailWord_5678688
  simp only [CollatzResearch.WordTrace]
  refine ⟨103559383425545346771194359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138079177900727129028259145 103559383425545346771194359)
  ·
    refine ⟨155339075138318020156791539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103559383425545346771194359 155339075138318020156791539)
    ·
      refine ⟨233008612707477030235187309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155339075138318020156791539 233008612707477030235187309)
      ·
        refine ⟨87378229765303886338195241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233008612707477030235187309 87378229765303886338195241)
        ·
          refine ⟨65533672323977914753646431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87378229765303886338195241 65533672323977914753646431)
          ·
            refine ⟨98300508485966872130469647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65533672323977914753646431 98300508485966872130469647)
            ·
              refine ⟨147450762728950308195704471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98300508485966872130469647 147450762728950308195704471)
              ·
                refine ⟨221176144093425462293556707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147450762728950308195704471 221176144093425462293556707)
                ·
                  refine ⟨331764216140138193440335061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221176144093425462293556707 331764216140138193440335061)
                  ·
                    refine ⟨7775723815784488908757853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 331764216140138193440335061 7775723815784488908757853)
                    ·
                      refine ⟨2915896430919183340784195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775723815784488908757853 2915896430919183340784195)
                      ·
                        rfl

theorem cell23_5678688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_5678688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678688 prefixEnd_5678688 := by exact prefixLift 5678688
  have htrace : WordTrace (prefixWord ++ tailWord_5678688) baseStart_5678688 baseEnd_5678688 := by
    simpa [prefixWord, tailWord_5678688, baseEnd_5678688] using wordTrace_append hprefix tailTrace_5678688
  have hstable : (prefixWord ++ tailWord_5678688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678688).length < 2 ^ (prefixWord ++ tailWord_5678688).sum := by decide
  have hdescent : baseEnd_5678688 < baseStart_5678688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678705 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 3]
def baseStart_5678705 : Nat := 118140960795 + 5678705 * 2 ^ 59
def prefixEnd_5678705 : Nat := 4983230072969 + 3 ^ 40 * 5678705 * 2
def baseEnd_5678705 : Nat := 2915905160090309774271617

theorem tailTrace_5678705 : CollatzResearch.WordTrace tailWord_5678705 prefixEnd_5678705 2915905160090309774271617 := by
  unfold tailWord_5678705
  simp only [CollatzResearch.WordTrace]
  refine ⟨207119386892029105445757569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138079591261352736963838379 207119386892029105445757569)
  ·
    refine ⟨155339540169021829084318177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207119386892029105445757569 155339540169021829084318177)
    ·
      refine ⟨116504655126766371813238633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155339540169021829084318177 116504655126766371813238633)
      ·
        refine ⟨87378491345074778859928975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116504655126766371813238633 87378491345074778859928975)
        ·
          refine ⟨131067737017612168289893463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87378491345074778859928975 131067737017612168289893463)
          ·
            refine ⟨196601605526418252434840195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131067737017612168289893463 196601605526418252434840195)
            ·
              refine ⟨294902408289627378652260293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196601605526418252434840195 294902408289627378652260293)
              ·
                refine ⟨55294201554305133497298805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294902408289627378652260293 55294201554305133497298805)
                ·
                  refine ⟨5183831395716106265371763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55294201554305133497298805 5183831395716106265371763)
                  ·
                    refine ⟨7775747093574159398057645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183831395716106265371763 7775747093574159398057645)
                    ·
                      refine ⟨2915905160090309774271617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775747093574159398057645 2915905160090309774271617)
                      ·
                        rfl

theorem cell23_5678705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_5678705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678705 prefixEnd_5678705 := by exact prefixLift 5678705
  have htrace : WordTrace (prefixWord ++ tailWord_5678705) baseStart_5678705 baseEnd_5678705 := by
    simpa [prefixWord, tailWord_5678705, baseEnd_5678705] using wordTrace_append hprefix tailTrace_5678705
  have hstable : (prefixWord ++ tailWord_5678705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678705).length < 2 ^ (prefixWord ++ tailWord_5678705).sum := by decide
  have hdescent : baseEnd_5678705 < baseStart_5678705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678745 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 4]
def baseStart_5678745 : Nat := 118140960795 + 5678745 * 2 ^ 59
def prefixEnd_5678745 : Nat := 4983230072969 + 3 ^ 40 * 5678745 * 2
def baseEnd_5678745 : Nat := 2915925699316489617771433

theorem tailTrace_5678745 : CollatzResearch.WordTrace tailWord_5678745 prefixEnd_5678745 2915925699316489617771433 := by
  unfold tailWord_5678745
  simp only [CollatzResearch.WordTrace]
  refine ⟨207120845811884192277213689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138080563874589461518142459 207120845811884192277213689)
  ·
    refine ⟨155340634358913144207910267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207120845811884192277213689 155340634358913144207910267)
    ·
      refine ⟨233010951538369716311865401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155340634358913144207910267 233010951538369716311865401)
      ·
        refine ⟨174758213653777287233899051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233010951538369716311865401 174758213653777287233899051)
        ·
          refine ⟨262137320480665930850848577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174758213653777287233899051 262137320480665930850848577)
          ·
            refine ⟨196602990360499448138136433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262137320480665930850848577 196602990360499448138136433)
            ·
              refine ⟨147452242770374586103602325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196602990360499448138136433 147452242770374586103602325)
              ·
                refine ⟨6911823879861308723606359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147452242770374586103602325 6911823879861308723606359)
                ·
                  refine ⟨10367735819791963085409539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911823879861308723606359 10367735819791963085409539)
                  ·
                    refine ⟨15551603729687944628114309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10367735819791963085409539 15551603729687944628114309)
                    ·
                      refine ⟨2915925699316489617771433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15551603729687944628114309 2915925699316489617771433)
                      ·
                        rfl

theorem cell23_5678745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_5678745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678745 prefixEnd_5678745 := by exact prefixLift 5678745
  have htrace : WordTrace (prefixWord ++ tailWord_5678745) baseStart_5678745 baseEnd_5678745 := by
    simpa [prefixWord, tailWord_5678745, baseEnd_5678745] using wordTrace_append hprefix tailTrace_5678745
  have hstable : (prefixWord ++ tailWord_5678745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678745).length < 2 ^ (prefixWord ++ tailWord_5678745).sum := by decide
  have hdescent : baseEnd_5678745 < baseStart_5678745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678782 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_5678782 : Nat := 118140960795 + 5678782 * 2 ^ 59
def prefixEnd_5678782 : Nat := 4983230072969 + 3 ^ 40 * 5678782 * 2
def baseEnd_5678782 : Nat := 2915944698100705973008763

theorem tailTrace_5678782 : CollatzResearch.WordTrace tailWord_5678782 prefixEnd_5678782 2915944698100705973008763 := by
  unfold tailWord_5678782
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890274414093768449538825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138081463541833431730873733 25890274414093768449538825)
  ·
    refine ⟨19417705810570326337154119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25890274414093768449538825 19417705810570326337154119)
    ·
      refine ⟨29126558715855489505731179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19417705810570326337154119 29126558715855489505731179)
      ·
        refine ⟨43689838073783234258596769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29126558715855489505731179 43689838073783234258596769)
        ·
          refine ⟨32767378555337425693947577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43689838073783234258596769 32767378555337425693947577)
          ·
            refine ⟨24575533916503069270460683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32767378555337425693947577 24575533916503069270460683)
            ·
              refine ⟨36863300874754603905691025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24575533916503069270460683 36863300874754603905691025)
              ·
                refine ⟨27647475656065952929268269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36863300874754603905691025 27647475656065952929268269)
                ·
                  refine ⟨10367803371024732348475601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27647475656065952929268269 10367803371024732348475601)
                  ·
                    refine ⟨7775852528268549261356701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10367803371024732348475601 7775852528268549261356701)
                    ·
                      refine ⟨2915944698100705973008763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775852528268549261356701 2915944698100705973008763)
                      ·
                        rfl

theorem cell23_5678782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_5678782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678782 prefixEnd_5678782 := by exact prefixLift 5678782
  have htrace : WordTrace (prefixWord ++ tailWord_5678782) baseStart_5678782 baseEnd_5678782 := by
    simpa [prefixWord, tailWord_5678782, baseEnd_5678782] using wordTrace_append hprefix tailTrace_5678782
  have hstable : (prefixWord ++ tailWord_5678782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678782).length < 2 ^ (prefixWord ++ tailWord_5678782).sum := by decide
  have hdescent : baseEnd_5678782 < baseStart_5678782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678796 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5678796 : Nat := 118140960795 + 5678796 * 2 ^ 59
def prefixEnd_5678796 : Nat := 4983230072969 + 3 ^ 40 * 5678796 * 2
def baseEnd_5678796 : Nat := 2915951886829868918233699

theorem tailTrace_5678796 : CollatzResearch.WordTrace tailWord_5678796 prefixEnd_5678796 2915951886829868918233699 := by
  unfold tailWord_5678796
  simp only [CollatzResearch.WordTrace]
  refine ⟨103561352967349713993660121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138081803956466285324880161 103561352967349713993660121)
  ·
    refine ⟨77671014725512285495245091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103561352967349713993660121 77671014725512285495245091)
    ·
      refine ⟨116506522088268428242867637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77671014725512285495245091 116506522088268428242867637)
      ·
        refine ⟨10922486445775165147768841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116506522088268428242867637 10922486445775165147768841)
        ·
          refine ⟨8191864834331373860826631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10922486445775165147768841 8191864834331373860826631)
          ·
            refine ⟨12287797251497060791239947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191864834331373860826631 12287797251497060791239947)
            ·
              refine ⟨18431695877245591186859921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287797251497060791239947 18431695877245591186859921)
              ·
                refine ⟨13823771907934193390144941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18431695877245591186859921 13823771907934193390144941)
                ·
                  refine ⟨5183914465475322521304353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13823771907934193390144941 5183914465475322521304353)
                  ·
                    refine ⟨3887935849106491890978265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5183914465475322521304353 3887935849106491890978265)
                    ·
                      refine ⟨2915951886829868918233699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887935849106491890978265 2915951886829868918233699)
                      ·
                        rfl

theorem cell23_5678796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5678796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678796 prefixEnd_5678796 := by exact prefixLift 5678796
  have htrace : WordTrace (prefixWord ++ tailWord_5678796) baseStart_5678796 baseEnd_5678796 := by
    simpa [prefixWord, tailWord_5678796, baseEnd_5678796] using wordTrace_append hprefix tailTrace_5678796
  have hstable : (prefixWord ++ tailWord_5678796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678796).length < 2 ^ (prefixWord ++ tailWord_5678796).sum := by decide
  have hdescent : baseEnd_5678796 < baseStart_5678796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678802 : List Nat := [3, 2, 2, 2, 2, 2, 3, 7]
def baseStart_5678802 : Nat := 118140960795 + 5678802 * 2 ^ 59
def prefixEnd_5678802 : Nat := 4983230072969 + 3 ^ 40 * 5678802 * 2
def baseEnd_5678802 : Nat := 107998332137547996102173

theorem tailTrace_5678802 : CollatzResearch.WordTrace tailWord_5678802 prefixEnd_5678802 107998332137547996102173 := by
  unfold tailWord_5678802
  simp only [CollatzResearch.WordTrace]
  refine ⟨51780731193169422753009665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138081949848451794008025773 51780731193169422753009665)
  ·
    refine ⟨38835548394877067064757249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51780731193169422753009665 38835548394877067064757249)
    ·
      refine ⟨29126661296157800298567937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38835548394877067064757249 29126661296157800298567937)
      ·
        refine ⟨21844995972118350223925953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29126661296157800298567937 21844995972118350223925953)
        ·
          refine ⟨16383746979088762667944465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21844995972118350223925953 16383746979088762667944465)
          ·
            refine ⟨12287810234316572000958349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16383746979088762667944465 12287810234316572000958349)
            ·
              refine ⟨4607928837868714500359381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12287810234316572000958349 4607928837868714500359381)
              ·
                refine ⟨107998332137547996102173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4607928837868714500359381 107998332137547996102173)
                ·
                  rfl

theorem cell23_5678802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_5678802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678802 prefixEnd_5678802 := by exact prefixLift 5678802
  have htrace : WordTrace (prefixWord ++ tailWord_5678802) baseStart_5678802 baseEnd_5678802 := by
    simpa [prefixWord, tailWord_5678802, baseEnd_5678802] using wordTrace_append hprefix tailTrace_5678802
  have hstable : (prefixWord ++ tailWord_5678802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678802).length < 2 ^ (prefixWord ++ tailWord_5678802).sum := by decide
  have hdescent : baseEnd_5678802 < baseStart_5678802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678813 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_5678813 : Nat := 118140960795 + 5678813 * 2 ^ 59
def prefixEnd_5678813 : Nat := 4983230072969 + 3 ^ 40 * 5678813 * 2
def baseEnd_5678813 : Nat := 2915960616000995351721121

theorem tailTrace_5678813 : CollatzResearch.WordTrace tailWord_5678813 prefixEnd_5678813 2915960616000995351721121 := by
  unfold tailWord_5678813
  simp only [CollatzResearch.WordTrace]
  refine ⟨207123325975637839890689093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138082217317091893260459395 207123325975637839890689093)
  ·
    refine ⟨38835623620432094979504205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207123325975637839890689093 38835623620432094979504205)
    ·
      refine ⟨14563358857662035617314077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38835623620432094979504205 14563358857662035617314077)
      ·
        refine ⟨5461259571623263356492779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14563358857662035617314077 5461259571623263356492779)
        ·
          refine ⟨8191889357434895034739169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461259571623263356492779 8191889357434895034739169)
          ·
            refine ⟨6143917018076171276054377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8191889357434895034739169 6143917018076171276054377)
            ·
              refine ⟨4607937763557128457040783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6143917018076171276054377 4607937763557128457040783)
              ·
                refine ⟨6911906645335692685561175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607937763557128457040783 6911906645335692685561175)
                ·
                  refine ⟨10367859968003539028341763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911906645335692685561175 10367859968003539028341763)
                  ·
                    refine ⟨15551789952005308542512645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10367859968003539028341763 15551789952005308542512645)
                    ·
                      refine ⟨2915960616000995351721121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15551789952005308542512645 2915960616000995351721121)
                      ·
                        rfl

theorem cell23_5678813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_5678813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678813 prefixEnd_5678813 := by exact prefixLift 5678813
  have htrace : WordTrace (prefixWord ++ tailWord_5678813) baseStart_5678813 baseEnd_5678813 := by
    simpa [prefixWord, tailWord_5678813, baseEnd_5678813] using wordTrace_append hprefix tailTrace_5678813
  have hstable : (prefixWord ++ tailWord_5678813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678813).length < 2 ^ (prefixWord ++ tailWord_5678813).sum := by decide
  have hdescent : baseEnd_5678813 < baseStart_5678813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678823 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 2, 4]
def baseStart_5678823 : Nat := 118140960795 + 5678823 * 2 ^ 59
def prefixEnd_5678823 : Nat := 4983230072969 + 3 ^ 40 * 5678823 * 2
def baseEnd_5678823 : Nat := 971988583602513437532025

theorem tailTrace_5678823 : CollatzResearch.WordTrace tailWord_5678823 prefixEnd_5678823 971988583602513437532025 := by
  unfold tailWord_5678823
  simp only [CollatzResearch.WordTrace]
  refine ⟨207123690705601611598553123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138082460470401074399035415 207123690705601611598553123)
  ·
    refine ⟨310685536058402417397829685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207123690705601611598553123 310685536058402417397829685)
    ·
      refine ⟨29126769005475226631046533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310685536058402417397829685 29126769005475226631046533)
      ·
        refine ⟨5461269188526604993321225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29126769005475226631046533 5461269188526604993321225)
        ·
          refine ⟨4095951891394953744990919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461269188526604993321225 4095951891394953744990919)
          ·
            refine ⟨6143927837092430617486379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095951891394953744990919 6143927837092430617486379)
            ·
              refine ⟨9215891755638645926229569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143927837092430617486379 9215891755638645926229569)
              ·
                refine ⟨6911918816728984444672177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9215891755638645926229569 6911918816728984444672177)
                ·
                  refine ⟨5183939112546738333504133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6911918816728984444672177 5183939112546738333504133)
                  ·
                    refine ⟨971988583602513437532025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5183939112546738333504133 971988583602513437532025)
                    ·
                      rfl

theorem cell23_5678823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_5678823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678823 prefixEnd_5678823 := by exact prefixLift 5678823
  have htrace : WordTrace (prefixWord ++ tailWord_5678823) baseStart_5678823 baseEnd_5678823 := by
    simpa [prefixWord, tailWord_5678823, baseEnd_5678823] using wordTrace_append hprefix tailTrace_5678823
  have hstable : (prefixWord ++ tailWord_5678823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678823).length < 2 ^ (prefixWord ++ tailWord_5678823).sum := by decide
  have hdescent : baseEnd_5678823 < baseStart_5678823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678829 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_5678829 : Nat := 118140960795 + 5678829 * 2 ^ 59
def prefixEnd_5678829 : Nat := 4983230072969 + 3 ^ 40 * 5678829 * 2
def baseEnd_5678829 : Nat := 2915968831691467289121047

theorem tailTrace_5678829 : CollatzResearch.WordTrace tailWord_5678829 prefixEnd_5678829 2915968831691467289121047 := by
  unfold tailWord_5678829
  simp only [CollatzResearch.WordTrace]
  refine ⟨207123909543579874623271541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138082606362386583082181027 207123909543579874623271541)
  ·
    refine ⟨19417866519710613245931707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207123909543579874623271541 19417866519710613245931707)
    ·
      refine ⟨29126799779565919868897561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19417866519710613245931707 29126799779565919868897561)
      ·
        refine ⟨21845099834674439901673171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29126799779565919868897561 21845099834674439901673171)
        ·
          refine ⟨32767649752011659852509757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21845099834674439901673171 32767649752011659852509757)
          ·
            refine ⟨12287868657004372444691159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32767649752011659852509757 12287868657004372444691159)
            ·
              refine ⟨18431802985506558667036739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12287868657004372444691159 18431802985506558667036739)
              ·
                refine ⟨27647704478259838000555109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18431802985506558667036739 27647704478259838000555109)
                ·
                  refine ⟨5183944589673719625104083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27647704478259838000555109 5183944589673719625104083)
                  ·
                    refine ⟨7775916884510579437656125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183944589673719625104083 7775916884510579437656125)
                    ·
                      refine ⟨2915968831691467289121047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775916884510579437656125 2915968831691467289121047)
                      ·
                        rfl

theorem cell23_5678829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_5678829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678829 prefixEnd_5678829 := by exact prefixLift 5678829
  have htrace : WordTrace (prefixWord ++ tailWord_5678829) baseStart_5678829 baseEnd_5678829 := by
    simpa [prefixWord, tailWord_5678829, baseEnd_5678829] using wordTrace_append hprefix tailTrace_5678829
  have hstable : (prefixWord ++ tailWord_5678829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678829).length < 2 ^ (prefixWord ++ tailWord_5678829).sum := by decide
  have hdescent : baseEnd_5678829 < baseStart_5678829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678846 : List Nat := [4, 2, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_5678846 : Nat := 118140960795 + 5678846 * 2 ^ 59
def prefixEnd_5678846 : Nat := 4983230072969 + 3 ^ 40 * 5678846 * 2
def baseEnd_5678846 : Nat := 2915977560862593722608469

theorem tailTrace_5678846 : CollatzResearch.WordTrace tailWord_5678846 prefixEnd_5678846 2915977560862593722608469 := by
  unfold tailWord_5678846
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890566198064785815830049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138083019723012191017760261 25890566198064785815830049)
  ·
    refine ⟨19417924648548589361872537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25890566198064785815830049 19417924648548589361872537)
    ·
      refine ⟨14563443486411442021404403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19417924648548589361872537 14563443486411442021404403)
      ·
        refine ⟨21845165229617163032106605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563443486411442021404403 21845165229617163032106605)
        ·
          refine ⟨8191936961106436137039977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21845165229617163032106605 8191936961106436137039977)
          ·
            refine ⟨6143952720829827102779983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8191936961106436137039977 6143952720829827102779983)
            ·
              refine ⟨9215929081244740654169975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143952720829827102779983 9215929081244740654169975)
              ·
                refine ⟨13823893621867110981254963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9215929081244740654169975 13823893621867110981254963)
                ·
                  refine ⟨20735840432800666471882445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13823893621867110981254963 20735840432800666471882445)
                  ·
                    refine ⟨7775940162300249926955917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20735840432800666471882445 7775940162300249926955917)
                    ·
                      refine ⟨2915977560862593722608469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7775940162300249926955917 2915977560862593722608469)
                      ·
                        rfl

theorem cell23_5678846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_5678846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678846 prefixEnd_5678846 := by exact prefixLift 5678846
  have htrace : WordTrace (prefixWord ++ tailWord_5678846) baseStart_5678846 baseEnd_5678846 := by
    simpa [prefixWord, tailWord_5678846, baseEnd_5678846] using wordTrace_append hprefix tailTrace_5678846
  have hstable : (prefixWord ++ tailWord_5678846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678846).length < 2 ^ (prefixWord ++ tailWord_5678846).sum := by decide
  have hdescent : baseEnd_5678846 < baseStart_5678846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678869 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_5678869 : Nat := 118140960795 + 5678869 * 2 ^ 59
def prefixEnd_5678869 : Nat := 4983230072969 + 3 ^ 40 * 5678869 * 2
def baseEnd_5678869 : Nat := 2915989370917647132620863

theorem tailTrace_5678869 : CollatzResearch.WordTrace tailWord_5678869 prefixEnd_5678869 2915989370917647132620863 := by
  unfold tailWord_5678869
  simp only [CollatzResearch.WordTrace]
  refine ⟨207125368463434961454727661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138083578975623307636485107 207125368463434961454727661)
  ·
    refine ⟨77672013173788110545522873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207125368463434961454727661 77672013173788110545522873)
    ·
      refine ⟨58254009880341082909142155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77672013173788110545522873 58254009880341082909142155)
      ·
        refine ⟨87381014820511624363713233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58254009880341082909142155 87381014820511624363713233)
        ·
          refine ⟨65535761115383718272784925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87381014820511624363713233 65535761115383718272784925)
          ·
            refine ⟨24575910418268894352294347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65535761115383718272784925 24575910418268894352294347)
            ·
              refine ⟨36863865627403341528441521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24575910418268894352294347 36863865627403341528441521)
              ·
                refine ⟨27647899220552506146331141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36863865627403341528441521 27647899220552506146331141)
                ·
                  refine ⟨5183981103853594902437089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27647899220552506146331141 5183981103853594902437089)
                  ·
                    refine ⟨3887985827890196176827817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5183981103853594902437089 3887985827890196176827817)
                    ·
                      refine ⟨2915989370917647132620863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3887985827890196176827817 2915989370917647132620863)
                      ·
                        rfl

theorem cell23_5678869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_5678869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678869 prefixEnd_5678869 := by exact prefixLift 5678869
  have htrace : WordTrace (prefixWord ++ tailWord_5678869) baseStart_5678869 baseEnd_5678869 := by
    simpa [prefixWord, tailWord_5678869, baseEnd_5678869] using wordTrace_append hprefix tailTrace_5678869
  have hstable : (prefixWord ++ tailWord_5678869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678869).length < 2 ^ (prefixWord ++ tailWord_5678869).sum := by decide
  have hdescent : baseEnd_5678869 < baseStart_5678869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678892 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 7]
def baseStart_5678892 : Nat := 118140960795 + 5678892 * 2 ^ 59
def prefixEnd_5678892 : Nat := 4983230072969 + 3 ^ 40 * 5678892 * 2
def baseEnd_5678892 : Nat := 324000131219188949181473

theorem tailTrace_5678892 : CollatzResearch.WordTrace tailWord_5678892 prefixEnd_5678892 324000131219188949181473 := by
  unfold tailWord_5678892
  simp only [CollatzResearch.WordTrace]
  refine ⟨103563103671175818191407465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138084138228234424255209953 103563103671175818191407465)
  ·
    refine ⟨77672327753381863643555599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103563103671175818191407465 77672327753381863643555599)
    ·
      refine ⟨116508491630072795465333399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77672327753381863643555599 116508491630072795465333399)
      ·
        refine ⟨174762737445109193198000099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116508491630072795465333399 174762737445109193198000099)
        ·
          refine ⟨262144106167663789797000149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174762737445109193198000099 262144106167663789797000149)
          ·
            refine ⟨6144002488304620073367191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 262144106167663789797000149 6144002488304620073367191)
            ·
              refine ⟨9216003732456930110050787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144002488304620073367191 9216003732456930110050787)
              ·
                refine ⟨13824005598685395165076181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216003732456930110050787 13824005598685395165076181)
                ·
                  refine ⟨324000131219188949181473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13824005598685395165076181 324000131219188949181473)
                  ·
                    rfl

theorem cell23_5678892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_5678892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678892 prefixEnd_5678892 := by exact prefixLift 5678892
  have htrace : WordTrace (prefixWord ++ tailWord_5678892) baseStart_5678892 baseEnd_5678892 := by
    simpa [prefixWord, tailWord_5678892, baseEnd_5678892] using wordTrace_append hprefix tailTrace_5678892
  have hstable : (prefixWord ++ tailWord_5678892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678892).length < 2 ^ (prefixWord ++ tailWord_5678892).sum := by decide
  have hdescent : baseEnd_5678892 < baseStart_5678892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678922 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_5678922 : Nat := 118140960795 + 5678922 * 2 ^ 59
def prefixEnd_5678922 : Nat := 4983230072969 + 3 ^ 40 * 5678922 * 2
def baseEnd_5678922 : Nat := 972005528464111808419373

theorem tailTrace_5678922 : CollatzResearch.WordTrace tailWord_5678922 prefixEnd_5678922 972005528464111808419373 := by
  unfold tailWord_5678922
  simp only [CollatzResearch.WordTrace]
  refine ⟨51781825383060737876601755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138084867688161967670938013 51781825383060737876601755)
  ·
    refine ⟨77672738074591106814902633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51781825383060737876601755 77672738074591106814902633)
    ·
      refine ⟨58254553555943330111176975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77672738074591106814902633 58254553555943330111176975)
      ·
        refine ⟨87381830333914995166765463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58254553555943330111176975 87381830333914995166765463)
        ·
          refine ⟨131072745500872492750148195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87381830333914995166765463 131072745500872492750148195)
          ·
            refine ⟨196609118251308739125222293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131072745500872492750148195 196609118251308739125222293)
            ·
              refine ⟨9216052418030097146494795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196609118251308739125222293 9216052418030097146494795)
              ·
                refine ⟨13824078627045145719742193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216052418030097146494795 13824078627045145719742193)
                ·
                  refine ⟨10368058970283859289806645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13824078627045145719742193 10368058970283859289806645)
                  ·
                    refine ⟨972005528464111808419373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10368058970283859289806645 972005528464111808419373)
                    ·
                      rfl

theorem cell23_5678922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_5678922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678922 prefixEnd_5678922 := by exact prefixLift 5678922
  have htrace : WordTrace (prefixWord ++ tailWord_5678922) baseStart_5678922 baseEnd_5678922 := by
    simpa [prefixWord, tailWord_5678922, baseEnd_5678922] using wordTrace_append hprefix tailTrace_5678922
  have hstable : (prefixWord ++ tailWord_5678922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678922).length < 2 ^ (prefixWord ++ tailWord_5678922).sum := by decide
  have hdescent : baseEnd_5678922 < baseStart_5678922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678932 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5678932 : Nat := 118140960795 + 5678932 * 2 ^ 59
def prefixEnd_5678932 : Nat := 4983230072969 + 3 ^ 40 * 5678932 * 2
def baseEnd_5678932 : Nat := 2916021720198880386133073

theorem tailTrace_5678932 : CollatzResearch.WordTrace tailWord_5678932 prefixEnd_5678932 2916021720198880386133073 := by
  unfold tailWord_5678932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103563833131103361607135525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138085110841471148809514033 103563833131103361607135525)
  ·
    refine ⟨19418218712081880301337911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103563833131103361607135525 19418218712081880301337911)
    ·
      refine ⟨29127328068122820452006867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19418218712081880301337911 29127328068122820452006867)
      ·
        refine ⟨43690992102184230678010301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29127328068122820452006867 43690992102184230678010301)
        ·
          refine ⟨16384122038319086504253863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43690992102184230678010301 16384122038319086504253863)
          ·
            refine ⟨24576183057478629756380795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16384122038319086504253863 24576183057478629756380795)
            ·
              refine ⟨36864274586217944634571193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24576183057478629756380795 36864274586217944634571193)
              ·
                refine ⟨27648205939663458475928395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36864274586217944634571193 27648205939663458475928395)
                ·
                  refine ⟨41472308909495187713892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27648205939663458475928395 41472308909495187713892593)
                  ·
                    refine ⟨31104231682121390785419445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41472308909495187713892593 31104231682121390785419445)
                    ·
                      refine ⟨2916021720198880386133073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31104231682121390785419445 2916021720198880386133073)
                      ·
                        rfl

theorem cell23_5678932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5678932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678932 prefixEnd_5678932 := by exact prefixLift 5678932
  have htrace : WordTrace (prefixWord ++ tailWord_5678932) baseStart_5678932 baseEnd_5678932 := by
    simpa [prefixWord, tailWord_5678932, baseEnd_5678932] using wordTrace_append hprefix tailTrace_5678932
  have hstable : (prefixWord ++ tailWord_5678932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678932).length < 2 ^ (prefixWord ++ tailWord_5678932).sum := by decide
  have hdescent : baseEnd_5678932 < baseStart_5678932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678945 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5678945 : Nat := 118140960795 + 5678945 * 2 ^ 59
def prefixEnd_5678945 : Nat := 4983230072969 + 3 ^ 40 * 5678945 * 2
def baseEnd_5678945 : Nat := 2916028395447388835270513

theorem tailTrace_5678945 : CollatzResearch.WordTrace tailWord_5678945 prefixEnd_5678945 2916028395447388835270513 := by
  unfold tailWord_5678945
  simp only [CollatzResearch.WordTrace]
  refine ⟨207128140411159626434494289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138085426940773084289662859 207128140411159626434494289)
  ·
    refine ⟨155346105308369719825870717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207128140411159626434494289 155346105308369719825870717)
    ·
      refine ⟨58254789490638644934701519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155346105308369719825870717 58254789490638644934701519)
      ·
        refine ⟨87382184235957967402052279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58254789490638644934701519 87382184235957967402052279)
        ·
          refine ⟨131073276353936951103078419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87382184235957967402052279 131073276353936951103078419)
          ·
            refine ⟨196609914530905426654617629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131073276353936951103078419 196609914530905426654617629)
            ·
              refine ⟨73728717949089534995481611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196609914530905426654617629 73728717949089534995481611)
              ·
                refine ⟨110593076923634302493222417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73728717949089534995481611 110593076923634302493222417)
                ·
                  refine ⟨82944807692725726869916813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110593076923634302493222417 82944807692725726869916813)
                  ·
                    refine ⟨31104302884772147576218805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82944807692725726869916813 31104302884772147576218805)
                    ·
                      refine ⟨2916028395447388835270513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31104302884772147576218805 2916028395447388835270513)
                      ·
                        rfl

theorem cell23_5678945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5678945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678945 prefixEnd_5678945 := by exact prefixLift 5678945
  have htrace : WordTrace (prefixWord ++ tailWord_5678945) baseStart_5678945 baseEnd_5678945 := by
    simpa [prefixWord, tailWord_5678945, baseEnd_5678945] using wordTrace_append hprefix tailTrace_5678945
  have hstable : (prefixWord ++ tailWord_5678945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678945).length < 2 ^ (prefixWord ++ tailWord_5678945).sum := by decide
  have hdescent : baseEnd_5678945 < baseStart_5678945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678955 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_5678955 : Nat := 118140960795 + 5678955 * 2 ^ 59
def prefixEnd_5678955 : Nat := 4983230072969 + 3 ^ 40 * 5678955 * 2
def baseEnd_5678955 : Nat := 2916033530253933796145467

theorem tailTrace_5678955 : CollatzResearch.WordTrace tailWord_5678955 prefixEnd_5678955 2916033530253933796145467 := by
  unfold tailWord_5678955
  simp only [CollatzResearch.WordTrace]
  refine ⟨207128505141123398142358319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138085670094082265428238879 207128505141123398142358319)
  ·
    refine ⟨310692757711685097213537479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207128505141123398142358319 310692757711685097213537479)
    ·
      refine ⟨466039136567527645820306219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310692757711685097213537479 466039136567527645820306219)
      ·
        refine ⟨699058704851291468730459329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466039136567527645820306219 699058704851291468730459329)
        ·
          refine ⟨524294028638468601547844497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699058704851291468730459329 524294028638468601547844497)
          ·
            refine ⟨393220521478851451160883373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524294028638468601547844497 393220521478851451160883373)
            ·
              refine ⟨147457695554569294185331265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393220521478851451160883373 147457695554569294185331265)
              ·
                refine ⟨110593271665926970638998449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147457695554569294185331265 110593271665926970638998449)
                ·
                  refine ⟨82944953749445227979248837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110593271665926970638998449 82944953749445227979248837)
                  ·
                    refine ⟨15552178828020980246109157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82944953749445227979248837 15552178828020980246109157)
                    ·
                      refine ⟨2916033530253933796145467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15552178828020980246109157 2916033530253933796145467)
                      ·
                        rfl

theorem cell23_5678955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_5678955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678955 prefixEnd_5678955 := by exact prefixLift 5678955
  have htrace : WordTrace (prefixWord ++ tailWord_5678955) baseStart_5678955 baseEnd_5678955 := by
    simpa [prefixWord, tailWord_5678955, baseEnd_5678955] using wordTrace_append hprefix tailTrace_5678955
  have hstable : (prefixWord ++ tailWord_5678955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678955).length < 2 ^ (prefixWord ++ tailWord_5678955).sum := by decide
  have hdescent : baseEnd_5678955 < baseStart_5678955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678962 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_5678962 : Nat := 118140960795 + 5678962 * 2 ^ 59
def prefixEnd_5678962 : Nat := 4983230072969 + 3 ^ 40 * 5678962 * 2
def baseEnd_5678962 : Nat := 2916037124618515268757935

theorem tailTrace_5678962 : CollatzResearch.WordTrace tailWord_5678962 prefixEnd_5678962 2916037124618515268757935 := by
  unfold tailWord_5678962
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782190113024509584465785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138085840301398692225242093 51782190113024509584465785)
  ·
    refine ⟨38836642584768382188349339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51782190113024509584465785 38836642584768382188349339)
    ·
      refine ⟨58254963877152573282524009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38836642584768382188349339 58254963877152573282524009)
      ·
        refine ⟨43691222907864429961893007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58254963877152573282524009 43691222907864429961893007)
        ·
          refine ⟨65536834361796644942839511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43691222907864429961893007 65536834361796644942839511)
          ·
            refine ⟨98305251542694967414259267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65536834361796644942839511 98305251542694967414259267)
            ·
              refine ⟨147457877314042451121388901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98305251542694967414259267 147457877314042451121388901)
              ·
                refine ⟨27648351996382959585260419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147457877314042451121388901 27648351996382959585260419)
                ·
                  refine ⟨41472527994574439377890629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27648351996382959585260419 41472527994574439377890629)
                  ·
                    refine ⟨7776098998982707383354493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41472527994574439377890629 7776098998982707383354493)
                    ·
                      refine ⟨2916037124618515268757935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776098998982707383354493 2916037124618515268757935)
                      ·
                        rfl

theorem cell23_5678962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_5678962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678962 prefixEnd_5678962 := by exact prefixLift 5678962
  have htrace : WordTrace (prefixWord ++ tailWord_5678962) baseStart_5678962 baseEnd_5678962 := by
    simpa [prefixWord, tailWord_5678962, baseEnd_5678962] using wordTrace_append hprefix tailTrace_5678962
  have hstable : (prefixWord ++ tailWord_5678962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678962).length < 2 ^ (prefixWord ++ tailWord_5678962).sum := by decide
  have hdescent : baseEnd_5678962 < baseStart_5678962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678979 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3]
def baseStart_5678979 : Nat := 118140960795 + 5678979 * 2 ^ 59
def prefixEnd_5678979 : Nat := 4983230072969 + 3 ^ 40 * 5678979 * 2
def baseEnd_5678979 : Nat := 2916045853789641702245357

theorem tailTrace_5678979 : CollatzResearch.WordTrace tailWord_5678979 prefixEnd_5678979 2916045853789641702245357 := by
  unfold tailWord_5678979
  simp only [CollatzResearch.WordTrace]
  refine ⟨207129380493036450241231991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138086253662024300160821327 207129380493036450241231991)
  ·
    refine ⟨310694070739554675361847987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207129380493036450241231991 310694070739554675361847987)
    ·
      refine ⟨466041106109332013042771981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310694070739554675361847987 466041106109332013042771981)
      ·
        refine ⟨174765414790999504891039493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466041106109332013042771981 174765414790999504891039493)
        ·
          refine ⟨32768515273312407167069905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174765414790999504891039493 32768515273312407167069905)
          ·
            refine ⟨24576386454984305375302429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32768515273312407167069905 24576386454984305375302429)
            ·
              refine ⟨9216144920619114515738411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24576386454984305375302429 9216144920619114515738411)
              ·
                refine ⟨13824217380928671773607617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216144920619114515738411 13824217380928671773607617)
                ·
                  refine ⟨10368163035696503830205713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13824217380928671773607617 10368163035696503830205713)
                  ·
                    refine ⟨7776122276772377872654285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10368163035696503830205713 7776122276772377872654285)
                    ·
                      refine ⟨2916045853789641702245357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776122276772377872654285 2916045853789641702245357)
                      ·
                        rfl

theorem cell23_5678979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_5678979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678979 prefixEnd_5678979 := by exact prefixLift 5678979
  have htrace : WordTrace (prefixWord ++ tailWord_5678979) baseStart_5678979 baseEnd_5678979 := by
    simpa [prefixWord, tailWord_5678979, baseEnd_5678979] using wordTrace_append hprefix tailTrace_5678979
  have hstable : (prefixWord ++ tailWord_5678979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678979).length < 2 ^ (prefixWord ++ tailWord_5678979).sum := by decide
  have hdescent : baseEnd_5678979 < baseStart_5678979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5678999 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 6]
def baseStart_5678999 : Nat := 118140960795 + 5678999 * 2 ^ 59
def prefixEnd_5678999 : Nat := 4983230072969 + 3 ^ 40 * 5678999 * 2
def baseEnd_5678999 : Nat := 324006235933636847110585

theorem tailTrace_5678999 : CollatzResearch.WordTrace tailWord_5678999 prefixEnd_5678999 324006235933636847110585 := by
  unfold tailWord_5678999
  simp only [CollatzResearch.WordTrace]
  refine ⟨207130109952963993656960051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138086739968642662437973367 207130109952963993656960051)
  ·
    refine ⟨310695164929445990485440077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207130109952963993656960051 310695164929445990485440077)
    ·
      refine ⟨116510686848542246432040029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310695164929445990485440077 116510686848542246432040029)
      ·
        refine ⟨43691507568203342412015011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116510686848542246432040029 43691507568203342412015011)
        ·
          refine ⟨65537261352305013618022517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43691507568203342412015011 65537261352305013618022517)
          ·
            refine ⟨6144118251778595026689611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65537261352305013618022517 6144118251778595026689611)
            ·
              refine ⟨9216177377667892540034417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144118251778595026689611 9216177377667892540034417)
              ·
                refine ⟨6912133033250919405025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9216177377667892540034417 6912133033250919405025813)
                ·
                  refine ⟨324006235933636847110585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6912133033250919405025813 324006235933636847110585)
                  ·
                    rfl

theorem cell23_5678999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 6].length) (baseStart_5678999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5678999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5678999 prefixEnd_5678999 := by exact prefixLift 5678999
  have htrace : WordTrace (prefixWord ++ tailWord_5678999) baseStart_5678999 baseEnd_5678999 := by
    simpa [prefixWord, tailWord_5678999, baseEnd_5678999] using wordTrace_append hprefix tailTrace_5678999
  have hstable : (prefixWord ++ tailWord_5678999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5678999).length < 2 ^ (prefixWord ++ tailWord_5678999).sum := by decide
  have hdescent : baseEnd_5678999 < baseStart_5678999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5678999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679002 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_5679002 : Nat := 118140960795 + 5679002 * 2 ^ 59
def prefixEnd_5679002 : Nat := 4983230072969 + 3 ^ 40 * 5679002 * 2
def baseEnd_5679002 : Nat := 2916057663844695112257751

theorem tailTrace_5679002 : CollatzResearch.WordTrace tailWord_5679002 prefixEnd_5679002 2916057663844695112257751 := by
  unfold tailWord_5679002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51782554842988281292329815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138086812914635416779546173 51782554842988281292329815)
  ·
    refine ⟨77673832264482421938494723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51782554842988281292329815 77673832264482421938494723)
    ·
      refine ⟨116510748396723632907742085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77673832264482421938494723 116510748396723632907742085)
      ·
        refine ⟨21845765324385681170201641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116510748396723632907742085 21845765324385681170201641)
        ·
          refine ⟨16384323993289260877651231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21845765324385681170201641 16384323993289260877651231)
          ·
            refine ⟨24576485989933891316476847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16384323993289260877651231 24576485989933891316476847)
            ·
              refine ⟨36864728984900836974715271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24576485989933891316476847 36864728984900836974715271)
              ·
                refine ⟨55297093477351255462072907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36864728984900836974715271 55297093477351255462072907)
                ·
                  refine ⟨82945640216026883193109361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55297093477351255462072907 82945640216026883193109361)
                  ·
                    refine ⟨62209230162020162394832021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82945640216026883193109361 62209230162020162394832021)
                    ·
                      refine ⟨2916057663844695112257751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62209230162020162394832021 2916057663844695112257751)
                      ·
                        rfl

theorem cell23_5679002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_5679002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679002 prefixEnd_5679002 := by exact prefixLift 5679002
  have htrace : WordTrace (prefixWord ++ tailWord_5679002) baseStart_5679002 baseEnd_5679002 := by
    simpa [prefixWord, tailWord_5679002, baseEnd_5679002] using wordTrace_append hprefix tailTrace_5679002
  have hstable : (prefixWord ++ tailWord_5679002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679002).length < 2 ^ (prefixWord ++ tailWord_5679002).sum := by decide
  have hdescent : baseEnd_5679002 < baseStart_5679002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679029 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5679029 : Nat := 118140960795 + 5679029 * 2 ^ 59
def prefixEnd_5679029 : Nat := 4983230072969 + 3 ^ 40 * 5679029 * 2
def baseEnd_5679029 : Nat := 972023842607455502206709

theorem tailTrace_5679029 : CollatzResearch.WordTrace tailWord_5679029 prefixEnd_5679029 972023842607455502206709 := by
  unfold tailWord_5679029
  simp only [CollatzResearch.WordTrace]
  refine ⟨207131204142855308780552141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138087469428570205853701427 207131204142855308780552141)
  ·
    refine ⟨77674201553570740792707053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207131204142855308780552141 77674201553570740792707053)
    ·
      refine ⟨29127825582589027797265145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77674201553570740792707053 29127825582589027797265145)
      ·
        refine ⟨21845869186941770847948859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29127825582589027797265145 21845869186941770847948859)
        ·
          refine ⟨32768803780412656271923289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21845869186941770847948859 32768803780412656271923289)
          ·
            refine ⟨24576602835309492203942467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32768803780412656271923289 24576602835309492203942467)
            ·
              refine ⟨36864904252964238305913701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24576602835309492203942467 36864904252964238305913701)
              ·
                refine ⟨6912169547430794682358819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36864904252964238305913701 6912169547430794682358819)
                ·
                  refine ⟨10368254321146192023538229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912169547430794682358819 10368254321146192023538229)
                  ·
                    refine ⟨972023842607455502206709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10368254321146192023538229 972023842607455502206709)
                    ·
                      rfl

theorem cell23_5679029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5679029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679029 prefixEnd_5679029 := by exact prefixLift 5679029
  have htrace : WordTrace (prefixWord ++ tailWord_5679029) baseStart_5679029 baseEnd_5679029 := by
    simpa [prefixWord, tailWord_5679029, baseEnd_5679029] using wordTrace_append hprefix tailTrace_5679029
  have hstable : (prefixWord ++ tailWord_5679029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679029).length < 2 ^ (prefixWord ++ tailWord_5679029).sum := by decide
  have hdescent : baseEnd_5679029 < baseStart_5679029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679060 : List Nat := [2, 4, 1, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_5679060 : Nat := 118140960795 + 5679060 * 2 ^ 59
def prefixEnd_5679060 : Nat := 4983230072969 + 3 ^ 40 * 5679060 * 2
def baseEnd_5679060 : Nat := 2916087445722655885332485

theorem tailTrace_5679060 : CollatzResearch.WordTrace tailWord_5679060 prefixEnd_5679060 2916087445722655885332485 := by
  unfold tailWord_5679060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103566167402871500537465317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138088223203828667383287089 103566167402871500537465317)
  ·
    refine ⟨19418656388038406350774747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103566167402871500537465317 19418656388038406350774747)
    ·
      refine ⟨29127984582057609526162121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19418656388038406350774747 29127984582057609526162121)
      ·
        refine ⟨21845988436543207144621591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29127984582057609526162121 21845988436543207144621591)
        ·
          refine ⟨32768982654814810716932387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21845988436543207144621591 32768982654814810716932387)
          ·
            refine ⟨49153473982222216075398581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32768982654814810716932387 49153473982222216075398581)
            ·
              refine ⟨4608138185833332757068617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49153473982222216075398581 4608138185833332757068617)
              ·
                refine ⟨3456103639374999567801463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608138185833332757068617 3456103639374999567801463)
                ·
                  refine ⟨5184155459062499351702195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456103639374999567801463 5184155459062499351702195)
                  ·
                    refine ⟨7776233188593749027553293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184155459062499351702195 7776233188593749027553293)
                    ·
                      refine ⟨2916087445722655885332485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776233188593749027553293 2916087445722655885332485)
                      ·
                        rfl

theorem cell23_5679060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_5679060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679060 prefixEnd_5679060 := by exact prefixLift 5679060
  have htrace : WordTrace (prefixWord ++ tailWord_5679060) baseStart_5679060 baseEnd_5679060 := by
    simpa [prefixWord, tailWord_5679060, baseEnd_5679060] using wordTrace_append hprefix tailTrace_5679060
  have hstable : (prefixWord ++ tailWord_5679060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679060).length < 2 ^ (prefixWord ++ tailWord_5679060).sum := by decide
  have hdescent : baseEnd_5679060 < baseStart_5679060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679086 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_5679086 : Nat := 118140960795 + 5679086 * 2 ^ 59
def prefixEnd_5679086 : Nat := 4983230072969 + 3 ^ 40 * 5679086 * 2
def baseEnd_5679086 : Nat := 2916100796219672783607365

theorem tailTrace_5679086 : CollatzResearch.WordTrace tailWord_5679086 prefixEnd_5679086 2916100796219672783607365 := by
  unfold tailWord_5679086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25891660387956100939422139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138088855402432538343584741 25891660387956100939422139)
  ·
    refine ⟨38837490581934151409133209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25891660387956100939422139 38837490581934151409133209)
    ·
      refine ⟨29128117936450613556849907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38837490581934151409133209 29128117936450613556849907)
      ·
        refine ⟨43692176904675920335274861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29128117936450613556849907 43692176904675920335274861)
        ·
          refine ⟨16384566339253470125728073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43692176904675920335274861 16384566339253470125728073)
          ·
            refine ⟨12288424754440102594296055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16384566339253470125728073 12288424754440102594296055)
            ·
              refine ⟨18432637131660153891444083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12288424754440102594296055 18432637131660153891444083)
              ·
                refine ⟨27648955697490230837166125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18432637131660153891444083 27648955697490230837166125)
                ·
                  refine ⟨10368358386558836563937297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27648955697490230837166125 10368358386558836563937297)
                  ·
                    refine ⟨7776268789919127422952973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10368358386558836563937297 7776268789919127422952973)
                    ·
                      refine ⟨2916100796219672783607365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776268789919127422952973 2916100796219672783607365)
                      ·
                        rfl

theorem cell23_5679086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_5679086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679086 prefixEnd_5679086 := by exact prefixLift 5679086
  have htrace : WordTrace (prefixWord ++ tailWord_5679086) baseStart_5679086 baseEnd_5679086 := by
    simpa [prefixWord, tailWord_5679086, baseEnd_5679086] using wordTrace_append hprefix tailTrace_5679086
  have hstable : (prefixWord ++ tailWord_5679086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679086).length < 2 ^ (prefixWord ++ tailWord_5679086).sum := by decide
  have hdescent : baseEnd_5679086 < baseStart_5679086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679099 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 3]
def baseStart_5679099 : Nat := 118140960795 + 5679099 * 2 ^ 59
def prefixEnd_5679099 : Nat := 4983230072969 + 3 ^ 40 * 5679099 * 2
def baseEnd_5679099 : Nat := 2916107471468181232744805

theorem tailTrace_5679099 : CollatzResearch.WordTrace tailWord_5679099 prefixEnd_5679099 2916107471468181232744805 := by
  unfold tailWord_5679099
  simp only [CollatzResearch.WordTrace]
  refine ⟨207133757252601710735600351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138089171501734473823733567 207133757252601710735600351)
  ·
    refine ⟨310700635878902566103400527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207133757252601710735600351 310700635878902566103400527)
    ·
      refine ⟨466050953818353849155100791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310700635878902566103400527 466050953818353849155100791)
      ·
        refine ⟨699076430727530773732651187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466050953818353849155100791 699076430727530773732651187)
        ·
          refine ⟨1048614646091296160598976781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699076430727530773732651187 1048614646091296160598976781)
          ·
            refine ⟨393230492284236060224616293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1048614646091296160598976781 393230492284236060224616293)
            ·
              refine ⟨73730717303294261292115555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393230492284236060224616293 73730717303294261292115555)
              ·
                refine ⟨110596075954941391938173333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73730717303294261292115555 110596075954941391938173333)
                ·
                  refine ⟨5184191060387877747101875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110596075954941391938173333 5184191060387877747101875)
                  ·
                    refine ⟨7776286590581816620652813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184191060387877747101875 7776286590581816620652813)
                    ·
                      refine ⟨2916107471468181232744805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776286590581816620652813 2916107471468181232744805)
                      ·
                        rfl

theorem cell23_5679099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 6, 1, 3].length) (baseStart_5679099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679099 prefixEnd_5679099 := by exact prefixLift 5679099
  have htrace : WordTrace (prefixWord ++ tailWord_5679099) baseStart_5679099 baseEnd_5679099 := by
    simpa [prefixWord, tailWord_5679099, baseEnd_5679099] using wordTrace_append hprefix tailTrace_5679099
  have hstable : (prefixWord ++ tailWord_5679099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679099).length < 2 ^ (prefixWord ++ tailWord_5679099).sum := by decide
  have hdescent : baseEnd_5679099 < baseStart_5679099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679133 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_5679133 : Nat := 118140960795 + 5679133 * 2 ^ 59
def prefixEnd_5679133 : Nat := 4983230072969 + 3 ^ 40 * 5679133 * 2
def baseEnd_5679133 : Nat := 2916124929810434099719649

theorem tailTrace_5679133 : CollatzResearch.WordTrace tailWord_5679133 prefixEnd_5679133 2916124929810434099719649 := by
  unfold tailWord_5679133
  simp only [CollatzResearch.WordTrace]
  refine ⟨207134997334478534542338053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138089998222985689694892035 207134997334478534542338053)
  ·
    refine ⟨38837812000214725226688385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207134997334478534542338053 38837812000214725226688385)
    ·
      refine ⟨29128359000161043920016289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38837812000214725226688385 29128359000161043920016289)
      ·
        refine ⟨21846269250120782940012217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29128359000161043920016289 21846269250120782940012217)
        ·
          refine ⟨16384701937590587205009163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21846269250120782940012217 16384701937590587205009163)
          ·
            refine ⟨24577052906385880807513745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16384701937590587205009163 24577052906385880807513745)
            ·
              refine ⟨18432789679789410605635309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24577052906385880807513745 18432789679789410605635309)
              ·
                refine ⟨6912296129921028977113241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18432789679789410605635309 6912296129921028977113241)
                ·
                  refine ⟨5184222097440771732834931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6912296129921028977113241 5184222097440771732834931)
                  ·
                    refine ⟨7776333146161157599252397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184222097440771732834931 7776333146161157599252397)
                    ·
                      refine ⟨2916124929810434099719649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776333146161157599252397 2916124929810434099719649)
                      ·
                        rfl

theorem cell23_5679133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_5679133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679133 prefixEnd_5679133 := by exact prefixLift 5679133
  have htrace : WordTrace (prefixWord ++ tailWord_5679133) baseStart_5679133 baseEnd_5679133 := by
    simpa [prefixWord, tailWord_5679133, baseEnd_5679133] using wordTrace_append hprefix tailTrace_5679133
  have hstable : (prefixWord ++ tailWord_5679133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679133).length < 2 ^ (prefixWord ++ tailWord_5679133).sum := by decide
  have hdescent : baseEnd_5679133 < baseStart_5679133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679162 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_5679162 : Nat := 118140960795 + 5679162 * 2 ^ 59
def prefixEnd_5679162 : Nat := 4983230072969 + 3 ^ 40 * 5679162 * 2
def baseEnd_5679162 : Nat := 324015535638823831806335

theorem tailTrace_5679162 : CollatzResearch.WordTrace tailWord_5679162 prefixEnd_5679162 324015535638823831806335 := by
  unfold tailWord_5679162
  simp only [CollatzResearch.WordTrace]
  refine ⟨51784013762843368123785935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138090703367582314996762493 51784013762843368123785935)
  ·
    refine ⟨77676020644265052185678903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51784013762843368123785935 77676020644265052185678903)
    ·
      refine ⟨116514030966397578278518355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77676020644265052185678903 116514030966397578278518355)
      ·
        refine ⟨174771046449596367417777533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116514030966397578278518355 174771046449596367417777533)
        ·
          refine ⟨65539142418598637781666575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174771046449596367417777533 65539142418598637781666575)
          ·
            refine ⟨98308713627897956672499863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65539142418598637781666575 98308713627897956672499863)
            ·
              refine ⟨147463070441846935008749795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98308713627897956672499863 147463070441846935008749795)
              ·
                refine ⟨221194605662770402513124693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147463070441846935008749795 221194605662770402513124693)
                ·
                  refine ⟨324015535638823831806335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 221194605662770402513124693 324015535638823831806335)
                  ·
                    rfl

theorem cell23_5679162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_5679162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679162 prefixEnd_5679162 := by exact prefixLift 5679162
  have htrace : WordTrace (prefixWord ++ tailWord_5679162) baseStart_5679162 baseEnd_5679162 := by
    simpa [prefixWord, tailWord_5679162, baseEnd_5679162] using wordTrace_append hprefix tailTrace_5679162
  have hstable : (prefixWord ++ tailWord_5679162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679162).length < 2 ^ (prefixWord ++ tailWord_5679162).sum := by decide
  have hdescent : baseEnd_5679162 < baseStart_5679162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679209 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 2, 5]
def baseStart_5679209 : Nat := 118140960795 + 5679209 * 2 ^ 59
def prefixEnd_5679209 : Nat := 4983230072969 + 3 ^ 40 * 5679209 * 2
def baseEnd_5679209 : Nat := 972054651446725267456433

theorem tailTrace_5679209 : CollatzResearch.WordTrace tailWord_5679209 prefixEnd_5679209 972054651446725267456433 := by
  unfold tailWord_5679209
  simp only [CollatzResearch.WordTrace]
  refine ⟨207137769282203199522104681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138091846188135466348069787 207137769282203199522104681)
  ·
    refine ⟨155353326961652399641578511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207137769282203199522104681 155353326961652399641578511)
    ·
      refine ⟨233029990442478599462367767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155353326961652399641578511 233029990442478599462367767)
      ·
        refine ⟨349544985663717899193551651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233029990442478599462367767 349544985663717899193551651)
        ·
          refine ⟨524317478495576848790327477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349544985663717899193551651 524317478495576848790327477)
          ·
            refine ⟨49154763608960329574093201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 524317478495576848790327477 49154763608960329574093201)
            ·
              refine ⟨36866072706720247180569901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49154763608960329574093201 36866072706720247180569901)
              ·
                refine ⟨13824777265020092692713713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36866072706720247180569901 13824777265020092692713713)
                ·
                  refine ⟨10368582948765069519535285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13824777265020092692713713 10368582948765069519535285)
                  ·
                    refine ⟨972054651446725267456433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10368582948765069519535285 972054651446725267456433)
                    ·
                      rfl

theorem cell23_5679209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 5].length) (baseStart_5679209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679209 prefixEnd_5679209 := by exact prefixLift 5679209
  have htrace : WordTrace (prefixWord ++ tailWord_5679209) baseStart_5679209 baseEnd_5679209 := by
    simpa [prefixWord, tailWord_5679209, baseEnd_5679209] using wordTrace_append hprefix tailTrace_5679209
  have hstable : (prefixWord ++ tailWord_5679209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679209).length < 2 ^ (prefixWord ++ tailWord_5679209).sum := by decide
  have hdescent : baseEnd_5679209 < baseStart_5679209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679263 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_5679263 : Nat := 118140960795 + 5679263 * 2 ^ 59
def prefixEnd_5679263 : Nat := 4983230072969 + 3 ^ 40 * 5679263 * 2
def baseEnd_5679263 : Nat := 2916191682295518591094051

theorem tailTrace_5679263 : CollatzResearch.WordTrace tailWord_5679263 prefixEnd_5679263 2916191682295518591094051 := by
  unfold tailWord_5679263
  simp only [CollatzResearch.WordTrace]
  refine ⟨207139738824007566744570443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138093159216005044496380295 207139738824007566744570443)
  ·
    refine ⟨310709608236011350116855665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207139738824007566744570443 310709608236011350116855665)
    ·
      refine ⟨233032206177008512587641749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310709608236011350116855665 233032206177008512587641749)
      ·
        refine ⟨10923384664547274027545707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233032206177008512587641749 10923384664547274027545707)
        ·
          refine ⟨16385076996820911041318561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923384664547274027545707 16385076996820911041318561)
          ·
            refine ⟨12288807747615683280988921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385076996820911041318561 12288807747615683280988921)
            ·
              refine ⟨9216605810711762460741691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12288807747615683280988921 9216605810711762460741691)
              ·
                refine ⟨13824908716067643691112537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216605810711762460741691 13824908716067643691112537)
                ·
                  refine ⟨10368681537050732768334403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13824908716067643691112537 10368681537050732768334403)
                  ·
                    refine ⟨15553022305576099152501605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10368681537050732768334403 15553022305576099152501605)
                    ·
                      refine ⟨2916191682295518591094051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15553022305576099152501605 2916191682295518591094051)
                      ·
                        rfl

theorem cell23_5679263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_5679263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679263 prefixEnd_5679263 := by exact prefixLift 5679263
  have htrace : WordTrace (prefixWord ++ tailWord_5679263) baseStart_5679263 baseEnd_5679263 := by
    simpa [prefixWord, tailWord_5679263, baseEnd_5679263] using wordTrace_append hprefix tailTrace_5679263
  have hstable : (prefixWord ++ tailWord_5679263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679263).length < 2 ^ (prefixWord ++ tailWord_5679263).sum := by decide
  have hdescent : baseEnd_5679263 < baseStart_5679263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679289 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 6]
def baseStart_5679289 : Nat := 118140960795 + 5679289 * 2 ^ 59
def prefixEnd_5679289 : Nat := 4983230072969 + 3 ^ 40 * 5679289 * 2
def baseEnd_5679289 : Nat := 2916205032792535489368931

theorem tailTrace_5679289 : CollatzResearch.WordTrace tailWord_5679289 prefixEnd_5679289 2916205032792535489368931 := by
  unfold tailWord_5679289
  simp only [CollatzResearch.WordTrace]
  refine ⟨207140687121913373185016921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138093791414608915456677947 207140687121913373185016921)
  ·
    refine ⟨155355515341435029888762691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207140687121913373185016921 155355515341435029888762691)
    ·
      refine ⟨233033273012152544833144037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155355515341435029888762691 233033273012152544833144037)
      ·
        refine ⟨43693738689778602156214507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233033273012152544833144037 43693738689778602156214507)
        ·
          refine ⟨65540608034667903234321761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43693738689778602156214507 65540608034667903234321761)
          ·
            refine ⟨49155456026000927425741321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65540608034667903234321761 49155456026000927425741321)
            ·
              refine ⟨36866592019500695569305991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49155456026000927425741321 36866592019500695569305991)
              ·
                refine ⟨55299888029251043353958987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36866592019500695569305991 55299888029251043353958987)
                ·
                  refine ⟨82949832043876565030938481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55299888029251043353958987 82949832043876565030938481)
                  ·
                    refine ⟨62212374032907423773203861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82949832043876565030938481 62212374032907423773203861)
                    ·
                      refine ⟨2916205032792535489368931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62212374032907423773203861 2916205032792535489368931)
                      ·
                        rfl

theorem cell23_5679289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_5679289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679289 prefixEnd_5679289 := by exact prefixLift 5679289
  have htrace : WordTrace (prefixWord ++ tailWord_5679289) baseStart_5679289 baseEnd_5679289 := by
    simpa [prefixWord, tailWord_5679289, baseEnd_5679289] using wordTrace_append hprefix tailTrace_5679289
  have hstable : (prefixWord ++ tailWord_5679289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679289).length < 2 ^ (prefixWord ++ tailWord_5679289).sum := by decide
  have hdescent : baseEnd_5679289 < baseStart_5679289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679290 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 1, 4]
def baseStart_5679290 : Nat := 118140960795 + 5679290 * 2 ^ 59
def prefixEnd_5679290 : Nat := 4983230072969 + 3 ^ 40 * 5679290 * 2
def baseEnd_5679290 : Nat := 972068515424396661818809

theorem tailTrace_5679290 : CollatzResearch.WordTrace tailWord_5679290 prefixEnd_5679290 972068515424396661818809 := by
  unfold tailWord_5679290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51785180898727437588950831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138093815729939833570535549 51785180898727437588950831)
  ·
    refine ⟨77677771348091156383426247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51785180898727437588950831 77677771348091156383426247)
    ·
      refine ⟨116516657022136734575139371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77677771348091156383426247 116516657022136734575139371)
      ·
        refine ⟨174774985533205101862709057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116516657022136734575139371 174774985533205101862709057)
        ·
          refine ⟨131081239149903826397031793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174774985533205101862709057 131081239149903826397031793)
          ·
            refine ⟨98310929362427869797773845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131081239149903826397031793 98310929362427869797773845)
            ·
              refine ⟨4608324813863806396770649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98310929362427869797773845 4608324813863806396770649)
              ·
                refine ⟨3456243610397854797577987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608324813863806396770649 3456243610397854797577987)
                ·
                  refine ⟨5184365415596782196366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456243610397854797577987 5184365415596782196366981)
                  ·
                    refine ⟨972068515424396661818809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184365415596782196366981 972068515424396661818809)
                    ·
                      rfl

theorem cell23_5679290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 4].length) (baseStart_5679290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679290 prefixEnd_5679290 := by exact prefixLift 5679290
  have htrace : WordTrace (prefixWord ++ tailWord_5679290) baseStart_5679290 baseEnd_5679290 := by
    simpa [prefixWord, tailWord_5679290, baseEnd_5679290] using wordTrace_append hprefix tailTrace_5679290
  have hstable : (prefixWord ++ tailWord_5679290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679290).length < 2 ^ (prefixWord ++ tailWord_5679290).sum := by decide
  have hdescent : baseEnd_5679290 < baseStart_5679290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679317 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5679317 : Nat := 118140960795 + 5679317 * 2 ^ 59
def prefixEnd_5679317 : Nat := 4983230072969 + 3 ^ 40 * 5679317 * 2
def baseEnd_5679317 : Nat := 2916219410250861379818803

theorem tailTrace_5679317 : CollatzResearch.WordTrace tailWord_5679317 prefixEnd_5679317 2916219410250861379818803 := by
  unfold tailWord_5679317
  simp only [CollatzResearch.WordTrace]
  refine ⟨207141708365811933967036205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138094472243874622644690803 207141708365811933967036205)
  ·
    refine ⟨77678140637179475237638577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207141708365811933967036205 77678140637179475237638577)
    ·
      refine ⟨58258605477884606428228933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77678140637179475237638577 58258605477884606428228933)
      ·
        refine ⟨10923488527103363705292925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58258605477884606428228933 10923488527103363705292925)
        ·
          refine ⟨4096308197663761389484847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10923488527103363705292925 4096308197663761389484847)
          ·
            refine ⟨6144462296495642084227271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096308197663761389484847 6144462296495642084227271)
            ·
              refine ⟨9216693444743463126340907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6144462296495642084227271 9216693444743463126340907)
              ·
                refine ⟨13825040167115194689511361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216693444743463126340907 13825040167115194689511361)
                ·
                  refine ⟨10368780125336396017133521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13825040167115194689511361 10368780125336396017133521)
                  ·
                    refine ⟨7776585094002297012850141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10368780125336396017133521 7776585094002297012850141)
                    ·
                      refine ⟨2916219410250861379818803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776585094002297012850141 2916219410250861379818803)
                      ·
                        rfl

theorem cell23_5679317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5679317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679317 prefixEnd_5679317 := by exact prefixLift 5679317
  have htrace : WordTrace (prefixWord ++ tailWord_5679317) baseStart_5679317 baseEnd_5679317 := by
    simpa [prefixWord, tailWord_5679317, baseEnd_5679317] using wordTrace_append hprefix tailTrace_5679317
  have hstable : (prefixWord ++ tailWord_5679317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679317).length < 2 ^ (prefixWord ++ tailWord_5679317).sum := by decide
  have hdescent : baseEnd_5679317 < baseStart_5679317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679324 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5679324 : Nat := 118140960795 + 5679324 * 2 ^ 59
def prefixEnd_5679324 : Nat := 4983230072969 + 3 ^ 40 * 5679324 * 2
def baseEnd_5679324 : Nat := 972074334871814284143757

theorem tailTrace_5679324 : CollatzResearch.WordTrace tailWord_5679324 prefixEnd_5679324 972074334871814284143757 := by
  unfold tailWord_5679324
  simp only [CollatzResearch.WordTrace]
  refine ⟨103570981838393287081270513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138094642451191049441694017 103570981838393287081270513)
  ·
    refine ⟨77678236378794965310952885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103570981838393287081270513 77678236378794965310952885)
    ·
      refine ⟨7282334660512027997901833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77678236378794965310952885 7282334660512027997901833)
      ·
        refine ⟨5461750995384020998426375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7282334660512027997901833 5461750995384020998426375)
        ·
          refine ⟨8192626493076031497639563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461750995384020998426375 8192626493076031497639563)
          ·
            refine ⟨12288939739614047246459345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192626493076031497639563 12288939739614047246459345)
            ·
              refine ⟨9216704804710535434844509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12288939739614047246459345 9216704804710535434844509)
              ·
                refine ⟨3456264301766450788066691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9216704804710535434844509 3456264301766450788066691)
                ·
                  refine ⟨5184396452649676182100037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456264301766450788066691 5184396452649676182100037)
                  ·
                    refine ⟨972074334871814284143757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184396452649676182100037 972074334871814284143757)
                    ·
                      rfl

theorem cell23_5679324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5679324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679324 prefixEnd_5679324 := by exact prefixLift 5679324
  have htrace : WordTrace (prefixWord ++ tailWord_5679324) baseStart_5679324 baseEnd_5679324 := by
    simpa [prefixWord, tailWord_5679324, baseEnd_5679324] using wordTrace_append hprefix tailTrace_5679324
  have hstable : (prefixWord ++ tailWord_5679324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679324).length < 2 ^ (prefixWord ++ tailWord_5679324).sum := by decide
  have hdescent : baseEnd_5679324 < baseStart_5679324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679333 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 1, 5]
def baseStart_5679333 : Nat := 118140960795 + 5679333 * 2 ^ 59
def prefixEnd_5679333 : Nat := 4983230072969 + 3 ^ 40 * 5679333 * 2
def baseEnd_5679333 : Nat := 972075875313777772406243

theorem tailTrace_5679333 : CollatzResearch.WordTrace tailWord_5679333 prefixEnd_5679333 972075875313777772406243 := by
  unfold tailWord_5679333
  simp only [CollatzResearch.WordTrace]
  refine ⟨207142291933753968699618653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138094861289169312466412435 207142291933753968699618653)
  ·
    refine ⟨77678359475157738262356995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207142291933753968699618653 77678359475157738262356995)
    ·
      refine ⟨116517539212736607393535493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77678359475157738262356995 116517539212736607393535493)
      ·
        refine ⟨21847038602388113886287905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116517539212736607393535493 21847038602388113886287905)
        ·
          refine ⟨16385278951791085414715929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21847038602388113886287905 16385278951791085414715929)
          ·
            refine ⟨12288959213843314061036947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385278951791085414715929 12288959213843314061036947)
            ·
              refine ⟨18433438820764971091555421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12288959213843314061036947 18433438820764971091555421)
              ·
                refine ⟨6912539557786864159333283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18433438820764971091555421 6912539557786864159333283)
                ·
                  refine ⟨10368809336680296238999925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912539557786864159333283 10368809336680296238999925)
                  ·
                    refine ⟨972075875313777772406243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10368809336680296238999925 972075875313777772406243)
                    ·
                      rfl

theorem cell23_5679333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_5679333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679333 prefixEnd_5679333 := by exact prefixLift 5679333
  have htrace : WordTrace (prefixWord ++ tailWord_5679333) baseStart_5679333 baseEnd_5679333 := by
    simpa [prefixWord, tailWord_5679333, baseEnd_5679333] using wordTrace_append hprefix tailTrace_5679333
  have hstable : (prefixWord ++ tailWord_5679333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679333).length < 2 ^ (prefixWord ++ tailWord_5679333).sum := by decide
  have hdescent : baseEnd_5679333 < baseStart_5679333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679356 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_5679356 : Nat := 118140960795 + 5679356 * 2 ^ 59
def prefixEnd_5679356 : Nat := 4983230072969 + 3 ^ 40 * 5679356 * 2
def baseEnd_5679356 : Nat := 2916239435996386727231123

theorem tailTrace_5679356 : CollatzResearch.WordTrace tailWord_5679356 prefixEnd_5679356 2916239435996386727231123 := by
  unfold tailWord_5679356
  simp only [CollatzResearch.WordTrace]
  refine ⟨103571565406335321813852961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138095420541780429085137281 103571565406335321813852961)
  ·
    refine ⟨77678674054751491360389721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103571565406335321813852961 77678674054751491360389721)
    ·
      refine ⟨58259005541063618520292291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77678674054751491360389721 58259005541063618520292291)
      ·
        refine ⟨87388508311595427780438437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58259005541063618520292291 87388508311595427780438437)
        ·
          refine ⟨16385345308424142708832207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87388508311595427780438437 16385345308424142708832207)
          ·
            refine ⟨24578017962636214063248311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16385345308424142708832207 24578017962636214063248311)
            ·
              refine ⟨36867026943954321094872467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24578017962636214063248311 36867026943954321094872467)
              ·
                refine ⟨55300540415931481642308701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36867026943954321094872467 55300540415931481642308701)
                ·
                  refine ⟨20737702655974305615865763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55300540415931481642308701 20737702655974305615865763)
                  ·
                    refine ⟨31106553983961458423798645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20737702655974305615865763 31106553983961458423798645)
                    ·
                      refine ⟨2916239435996386727231123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31106553983961458423798645 2916239435996386727231123)
                      ·
                        rfl

theorem cell23_5679356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_5679356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679356 prefixEnd_5679356 := by exact prefixLift 5679356
  have htrace : WordTrace (prefixWord ++ tailWord_5679356) baseStart_5679356 baseEnd_5679356 := by
    simpa [prefixWord, tailWord_5679356, baseEnd_5679356] using wordTrace_append hprefix tailTrace_5679356
  have hstable : (prefixWord ++ tailWord_5679356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679356).length < 2 ^ (prefixWord ++ tailWord_5679356).sum := by decide
  have hdescent : baseEnd_5679356 < baseStart_5679356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679359 : List Nat := [1, 1, 2, 2, 1, 4, 2, 10]
def baseStart_5679359 : Nat := 118140960795 + 5679359 * 2 ^ 59
def prefixEnd_5679359 : Nat := 4983230072969 + 3 ^ 40 * 5679359 * 2
def baseEnd_5679359 : Nat := 108008925053272230203467

theorem tailTrace_5679359 : CollatzResearch.WordTrace tailWord_5679359 prefixEnd_5679359 108008925053272230203467 := by
  unfold tailWord_5679359
  simp only [CollatzResearch.WordTrace]
  refine ⟨207143240231659775140065131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138095493487773183426710087 207143240231659775140065131)
  ·
    refine ⟨310714860347489662710097697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207143240231659775140065131 310714860347489662710097697)
    ·
      refine ⟨233036145260617247032573273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310714860347489662710097697 233036145260617247032573273)
      ·
        refine ⟨174777108945462935274429955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233036145260617247032573273 174777108945462935274429955)
        ·
          refine ⟨262165663418194402911644933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174777108945462935274429955 262165663418194402911644933)
          ·
            refine ⟨49156061890911450545933425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262165663418194402911644933 49156061890911450545933425)
            ·
              refine ⟨36867046418183587909450069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49156061890911450545933425 36867046418183587909450069)
              ·
                refine ⟨108008925053272230203467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36867046418183587909450069 108008925053272230203467)
                ·
                  rfl

theorem cell23_5679359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 10].length) (baseStart_5679359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679359 prefixEnd_5679359 := by exact prefixLift 5679359
  have htrace : WordTrace (prefixWord ++ tailWord_5679359) baseStart_5679359 baseEnd_5679359 := by
    simpa [prefixWord, tailWord_5679359, baseEnd_5679359] using wordTrace_append hprefix tailTrace_5679359
  have hstable : (prefixWord ++ tailWord_5679359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679359).length < 2 ^ (prefixWord ++ tailWord_5679359).sum := by decide
  have hdescent : baseEnd_5679359 < baseStart_5679359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679370 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_5679370 : Nat := 118140960795 + 5679370 * 2 ^ 59
def prefixEnd_5679370 : Nat := 4983230072969 + 3 ^ 40 * 5679370 * 2
def baseEnd_5679370 : Nat := 2916246624725549672456059

theorem tailTrace_5679370 : CollatzResearch.WordTrace tailWord_5679370 prefixEnd_5679370 2916246624725549672456059 := by
  unfold tailWord_5679370
  simp only [CollatzResearch.WordTrace]
  refine ⟨51785910358654981004678891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138095760956413282679143709 51785910358654981004678891)
  ·
    refine ⟨77678865537982471507018337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51785910358654981004678891 77678865537982471507018337)
    ·
      refine ⟨58259149153486853630263753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77678865537982471507018337 58259149153486853630263753)
      ·
        refine ⟨43694361865115140222697815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58259149153486853630263753 43694361865115140222697815)
        ·
          refine ⟨65541542797672710334046723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43694361865115140222697815 65541542797672710334046723)
          ·
            refine ⟨98312314196509065501070085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65541542797672710334046723 98312314196509065501070085)
            ·
              refine ⟨18433558911845449781450641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98312314196509065501070085 18433558911845449781450641)
              ·
                refine ⟨13825169183884087336087981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18433558911845449781450641 13825169183884087336087981)
                ·
                  refine ⟨5184438443956532751032993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13825169183884087336087981 5184438443956532751032993)
                  ·
                    refine ⟨3888328832967399563274745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5184438443956532751032993 3888328832967399563274745)
                    ·
                      refine ⟨2916246624725549672456059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888328832967399563274745 2916246624725549672456059)
                      ·
                        rfl

theorem cell23_5679370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_5679370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679370 prefixEnd_5679370 := by exact prefixLift 5679370
  have htrace : WordTrace (prefixWord ++ tailWord_5679370) baseStart_5679370 baseEnd_5679370 := by
    simpa [prefixWord, tailWord_5679370, baseEnd_5679370] using wordTrace_append hprefix tailTrace_5679370
  have hstable : (prefixWord ++ tailWord_5679370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679370).length < 2 ^ (prefixWord ++ tailWord_5679370).sum := by decide
  have hdescent : baseEnd_5679370 < baseStart_5679370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679379 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_5679379 : Nat := 118140960795 + 5679379 * 2 ^ 59
def prefixEnd_5679379 : Nat := 4983230072969 + 3 ^ 40 * 5679379 * 2
def baseEnd_5679379 : Nat := 2916251246051440137243517

theorem tailTrace_5679379 : CollatzResearch.WordTrace tailWord_5679379 prefixEnd_5679379 2916251246051440137243517 := by
  unfold tailWord_5679379
  simp only [CollatzResearch.WordTrace]
  refine ⟨207143969691587318555793191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138095979794391545703862127 207143969691587318555793191)
  ·
    refine ⟨310715954537380977833689787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207143969691587318555793191 310715954537380977833689787)
    ·
      refine ⟨466073931806071466750534681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310715954537380977833689787 466073931806071466750534681)
      ·
        refine ⟨349555448854553600062901011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466073931806071466750534681 349555448854553600062901011)
        ·
          refine ⟨524333173281830400094351517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349555448854553600062901011 524333173281830400094351517)
          ·
            refine ⟨196624939980686400035381819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524333173281830400094351517 196624939980686400035381819)
            ·
              refine ⟨294937409971029600053072729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196624939980686400035381819 294937409971029600053072729)
              ·
                refine ⟨221203057478272200039804547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294937409971029600053072729 221203057478272200039804547)
                ·
                  refine ⟨331804586217408300059706821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221203057478272200039804547 331804586217408300059706821)
                  ·
                    refine ⟨62213359915764056261195029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331804586217408300059706821 62213359915764056261195029)
                    ·
                      refine ⟨2916251246051440137243517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62213359915764056261195029 2916251246051440137243517)
                      ·
                        rfl

theorem cell23_5679379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_5679379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679379 prefixEnd_5679379 := by exact prefixLift 5679379
  have htrace : WordTrace (prefixWord ++ tailWord_5679379) baseStart_5679379 baseEnd_5679379 := by
    simpa [prefixWord, tailWord_5679379, baseEnd_5679379] using wordTrace_append hprefix tailTrace_5679379
  have hstable : (prefixWord ++ tailWord_5679379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679379).length < 2 ^ (prefixWord ++ tailWord_5679379).sum := by decide
  have hdescent : baseEnd_5679379 < baseStart_5679379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679387 : List Nat := [1, 1, 1, 1, 1, 1, 9, 3, 1, 2, 2]
def baseStart_5679387 : Nat := 118140960795 + 5679387 * 2 ^ 59
def prefixEnd_5679387 : Nat := 4983230072969 + 3 ^ 40 * 5679387 * 2
def baseEnd_5679387 : Nat := 2916255353896676105943481

theorem tailTrace_5679387 : CollatzResearch.WordTrace tailWord_5679387 prefixEnd_5679387 2916255353896676105943481 := by
  unfold tailWord_5679387
  simp only [CollatzResearch.WordTrace]
  refine ⟨207144261475558335922084415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138096174317038890614722943 207144261475558335922084415)
  ·
    refine ⟨310716392213337503883126623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207144261475558335922084415 310716392213337503883126623)
    ·
      refine ⟨466074588320006255824689935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310716392213337503883126623 466074588320006255824689935)
      ·
        refine ⟨699111882480009383737034903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466074588320006255824689935 699111882480009383737034903)
        ·
          refine ⟨1048667823720014075605552355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699111882480009383737034903 1048667823720014075605552355)
          ·
            refine ⟨1573001735580021113408328533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048667823720014075605552355 1573001735580021113408328533)
            ·
              refine ⟨9216807044414186211376925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1573001735580021113408328533 9216807044414186211376925)
              ·
                refine ⟨3456302641655319829266347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9216807044414186211376925 3456302641655319829266347)
                ·
                  refine ⟨5184453962482979743899521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456302641655319829266347 5184453962482979743899521)
                  ·
                    refine ⟨3888340471862234807924641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5184453962482979743899521 3888340471862234807924641)
                    ·
                      refine ⟨2916255353896676105943481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888340471862234807924641 2916255353896676105943481)
                      ·
                        rfl

theorem cell23_5679387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 3, 1, 2, 2].length) (baseStart_5679387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679387 prefixEnd_5679387 := by exact prefixLift 5679387
  have htrace : WordTrace (prefixWord ++ tailWord_5679387) baseStart_5679387 baseEnd_5679387 := by
    simpa [prefixWord, tailWord_5679387, baseEnd_5679387] using wordTrace_append hprefix tailTrace_5679387
  have hstable : (prefixWord ++ tailWord_5679387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679387).length < 2 ^ (prefixWord ++ tailWord_5679387).sum := by decide
  have hdescent : baseEnd_5679387 < baseStart_5679387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679390 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5679390 : Nat := 118140960795 + 5679390 * 2 ^ 59
def prefixEnd_5679390 : Nat := 4983230072969 + 3 ^ 40 * 5679390 * 2
def baseEnd_5679390 : Nat := 2916256894338639594205967

theorem tailTrace_5679390 : CollatzResearch.WordTrace tailWord_5679390 prefixEnd_5679390 2916256894338639594205967 := by
  unfold tailWord_5679390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25893046361818433429305453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138096247263031644956295749 25893046361818433429305453)
  ·
    refine ⟨9709892385681912535989545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25893046361818433429305453 9709892385681912535989545)
    ·
      refine ⟨7282419289261434401992159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9709892385681912535989545 7282419289261434401992159)
      ·
        refine ⟨10923628933892151602988239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7282419289261434401992159 10923628933892151602988239)
        ·
          refine ⟨16385443400838227404482359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923628933892151602988239 16385443400838227404482359)
          ·
            refine ⟨24578165101257341106723539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16385443400838227404482359 24578165101257341106723539)
            ·
              refine ⟨36867247651886011660085309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24578165101257341106723539 36867247651886011660085309)
              ·
                refine ⟨13825217869457254372531991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36867247651886011660085309 13825217869457254372531991)
                ·
                  refine ⟨20737826804185881558797987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13825217869457254372531991 20737826804185881558797987)
                  ·
                    refine ⟨31106740206278822338196981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20737826804185881558797987 31106740206278822338196981)
                    ·
                      refine ⟨2916256894338639594205967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31106740206278822338196981 2916256894338639594205967)
                      ·
                        rfl

theorem cell23_5679390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5679390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679390 prefixEnd_5679390 := by exact prefixLift 5679390
  have htrace : WordTrace (prefixWord ++ tailWord_5679390) baseStart_5679390 baseEnd_5679390 := by
    simpa [prefixWord, tailWord_5679390, baseEnd_5679390] using wordTrace_append hprefix tailTrace_5679390
  have hstable : (prefixWord ++ tailWord_5679390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679390).length < 2 ^ (prefixWord ++ tailWord_5679390).sum := by decide
  have hdescent : baseEnd_5679390 < baseStart_5679390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679420 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_5679420 : Nat := 118140960795 + 5679420 * 2 ^ 59
def prefixEnd_5679420 : Nat := 4983230072969 + 3 ^ 40 * 5679420 * 2
def baseEnd_5679420 : Nat := 2916272298758274476830829

theorem tailTrace_5679420 : CollatzResearch.WordTrace tailWord_5679420 prefixEnd_5679420 2916272298758274476830829 := by
  unfold tailWord_5679420
  simp only [CollatzResearch.WordTrace]
  refine ⟨103572732542219391279017857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138096976722959188372023809 103572732542219391279017857)
  ·
    refine ⟨77679549406664543459263393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103572732542219391279017857 77679549406664543459263393)
    ·
      refine ⟨58259662054998407594447545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77679549406664543459263393 58259662054998407594447545)
      ·
        refine ⟨43694746541248805695835659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58259662054998407594447545 43694746541248805695835659)
        ·
          refine ⟨65542119811873208543753489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43694746541248805695835659 65542119811873208543753489)
          ·
            refine ⟨49156589858904906407815117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65542119811873208543753489 49156589858904906407815117)
            ·
              refine ⟨18433721197089339902930669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49156589858904906407815117 18433721197089339902930669)
              ·
                refine ⟨6912645448908502463599001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18433721197089339902930669 6912645448908502463599001)
                ·
                  refine ⟨5184484086681376847699251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6912645448908502463599001 5184484086681376847699251)
                  ·
                    refine ⟨7776726130022065271548877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184484086681376847699251 7776726130022065271548877)
                    ·
                      refine ⟨2916272298758274476830829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776726130022065271548877 2916272298758274476830829)
                      ·
                        rfl

theorem cell23_5679420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_5679420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679420 prefixEnd_5679420 := by exact prefixLift 5679420
  have htrace : WordTrace (prefixWord ++ tailWord_5679420) baseStart_5679420 baseEnd_5679420 := by
    simpa [prefixWord, tailWord_5679420, baseEnd_5679420] using wordTrace_append hprefix tailTrace_5679420
  have hstable : (prefixWord ++ tailWord_5679420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679420).length < 2 ^ (prefixWord ++ tailWord_5679420).sum := by decide
  have hdescent : baseEnd_5679420 < baseStart_5679420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679447 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 1, 3, 2]
def baseStart_5679447 : Nat := 118140960795 + 5679447 * 2 ^ 59
def prefixEnd_5679447 : Nat := 4983230072969 + 3 ^ 40 * 5679447 * 2
def baseEnd_5679447 : Nat := 2916286162735945871193205

theorem tailTrace_5679447 : CollatzResearch.WordTrace tailWord_5679447 prefixEnd_5679447 2916286162735945871193205 := by
  unfold tailWord_5679447
  simp only [CollatzResearch.WordTrace]
  refine ⟨207146449855340966169268595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138097633236893977446179063 207146449855340966169268595)
  ·
    refine ⟨310719674783011449253902893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207146449855340966169268595 310719674783011449253902893)
    ·
      refine ⟨116519878043629293470213585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310719674783011449253902893 116519878043629293470213585)
      ·
        refine ⟨87389908532721970102660189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116519878043629293470213585 87389908532721970102660189)
        ·
          refine ⟨32771215699770738788497571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87389908532721970102660189 32771215699770738788497571)
          ·
            refine ⟨49156823549656108182746357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32771215699770738788497571 49156823549656108182746357)
            ·
              refine ⟨4608452207780260142132471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49156823549656108182746357 4608452207780260142132471)
              ·
                refine ⟨6912678311670390213198707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608452207780260142132471 6912678311670390213198707)
                ·
                  refine ⟨10369017467505585319798061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912678311670390213198707 10369017467505585319798061)
                  ·
                    refine ⟨3888381550314594494924273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10369017467505585319798061 3888381550314594494924273)
                    ·
                      refine ⟨2916286162735945871193205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888381550314594494924273 2916286162735945871193205)
                      ·
                        rfl

theorem cell23_5679447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_5679447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679447 prefixEnd_5679447 := by exact prefixLift 5679447
  have htrace : WordTrace (prefixWord ++ tailWord_5679447) baseStart_5679447 baseEnd_5679447 := by
    simpa [prefixWord, tailWord_5679447, baseEnd_5679447] using wordTrace_append hprefix tailTrace_5679447
  have hstable : (prefixWord ++ tailWord_5679447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679447).length < 2 ^ (prefixWord ++ tailWord_5679447).sum := by decide
  have hdescent : baseEnd_5679447 < baseStart_5679447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679463 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3]
def baseStart_5679463 : Nat := 118140960795 + 5679463 * 2 ^ 59
def prefixEnd_5679463 : Nat := 4983230072969 + 3 ^ 40 * 5679463 * 2
def baseEnd_5679463 : Nat := 2916294378426417808593131

theorem tailTrace_5679463 : CollatzResearch.WordTrace tailWord_5679463 prefixEnd_5679463 2916294378426417808593131 := by
  unfold tailWord_5679463
  simp only [CollatzResearch.WordTrace]
  refine ⟨207147033423283000901851043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138098022282188667267900695 207147033423283000901851043)
  ·
    refine ⟨310720550134924501352776565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207147033423283000901851043 310720550134924501352776565)
    ·
      refine ⟨29130051575149172001822803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310720550134924501352776565 29130051575149172001822803)
      ·
        refine ⟨43695077362723758002734205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29130051575149172001822803 43695077362723758002734205)
        ·
          refine ⟨16385654011021409251025327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43695077362723758002734205 16385654011021409251025327)
          ·
            refine ⟨24578481016532113876537991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16385654011021409251025327 24578481016532113876537991)
            ·
              refine ⟨36867721524798170814806987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24578481016532113876537991 36867721524798170814806987)
              ·
                refine ⟨55301582287197256222210481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36867721524798170814806987 55301582287197256222210481)
                ·
                  refine ⟨41476186715397942166657861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55301582287197256222210481 41476186715397942166657861)
                  ·
                    refine ⟨7776785009137114156248349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41476186715397942166657861 7776785009137114156248349)
                    ·
                      refine ⟨2916294378426417808593131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776785009137114156248349 2916294378426417808593131)
                      ·
                        rfl

theorem cell23_5679463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_5679463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679463 prefixEnd_5679463 := by exact prefixLift 5679463
  have htrace : WordTrace (prefixWord ++ tailWord_5679463) baseStart_5679463 baseEnd_5679463 := by
    simpa [prefixWord, tailWord_5679463, baseEnd_5679463] using wordTrace_append hprefix tailTrace_5679463
  have hstable : (prefixWord ++ tailWord_5679463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679463).length < 2 ^ (prefixWord ++ tailWord_5679463).sum := by decide
  have hdescent : baseEnd_5679463 < baseStart_5679463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679477 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5679477 : Nat := 118140960795 + 5679477 * 2 ^ 59
def prefixEnd_5679477 : Nat := 4983230072969 + 3 ^ 40 * 5679477 * 2
def baseEnd_5679477 : Nat := 2916301567155580753818067

theorem tailTrace_5679477 : CollatzResearch.WordTrace tailWord_5679477 prefixEnd_5679477 2916301567155580753818067 := by
  unfold tailWord_5679477
  simp only [CollatzResearch.WordTrace]
  refine ⟨207147544045232281292860685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138098362696821520861907123 207147544045232281292860685)
  ·
    refine ⟨77680329016962105484822757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207147544045232281292860685 77680329016962105484822757)
    ·
      refine ⟨14565061690680394778404267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77680329016962105484822757 14565061690680394778404267)
      ·
        refine ⟨21847592536020592167606401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14565061690680394778404267 21847592536020592167606401)
        ·
          refine ⟨16385694402015444125704801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21847592536020592167606401 16385694402015444125704801)
          ·
            refine ⟨12289270801511583094278601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385694402015444125704801 12289270801511583094278601)
            ·
              refine ⟨9216953101133687320708951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12289270801511583094278601 9216953101133687320708951)
              ·
                refine ⟨13825429651700530981063427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9216953101133687320708951 13825429651700530981063427)
                ·
                  refine ⟨20738144477550796471595141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13825429651700530981063427 20738144477550796471595141)
                  ·
                    refine ⟨3888402089540774338424089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20738144477550796471595141 3888402089540774338424089)
                    ·
                      refine ⟨2916301567155580753818067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888402089540774338424089 2916301567155580753818067)
                      ·
                        rfl

theorem cell23_5679477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5679477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679477 prefixEnd_5679477 := by exact prefixLift 5679477
  have htrace : WordTrace (prefixWord ++ tailWord_5679477) baseStart_5679477 baseEnd_5679477 := by
    simpa [prefixWord, tailWord_5679477, baseEnd_5679477] using wordTrace_append hprefix tailTrace_5679477
  have hstable : (prefixWord ++ tailWord_5679477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679477).length < 2 ^ (prefixWord ++ tailWord_5679477).sum := by decide
  have hdescent : baseEnd_5679477 < baseStart_5679477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679498 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_5679498 : Nat := 118140960795 + 5679498 * 2 ^ 59
def prefixEnd_5679498 : Nat := 4983230072969 + 3 ^ 40 * 5679498 * 2
def baseEnd_5679498 : Nat := 2916312350249325171655471

theorem tailTrace_5679498 : CollatzResearch.WordTrace tailWord_5679498 prefixEnd_5679498 2916312350249325171655471 := by
  unfold tailWord_5679498
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787077494539050469843787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138098873318770801252916765 51787077494539050469843787)
  ·
    refine ⟨77680616241808575704765681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51787077494539050469843787 77680616241808575704765681)
    ·
      refine ⟨58260462181356431778574261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77680616241808575704765681 58260462181356431778574261)
      ·
        refine ⟨5461918329502165479241337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58260462181356431778574261 5461918329502165479241337)
        ·
          refine ⟨4096438747126624109431003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5461918329502165479241337 4096438747126624109431003)
          ·
            refine ⟨6144658120689936164146505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096438747126624109431003 6144658120689936164146505)
            ·
              refine ⟨4608493590517452123109879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144658120689936164146505 4608493590517452123109879)
              ·
                refine ⟨6912740385776178184664819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608493590517452123109879 6912740385776178184664819)
                ·
                  refine ⟨10369110578664267276997229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912740385776178184664819 10369110578664267276997229)
                  ·
                    refine ⟨3888416466999100228873961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10369110578664267276997229 3888416466999100228873961)
                    ·
                      refine ⟨2916312350249325171655471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888416466999100228873961 2916312350249325171655471)
                      ·
                        rfl

theorem cell23_5679498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_5679498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679498 prefixEnd_5679498 := by exact prefixLift 5679498
  have htrace : WordTrace (prefixWord ++ tailWord_5679498) baseStart_5679498 baseEnd_5679498 := by
    simpa [prefixWord, tailWord_5679498, baseEnd_5679498] using wordTrace_append hprefix tailTrace_5679498
  have hstable : (prefixWord ++ tailWord_5679498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679498).length < 2 ^ (prefixWord ++ tailWord_5679498).sum := by decide
  have hdescent : baseEnd_5679498 < baseStart_5679498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679500 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 5]
def baseStart_5679500 : Nat := 118140960795 + 5679500 * 2 ^ 59
def prefixEnd_5679500 : Nat := 4983230072969 + 3 ^ 40 * 5679500 * 2
def baseEnd_5679500 : Nat := 324034819690070462647829

theorem tailTrace_5679500 : CollatzResearch.WordTrace tailWord_5679500 prefixEnd_5679500 324034819690070462647829 := by
  unfold tailWord_5679500
  simp only [CollatzResearch.WordTrace]
  refine ⟨103574191462074478110473977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138098921949432637480631969 103574191462074478110473977)
  ·
    refine ⟨77680643596555858582855483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103574191462074478110473977 77680643596555858582855483)
    ·
      refine ⟨116520965394833787874283225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77680643596555858582855483 116520965394833787874283225)
      ·
        refine ⟨87390724046125340905712419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116520965394833787874283225 87390724046125340905712419)
        ·
          refine ⟨131086086069188011358568629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87390724046125340905712419 131086086069188011358568629)
          ·
            refine ⟨12289320568986376064865809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131086086069188011358568629 12289320568986376064865809)
            ·
              refine ⟨9216990426739782048649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12289320568986376064865809 9216990426739782048649357)
              ·
                refine ⟨3456371410027418268243509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9216990426739782048649357 3456371410027418268243509)
                ·
                  refine ⟨324034819690070462647829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456371410027418268243509 324034819690070462647829)
                  ·
                    rfl

theorem cell23_5679500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 5].length) (baseStart_5679500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679500 prefixEnd_5679500 := by exact prefixLift 5679500
  have htrace : WordTrace (prefixWord ++ tailWord_5679500) baseStart_5679500 baseEnd_5679500 := by
    simpa [prefixWord, tailWord_5679500, baseEnd_5679500] using wordTrace_append hprefix tailTrace_5679500
  have hstable : (prefixWord ++ tailWord_5679500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679500).length < 2 ^ (prefixWord ++ tailWord_5679500).sum := by decide
  have hdescent : baseEnd_5679500 < baseStart_5679500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679536 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_5679536 : Nat := 118140960795 + 5679536 * 2 ^ 59
def prefixEnd_5679536 : Nat := 4983230072969 + 3 ^ 40 * 5679536 * 2
def baseEnd_5679536 : Nat := 2916331862514196022980295

theorem tailTrace_5679536 : CollatzResearch.WordTrace tailWord_5679536 prefixEnd_5679536 2916331862514196022980295 := by
  unfold tailWord_5679536
  simp only [CollatzResearch.WordTrace]
  refine ⟨103574847976009267184629231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138099797301345689579505641 103574847976009267184629231)
  ·
    refine ⟨155362271964013900776943847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103574847976009267184629231 155362271964013900776943847)
    ·
      refine ⟨233043407946020851165415771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155362271964013900776943847 233043407946020851165415771)
      ·
        refine ⟨349565111919031276748123657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233043407946020851165415771 349565111919031276748123657)
        ·
          refine ⟨262173833939273457561092743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349565111919031276748123657 262173833939273457561092743)
          ·
            refine ⟨393260750908910186341639115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262173833939273457561092743 393260750908910186341639115)
            ·
              refine ⟨589891126363365279512458673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393260750908910186341639115 589891126363365279512458673)
              ·
                refine ⟨442418344772523959634344005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589891126363365279512458673 442418344772523959634344005)
                ·
                  refine ⟨82953439644848242431439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442418344772523959634344005 82953439644848242431439501)
                  ·
                    refine ⟨31107539866818090911789813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82953439644848242431439501 31107539866818090911789813)
                    ·
                      refine ⟨2916331862514196022980295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31107539866818090911789813 2916331862514196022980295)
                      ·
                        rfl

theorem cell23_5679536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_5679536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679536 prefixEnd_5679536 := by exact prefixLift 5679536
  have htrace : WordTrace (prefixWord ++ tailWord_5679536) baseStart_5679536 baseEnd_5679536 := by
    simpa [prefixWord, tailWord_5679536, baseEnd_5679536] using wordTrace_append hprefix tailTrace_5679536
  have hstable : (prefixWord ++ tailWord_5679536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679536).length < 2 ^ (prefixWord ++ tailWord_5679536).sum := by decide
  have hdescent : baseEnd_5679536 < baseStart_5679536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679550 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_5679550 : Nat := 118140960795 + 5679550 * 2 ^ 59
def prefixEnd_5679550 : Nat := 4983230072969 + 3 ^ 40 * 5679550 * 2
def baseEnd_5679550 : Nat := 2916339051243358968205231

theorem tailTrace_5679550 : CollatzResearch.WordTrace tailWord_5679550 prefixEnd_5679550 2916339051243358968205231 := by
  unfold tailWord_5679550
  simp only [CollatzResearch.WordTrace]
  refine ⟨25893775821745976845033513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138100137715978543173512069 25893775821745976845033513)
  ·
    refine ⟨19420331866309482633775135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25893775821745976845033513 19420331866309482633775135)
    ·
      refine ⟨29130497799464223950662703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19420331866309482633775135 29130497799464223950662703)
      ·
        refine ⟨43695746699196335925994055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29130497799464223950662703 43695746699196335925994055)
        ·
          refine ⟨65543620048794503888991083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43695746699196335925994055 65543620048794503888991083)
          ·
            refine ⟨98315430073191755833486625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65543620048794503888991083 98315430073191755833486625)
            ·
              refine ⟨73736572554893816875114969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98315430073191755833486625 73736572554893816875114969)
              ·
                refine ⟨55302429416170362656336227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73736572554893816875114969 55302429416170362656336227)
                ·
                  refine ⟨82953644124255543984504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55302429416170362656336227 82953644124255543984504341)
                  ·
                    refine ⟨3888452068324478624273641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82953644124255543984504341 3888452068324478624273641)
                    ·
                      refine ⟨2916339051243358968205231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888452068324478624273641 2916339051243358968205231)
                      ·
                        rfl

theorem cell23_5679550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_5679550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679550 prefixEnd_5679550 := by exact prefixLift 5679550
  have htrace : WordTrace (prefixWord ++ tailWord_5679550) baseStart_5679550 baseEnd_5679550 := by
    simpa [prefixWord, tailWord_5679550, baseEnd_5679550] using wordTrace_append hprefix tailTrace_5679550
  have hstable : (prefixWord ++ tailWord_5679550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679550).length < 2 ^ (prefixWord ++ tailWord_5679550).sum := by decide
  have hdescent : baseEnd_5679550 < baseStart_5679550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679573 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 8]
def baseStart_5679573 : Nat := 118140960795 + 5679573 * 2 ^ 59
def prefixEnd_5679573 : Nat := 4983230072969 + 3 ^ 40 * 5679573 * 2
def baseEnd_5679573 : Nat := 324038984588712486468625

theorem tailTrace_5679573 : CollatzResearch.WordTrace tailWord_5679573 prefixEnd_5679573 324038984588712486468625 := by
  unfold tailWord_5679573
  simp only [CollatzResearch.WordTrace]
  refine ⟨207151045452884489688355373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138100696968589659792236915 207151045452884489688355373)
  ·
    refine ⟨77681642044831683633133265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207151045452884489688355373 77681642044831683633133265)
    ·
      refine ⟨58261231533623762724849949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77681642044831683633133265 58261231533623762724849949)
      ·
        refine ⟨21847961825108911021818731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58261231533623762724849949 21847961825108911021818731)
        ·
          refine ⟨32771942737663366532728097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21847961825108911021818731 32771942737663366532728097)
          ·
            refine ⟨24578957053247524899546073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32771942737663366532728097 24578957053247524899546073)
            ·
              refine ⟨18434217789935643674659555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24578957053247524899546073 18434217789935643674659555)
              ·
                refine ⟨27651326684903465511989333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18434217789935643674659555 27651326684903465511989333)
                ·
                  refine ⟨324038984588712486468625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27651326684903465511989333 324038984588712486468625)
                  ·
                    rfl

theorem cell23_5679573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 8].length) (baseStart_5679573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679573 prefixEnd_5679573 := by exact prefixLift 5679573
  have htrace : WordTrace (prefixWord ++ tailWord_5679573) baseStart_5679573 baseEnd_5679573 := by
    simpa [prefixWord, tailWord_5679573, baseEnd_5679573] using wordTrace_append hprefix tailTrace_5679573
  have hstable : (prefixWord ++ tailWord_5679573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679573).length < 2 ^ (prefixWord ++ tailWord_5679573).sum := by decide
  have hdescent : baseEnd_5679573 < baseStart_5679573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679600 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_5679600 : Nat := 118140960795 + 5679600 * 2 ^ 59
def prefixEnd_5679600 : Nat := 4983230072969 + 3 ^ 40 * 5679600 * 2
def baseEnd_5679600 : Nat := 2916364725276083772580001

theorem tailTrace_5679600 : CollatzResearch.WordTrace tailWord_5679600 prefixEnd_5679600 2916364725276083772580001 := by
  unfold tailWord_5679600
  simp only [CollatzResearch.WordTrace]
  refine ⟨103576015111893336649794127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138101353482524448866392169 103576015111893336649794127)
  ·
    refine ⟨155364022667840004974691191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103576015111893336649794127 155364022667840004974691191)
    ·
      refine ⟨233046034001760007462036787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155364022667840004974691191 233046034001760007462036787)
      ·
        refine ⟨349569051002640011193055181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233046034001760007462036787 349569051002640011193055181)
        ·
          refine ⟨131088394125990004197395693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349569051002640011193055181 131088394125990004197395693)
          ·
            refine ⟨49158147797246251574023385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131088394125990004197395693 49158147797246251574023385)
            ·
              refine ⟨36868610847934688680517539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49158147797246251574023385 36868610847934688680517539)
              ·
                refine ⟨55302916271902033020776309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36868610847934688680517539 55302916271902033020776309)
                ·
                  refine ⟨5184648400490815595697779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55302916271902033020776309 5184648400490815595697779)
                  ·
                    refine ⟨7776972600736223393546669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184648400490815595697779 7776972600736223393546669)
                    ·
                      refine ⟨2916364725276083772580001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7776972600736223393546669 2916364725276083772580001)
                      ·
                        rfl

theorem cell23_5679600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_5679600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679600 prefixEnd_5679600 := by exact prefixLift 5679600
  have htrace : WordTrace (prefixWord ++ tailWord_5679600) baseStart_5679600 baseEnd_5679600 := by
    simpa [prefixWord, tailWord_5679600, baseEnd_5679600] using wordTrace_append hprefix tailTrace_5679600
  have hstable : (prefixWord ++ tailWord_5679600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679600).length < 2 ^ (prefixWord ++ tailWord_5679600).sum := by decide
  have hdescent : baseEnd_5679600 < baseStart_5679600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679603 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 3, 5]
def baseStart_5679603 : Nat := 118140960795 + 5679603 * 2 ^ 59
def prefixEnd_5679603 : Nat := 4983230072969 + 3 ^ 40 * 5679603 * 2
def baseEnd_5679603 : Nat := 972122088572682420280829

theorem tailTrace_5679603 : CollatzResearch.WordTrace tailWord_5679603 prefixEnd_5679603 972122088572682420280829 := by
  unfold tailWord_5679603
  simp only [CollatzResearch.WordTrace]
  refine ⟨207152139642775804811947463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138101426428517203207964975 207152139642775804811947463)
  ·
    refine ⟨310728209464163707217921195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207152139642775804811947463 310728209464163707217921195)
    ·
      refine ⟨466092314196245560826881793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310728209464163707217921195 466092314196245560826881793)
      ·
        refine ⟨349569235647184170620161345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466092314196245560826881793 349569235647184170620161345)
        ·
          refine ⟨262176926735388127965121009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349569235647184170620161345 262176926735388127965121009)
          ·
            refine ⟨196632695051541095973840757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262176926735388127965121009 196632695051541095973840757)
            ·
              refine ⟨18434315161081977747547571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196632695051541095973840757 18434315161081977747547571)
              ·
                refine ⟨27651472741622966621321357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18434315161081977747547571 27651472741622966621321357)
                ·
                  refine ⟨10369302278108612482995509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27651472741622966621321357 10369302278108612482995509)
                  ·
                    refine ⟨972122088572682420280829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10369302278108612482995509 972122088572682420280829)
                    ·
                      rfl

theorem cell23_5679603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 5].length) (baseStart_5679603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679603 prefixEnd_5679603 := by exact prefixLift 5679603
  have htrace : WordTrace (prefixWord ++ tailWord_5679603) baseStart_5679603 baseEnd_5679603 := by
    simpa [prefixWord, tailWord_5679603, baseEnd_5679603] using wordTrace_append hprefix tailTrace_5679603
  have hstable : (prefixWord ++ tailWord_5679603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679603).length < 2 ^ (prefixWord ++ tailWord_5679603).sum := by decide
  have hdescent : baseEnd_5679603 < baseStart_5679603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679627 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 2, 3, 2]
def baseStart_5679627 : Nat := 118140960795 + 5679627 * 2 ^ 59
def prefixEnd_5679627 : Nat := 4983230072969 + 3 ^ 40 * 5679627 * 2
def baseEnd_5679627 : Nat := 2916378589253755166942377

theorem tailTrace_5679627 : CollatzResearch.WordTrace tailWord_5679627 prefixEnd_5679627 2916378589253755166942377 := by
  unfold tailWord_5679627
  simp only [CollatzResearch.WordTrace]
  refine ⟨207153014994688856910821135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138102009996459237940547423 207153014994688856910821135)
  ·
    refine ⟨310729522492033285366231703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207153014994688856910821135 310729522492033285366231703)
    ·
      refine ⟨466094283738049928049347555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310729522492033285366231703 466094283738049928049347555)
      ·
        refine ⟨699141425607074892074021333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466094283738049928049347555 699141425607074892074021333)
        ·
          refine ⟨16386127162665817782984875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 699141425607074892074021333 16386127162665817782984875)
          ·
            refine ⟨24579190743998726674477313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16386127162665817782984875 24579190743998726674477313)
            ·
              refine ⟨18434393057999045005857985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24579190743998726674477313 18434393057999045005857985)
              ·
                refine ⟨13825794793499283754393489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18434393057999045005857985 13825794793499283754393489)
                ·
                  refine ⟨10369346095124462815795117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13825794793499283754393489 10369346095124462815795117)
                  ·
                    refine ⟨3888504785671673555923169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10369346095124462815795117 3888504785671673555923169)
                    ·
                      refine ⟨2916378589253755166942377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888504785671673555923169 2916378589253755166942377)
                      ·
                        rfl

theorem cell23_5679627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 3, 2].length) (baseStart_5679627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679627 prefixEnd_5679627 := by exact prefixLift 5679627
  have htrace : WordTrace (prefixWord ++ tailWord_5679627) baseStart_5679627 baseEnd_5679627 := by
    simpa [prefixWord, tailWord_5679627, baseEnd_5679627] using wordTrace_append hprefix tailTrace_5679627
  have hstable : (prefixWord ++ tailWord_5679627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679627).length < 2 ^ (prefixWord ++ tailWord_5679627).sum := by decide
  have hdescent : baseEnd_5679627 < baseStart_5679627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679640 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_5679640 : Nat := 118140960795 + 5679640 * 2 ^ 59
def prefixEnd_5679640 : Nat := 4983230072969 + 3 ^ 40 * 5679640 * 2
def baseEnd_5679640 : Nat := 2916385264502263616079817

theorem tailTrace_5679640 : CollatzResearch.WordTrace tailWord_5679640 prefixEnd_5679640 2916385264502263616079817 := by
  unfold tailWord_5679640
  simp only [CollatzResearch.WordTrace]
  refine ⟨103576744571820880065522187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138102326095761173420696249 103576744571820880065522187)
  ·
    refine ⟨155365116857731320098283281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103576744571820880065522187 155365116857731320098283281)
    ·
      refine ⟨116523837643298490073712461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155365116857731320098283281 116523837643298490073712461)
      ·
        refine ⟨43696439116236933777642173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116523837643298490073712461 43696439116236933777642173)
        ·
          refine ⟨16386164668588850166615815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43696439116236933777642173 16386164668588850166615815)
          ·
            refine ⟨24579247002883275249923723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16386164668588850166615815 24579247002883275249923723)
            ·
              refine ⟨36868870504324912874885585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24579247002883275249923723 36868870504324912874885585)
              ·
                refine ⟨27651652878243684656164189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36868870504324912874885585 27651652878243684656164189)
                ·
                  refine ⟨10369369829341381746061571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27651652878243684656164189 10369369829341381746061571)
                  ·
                    refine ⟨15554054744012072619092357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10369369829341381746061571 15554054744012072619092357)
                    ·
                      refine ⟨2916385264502263616079817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15554054744012072619092357 2916385264502263616079817)
                      ·
                        rfl

theorem cell23_5679640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_5679640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679640 prefixEnd_5679640 := by exact prefixLift 5679640
  have htrace : WordTrace (prefixWord ++ tailWord_5679640) baseStart_5679640 baseEnd_5679640 := by
    simpa [prefixWord, tailWord_5679640, baseEnd_5679640] using wordTrace_append hprefix tailTrace_5679640
  have hstable : (prefixWord ++ tailWord_5679640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679640).length < 2 ^ (prefixWord ++ tailWord_5679640).sum := by decide
  have hdescent : baseEnd_5679640 < baseStart_5679640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679650 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 6, 4]
def baseStart_5679650 : Nat := 118140960795 + 5679650 * 2 ^ 59
def prefixEnd_5679650 : Nat := 4983230072969 + 3 ^ 40 * 5679650 * 2
def baseEnd_5679650 : Nat := 972130133102936192318257

theorem tailTrace_5679650 : CollatzResearch.WordTrace tailWord_5679650 prefixEnd_5679650 972130133102936192318257 := by
  unfold tailWord_5679650
  simp only [CollatzResearch.WordTrace]
  refine ⟨51788463468401382959727101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138102569249070354559272269 51788463468401382959727101)
  ·
    refine ⟨19420673800650518609897663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51788463468401382959727101 19420673800650518609897663)
    ·
      refine ⟨29131010700975777914846495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19420673800650518609897663 29131010700975777914846495)
      ·
        refine ⟨43696516051463666872269743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29131010700975777914846495 43696516051463666872269743)
        ·
          refine ⟨65544774077195500308404615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43696516051463666872269743 65544774077195500308404615)
          ·
            refine ⟨98317161115793250462606923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65544774077195500308404615 98317161115793250462606923)
            ·
              refine ⟨147475741673689875693910385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98317161115793250462606923 147475741673689875693910385)
              ·
                refine ⟨110606806255267406770432789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147475741673689875693910385 110606806255267406770432789)
                ·
                  refine ⟨5184694043215659692364037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110606806255267406770432789 5184694043215659692364037)
                  ·
                    refine ⟨972130133102936192318257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184694043215659692364037 972130133102936192318257)
                    ·
                      rfl

theorem cell23_5679650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_5679650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679650 prefixEnd_5679650 := by exact prefixLift 5679650
  have htrace : WordTrace (prefixWord ++ tailWord_5679650) baseStart_5679650 baseEnd_5679650 := by
    simpa [prefixWord, tailWord_5679650, baseEnd_5679650] using wordTrace_append hprefix tailTrace_5679650
  have hstable : (prefixWord ++ tailWord_5679650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679650).length < 2 ^ (prefixWord ++ tailWord_5679650).sum := by decide
  have hdescent : baseEnd_5679650 < baseStart_5679650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679653 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_5679653 : Nat := 118140960795 + 5679653 * 2 ^ 59
def prefixEnd_5679653 : Nat := 4983230072969 + 3 ^ 40 * 5679653 * 2
def baseEnd_5679653 : Nat := 2916391939750772065217257

theorem tailTrace_5679653 : CollatzResearch.WordTrace tailWord_5679653 prefixEnd_5679653 2916391939750772065217257 := by
  unfold tailWord_5679653
  simp only [CollatzResearch.WordTrace]
  refine ⟨207153963292594663351267613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138102642195063108900845075 207153963292594663351267613)
  ·
    refine ⟨77682736234722998756725355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207153963292594663351267613 77682736234722998756725355)
    ·
      refine ⟨116524104352084498135088033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77682736234722998756725355 116524104352084498135088033)
      ·
        refine ⟨87393078264063373601316025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116524104352084498135088033 87393078264063373601316025)
        ·
          refine ⟨65544808698047530200987019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87393078264063373601316025 65544808698047530200987019)
          ·
            refine ⟨98317213047071295301480529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65544808698047530200987019 98317213047071295301480529)
            ·
              refine ⟨73737909785303471476110397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98317213047071295301480529 73737909785303471476110397)
              ·
                refine ⟨27651716169488801803541399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73737909785303471476110397 27651716169488801803541399)
                ·
                  refine ⟨41477574254233202705312099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27651716169488801803541399 41477574254233202705312099)
                  ·
                    refine ⟨62216361381349804057968149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41477574254233202705312099 62216361381349804057968149)
                    ·
                      refine ⟨2916391939750772065217257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62216361381349804057968149 2916391939750772065217257)
                      ·
                        rfl

theorem cell23_5679653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_5679653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679653 prefixEnd_5679653 := by exact prefixLift 5679653
  have htrace : WordTrace (prefixWord ++ tailWord_5679653) baseStart_5679653 baseEnd_5679653 := by
    simpa [prefixWord, tailWord_5679653, baseEnd_5679653] using wordTrace_append hprefix tailTrace_5679653
  have hstable : (prefixWord ++ tailWord_5679653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679653).length < 2 ^ (prefixWord ++ tailWord_5679653).sum := by decide
  have hdescent : baseEnd_5679653 < baseStart_5679653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679674 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_5679674 : Nat := 118140960795 + 5679674 * 2 ^ 59
def prefixEnd_5679674 : Nat := 4983230072969 + 3 ^ 40 * 5679674 * 2
def baseEnd_5679674 : Nat := 2916402722844516483054661

theorem tailTrace_5679674 : CollatzResearch.WordTrace tailWord_5679674 prefixEnd_5679674 2916402722844516483054661 := by
  unfold tailWord_5679674
  simp only [CollatzResearch.WordTrace]
  refine ⟨51788682306379645984445519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138103152817012389291854717 51788682306379645984445519)
  ·
    refine ⟨77683023459569468976668279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51788682306379645984445519 77683023459569468976668279)
    ·
      refine ⟨116524535189354203465002419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77683023459569468976668279 116524535189354203465002419)
      ·
        refine ⟨174786802784031305197503629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116524535189354203465002419 174786802784031305197503629)
        ·
          refine ⟨65545051044011739449063861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174786802784031305197503629 65545051044011739449063861)
          ·
            refine ⟨6144848535376100573349737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65545051044011739449063861 6144848535376100573349737)
            ·
              refine ⟨4608636401532075430012303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144848535376100573349737 4608636401532075430012303)
              ·
                refine ⟨6912954602298113145018455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608636401532075430012303 6912954602298113145018455)
                ·
                  refine ⟨10369431903447169717527683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6912954602298113145018455 10369431903447169717527683)
                  ·
                    refine ⟨15554147855170754576291525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10369431903447169717527683 15554147855170754576291525)
                    ·
                      refine ⟨2916402722844516483054661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15554147855170754576291525 2916402722844516483054661)
                      ·
                        rfl

theorem cell23_5679674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_5679674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679674 prefixEnd_5679674 := by exact prefixLift 5679674
  have htrace : WordTrace (prefixWord ++ tailWord_5679674) baseStart_5679674 baseEnd_5679674 := by
    simpa [prefixWord, tailWord_5679674, baseEnd_5679674] using wordTrace_append hprefix tailTrace_5679674
  have hstable : (prefixWord ++ tailWord_5679674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679674).length < 2 ^ (prefixWord ++ tailWord_5679674).sum := by decide
  have hdescent : baseEnd_5679674 < baseStart_5679674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679723 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 6]
def baseStart_5679723 : Nat := 118140960795 + 5679723 * 2 ^ 59
def prefixEnd_5679723 : Nat := 4983230072969 + 3 ^ 40 * 5679723 * 2
def baseEnd_5679723 : Nat := 972142627798862263780645

theorem tailTrace_5679723 : CollatzResearch.WordTrace tailWord_5679723 prefixEnd_5679723 972142627798862263780645 := by
  unfold tailWord_5679723
  simp only [CollatzResearch.WordTrace]
  refine ⟨207156516402341065306315823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138104344268227376870877215 207156516402341065306315823)
  ·
    refine ⟨310734774603511597959473735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207156516402341065306315823 310734774603511597959473735)
    ·
      refine ⟨466102161905267396939210603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310734774603511597959473735 466102161905267396939210603)
      ·
        refine ⟨699153242857901095408815905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466102161905267396939210603 699153242857901095408815905)
        ·
          refine ⟨524364932143425821556611929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699153242857901095408815905 524364932143425821556611929)
          ·
            refine ⟨393273699107569366167458947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524364932143425821556611929 393273699107569366167458947)
            ·
              refine ⟨589910548661354049251188421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393273699107569366167458947 589910548661354049251188421)
              ·
                refine ⟨110608227874003884234597829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 589910548661354049251188421 110608227874003884234597829)
                ·
                  refine ⟨20739042726375728293987093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110608227874003884234597829 20739042726375728293987093)
                  ·
                    refine ⟨972142627798862263780645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20739042726375728293987093 972142627798862263780645)
                    ·
                      rfl

theorem cell23_5679723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_5679723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679723 prefixEnd_5679723 := by exact prefixLift 5679723
  have htrace : WordTrace (prefixWord ++ tailWord_5679723) baseStart_5679723 baseEnd_5679723 := by
    simpa [prefixWord, tailWord_5679723, baseEnd_5679723] using wordTrace_append hprefix tailTrace_5679723
  have hstable : (prefixWord ++ tailWord_5679723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679723).length < 2 ^ (prefixWord ++ tailWord_5679723).sum := by decide
  have hdescent : baseEnd_5679723 < baseStart_5679723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679743 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_5679743 : Nat := 118140960795 + 5679743 * 2 ^ 59
def prefixEnd_5679743 : Nat := 4983230072969 + 3 ^ 40 * 5679743 * 2
def baseEnd_5679743 : Nat := 2916438153009676713091843

theorem tailTrace_5679743 : CollatzResearch.WordTrace tailWord_5679743 prefixEnd_5679743 2916438153009676713091843 := by
  unfold tailWord_5679743
  simp only [CollatzResearch.WordTrace]
  refine ⟨207157245862268608722043883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138104830574845739148029255 207157245862268608722043883)
  ·
    refine ⟨310735868793402913083065825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207157245862268608722043883 310735868793402913083065825)
    ·
      refine ⟨233051901595052184812299369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310735868793402913083065825 233051901595052184812299369)
      ·
        refine ⟨174788926196289138609224527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233051901595052184812299369 174788926196289138609224527)
        ·
          refine ⟨262183389294433707913836791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174788926196289138609224527 262183389294433707913836791)
          ·
            refine ⟨393275083941650561870755187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262183389294433707913836791 393275083941650561870755187)
            ·
              refine ⟨589912625912475842806132781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393275083941650561870755187 589912625912475842806132781)
              ·
                refine ⟨221217234717178441052299793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589912625912475842806132781 221217234717178441052299793)
                ·
                  refine ⟨165912926037883830789224845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221217234717178441052299793 165912926037883830789224845)
                  ·
                    refine ⟨62217347264206436545959317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 165912926037883830789224845 62217347264206436545959317)
                    ·
                      refine ⟨2916438153009676713091843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62217347264206436545959317 2916438153009676713091843)
                      ·
                        rfl

theorem cell23_5679743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_5679743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679743 prefixEnd_5679743 := by exact prefixLift 5679743
  have htrace : WordTrace (prefixWord ++ tailWord_5679743) baseStart_5679743 baseEnd_5679743 := by
    simpa [prefixWord, tailWord_5679743, baseEnd_5679743] using wordTrace_append hprefix tailTrace_5679743
  have hstable : (prefixWord ++ tailWord_5679743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679743).length < 2 ^ (prefixWord ++ tailWord_5679743).sum := by decide
  have hdescent : baseEnd_5679743 < baseStart_5679743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679763 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_5679763 : Nat := 118140960795 + 5679763 * 2 ^ 59
def prefixEnd_5679763 : Nat := 4983230072969 + 3 ^ 40 * 5679763 * 2
def baseEnd_5679763 : Nat := 2916448422622766634841751

theorem tailTrace_5679763 : CollatzResearch.WordTrace tailWord_5679763 prefixEnd_5679763 2916448422622766634841751 := by
  unfold tailWord_5679763
  simp only [CollatzResearch.WordTrace]
  refine ⟨207157975322196152137771943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138105316881464101425181295 207157975322196152137771943)
  ·
    refine ⟨310736962983294228206657915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207157975322196152137771943 310736962983294228206657915)
    ·
      refine ⟨466105444474941342309986873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310736962983294228206657915 466105444474941342309986873)
      ·
        refine ⟨349579083356206006732490155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466105444474941342309986873 349579083356206006732490155)
        ·
          refine ⟨524368625034309010098735233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349579083356206006732490155 524368625034309010098735233)
          ·
            refine ⟨393276468775731757574051425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524368625034309010098735233 393276468775731757574051425)
            ·
              refine ⟨294957351581798818180538569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393276468775731757574051425 294957351581798818180538569)
              ·
                refine ⟨221218013686349113635403927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294957351581798818180538569 221218013686349113635403927)
                ·
                  refine ⟨331827020529523670453105891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221218013686349113635403927 331827020529523670453105891)
                  ·
                    refine ⟨497740530794285505679658837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 331827020529523670453105891 497740530794285505679658837)
                    ·
                      refine ⟨2916448422622766634841751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 497740530794285505679658837 2916448422622766634841751)
                      ·
                        rfl

theorem cell23_5679763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_5679763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679763 prefixEnd_5679763 := by exact prefixLift 5679763
  have htrace : WordTrace (prefixWord ++ tailWord_5679763) baseStart_5679763 baseEnd_5679763 := by
    simpa [prefixWord, tailWord_5679763, baseEnd_5679763] using wordTrace_append hprefix tailTrace_5679763
  have hstable : (prefixWord ++ tailWord_5679763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679763).length < 2 ^ (prefixWord ++ tailWord_5679763).sum := by decide
  have hdescent : baseEnd_5679763 < baseStart_5679763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679807 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 2, 5, 2]
def baseStart_5679807 : Nat := 118140960795 + 5679807 * 2 ^ 59
def prefixEnd_5679807 : Nat := 4983230072969 + 3 ^ 40 * 5679807 * 2
def baseEnd_5679807 : Nat := 2916471015771564462691549

theorem tailTrace_5679807 : CollatzResearch.WordTrace tailWord_5679807 prefixEnd_5679807 2916471015771564462691549 := by
  unfold tailWord_5679807
  simp only [CollatzResearch.WordTrace]
  refine ⟨207159580134036747652373675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138106386756024498434915783 207159580134036747652373675)
  ·
    refine ⟨310739370201055121478560513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207159580134036747652373675 310739370201055121478560513)
    ·
      refine ⟨233054527650791341108920385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310739370201055121478560513 233054527650791341108920385)
      ·
        refine ⟨174790895738093505831690289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233054527650791341108920385 174790895738093505831690289)
        ·
          refine ⟨131093171803570129373767717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174790895738093505831690289 131093171803570129373767717)
          ·
            refine ⟨24579969713169399257581447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131093171803570129373767717 24579969713169399257581447)
            ·
              refine ⟨36869954569754098886372171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24579969713169399257581447 36869954569754098886372171)
              ·
                refine ⟨55304931854631148329558257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36869954569754098886372171 55304931854631148329558257)
                ·
                  refine ⟨41478698890973361247168693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55304931854631148329558257 41478698890973361247168693)
                  ·
                    refine ⟨3888628021028752616922065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41478698890973361247168693 3888628021028752616922065)
                    ·
                      refine ⟨2916471015771564462691549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888628021028752616922065 2916471015771564462691549)
                      ·
                        rfl

theorem cell23_5679807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_5679807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679807 prefixEnd_5679807 := by exact prefixLift 5679807
  have htrace : WordTrace (prefixWord ++ tailWord_5679807) baseStart_5679807 baseEnd_5679807 := by
    simpa [prefixWord, tailWord_5679807, baseEnd_5679807] using wordTrace_append hprefix tailTrace_5679807
  have hstable : (prefixWord ++ tailWord_5679807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679807).length < 2 ^ (prefixWord ++ tailWord_5679807).sum := by decide
  have hdescent : baseEnd_5679807 < baseStart_5679807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679854 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2]
def baseStart_5679854 : Nat := 118140960795 + 5679854 * 2 ^ 59
def prefixEnd_5679854 : Nat := 4983230072969 + 3 ^ 40 * 5679854 * 2
def baseEnd_5679854 : Nat := 2916495149362325778803833

theorem tailTrace_5679854 : CollatzResearch.WordTrace tailWord_5679854 prefixEnd_5679854 2916495149362325778803833 := by
  unfold tailWord_5679854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25895161795608309334916827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138107529576577649786223077 25895161795608309334916827)
  ·
    refine ⟨38842742693412464002375241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25895161795608309334916827 38842742693412464002375241)
    ·
      refine ⟨29132057020059348001781431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38842742693412464002375241 29132057020059348001781431)
      ·
        refine ⟨43698085530089022002672147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29132057020059348001781431 43698085530089022002672147)
        ·
          refine ⟨65547128295133533004008221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43698085530089022002672147 65547128295133533004008221)
          ·
            refine ⟨24580173110675074876503083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65547128295133533004008221 24580173110675074876503083)
            ·
              refine ⟨36870259666012612314754625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24580173110675074876503083 36870259666012612314754625)
              ·
                refine ⟨27652694749509459236065969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36870259666012612314754625 27652694749509459236065969)
                ·
                  refine ⟨20739521062132094427049477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27652694749509459236065969 20739521062132094427049477)
                  ·
                    refine ⟨3888660199149767705071777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20739521062132094427049477 3888660199149767705071777)
                    ·
                      refine ⟨2916495149362325778803833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888660199149767705071777 2916495149362325778803833)
                      ·
                        rfl

theorem cell23_5679854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_5679854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679854 prefixEnd_5679854 := by exact prefixLift 5679854
  have htrace : WordTrace (prefixWord ++ tailWord_5679854) baseStart_5679854 baseEnd_5679854 := by
    simpa [prefixWord, tailWord_5679854, baseEnd_5679854] using wordTrace_append hprefix tailTrace_5679854
  have hstable : (prefixWord ++ tailWord_5679854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679854).length < 2 ^ (prefixWord ++ tailWord_5679854).sum := by decide
  have hdescent : baseEnd_5679854 < baseStart_5679854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679857 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 3]
def baseStart_5679857 : Nat := 118140960795 + 5679857 * 2 ^ 59
def prefixEnd_5679857 : Nat := 4983230072969 + 3 ^ 40 * 5679857 * 2
def baseEnd_5679857 : Nat := 2916496689804289267066319

theorem tailTrace_5679857 : CollatzResearch.WordTrace tailWord_5679857 prefixEnd_5679857 2916496689804289267066319 := by
  unfold tailWord_5679857
  simp only [CollatzResearch.WordTrace]
  refine ⟨207161403783855606191693825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138107602522570404127795883 207161403783855606191693825)
  ·
    refine ⟨155371052837891704643770369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207161403783855606191693825 155371052837891704643770369)
    ·
      refine ⟨116528289628418778482827777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155371052837891704643770369 116528289628418778482827777)
      ·
        refine ⟨87396217221314083862120833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116528289628418778482827777 87396217221314083862120833)
        ·
          refine ⟨65547162915985562896590625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87396217221314083862120833 65547162915985562896590625)
          ·
            refine ⟨49160372186989172172442969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65547162915985562896590625 49160372186989172172442969)
            ·
              refine ⟨36870279140241879129332227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49160372186989172172442969 36870279140241879129332227)
              ·
                refine ⟨55305418710362818693998341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36870279140241879129332227 55305418710362818693998341)
                ·
                  refine ⟨10369766008193028505124689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55305418710362818693998341 10369766008193028505124689)
                  ·
                    refine ⟨7777324506144771378843517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10369766008193028505124689 7777324506144771378843517)
                    ·
                      refine ⟨2916496689804289267066319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777324506144771378843517 2916496689804289267066319)
                      ·
                        rfl

theorem cell23_5679857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_5679857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679857 prefixEnd_5679857 := by exact prefixLift 5679857
  have htrace : WordTrace (prefixWord ++ tailWord_5679857) baseStart_5679857 baseEnd_5679857 := by
    simpa [prefixWord, tailWord_5679857, baseEnd_5679857] using wordTrace_append hprefix tailTrace_5679857
  have hstable : (prefixWord ++ tailWord_5679857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679857).length < 2 ^ (prefixWord ++ tailWord_5679857).sum := by decide
  have hdescent : baseEnd_5679857 < baseStart_5679857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679864 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 1, 4]
def baseStart_5679864 : Nat := 118140960795 + 5679864 * 2 ^ 59
def prefixEnd_5679864 : Nat := 4983230072969 + 3 ^ 40 * 5679864 * 2
def baseEnd_5679864 : Nat := 972166761389623579892929

theorem tailTrace_5679864 : CollatzResearch.WordTrace tailWord_5679864 prefixEnd_5679864 972166761389623579892929 := by
  unfold tailWord_5679864
  simp only [CollatzResearch.WordTrace]
  refine ⟨103580829547415123193599323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138107772729886830924799097 103580829547415123193599323)
  ·
    refine ⟨155371244321122684790398985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103580829547415123193599323 155371244321122684790398985)
    ·
      refine ⟨116528433240842013592799239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155371244321122684790398985 116528433240842013592799239)
      ·
        refine ⟨174792649861263020389198859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116528433240842013592799239 174792649861263020389198859)
        ·
          refine ⟨262188974791894530583798289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174792649861263020389198859 262188974791894530583798289)
          ·
            refine ⟨196641731093920897937848717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262188974791894530583798289 196641731093920897937848717)
            ·
              refine ⟨73740649160220336726693269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196641731093920897937848717 73740649160220336726693269)
              ·
                refine ⟨3456592929385328284063747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73740649160220336726693269 3456592929385328284063747)
                ·
                  refine ⟨5184889394077992426095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456592929385328284063747 5184889394077992426095621)
                  ·
                    refine ⟨972166761389623579892929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184889394077992426095621 972166761389623579892929)
                    ·
                      rfl

theorem cell23_5679864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 4].length) (baseStart_5679864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679864 prefixEnd_5679864 := by exact prefixLift 5679864
  have htrace : WordTrace (prefixWord ++ tailWord_5679864) baseStart_5679864 baseEnd_5679864 := by
    simpa [prefixWord, tailWord_5679864, baseEnd_5679864] using wordTrace_append hprefix tailTrace_5679864
  have hstable : (prefixWord ++ tailWord_5679864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679864).length < 2 ^ (prefixWord ++ tailWord_5679864).sum := by decide
  have hdescent : baseEnd_5679864 < baseStart_5679864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679874 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 1, 4, 3]
def baseStart_5679874 : Nat := 118140960795 + 5679874 * 2 ^ 59
def prefixEnd_5679874 : Nat := 4983230072969 + 3 ^ 40 * 5679874 * 2
def baseEnd_5679874 : Nat := 2916505418975415700553741

theorem tailTrace_5679874 : CollatzResearch.WordTrace tailWord_5679874 prefixEnd_5679874 2916505418975415700553741 := by
  unfold tailWord_5679874
  simp only [CollatzResearch.WordTrace]
  refine ⟨51790505956198504523765669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138108015883196012063375117 51790505956198504523765669)
  ·
    refine ⟨9710719866787219598206063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51790505956198504523765669 9710719866787219598206063)
    ·
      refine ⟨14566079800180829397309095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9710719866787219598206063 14566079800180829397309095)
      ·
        refine ⟨21849119700271244095963643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566079800180829397309095 21849119700271244095963643)
        ·
          refine ⟨32773679550406866143945465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21849119700271244095963643 32773679550406866143945465)
          ·
            refine ⟨24580259662805149607959099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32773679550406866143945465 24580259662805149607959099)
            ·
              refine ⟨36870389494207724411938649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24580259662805149607959099 36870389494207724411938649)
              ·
                refine ⟨27652792120655793308953987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36870389494207724411938649 27652792120655793308953987)
                ·
                  refine ⟨41479188180983689963430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27652792120655793308953987 41479188180983689963430981)
                  ·
                    refine ⟨7777347783934441868143309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41479188180983689963430981 7777347783934441868143309)
                    ·
                      refine ⟨2916505418975415700553741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777347783934441868143309 2916505418975415700553741)
                      ·
                        rfl

theorem cell23_5679874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_5679874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679874 prefixEnd_5679874 := by exact prefixLift 5679874
  have htrace : WordTrace (prefixWord ++ tailWord_5679874) baseStart_5679874 baseEnd_5679874 := by
    simpa [prefixWord, tailWord_5679874, baseEnd_5679874] using wordTrace_append hprefix tailTrace_5679874
  have hstable : (prefixWord ++ tailWord_5679874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679874).length < 2 ^ (prefixWord ++ tailWord_5679874).sum := by decide
  have hdescent : baseEnd_5679874 < baseStart_5679874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679927 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4]
def baseStart_5679927 : Nat := 118140960795 + 5679927 * 2 ^ 59
def prefixEnd_5679927 : Nat := 4983230072969 + 3 ^ 40 * 5679927 * 2
def baseEnd_5679927 : Nat := 2916532633450103993190997

theorem tailTrace_5679927 : CollatzResearch.WordTrace tailWord_5679927 prefixEnd_5679927 2916532633450103993190997 := by
  unfold tailWord_5679927
  simp only [CollatzResearch.WordTrace]
  refine ⟨207163956893602008146742035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138109304595734672097828023 207163956893602008146742035)
  ·
    refine ⟨310745935340403012220113053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207163956893602008146742035 310745935340403012220113053)
    ·
      refine ⟨116529725752651129582542395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310745935340403012220113053 116529725752651129582542395)
      ·
        refine ⟨174794588628976694373813593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116529725752651129582542395 174794588628976694373813593)
        ·
          refine ⟨131095941471732520780360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174794588628976694373813593 131095941471732520780360195)
          ·
            refine ⟨196643912207598781170540293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131095941471732520780360195 196643912207598781170540293)
            ·
              refine ⟨36870733538924771469476305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196643912207598781170540293 36870733538924771469476305)
              ·
                refine ⟨27653050154193578602107229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36870733538924771469476305 27653050154193578602107229)
                ·
                  refine ⟨10369893807822591975790211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27653050154193578602107229 10369893807822591975790211)
                  ·
                    refine ⟨15554840711733887963685317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10369893807822591975790211 15554840711733887963685317)
                    ·
                      refine ⟨2916532633450103993190997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15554840711733887963685317 2916532633450103993190997)
                      ·
                        rfl

theorem cell23_5679927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_5679927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679927 prefixEnd_5679927 := by exact prefixLift 5679927
  have htrace : WordTrace (prefixWord ++ tailWord_5679927) baseStart_5679927 baseEnd_5679927 := by
    simpa [prefixWord, tailWord_5679927, baseEnd_5679927] using wordTrace_append hprefix tailTrace_5679927
  have hstable : (prefixWord ++ tailWord_5679927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679927).length < 2 ^ (prefixWord ++ tailWord_5679927).sum := by decide
  have hdescent : baseEnd_5679927 < baseStart_5679927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679961 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 1, 1, 4]
def baseStart_5679961 : Nat := 118140960795 + 5679961 * 2 ^ 59
def prefixEnd_5679961 : Nat := 4983230072969 + 3 ^ 40 * 5679961 * 2
def baseEnd_5679961 : Nat := 2916550091792356860165841

theorem tailTrace_5679961 : CollatzResearch.WordTrace tailWord_5679961 prefixEnd_5679961 2916550091792356860165841 := by
  unfold tailWord_5679961
  simp only [CollatzResearch.WordTrace]
  refine ⟨207165196975478831953479737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138110131316985887968986491 207165196975478831953479737)
  ·
    refine ⟨155373897731609123965109803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207165196975478831953479737 155373897731609123965109803)
    ·
      refine ⟨233060846597413685947664705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155373897731609123965109803 233060846597413685947664705)
      ·
        refine ⟨174795634948060264460748529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233060846597413685947664705 174795634948060264460748529)
        ·
          refine ⟨131096726211045198345561397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174795634948060264460748529 131096726211045198345561397)
          ·
            refine ⟨12290318082285487344896381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131096726211045198345561397 12290318082285487344896381)
            ·
              refine ⟨4608869280857057754336143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12290318082285487344896381 4608869280857057754336143)
              ·
                refine ⟨6913303921285586631504215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4608869280857057754336143 6913303921285586631504215)
                ·
                  refine ⟨10369955881928379947256323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913303921285586631504215 10369955881928379947256323)
                  ·
                    refine ⟨15554933822892569920884485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10369955881928379947256323 15554933822892569920884485)
                    ·
                      refine ⟨2916550091792356860165841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15554933822892569920884485 2916550091792356860165841)
                      ·
                        rfl

theorem cell23_5679961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_5679961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679961 prefixEnd_5679961 := by exact prefixLift 5679961
  have htrace : WordTrace (prefixWord ++ tailWord_5679961) baseStart_5679961 baseEnd_5679961 := by
    simpa [prefixWord, tailWord_5679961, baseEnd_5679961] using wordTrace_append hprefix tailTrace_5679961
  have hstable : (prefixWord ++ tailWord_5679961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679961).length < 2 ^ (prefixWord ++ tailWord_5679961).sum := by decide
  have hdescent : baseEnd_5679961 < baseStart_5679961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679971 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 2, 4]
def baseStart_5679971 : Nat := 118140960795 + 5679971 * 2 ^ 59
def prefixEnd_5679971 : Nat := 4983230072969 + 3 ^ 40 * 5679971 * 2
def baseEnd_5679971 : Nat := 972185075532967273680265

theorem tailTrace_5679971 : CollatzResearch.WordTrace tailWord_5679971 prefixEnd_5679971 972185075532967273680265 := by
  unfold tailWord_5679971
  simp only [CollatzResearch.WordTrace]
  refine ⟨207165561705442603661343767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138110374470295069107562511 207165561705442603661343767)
  ·
    refine ⟨310748342558163905492015651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207165561705442603661343767 310748342558163905492015651)
    ·
      refine ⟨466122513837245858238023477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310748342558163905492015651 466122513837245858238023477)
      ·
        refine ⟨43698985672241799209814701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 466122513837245858238023477 43698985672241799209814701)
        ·
          refine ⟨16387119627090674703680513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43698985672241799209814701 16387119627090674703680513)
          ·
            refine ⟨12290339720318006027760385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16387119627090674703680513 12290339720318006027760385)
            ·
              refine ⟨9217754790238504520820289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12290339720318006027760385 9217754790238504520820289)
              ·
                refine ⟨6913316092678878390615217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9217754790238504520820289 6913316092678878390615217)
                ·
                  refine ⟨5184987069509158792961413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6913316092678878390615217 5184987069509158792961413)
                  ·
                    refine ⟨972185075532967273680265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184987069509158792961413 972185075532967273680265)
                    ·
                      rfl

theorem cell23_5679971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 4].length) (baseStart_5679971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679971 prefixEnd_5679971 := by exact prefixLift 5679971
  have htrace : WordTrace (prefixWord ++ tailWord_5679971) baseStart_5679971 baseEnd_5679971 := by
    simpa [prefixWord, tailWord_5679971, baseEnd_5679971] using wordTrace_append hprefix tailTrace_5679971
  have hstable : (prefixWord ++ tailWord_5679971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679971).length < 2 ^ (prefixWord ++ tailWord_5679971).sum := by decide
  have hdescent : baseEnd_5679971 < baseStart_5679971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5679994 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_5679994 : Nat := 118140960795 + 5679994 * 2 ^ 59
def prefixEnd_5679994 : Nat := 4983230072969 + 3 ^ 40 * 5679994 * 2
def baseEnd_5679994 : Nat := 2916567036653955231053189

theorem tailTrace_5679994 : CollatzResearch.WordTrace tailWord_5679994 prefixEnd_5679994 2916567036653955231053189 := by
  unfold tailWord_5679994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51791600146089819647357759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138110933722906185726287357 51791600146089819647357759)
  ·
    refine ⟨77687400219134729471036639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51791600146089819647357759 77687400219134729471036639)
    ·
      refine ⟨116531100328702094206554959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77687400219134729471036639 116531100328702094206554959)
      ·
        refine ⟨174796650493053141309832439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116531100328702094206554959 174796650493053141309832439)
        ·
          refine ⟨262194975739579711964748659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174796650493053141309832439 262194975739579711964748659)
          ·
            refine ⟨393292463609369567947122989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262194975739579711964748659 393292463609369567947122989)
            ·
              refine ⟨147484673853513587980171121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393292463609369567947122989 147484673853513587980171121)
              ·
                refine ⟨110613505390135190985128341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147484673853513587980171121 110613505390135190985128341)
                ·
                  refine ⟨5185008065162587077427891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110613505390135190985128341 5185008065162587077427891)
                  ·
                    refine ⟨7777512097743880616141837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185008065162587077427891 7777512097743880616141837)
                    ·
                      refine ⟨2916567036653955231053189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777512097743880616141837 2916567036653955231053189)
                      ·
                        rfl

theorem cell23_5679994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_5679994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5679994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5679994 prefixEnd_5679994 := by exact prefixLift 5679994
  have htrace : WordTrace (prefixWord ++ tailWord_5679994) baseStart_5679994 baseEnd_5679994 := by
    simpa [prefixWord, tailWord_5679994, baseEnd_5679994] using wordTrace_append hprefix tailTrace_5679994
  have hstable : (prefixWord ++ tailWord_5679994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5679994).length < 2 ^ (prefixWord ++ tailWord_5679994).sum := by decide
  have hdescent : baseEnd_5679994 < baseStart_5679994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5679994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680022 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5680022 : Nat := 118140960795 + 5680022 * 2 ^ 59
def prefixEnd_5680022 : Nat := 4983230072969 + 3 ^ 40 * 5680022 * 2
def baseEnd_5680022 : Nat := 972193804704093707167687

theorem tailTrace_5680022 : CollatzResearch.WordTrace tailWord_5680022 prefixEnd_5680022 972193804704093707167687 := by
  unfold tailWord_5680022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12947963864266114960715645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138111614552171892914300213 12947963864266114960715645)
  ·
    refine ⟨4855486449099793110268367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12947963864266114960715645 4855486449099793110268367)
    ·
      refine ⟨7283229673649689665402551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855486449099793110268367 7283229673649689665402551)
      ·
        refine ⟨10924844510474534498103827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283229673649689665402551 10924844510474534498103827)
        ·
          refine ⟨16387266765711801747155741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10924844510474534498103827 16387266765711801747155741)
          ·
            refine ⟨6145225037141925655183403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16387266765711801747155741 6145225037141925655183403)
            ·
              refine ⟨9217837555712888482775105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145225037141925655183403 9217837555712888482775105)
              ·
                refine ⟨6913378166784666362081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9217837555712888482775105 6913378166784666362081329)
                ·
                  refine ⟨5185033625088499771560997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6913378166784666362081329 5185033625088499771560997)
                  ·
                    refine ⟨972193804704093707167687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5185033625088499771560997 972193804704093707167687)
                    ·
                      rfl

theorem cell23_5680022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5680022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680022 prefixEnd_5680022 := by exact prefixLift 5680022
  have htrace : WordTrace (prefixWord ++ tailWord_5680022) baseStart_5680022 baseEnd_5680022 := by
    simpa [prefixWord, tailWord_5680022, baseEnd_5680022] using wordTrace_append hprefix tailTrace_5680022
  have hstable : (prefixWord ++ tailWord_5680022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680022).length < 2 ^ (prefixWord ++ tailWord_5680022).sum := by decide
  have hdescent : baseEnd_5680022 < baseStart_5680022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680028 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5680028 : Nat := 118140960795 + 5680028 * 2 ^ 59
def prefixEnd_5680028 : Nat := 4983230072969 + 3 ^ 40 * 5680028 * 2
def baseEnd_5680028 : Nat := 2916584494996208098028033

theorem tailTrace_5680028 : CollatzResearch.WordTrace tailWord_5680028 prefixEnd_5680028 2916584494996208098028033 := by
  unfold tailWord_5680028
  simp only [CollatzResearch.WordTrace]
  refine ⟨103583820333118051198084369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138111760444157401597445825 103583820333118051198084369)
  ·
    refine ⟨77687865249838538398563277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103583820333118051198084369 77687865249838538398563277)
    ·
      refine ⟨29132949468689451899461229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77687865249838538398563277 29132949468689451899461229)
      ·
        refine ⟨10924856050758544462297961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29132949468689451899461229 10924856050758544462297961)
        ·
          refine ⟨8193642038068908346723471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10924856050758544462297961 8193642038068908346723471)
          ·
            refine ⟨12290463057103362520085207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8193642038068908346723471 12290463057103362520085207)
            ·
              refine ⟨18435694585655043780127811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12290463057103362520085207 18435694585655043780127811)
              ·
                refine ⟨27653541878482565670191717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18435694585655043780127811 27653541878482565670191717)
                ·
                  refine ⟨5185039102215481063160947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27653541878482565670191717 5185039102215481063160947)
                  ·
                    refine ⟨7777558653323221594741421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185039102215481063160947 7777558653323221594741421)
                    ·
                      refine ⟨2916584494996208098028033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777558653323221594741421 2916584494996208098028033)
                      ·
                        rfl

theorem cell23_5680028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5680028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680028 prefixEnd_5680028 := by exact prefixLift 5680028
  have htrace : WordTrace (prefixWord ++ tailWord_5680028) baseStart_5680028 baseEnd_5680028 := by
    simpa [prefixWord, tailWord_5680028, baseEnd_5680028] using wordTrace_append hprefix tailTrace_5680028
  have hstable : (prefixWord ++ tailWord_5680028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680028).length < 2 ^ (prefixWord ++ tailWord_5680028).sum := by decide
  have hdescent : baseEnd_5680028 < baseStart_5680028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680037 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_5680037 : Nat := 118140960795 + 5680037 * 2 ^ 59
def prefixEnd_5680037 : Nat := 4983230072969 + 3 ^ 40 * 5680037 * 2
def baseEnd_5680037 : Nat := 2916589116322098562815491

theorem tailTrace_5680037 : CollatzResearch.WordTrace tailWord_5680037 prefixEnd_5680037 2916589116322098562815491 := by
  unfold tailWord_5680037
  simp only [CollatzResearch.WordTrace]
  refine ⟨207167968923203496933246365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138111979282135664622164243 207167968923203496933246365)
  ·
    refine ⟨77687988346201311349967387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207167968923203496933246365 77687988346201311349967387)
    ·
      refine ⟨116531982519301967024951081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77687988346201311349967387 116531982519301967024951081)
      ·
        refine ⟨87398986889476475268713311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116531982519301967024951081 87398986889476475268713311)
        ·
          refine ⟨131098480334214712903069967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87398986889476475268713311 131098480334214712903069967)
          ·
            refine ⟨196647720501322069354604951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131098480334214712903069967 196647720501322069354604951)
            ·
              refine ⟨294971580751983104031907427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196647720501322069354604951 294971580751983104031907427)
              ·
                refine ⟨442457371127974656047861141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294971580751983104031907427 442457371127974656047861141)
                ·
                  refine ⟨20740189271623812002243491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 442457371127974656047861141 20740189271623812002243491)
                  ·
                    refine ⟨31110283907435718003365237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20740189271623812002243491 31110283907435718003365237)
                    ·
                      refine ⟨2916589116322098562815491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31110283907435718003365237 2916589116322098562815491)
                      ·
                        rfl

theorem cell23_5680037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_5680037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680037 prefixEnd_5680037 := by exact prefixLift 5680037
  have htrace : WordTrace (prefixWord ++ tailWord_5680037) baseStart_5680037 baseEnd_5680037 := by
    simpa [prefixWord, tailWord_5680037, baseEnd_5680037] using wordTrace_append hprefix tailTrace_5680037
  have hstable : (prefixWord ++ tailWord_5680037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680037).length < 2 ^ (prefixWord ++ tailWord_5680037).sum := by decide
  have hdescent : baseEnd_5680037 < baseStart_5680037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680045 : List Nat := [1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_5680045 : Nat := 118140960795 + 5680045 * 2 ^ 59
def prefixEnd_5680045 : Nat := 4983230072969 + 3 ^ 40 * 5680045 * 2
def baseEnd_5680045 : Nat := 2916593224167334531515455

theorem tailTrace_5680045 : CollatzResearch.WordTrace tailWord_5680045 prefixEnd_5680045 2916593224167334531515455 := by
  unfold tailWord_5680045
  simp only [CollatzResearch.WordTrace]
  refine ⟨207168260707174514299537589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138112173804783009533025059 207168260707174514299537589)
  ·
    refine ⟨19422024441297610715581649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207168260707174514299537589 19422024441297610715581649)
    ·
      refine ⟨14566518330973208036686237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19422024441297610715581649 14566518330973208036686237)
      ·
        refine ⟨5462444374114953013757339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14566518330973208036686237 5462444374114953013757339)
        ·
          refine ⟨8193666561172429520636009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5462444374114953013757339 8193666561172429520636009)
          ·
            refine ⟨6145249920879322140477007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8193666561172429520636009 6145249920879322140477007)
            ·
              refine ⟨9217874881318983210715511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145249920879322140477007 9217874881318983210715511)
              ·
                refine ⟨13826812321978474816073267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9217874881318983210715511 13826812321978474816073267)
                ·
                  refine ⟨20740218482967712224109901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13826812321978474816073267 20740218482967712224109901)
                  ·
                    refine ⟨7777581931112892084041213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20740218482967712224109901 7777581931112892084041213)
                    ·
                      refine ⟨2916593224167334531515455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777581931112892084041213 2916593224167334531515455)
                      ·
                        rfl

theorem cell23_5680045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_5680045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680045 prefixEnd_5680045 := by exact prefixLift 5680045
  have htrace : WordTrace (prefixWord ++ tailWord_5680045) baseStart_5680045 baseEnd_5680045 := by
    simpa [prefixWord, tailWord_5680045, baseEnd_5680045] using wordTrace_append hprefix tailTrace_5680045
  have hstable : (prefixWord ++ tailWord_5680045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680045).length < 2 ^ (prefixWord ++ tailWord_5680045).sum := by decide
  have hdescent : baseEnd_5680045 < baseStart_5680045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680047 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_5680047 : Nat := 118140960795 + 5680047 * 2 ^ 59
def prefixEnd_5680047 : Nat := 4983230072969 + 3 ^ 40 * 5680047 * 2
def baseEnd_5680047 : Nat := 2916594251128643523690445

theorem tailTrace_5680047 : CollatzResearch.WordTrace tailWord_5680047 prefixEnd_5680047 2916594251128643523690445 := by
  unfold tailWord_5680047
  simp only [CollatzResearch.WordTrace]
  refine ⟨207168333653167268641110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138112222435444845760740263 207168333653167268641110395)
  ·
    refine ⟨310752500479750902961665593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207168333653167268641110395 310752500479750902961665593)
    ·
      refine ⟨233064375359813177221249195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310752500479750902961665593 233064375359813177221249195)
      ·
        refine ⟨349596563039719765831873793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233064375359813177221249195 349596563039719765831873793)
        ·
          refine ⟨262197422279789824373905345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349596563039719765831873793 262197422279789824373905345)
          ·
            refine ⟨196648066709842368280429009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262197422279789824373905345 196648066709842368280429009)
            ·
              refine ⟨147486050032381776210321757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196648066709842368280429009 147486050032381776210321757)
              ·
                refine ⟨55307268762143166078870659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147486050032381776210321757 55307268762143166078870659)
                ·
                  refine ⟨82960903143214749118305989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55307268762143166078870659 82960903143214749118305989)
                  ·
                    refine ⟨15555169339352765459682373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82960903143214749118305989 15555169339352765459682373)
                    ·
                      refine ⟨2916594251128643523690445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15555169339352765459682373 2916594251128643523690445)
                      ·
                        rfl

theorem cell23_5680047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_5680047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680047 prefixEnd_5680047 := by exact prefixLift 5680047
  have htrace : WordTrace (prefixWord ++ tailWord_5680047) baseStart_5680047 baseEnd_5680047 := by
    simpa [prefixWord, tailWord_5680047, baseEnd_5680047] using wordTrace_append hprefix tailTrace_5680047
  have hstable : (prefixWord ++ tailWord_5680047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680047).length < 2 ^ (prefixWord ++ tailWord_5680047).sum := by decide
  have hdescent : baseEnd_5680047 < baseStart_5680047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680087 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 7]
def baseStart_5680087 : Nat := 118140960795 + 5680087 * 2 ^ 59
def prefixEnd_5680087 : Nat := 4983230072969 + 3 ^ 40 * 5680087 * 2
def baseEnd_5680087 : Nat := 972204930118274455730087

theorem tailTrace_5680087 : CollatzResearch.WordTrace tailWord_5680087 prefixEnd_5680087 972204930118274455730087 := by
  unfold tailWord_5680087
  simp only [CollatzResearch.WordTrace]
  refine ⟨207169792573022355472566515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138113195048681570315044343 207169792573022355472566515)
  ·
    refine ⟨310754688859533533208849773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207169792573022355472566515 310754688859533533208849773)
    ·
      refine ⟨116533008322325074953318665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310754688859533533208849773 116533008322325074953318665)
      ·
        refine ⟨87399756241743806214988999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116533008322325074953318665 87399756241743806214988999)
        ·
          refine ⟨131099634362615709322483499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87399756241743806214988999 131099634362615709322483499)
          ·
            refine ⟨196649451543923563983725249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131099634362615709322483499 196649451543923563983725249)
            ·
              refine ⟨147487088657942672987793937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196649451543923563983725249 147487088657942672987793937)
              ·
                refine ⟨110615316493457004740845453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147487088657942672987793937 110615316493457004740845453)
                ·
                  refine ⟨41480743685046376777817045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110615316493457004740845453 41480743685046376777817045)
                  ·
                    refine ⟨972204930118274455730087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41480743685046376777817045 972204930118274455730087)
                    ·
                      rfl

theorem cell23_5680087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_5680087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680087 prefixEnd_5680087 := by exact prefixLift 5680087
  have htrace : WordTrace (prefixWord ++ tailWord_5680087) baseStart_5680087 baseEnd_5680087 := by
    simpa [prefixWord, tailWord_5680087, baseEnd_5680087] using wordTrace_append hprefix tailTrace_5680087
  have hstable : (prefixWord ++ tailWord_5680087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680087).length < 2 ^ (prefixWord ++ tailWord_5680087).sum := by decide
  have hdescent : baseEnd_5680087 < baseStart_5680087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680127 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_5680127 : Nat := 118140960795 + 5680127 * 2 ^ 59
def prefixEnd_5680127 : Nat := 4983230072969 + 3 ^ 40 * 5680127 * 2
def baseEnd_5680127 : Nat := 2916635329581003210690077

theorem tailTrace_5680127 : CollatzResearch.WordTrace tailWord_5680127 prefixEnd_5680127 2916635329581003210690077 := by
  unfold tailWord_5680127
  simp only [CollatzResearch.WordTrace]
  refine ⟨207171251492877442304022635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138114167661918294869348423 207171251492877442304022635)
  ·
    refine ⟨310756877239316163456033953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207171251492877442304022635 310756877239316163456033953)
    ·
      refine ⟨233067657929487122592025465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310756877239316163456033953 233067657929487122592025465)
      ·
        refine ⟨174800743447115341944019099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233067657929487122592025465 174800743447115341944019099)
        ·
          refine ⟨262201115170673012916028649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174800743447115341944019099 262201115170673012916028649)
          ·
            refine ⟨196650836378004759687021487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262201115170673012916028649 196650836378004759687021487)
            ·
              refine ⟨294976254567007139530532231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196650836378004759687021487 294976254567007139530532231)
              ·
                refine ⟨442464381850510709295798347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294976254567007139530532231 442464381850510709295798347)
                ·
                  refine ⟨663696572775766063943697521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442464381850510709295798347 663696572775766063943697521)
                  ·
                    refine ⟨497772429581824547957773141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 663696572775766063943697521 497772429581824547957773141)
                    ·
                      refine ⟨2916635329581003210690077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 497772429581824547957773141 2916635329581003210690077)
                      ·
                        rfl

theorem cell23_5680127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_5680127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680127 prefixEnd_5680127 := by exact prefixLift 5680127
  have htrace : WordTrace (prefixWord ++ tailWord_5680127) baseStart_5680127 baseEnd_5680127 := by
    simpa [prefixWord, tailWord_5680127, baseEnd_5680127] using wordTrace_append hprefix tailTrace_5680127
  have hstable : (prefixWord ++ tailWord_5680127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680127).length < 2 ^ (prefixWord ++ tailWord_5680127).sum := by decide
  have hdescent : baseEnd_5680127 < baseStart_5680127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680185 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 1, 4]
def baseStart_5680185 : Nat := 118140960795 + 5680185 * 2 ^ 59
def prefixEnd_5680185 : Nat := 4983230072969 + 3 ^ 40 * 5680185 * 2
def baseEnd_5680185 : Nat := 972221703819654661254937

theorem tailTrace_5680185 : CollatzResearch.WordTrace tailWord_5680185 prefixEnd_5680185 972221703819654661254937 := by
  unfold tailWord_5680185
  simp only [CollatzResearch.WordTrace]
  refine ⟨207173366926667318209634009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138115577951111545473089339 207173366926667318209634009)
  ·
    refine ⟨155380025195000488657225507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207173366926667318209634009 155380025195000488657225507)
    ·
      refine ⟨233070037792500732985838261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155380025195000488657225507 233070037792500732985838261)
      ·
        refine ⟨21850316043046943717422337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233070037792500732985838261 21850316043046943717422337)
        ·
          refine ⟨16387737032285207788066753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21850316043046943717422337 16387737032285207788066753)
          ·
            refine ⟨12290802774213905841050065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16387737032285207788066753 12290802774213905841050065)
            ·
              refine ⟨9218102080660429380787549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12290802774213905841050065 9218102080660429380787549)
              ·
                refine ⟨3456788280247661017795331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9218102080660429380787549 3456788280247661017795331)
                ·
                  refine ⟨5185182420371491526692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456788280247661017795331 5185182420371491526692997)
                  ·
                    refine ⟨972221703819654661254937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5185182420371491526692997 972221703819654661254937)
                    ·
                      rfl

theorem cell23_5680185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 4].length) (baseStart_5680185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680185 prefixEnd_5680185 := by exact prefixLift 5680185
  have htrace : WordTrace (prefixWord ++ tailWord_5680185) baseStart_5680185 baseEnd_5680185 := by
    simpa [prefixWord, tailWord_5680185, baseEnd_5680185] using wordTrace_append hprefix tailTrace_5680185
  have hstable : (prefixWord ++ tailWord_5680185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680185).length < 2 ^ (prefixWord ++ tailWord_5680185).sum := by decide
  have hdescent : baseEnd_5680185 < baseStart_5680185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680191 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 3]
def baseStart_5680191 : Nat := 118140960795 + 5680191 * 2 ^ 59
def prefixEnd_5680191 : Nat := 4983230072969 + 3 ^ 40 * 5680191 * 2
def baseEnd_5680191 : Nat := 2916668192342890960289783

theorem tailTrace_5680191 : CollatzResearch.WordTrace tailWord_5680191 prefixEnd_5680191 2916668192342890960289783 := by
  unfold tailWord_5680191
  simp only [CollatzResearch.WordTrace]
  refine ⟨207173585764645581234352427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138115723843097054156234951 207173585764645581234352427)
  ·
    refine ⟨310760378646968371851528641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207173585764645581234352427 310760378646968371851528641)
    ·
      refine ⟨233070283985226278888646481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310760378646968371851528641 233070283985226278888646481)
      ·
        refine ⟨174802712988919709166484861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233070283985226278888646481 174802712988919709166484861)
        ·
          refine ⟨65551017370844890937431823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174802712988919709166484861 65551017370844890937431823)
          ·
            refine ⟨98326526056267336406147735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65551017370844890937431823 98326526056267336406147735)
            ·
              refine ⟨147489789084401004609221603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98326526056267336406147735 147489789084401004609221603)
              ·
                refine ⟨221234683626601506913832405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147489789084401004609221603 221234683626601506913832405)
                ·
                  refine ⟨5185187897498472818292947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 221234683626601506913832405 5185187897498472818292947)
                  ·
                    refine ⟨7777781846247709227439421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185187897498472818292947 7777781846247709227439421)
                    ·
                      refine ⟨2916668192342890960289783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777781846247709227439421 2916668192342890960289783)
                      ·
                        rfl

theorem cell23_5680191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_5680191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680191 prefixEnd_5680191 := by exact prefixLift 5680191
  have htrace : WordTrace (prefixWord ++ tailWord_5680191) baseStart_5680191 baseEnd_5680191 := by
    simpa [prefixWord, tailWord_5680191, baseEnd_5680191] using wordTrace_append hprefix tailTrace_5680191
  have hstable : (prefixWord ++ tailWord_5680191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680191).length < 2 ^ (prefixWord ++ tailWord_5680191).sum := by decide
  have hdescent : baseEnd_5680191 < baseStart_5680191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680198 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5680198 : Nat := 118140960795 + 5680198 * 2 ^ 59
def prefixEnd_5680198 : Nat := 4983230072969 + 3 ^ 40 * 5680198 * 2
def baseEnd_5680198 : Nat := 324074642967496936989139

theorem tailTrace_5680198 : CollatzResearch.WordTrace tailWord_5680198 prefixEnd_5680198 324074642967496936989139 := by
  unfold tailWord_5680198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474182533613131919683039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138115894050413480953238165 6474182533613131919683039)
  ·
    refine ⟨9711273800419697879524559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474182533613131919683039 9711273800419697879524559)
    ·
      refine ⟨14566910700629546819286839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9711273800419697879524559 14566910700629546819286839)
      ·
        refine ⟨21850366050944320228930259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14566910700629546819286839 21850366050944320228930259)
        ·
          refine ⟨32775549076416480343395389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21850366050944320228930259 32775549076416480343395389)
          ·
            refine ⟨12290830903656180128773271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32775549076416480343395389 12290830903656180128773271)
            ·
              refine ⟨18436246355484270193159907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12290830903656180128773271 18436246355484270193159907)
              ·
                refine ⟨27654369533226405289739861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18436246355484270193159907 27654369533226405289739861)
                ·
                  refine ⟨324074642967496936989139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27654369533226405289739861 324074642967496936989139)
                  ·
                    rfl

theorem cell23_5680198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5680198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680198 prefixEnd_5680198 := by exact prefixLift 5680198
  have htrace : WordTrace (prefixWord ++ tailWord_5680198) baseStart_5680198 baseEnd_5680198 := by
    simpa [prefixWord, tailWord_5680198, baseEnd_5680198] using wordTrace_append hprefix tailTrace_5680198
  have hstable : (prefixWord ++ tailWord_5680198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680198).length < 2 ^ (prefixWord ++ tailWord_5680198).sum := by decide
  have hdescent : baseEnd_5680198 < baseStart_5680198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680248 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2]
def baseStart_5680248 : Nat := 118140960795 + 5680248 * 2 ^ 59
def prefixEnd_5680248 : Nat := 4983230072969 + 3 ^ 40 * 5680248 * 2
def baseEnd_5680248 : Nat := 2916697460740197237277021

theorem tailTrace_5680248 : CollatzResearch.WordTrace tailWord_5680248 prefixEnd_5680248 2916697460740197237277021 := by
  unfold tailWord_5680248
  simp only [CollatzResearch.WordTrace]
  refine ⟨103587832362719539984588699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138117109816959386646118265 103587832362719539984588699)
  ·
    refine ⟨155381748544079309976883049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103587832362719539984588699 155381748544079309976883049)
    ·
      refine ⟨116536311408059482482662287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155381748544079309976883049 116536311408059482482662287)
      ·
        refine ⟨174804467112089223723993431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116536311408059482482662287 174804467112089223723993431)
        ·
          refine ⟨262206700668133835585990147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174804467112089223723993431 262206700668133835585990147)
          ·
            refine ⟨393310051002200753378985221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262206700668133835585990147 393310051002200753378985221)
            ·
              refine ⟨73745634562912641258559729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393310051002200753378985221 73745634562912641258559729)
              ·
                refine ⟨55309225922184480943919797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73745634562912641258559729 55309225922184480943919797)
                ·
                  refine ⟨5185239930204795088492481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55309225922184480943919797 5185239930204795088492481)
                  ·
                    refine ⟨3888929947653596316369361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185239930204795088492481 3888929947653596316369361)
                    ·
                      refine ⟨2916697460740197237277021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888929947653596316369361 2916697460740197237277021)
                      ·
                        rfl

theorem cell23_5680248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_5680248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680248 prefixEnd_5680248 := by exact prefixLift 5680248
  have htrace : WordTrace (prefixWord ++ tailWord_5680248) baseStart_5680248 baseEnd_5680248 := by
    simpa [prefixWord, tailWord_5680248, baseEnd_5680248] using wordTrace_append hprefix tailTrace_5680248
  have hstable : (prefixWord ++ tailWord_5680248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680248).length < 2 ^ (prefixWord ++ tailWord_5680248).sum := by decide
  have hdescent : baseEnd_5680248 < baseStart_5680248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680265 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 3, 2, 2]
def baseStart_5680265 : Nat := 118140960795 + 5680265 * 2 ^ 59
def prefixEnd_5680265 : Nat := 4983230072969 + 3 ^ 40 * 5680265 * 2
def baseEnd_5680265 : Nat := 2916706189911323670764443

theorem tailTrace_5680265 : CollatzResearch.WordTrace tailWord_5680265 prefixEnd_5680265 2916706189911323670764443 := by
  unfold tailWord_5680265
  simp only [CollatzResearch.WordTrace]
  refine ⟨207176284766377491872546249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138117523177584994581697499 207176284766377491872546249)
  ·
    refine ⟨155382213574783118904409687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207176284766377491872546249 155382213574783118904409687)
    ·
      refine ⟨233073320362174678356614531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155382213574783118904409687 233073320362174678356614531)
      ·
        refine ⟨349609980543262017534921797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233073320362174678356614531 349609980543262017534921797)
        ·
          refine ⟨65551871351861628287797837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349609980543262017534921797 65551871351861628287797837)
          ·
            refine ⟨24581951756948110607924189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65551871351861628287797837 24581951756948110607924189)
            ·
              refine ⟨9218231908855541477971571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24581951756948110607924189 9218231908855541477971571)
              ·
                refine ⟨13827347863283312216957357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218231908855541477971571 13827347863283312216957357)
                ·
                  refine ⟨5185255448731242081359009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13827347863283312216957357 5185255448731242081359009)
                  ·
                    refine ⟨3888941586548431561019257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185255448731242081359009 3888941586548431561019257)
                    ·
                      refine ⟨2916706189911323670764443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888941586548431561019257 2916706189911323670764443)
                      ·
                        rfl

theorem cell23_5680265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 3, 2, 2].length) (baseStart_5680265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680265 prefixEnd_5680265 := by exact prefixLift 5680265
  have htrace : WordTrace (prefixWord ++ tailWord_5680265) baseStart_5680265 baseEnd_5680265 := by
    simpa [prefixWord, tailWord_5680265, baseEnd_5680265] using wordTrace_append hprefix tailTrace_5680265
  have hstable : (prefixWord ++ tailWord_5680265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680265).length < 2 ^ (prefixWord ++ tailWord_5680265).sum := by decide
  have hdescent : baseEnd_5680265 < baseStart_5680265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680304 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_5680304 : Nat := 118140960795 + 5680304 * 2 ^ 59
def prefixEnd_5680304 : Nat := 4983230072969 + 3 ^ 40 * 5680304 * 2
def baseEnd_5680304 : Nat := 2916726215656849018176763

theorem tailTrace_5680304 : CollatzResearch.WordTrace tailWord_5680304 prefixEnd_5680304 2916726215656849018176763 := by
  unfold tailWord_5680304
  simp only [CollatzResearch.WordTrace]
  refine ⟨103588853606618100766607983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138118471475490801022143977 103588853606618100766607983)
  ·
    refine ⟨155383280409927151149911975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103588853606618100766607983 155383280409927151149911975)
    ·
      refine ⟨233074920614890726724867963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155383280409927151149911975 233074920614890726724867963)
      ·
        refine ⟨349612380922336090087301945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233074920614890726724867963 349612380922336090087301945)
        ·
          refine ⟨262209285691752067565476459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349612380922336090087301945 262209285691752067565476459)
          ·
            refine ⟨393313928537628101348214689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262209285691752067565476459 393313928537628101348214689)
            ·
              refine ⟨294985446403221076011161017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393313928537628101348214689 294985446403221076011161017)
              ·
                refine ⟨221239084802415807008370763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294985446403221076011161017 221239084802415807008370763)
                ·
                  refine ⟨331858627203623710512556145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221239084802415807008370763 331858627203623710512556145)
                  ·
                    refine ⟨248893970402717782884417109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 331858627203623710512556145 248893970402717782884417109)
                    ·
                      refine ⟨2916726215656849018176763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 248893970402717782884417109 2916726215656849018176763)
                      ·
                        rfl

theorem cell23_5680304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_5680304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680304 prefixEnd_5680304 := by exact prefixLift 5680304
  have htrace : WordTrace (prefixWord ++ tailWord_5680304) baseStart_5680304 baseEnd_5680304 := by
    simpa [prefixWord, tailWord_5680304, baseEnd_5680304] using wordTrace_append hprefix tailTrace_5680304
  have hstable : (prefixWord ++ tailWord_5680304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680304).length < 2 ^ (prefixWord ++ tailWord_5680304).sum := by decide
  have hdescent : baseEnd_5680304 < baseStart_5680304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680310 : List Nat := [5, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5680310 : Nat := 118140960795 + 5680310 * 2 ^ 59
def prefixEnd_5680310 : Nat := 4983230072969 + 3 ^ 40 * 5680310 * 2
def baseEnd_5680310 : Nat := 2916729296540775994701737

theorem tailTrace_5680310 : CollatzResearch.WordTrace tailWord_5680310 prefixEnd_5680310 2916729296540775994701737 := by
  unfold tailWord_5680310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948620378200904034870899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138118617367476309705289589 12948620378200904034870899)
  ·
    refine ⟨19422930567301356052306349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12948620378200904034870899 19422930567301356052306349)
    ·
      refine ⟨7283598962738008519614881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19422930567301356052306349 7283598962738008519614881)
      ·
        refine ⟨5462699222053506389711161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7283598962738008519614881 5462699222053506389711161)
        ·
          refine ⟨4097024416540129792283371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5462699222053506389711161 4097024416540129792283371)
          ·
            refine ⟨6145536624810194688425057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097024416540129792283371 6145536624810194688425057)
            ·
              refine ⟨4609152468607646016318793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6145536624810194688425057 4609152468607646016318793)
              ·
                refine ⟨3456864351455734512239095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609152468607646016318793 3456864351455734512239095)
                ·
                  refine ⟨5185296527183601768358643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456864351455734512239095 5185296527183601768358643)
                  ·
                    refine ⟨7777944790775402652537965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185296527183601768358643 7777944790775402652537965)
                    ·
                      refine ⟨2916729296540775994701737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7777944790775402652537965 2916729296540775994701737)
                      ·
                        rfl

theorem cell23_5680310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5680310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680310 prefixEnd_5680310 := by exact prefixLift 5680310
  have htrace : WordTrace (prefixWord ++ tailWord_5680310) baseStart_5680310 baseEnd_5680310 := by
    simpa [prefixWord, tailWord_5680310, baseEnd_5680310] using wordTrace_append hprefix tailTrace_5680310
  have hstable : (prefixWord ++ tailWord_5680310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680310).length < 2 ^ (prefixWord ++ tailWord_5680310).sum := by decide
  have hdescent : baseEnd_5680310 < baseStart_5680310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680316 : List Nat := [2, 2, 2, 3, 2, 3, 2, 2, 1, 2, 2]
def baseStart_5680316 : Nat := 118140960795 + 5680316 * 2 ^ 59
def prefixEnd_5680316 : Nat := 4983230072969 + 3 ^ 40 * 5680316 * 2
def baseEnd_5680316 : Nat := 2916732377424702971226709

theorem tailTrace_5680316 : CollatzResearch.WordTrace tailWord_5680316 prefixEnd_5680316 2916732377424702971226709 := by
  unfold tailWord_5680316
  simp only [CollatzResearch.WordTrace]
  refine ⟨103589072444596363791326401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138118763259461818388435201 103589072444596363791326401)
  ·
    refine ⟨77691804333447272843494801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103589072444596363791326401 77691804333447272843494801)
    ·
      refine ⟨58268853250085454632621101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77691804333447272843494801 58268853250085454632621101)
      ·
        refine ⟨21850819968782045487232913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58268853250085454632621101 21850819968782045487232913)
        ·
          refine ⟨16388114976586534115424685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21850819968782045487232913 16388114976586534115424685)
          ·
            refine ⟨6145543116219950293284257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16388114976586534115424685 6145543116219950293284257)
            ·
              refine ⟨4609157337164962719963193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6145543116219950293284257 4609157337164962719963193)
              ·
                refine ⟨3456868002873722039972395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609157337164962719963193 3456868002873722039972395)
                ·
                  refine ⟨5185302004310583059958593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456868002873722039972395 5185302004310583059958593)
                  ·
                    refine ⟨3888976503232937294968945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185302004310583059958593 3888976503232937294968945)
                    ·
                      refine ⟨2916732377424702971226709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3888976503232937294968945 2916732377424702971226709)
                      ·
                        rfl

theorem cell23_5680316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_5680316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680316 prefixEnd_5680316 := by exact prefixLift 5680316
  have htrace : WordTrace (prefixWord ++ tailWord_5680316) baseStart_5680316 baseEnd_5680316 := by
    simpa [prefixWord, tailWord_5680316, baseEnd_5680316] using wordTrace_append hprefix tailTrace_5680316
  have hstable : (prefixWord ++ tailWord_5680316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680316).length < 2 ^ (prefixWord ++ tailWord_5680316).sum := by decide
  have hdescent : baseEnd_5680316 < baseStart_5680316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680322 : List Nat := [3, 5, 1, 1, 2, 2, 1, 8]
def baseStart_5680322 : Nat := 118140960795 + 5680322 * 2 ^ 59
def prefixEnd_5680322 : Nat := 4983230072969 + 3 ^ 40 * 5680322 * 2
def baseEnd_5680322 : Nat := 108027239196615923990803

theorem tailTrace_5680322 : CollatzResearch.WordTrace tailWord_5680322 prefixEnd_5680322 108027239196615923990803 := by
  unfold tailWord_5680322
  simp only [CollatzResearch.WordTrace]
  refine ⟨51794590931792747651842805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138118909151447327071580813 51794590931792747651842805)
  ·
    refine ⟨4855742899855570092360263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51794590931792747651842805 4855742899855570092360263)
    ·
      refine ⟨7283614349783355138540395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855742899855570092360263 7283614349783355138540395)
      ·
        refine ⟨10925421524675032707810593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283614349783355138540395 10925421524675032707810593)
        ·
          refine ⟨8194066143506274530857945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10925421524675032707810593 8194066143506274530857945)
          ·
            refine ⟨6145549607629705898143459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8194066143506274530857945 6145549607629705898143459)
            ·
              refine ⟨9218324411444558847215189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145549607629705898143459 9218324411444558847215189)
              ·
                refine ⟨108027239196615923990803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9218324411444558847215189 108027239196615923990803)
                ·
                  rfl

theorem cell23_5680322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 8].length) (baseStart_5680322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680322 prefixEnd_5680322 := by exact prefixLift 5680322
  have htrace : WordTrace (prefixWord ++ tailWord_5680322) baseStart_5680322 baseEnd_5680322 := by
    simpa [prefixWord, tailWord_5680322, baseEnd_5680322] using wordTrace_append hprefix tailTrace_5680322
  have hstable : (prefixWord ++ tailWord_5680322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680322).length < 2 ^ (prefixWord ++ tailWord_5680322).sum := by decide
  have hdescent : baseEnd_5680322 < baseStart_5680322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680378 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_5680378 : Nat := 118140960795 + 5680378 * 2 ^ 59
def prefixEnd_5680378 : Nat := 4983230072969 + 3 ^ 40 * 5680378 * 2
def baseEnd_5680378 : Nat := 324084912580586858739047

theorem tailTrace_5680378 : CollatzResearch.WordTrace tailWord_5680378 prefixEnd_5680378 324084912580586858739047 := by
  unfold tailWord_5680378
  simp only [CollatzResearch.WordTrace]
  refine ⟨51795101553742028042852447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138120270809978741447606525 51795101553742028042852447)
  ·
    refine ⟨77692652330613042064278671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51795101553742028042852447 77692652330613042064278671)
    ·
      refine ⟨116538978495919563096418007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77692652330613042064278671 116538978495919563096418007)
      ·
        refine ⟨174808467743879344644627011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116538978495919563096418007 174808467743879344644627011)
        ·
          refine ⟨262212701615819016966940517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174808467743879344644627011 262212701615819016966940517)
          ·
            refine ⟨49164881552966065681301347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262212701615819016966940517 49164881552966065681301347)
            ·
              refine ⟨73747322329449098521952021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49164881552966065681301347 73747322329449098521952021)
              ·
                refine ⟨3456905734192926493216501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73747322329449098521952021 3456905734192926493216501)
                ·
                  refine ⟨324084912580586858739047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456905734192926493216501 324084912580586858739047)
                  ·
                    rfl

theorem cell23_5680378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_5680378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680378 prefixEnd_5680378 := by exact prefixLift 5680378
  have htrace : WordTrace (prefixWord ++ tailWord_5680378) baseStart_5680378 baseEnd_5680378 := by
    simpa [prefixWord, tailWord_5680378, baseEnd_5680378] using wordTrace_append hprefix tailTrace_5680378
  have hstable : (prefixWord ++ tailWord_5680378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680378).length < 2 ^ (prefixWord ++ tailWord_5680378).sum := by decide
  have hdescent : baseEnd_5680378 < baseStart_5680378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680429 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 5]
def baseStart_5680429 : Nat := 118140960795 + 5680429 * 2 ^ 59
def prefixEnd_5680429 : Nat := 4983230072969 + 3 ^ 40 * 5680429 * 2
def baseEnd_5680429 : Nat := 324087822304295669901521

theorem tailTrace_5680429 : CollatzResearch.WordTrace tailWord_5680429 prefixEnd_5680429 324087822304295669901521 := by
  unfold tailWord_5680429
  simp only [CollatzResearch.WordTrace]
  refine ⟨207182266337783347881516341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138121510891855565254344227 207182266337783347881516341)
  ·
    refine ⟨19423337469167188863892157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207182266337783347881516341 19423337469167188863892157)
    ·
      refine ⟨7283751550937695823959559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19423337469167188863892157 7283751550937695823959559)
      ·
        refine ⟨10925627326406543735939339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283751550937695823959559 10925627326406543735939339)
        ·
          refine ⟨16388440989609815603909009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10925627326406543735939339 16388440989609815603909009)
          ·
            refine ⟨12291330742207361702931757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16388440989609815603909009 12291330742207361702931757)
            ·
              refine ⟨4609249028327760638599409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12291330742207361702931757 4609249028327760638599409)
              ·
                refine ⟨3456936771245820478949557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4609249028327760638599409 3456936771245820478949557)
                ·
                  refine ⟨324087822304295669901521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456936771245820478949557 324087822304295669901521)
                  ·
                    rfl

theorem cell23_5680429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_5680429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680429 prefixEnd_5680429 := by exact prefixLift 5680429
  have htrace : WordTrace (prefixWord ++ tailWord_5680429) baseStart_5680429 baseEnd_5680429 := by
    simpa [prefixWord, tailWord_5680429, baseEnd_5680429] using wordTrace_append hprefix tailTrace_5680429
  have hstable : (prefixWord ++ tailWord_5680429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680429).length < 2 ^ (prefixWord ++ tailWord_5680429).sum := by decide
  have hdescent : baseEnd_5680429 < baseStart_5680429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680448 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_5680448 : Nat := 118140960795 + 5680448 * 2 ^ 59
def prefixEnd_5680448 : Nat := 4983230072969 + 3 ^ 40 * 5680448 * 2
def baseEnd_5680448 : Nat := 2916800156871096454776101

theorem tailTrace_5680448 : CollatzResearch.WordTrace tailWord_5680448 prefixEnd_5680448 2916800156871096454776101 := by
  unfold tailWord_5680448
  simp only [CollatzResearch.WordTrace]
  refine ⟨103591479662357257063228999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138121972883143009417638665 103591479662357257063228999)
  ·
    refine ⟨155387219493535885594843499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103591479662357257063228999 155387219493535885594843499)
    ·
      refine ⟨233080829240303828392265249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155387219493535885594843499 233080829240303828392265249)
      ·
        refine ⟨174810621930227871294198937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233080829240303828392265249 174810621930227871294198937)
        ·
          refine ⟨131107966447670903470649203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174810621930227871294198937 131107966447670903470649203)
          ·
            refine ⟨196661949671506355205973805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131107966447670903470649203 196661949671506355205973805)
            ·
              refine ⟨73748231126814883202240177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196661949671506355205973805 73748231126814883202240177)
              ·
                refine ⟨55311173345111162401680133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73748231126814883202240177 55311173345111162401680133)
                ·
                  refine ⟨10370845002208342950315025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55311173345111162401680133 10370845002208342950315025)
                  ·
                    refine ⟨7778133751656257212736269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10370845002208342950315025 7778133751656257212736269)
                    ·
                      refine ⟨2916800156871096454776101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778133751656257212736269 2916800156871096454776101)
                      ·
                        rfl

theorem cell23_5680448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_5680448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680448 prefixEnd_5680448 := by exact prefixLift 5680448
  have htrace : WordTrace (prefixWord ++ tailWord_5680448) baseStart_5680448 baseEnd_5680448 := by
    simpa [prefixWord, tailWord_5680448, baseEnd_5680448] using wordTrace_append hprefix tailTrace_5680448
  have hstable : (prefixWord ++ tailWord_5680448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680448).length < 2 ^ (prefixWord ++ tailWord_5680448).sum := by decide
  have hdescent : baseEnd_5680448 < baseStart_5680448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680465 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 3]
def baseStart_5680465 : Nat := 118140960795 + 5680465 * 2 ^ 59
def prefixEnd_5680465 : Nat := 4983230072969 + 3 ^ 40 * 5680465 * 2
def baseEnd_5680465 : Nat := 2916808886042222888263523

theorem tailTrace_5680465 : CollatzResearch.WordTrace tailWord_5680465 prefixEnd_5680465 2916808886042222888263523 := by
  unfold tailWord_5680465
  simp only [CollatzResearch.WordTrace]
  refine ⟨207183579365652926029826849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138122386243768617353217899 207183579365652926029826849)
  ·
    refine ⟨155387684524239694522370137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207183579365652926029826849 155387684524239694522370137)
    ·
      refine ⟨116540763393179770891777603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155387684524239694522370137 116540763393179770891777603)
      ·
        refine ⟨174811145089769656337666405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116540763393179770891777603 174811145089769656337666405)
        ·
          refine ⟨32777089704331810563312451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174811145089769656337666405 32777089704331810563312451)
          ·
            refine ⟨49165634556497715844968677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32777089704331810563312451 49165634556497715844968677)
            ·
              refine ⟨9218556479343321720931627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49165634556497715844968677 9218556479343321720931627)
              ·
                refine ⟨13827834719014982581397441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9218556479343321720931627 13827834719014982581397441)
                ·
                  refine ⟨10370876039261236936048081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13827834719014982581397441 10370876039261236936048081)
                  ·
                    refine ⟨7778157029445927702036061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10370876039261236936048081 7778157029445927702036061)
                    ·
                      refine ⟨2916808886042222888263523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778157029445927702036061 2916808886042222888263523)
                      ·
                        rfl

theorem cell23_5680465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_5680465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680465 prefixEnd_5680465 := by exact prefixLift 5680465
  have htrace : WordTrace (prefixWord ++ tailWord_5680465) baseStart_5680465 baseEnd_5680465 := by
    simpa [prefixWord, tailWord_5680465, baseEnd_5680465] using wordTrace_append hprefix tailTrace_5680465
  have hstable : (prefixWord ++ tailWord_5680465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680465).length < 2 ^ (prefixWord ++ tailWord_5680465).sum := by decide
  have hdescent : baseEnd_5680465 < baseStart_5680465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680491 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7]
def baseStart_5680491 : Nat := 118140960795 + 5680491 * 2 ^ 59
def prefixEnd_5680491 : Nat := 4983230072969 + 3 ^ 40 * 5680491 * 2
def baseEnd_5680491 : Nat := 2916822236539239786538403

theorem tailTrace_5680491 : CollatzResearch.WordTrace tailWord_5680491 prefixEnd_5680491 2916822236539239786538403 := by
  unfold tailWord_5680491
  simp only [CollatzResearch.WordTrace]
  refine ⟨207184527663558732470273327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138123018442372488313515551 207184527663558732470273327)
  ·
    refine ⟨310776791495338098705409991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207184527663558732470273327 310776791495338098705409991)
    ·
      refine ⟨466165187243007148058114987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310776791495338098705409991 466165187243007148058114987)
      ·
        refine ⟨699247780864510722087172481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466165187243007148058114987 699247780864510722087172481)
        ·
          refine ⟨524435835648383041565379361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699247780864510722087172481 524435835648383041565379361)
          ·
            refine ⟨393326876736287281174034521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524435835648383041565379361 393326876736287281174034521)
            ·
              refine ⟨294995157552215460880525891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393326876736287281174034521 294995157552215460880525891)
              ·
                refine ⟨442492736328323191320788837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294995157552215460880525891 442492736328323191320788837)
                ·
                  refine ⟨82967388061560598372647907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 442492736328323191320788837 82967388061560598372647907)
                  ·
                    refine ⟨124451082092340897558971861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82967388061560598372647907 124451082092340897558971861)
                    ·
                      refine ⟨2916822236539239786538403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124451082092340897558971861 2916822236539239786538403)
                      ·
                        rfl

theorem cell23_5680491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_5680491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680491 prefixEnd_5680491 := by exact prefixLift 5680491
  have htrace : WordTrace (prefixWord ++ tailWord_5680491) baseStart_5680491 baseEnd_5680491 := by
    simpa [prefixWord, tailWord_5680491, baseEnd_5680491] using wordTrace_append hprefix tailTrace_5680491
  have hstable : (prefixWord ++ tailWord_5680491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680491).length < 2 ^ (prefixWord ++ tailWord_5680491).sum := by decide
  have hdescent : baseEnd_5680491 < baseStart_5680491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680495 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 3]
def baseStart_5680495 : Nat := 118140960795 + 5680495 * 2 ^ 59
def prefixEnd_5680495 : Nat := 4983230072969 + 3 ^ 40 * 5680495 * 2
def baseEnd_5680495 : Nat := 2916824290461857770888385

theorem tailTrace_5680495 : CollatzResearch.WordTrace tailWord_5680495 prefixEnd_5680495 2916824290461857770888385 := by
  unfold tailWord_5680495
  simp only [CollatzResearch.WordTrace]
  refine ⟨207184673555544241153418939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138123115703696160768945959 207184673555544241153418939)
  ·
    refine ⟨310777010333316361730128409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207184673555544241153418939 310777010333316361730128409)
    ·
      refine ⟨233082757749987271297596307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310777010333316361730128409 233082757749987271297596307)
      ·
        refine ⟨349624136624980906946394461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233082757749987271297596307 349624136624980906946394461)
        ·
          refine ⟨131109051234367840104897923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349624136624980906946394461 131109051234367840104897923)
          ·
            refine ⟨196663576851551760157346885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131109051234367840104897923 196663576851551760157346885)
            ·
              refine ⟨36874420659665955029502541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196663576851551760157346885 36874420659665955029502541)
              ·
                refine ⟨13827907747374733136063453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36874420659665955029502541 13827907747374733136063453)
                ·
                  refine ⟨5185465405265524926023795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13827907747374733136063453 5185465405265524926023795)
                  ·
                    refine ⟨7778198107898287389035693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185465405265524926023795 7778198107898287389035693)
                    ·
                      refine ⟨2916824290461857770888385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778198107898287389035693 2916824290461857770888385)
                      ·
                        rfl

theorem cell23_5680495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 3, 1, 3].length) (baseStart_5680495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680495 prefixEnd_5680495 := by exact prefixLift 5680495
  have htrace : WordTrace (prefixWord ++ tailWord_5680495) baseStart_5680495 baseEnd_5680495 := by
    simpa [prefixWord, tailWord_5680495, baseEnd_5680495] using wordTrace_append hprefix tailTrace_5680495
  have hstable : (prefixWord ++ tailWord_5680495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680495).length < 2 ^ (prefixWord ++ tailWord_5680495).sum := by decide
  have hdescent : baseEnd_5680495 < baseStart_5680495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680498 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_5680498 : Nat := 118140960795 + 5680498 * 2 ^ 59
def prefixEnd_5680498 : Nat := 4983230072969 + 3 ^ 40 * 5680498 * 2
def baseEnd_5680498 : Nat := 972275276967940419716957

theorem tailTrace_5680498 : CollatzResearch.WordTrace tailWord_5680498 prefixEnd_5680498 972275276967940419716957 := by
  unfold tailWord_5680498
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796195743633343166444537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138123188649688915110518765 51796195743633343166444537)
  ·
    refine ⟨38847146807725007374833403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51796195743633343166444537 38847146807725007374833403)
    ·
      refine ⟨58270720211587511062250105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38847146807725007374833403 58270720211587511062250105)
      ·
        refine ⟨43703040158690633296687579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58270720211587511062250105 43703040158690633296687579)
        ·
          refine ⟨65554560238035949945031369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43703040158690633296687579 65554560238035949945031369)
          ·
            refine ⟨49165920178526962458773527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65554560238035949945031369 49165920178526962458773527)
            ·
              refine ⟨73748880267790443688160291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49165920178526962458773527 73748880267790443688160291)
              ·
                refine ⟨110623320401685665532240437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73748880267790443688160291 110623320401685665532240437)
                ·
                  refine ⟨10370936287658031143647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110623320401685665532240437 10370936287658031143647541)
                  ·
                    refine ⟨972275276967940419716957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10370936287658031143647541 972275276967940419716957)
                    ·
                      rfl

theorem cell23_5680498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_5680498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680498 prefixEnd_5680498 := by exact prefixLift 5680498
  have htrace : WordTrace (prefixWord ++ tailWord_5680498) baseStart_5680498 baseEnd_5680498 := by
    simpa [prefixWord, tailWord_5680498, baseEnd_5680498] using wordTrace_append hprefix tailTrace_5680498
  have hstable : (prefixWord ++ tailWord_5680498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680498).length < 2 ^ (prefixWord ++ tailWord_5680498).sum := by decide
  have hdescent : baseEnd_5680498 < baseStart_5680498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680505 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 4, 3, 2]
def baseStart_5680505 : Nat := 118140960795 + 5680505 * 2 ^ 59
def prefixEnd_5680505 : Nat := 4983230072969 + 3 ^ 40 * 5680505 * 2
def baseEnd_5680505 : Nat := 2916829425268402731763339

theorem tailTrace_5680505 : CollatzResearch.WordTrace tailWord_5680505 prefixEnd_5680505 2916829425268402731763339 := by
  unfold tailWord_5680505
  simp only [CollatzResearch.WordTrace]
  refine ⟨207185038285508012861282969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138123358857005341907521979 207185038285508012861282969)
  ·
    refine ⟨155388778714131009645962227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207185038285508012861282969 155388778714131009645962227)
    ·
      refine ⟨233083168071196514468943341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155388778714131009645962227 233083168071196514468943341)
      ·
        refine ⟨87406188026698692925853753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233083168071196514468943341 87406188026698692925853753)
        ·
          refine ⟨65554641020024019694390315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87406188026698692925853753 65554641020024019694390315)
          ·
            refine ⟨98331961530036029541585473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65554641020024019694390315 98331961530036029541585473)
            ·
              refine ⟨73748971147527022156189105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98331961530036029541585473 73748971147527022156189105)
              ·
                refine ⟨55311728360645266617141829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73748971147527022156189105 55311728360645266617141829)
                ·
                  refine ⟨10370949067620987490714093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55311728360645266617141829 10370949067620987490714093)
                  ·
                    refine ⟨3889105900357870309017785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10370949067620987490714093 3889105900357870309017785)
                    ·
                      refine ⟨2916829425268402731763339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889105900357870309017785 2916829425268402731763339)
                      ·
                        rfl

theorem cell23_5680505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_5680505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680505 prefixEnd_5680505 := by exact prefixLift 5680505
  have htrace : WordTrace (prefixWord ++ tailWord_5680505) baseStart_5680505 baseEnd_5680505 := by
    simpa [prefixWord, tailWord_5680505, baseEnd_5680505] using wordTrace_append hprefix tailTrace_5680505
  have hstable : (prefixWord ++ tailWord_5680505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680505).length < 2 ^ (prefixWord ++ tailWord_5680505).sum := by decide
  have hdescent : baseEnd_5680505 < baseStart_5680505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680532 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_5680532 : Nat := 118140960795 + 5680532 * 2 ^ 59
def prefixEnd_5680532 : Nat := 4983230072969 + 3 ^ 40 * 5680532 * 2
def baseEnd_5680532 : Nat := 972281096415358042041905

theorem tailTrace_5680532 : CollatzResearch.WordTrace tailWord_5680532 prefixEnd_5680532 972281096415358042041905 := by
  unfold tailWord_5680532
  simp only [CollatzResearch.WordTrace]
  refine ⟨103593011528205098236257925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138124015370940130981677233 103593011528205098236257925)
  ·
    refine ⟨19423689661538455919298361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103593011528205098236257925 19423689661538455919298361)
    ·
      refine ⟨14567767246153841939473771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19423689661538455919298361 14567767246153841939473771)
      ·
        refine ⟨21851650869230762909210657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14567767246153841939473771 21851650869230762909210657)
        ·
          refine ⟨16388738151923072181907993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21851650869230762909210657 16388738151923072181907993)
          ·
            refine ⟨12291553613942304136430995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16388738151923072181907993 12291553613942304136430995)
            ·
              refine ⟨18437330420913456204646493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291553613942304136430995 18437330420913456204646493)
              ·
                refine ⟨6913998907842546076742435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18437330420913456204646493 6913998907842546076742435)
                ·
                  refine ⟨10370998361763819115113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913998907842546076742435 10370998361763819115113653)
                  ·
                    refine ⟨972281096415358042041905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10370998361763819115113653 972281096415358042041905)
                    ·
                      rfl

theorem cell23_5680532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_5680532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680532 prefixEnd_5680532 := by exact prefixLift 5680532
  have htrace : WordTrace (prefixWord ++ tailWord_5680532) baseStart_5680532 baseEnd_5680532 := by
    simpa [prefixWord, tailWord_5680532, baseEnd_5680532] using wordTrace_append hprefix tailTrace_5680532
  have hstable : (prefixWord ++ tailWord_5680532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680532).length < 2 ^ (prefixWord ++ tailWord_5680532).sum := by decide
  have hdescent : baseEnd_5680532 < baseStart_5680532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680548 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_5680548 : Nat := 118140960795 + 5680548 * 2 ^ 59
def prefixEnd_5680548 : Nat := 4983230072969 + 3 ^ 40 * 5680548 * 2
def baseEnd_5680548 : Nat := 2916851504936546063525641

theorem tailTrace_5680548 : CollatzResearch.WordTrace tailWord_5680548 prefixEnd_5680548 2916851504936546063525641 := by
  unfold tailWord_5680548
  simp only [CollatzResearch.WordTrace]
  refine ⟨103593303312176115602549149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138124404416234820803398865 103593303312176115602549149)
  ·
    refine ⟨38847488742066043350955931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103593303312176115602549149 38847488742066043350955931)
    ·
      refine ⟨58271233113099065026433897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38847488742066043350955931 58271233113099065026433897)
      ·
        refine ⟨43703424834824298769825423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58271233113099065026433897 43703424834824298769825423)
        ·
          refine ⟨65555137252236448154738135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43703424834824298769825423 65555137252236448154738135)
          ·
            refine ⟨98332705878354672232107203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65555137252236448154738135 98332705878354672232107203)
            ·
              refine ⟨147499058817532008348160805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98332705878354672232107203 147499058817532008348160805)
              ·
                refine ⟨27656073528287251565280151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147499058817532008348160805 27656073528287251565280151)
                ·
                  refine ⟨41484110292430877347920227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27656073528287251565280151 41484110292430877347920227)
                  ·
                    refine ⟨62226165438646316021880341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41484110292430877347920227 62226165438646316021880341)
                    ·
                      refine ⟨2916851504936546063525641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62226165438646316021880341 2916851504936546063525641)
                      ·
                        rfl

theorem cell23_5680548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_5680548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680548 prefixEnd_5680548 := by exact prefixLift 5680548
  have htrace : WordTrace (prefixWord ++ tailWord_5680548) baseStart_5680548 baseEnd_5680548 := by
    simpa [prefixWord, tailWord_5680548, baseEnd_5680548] using wordTrace_append hprefix tailTrace_5680548
  have hstable : (prefixWord ++ tailWord_5680548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680548).length < 2 ^ (prefixWord ++ tailWord_5680548).sum := by decide
  have hdescent : baseEnd_5680548 < baseStart_5680548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680565 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_5680565 : Nat := 118140960795 + 5680565 * 2 ^ 59
def prefixEnd_5680565 : Nat := 4983230072969 + 3 ^ 40 * 5680565 * 2
def baseEnd_5680565 : Nat := 2916860234107672497013063

theorem tailTrace_5680565 : CollatzResearch.WordTrace tailWord_5680565 prefixEnd_5680565 2916860234107672497013063 := by
  unfold tailWord_5680565
  simp only [CollatzResearch.WordTrace]
  refine ⟨207187226665290643108467149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138124817776860428738978099 207187226665290643108467149)
  ·
    refine ⟨77695209999483991165675181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207187226665290643108467149 77695209999483991165675181)
    ·
      refine ⟨29135703749806496687128193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77695209999483991165675181 29135703749806496687128193)
      ·
        refine ⟨21851777812354872515346145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29135703749806496687128193 21851777812354872515346145)
        ·
          refine ⟨16388833359266154386509609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21851777812354872515346145 16388833359266154386509609)
          ·
            refine ⟨12291625019449615789882207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16388833359266154386509609 12291625019449615789882207)
            ·
              refine ⟨18437437529174423684823311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291625019449615789882207 18437437529174423684823311)
              ·
                refine ⟨27656156293761635527234967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437437529174423684823311 27656156293761635527234967)
                ·
                  refine ⟨41484234440642453290852451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27656156293761635527234967 41484234440642453290852451)
                  ·
                    refine ⟨62226351660963679936278677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41484234440642453290852451 62226351660963679936278677)
                    ·
                      refine ⟨2916860234107672497013063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62226351660963679936278677 2916860234107672497013063)
                      ·
                        rfl

theorem cell23_5680565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_5680565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680565 prefixEnd_5680565 := by exact prefixLift 5680565
  have htrace : WordTrace (prefixWord ++ tailWord_5680565) baseStart_5680565 baseEnd_5680565 := by
    simpa [prefixWord, tailWord_5680565, baseEnd_5680565] using wordTrace_append hprefix tailTrace_5680565
  have hstable : (prefixWord ++ tailWord_5680565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680565).length < 2 ^ (prefixWord ++ tailWord_5680565).sum := by decide
  have hdescent : baseEnd_5680565 < baseStart_5680565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680586 : List Nat := [3, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2]
def baseStart_5680586 : Nat := 118140960795 + 5680586 * 2 ^ 59
def prefixEnd_5680586 : Nat := 4983230072969 + 3 ^ 40 * 5680586 * 2
def baseEnd_5680586 : Nat := 2916871017201416914850467

theorem tailTrace_5680586 : CollatzResearch.WordTrace tailWord_5680586 prefixEnd_5680586 2916871017201416914850467 := by
  unfold tailWord_5680586
  simp only [CollatzResearch.WordTrace]
  refine ⟨51796998149553640923745403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138125328398809709129987741 51796998149553640923745403)
  ·
    refine ⟨77695497224330461385618105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51796998149553640923745403 77695497224330461385618105)
    ·
      refine ⟨58271622918247846039213579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77695497224330461385618105 58271622918247846039213579)
      ·
        refine ⟨87407434377371769058820369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58271622918247846039213579 87407434377371769058820369)
        ·
          refine ⟨65555575783028826794115277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87407434377371769058820369 65555575783028826794115277)
          ·
            refine ⟨24583340918635810047793229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65555575783028826794115277 24583340918635810047793229)
            ·
              refine ⟨9218752844488428767922461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24583340918635810047793229 9218752844488428767922461)
              ·
                refine ⟨3457032316683160787970923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9218752844488428767922461 3457032316683160787970923)
                ·
                  refine ⟨5185548475024741181956385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457032316683160787970923 5185548475024741181956385)
                  ·
                    refine ⟨3889161356268555886467289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185548475024741181956385 3889161356268555886467289)
                    ·
                      refine ⟨2916871017201416914850467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889161356268555886467289 2916871017201416914850467)
                      ·
                        rfl

theorem cell23_5680586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_5680586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680586 prefixEnd_5680586 := by exact prefixLift 5680586
  have htrace : WordTrace (prefixWord ++ tailWord_5680586) baseStart_5680586 baseEnd_5680586 := by
    simpa [prefixWord, tailWord_5680586, baseEnd_5680586] using wordTrace_append hprefix tailTrace_5680586
  have hstable : (prefixWord ++ tailWord_5680586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680586).length < 2 ^ (prefixWord ++ tailWord_5680586).sum := by decide
  have hdescent : baseEnd_5680586 < baseStart_5680586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680602 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_5680602 : Nat := 118140960795 + 5680602 * 2 ^ 59
def prefixEnd_5680602 : Nat := 4983230072969 + 3 ^ 40 * 5680602 * 2
def baseEnd_5680602 : Nat := 2916879232891888852250393

theorem tailTrace_5680602 : CollatzResearch.WordTrace tailWord_5680602 prefixEnd_5680602 2916879232891888852250393 := by
  unfold tailWord_5680602
  simp only [CollatzResearch.WordTrace]
  refine ⟨51797144041539149606891015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138125717444104398951709373 51797144041539149606891015)
  ·
    refine ⟨77695716062308724410336523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51797144041539149606891015 77695716062308724410336523)
    ·
      refine ⟨116543574093463086615504785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77695716062308724410336523 116543574093463086615504785)
      ·
        refine ⟨87407680570097314961628589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116543574093463086615504785 87407680570097314961628589)
        ·
          refine ⟨32777880213786493110610721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87407680570097314961628589 32777880213786493110610721)
          ·
            refine ⟨24583410160339869832958041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32777880213786493110610721 24583410160339869832958041)
            ·
              refine ⟨18437557620254902374718531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24583410160339869832958041 18437557620254902374718531)
              ·
                refine ⟨27656336430382353562077797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437557620254902374718531 27656336430382353562077797)
                ·
                  refine ⟨5185563080696691292889587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27656336430382353562077797 5185563080696691292889587)
                  ·
                    refine ⟨7778344621045036939334381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5185563080696691292889587 7778344621045036939334381)
                    ·
                      refine ⟨2916879232891888852250393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778344621045036939334381 2916879232891888852250393)
                      ·
                        rfl

theorem cell23_5680602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_5680602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680602 prefixEnd_5680602 := by exact prefixLift 5680602
  have htrace : WordTrace (prefixWord ++ tailWord_5680602) baseStart_5680602 baseEnd_5680602 := by
    simpa [prefixWord, tailWord_5680602, baseEnd_5680602] using wordTrace_append hprefix tailTrace_5680602
  have hstable : (prefixWord ++ tailWord_5680602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680602).length < 2 ^ (prefixWord ++ tailWord_5680602).sum := by decide
  have hdescent : baseEnd_5680602 < baseStart_5680602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680659 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 2, 2, 2]
def baseStart_5680659 : Nat := 118140960795 + 5680659 * 2 ^ 59
def prefixEnd_5680659 : Nat := 4983230072969 + 3 ^ 40 * 5680659 * 2
def baseEnd_5680659 : Nat := 2916908501289195129237631

theorem tailTrace_5680659 : CollatzResearch.WordTrace tailWord_5680659 prefixEnd_5680659 2916908501289195129237631 := by
  unfold tailWord_5680659
  simp only [CollatzResearch.WordTrace]
  refine ⟨207190655126950097162389031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138127103417966731441592687 207190655126950097162389031)
  ·
    refine ⟨310785982690425145743583547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207190655126950097162389031 310785982690425145743583547)
    ·
      refine ⟨466178974035637718615375321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310785982690425145743583547 466178974035637718615375321)
      ·
        refine ⟨349634230526728288961531491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466178974035637718615375321 349634230526728288961531491)
        ·
          refine ⟨524451345790092433442297237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349634230526728288961531491 524451345790092433442297237)
          ·
            refine ⟨24583656833910582817607683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 524451345790092433442297237 24583656833910582817607683)
            ·
              refine ⟨36875485250865874226411525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24583656833910582817607683 36875485250865874226411525)
              ·
                refine ⟨6914153484537351417452161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36875485250865874226411525 6914153484537351417452161)
                ·
                  refine ⟨5185615113403013563089121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6914153484537351417452161 5185615113403013563089121)
                  ·
                    refine ⟨3889211335052260172316841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185615113403013563089121 3889211335052260172316841)
                    ·
                      refine ⟨2916908501289195129237631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889211335052260172316841 2916908501289195129237631)
                      ·
                        rfl

theorem cell23_5680659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2, 2, 2].length) (baseStart_5680659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680659 prefixEnd_5680659 := by exact prefixLift 5680659
  have htrace : WordTrace (prefixWord ++ tailWord_5680659) baseStart_5680659 baseEnd_5680659 := by
    simpa [prefixWord, tailWord_5680659, baseEnd_5680659] using wordTrace_append hprefix tailTrace_5680659
  have hstable : (prefixWord ++ tailWord_5680659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680659).length < 2 ^ (prefixWord ++ tailWord_5680659).sum := by decide
  have hdescent : baseEnd_5680659 < baseStart_5680659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680672 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5680672 : Nat := 118140960795 + 5680672 * 2 ^ 59
def prefixEnd_5680672 : Nat := 4983230072969 + 3 ^ 40 * 5680672 * 2
def baseEnd_5680672 : Nat := 2916915176537703578375071

theorem tailTrace_5680672 : CollatzResearch.WordTrace tailWord_5680672 prefixEnd_5680672 2916915176537703578375071 := by
  unfold tailWord_5680672
  simp only [CollatzResearch.WordTrace]
  refine ⟨103595564637951500191306135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138127419517268666921741513 103595564637951500191306135)
  ·
    refine ⟨155393346956927250286959203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103595564637951500191306135 155393346956927250286959203)
    ·
      refine ⟨233090020435390875430438805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155393346956927250286959203 233090020435390875430438805)
      ·
        refine ⟨10926094707908947285801819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233090020435390875430438805 10926094707908947285801819)
        ·
          refine ⟨16389142061863420928702729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10926094707908947285801819 16389142061863420928702729)
          ·
            refine ⟨12291856546397565696527047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16389142061863420928702729 12291856546397565696527047)
            ·
              refine ⟨18437784819596348544790571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291856546397565696527047 18437784819596348544790571)
              ·
                refine ⟨27656677229394522817185857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437784819596348544790571 27656677229394522817185857)
                ·
                  refine ⟨20742507922045892112889393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27656677229394522817185857 20742507922045892112889393)
                  ·
                    refine ⟨15556880941534419084667045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20742507922045892112889393 15556880941534419084667045)
                    ·
                      refine ⟨2916915176537703578375071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15556880941534419084667045 2916915176537703578375071)
                      ·
                        rfl

theorem cell23_5680672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5680672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680672 prefixEnd_5680672 := by exact prefixLift 5680672
  have htrace : WordTrace (prefixWord ++ tailWord_5680672) baseStart_5680672 baseEnd_5680672 := by
    simpa [prefixWord, tailWord_5680672, baseEnd_5680672] using wordTrace_append hprefix tailTrace_5680672
  have hstable : (prefixWord ++ tailWord_5680672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680672).length < 2 ^ (prefixWord ++ tailWord_5680672).sum := by decide
  have hdescent : baseEnd_5680672 < baseStart_5680672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680695 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 7]
def baseStart_5680695 : Nat := 118140960795 + 5680695 * 2 ^ 59
def prefixEnd_5680695 : Nat := 4983230072969 + 3 ^ 40 * 5680695 * 2
def baseEnd_5680695 : Nat := 972308995530918996129155

theorem tailTrace_5680695 : CollatzResearch.WordTrace tailWord_5680695 prefixEnd_5680695 972308995530918996129155 := by
  unfold tailWord_5680695
  simp only [CollatzResearch.WordTrace]
  refine ⟨207191968154819675310699539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138127978769879783540466359 207191968154819675310699539)
  ·
    refine ⟨310787952232229512966049309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207191968154819675310699539 310787952232229512966049309)
    ·
      refine ⟨116545482087086067362268491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310787952232229512966049309 116545482087086067362268491)
      ·
        refine ⟨174818223130629101043402737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116545482087086067362268491 174818223130629101043402737)
        ·
          refine ⟨131113667347971825782552053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174818223130629101043402737 131113667347971825782552053)
          ·
            refine ⟨12291906313872358667114255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131113667347971825782552053 12291906313872358667114255)
            ·
              refine ⟨18437859470808538000671383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12291906313872358667114255 18437859470808538000671383)
              ·
                refine ⟨27656789206212807001007075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18437859470808538000671383 27656789206212807001007075)
                ·
                  refine ⟨41485183809319210501510613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27656789206212807001007075 41485183809319210501510613)
                  ·
                    refine ⟨972308995530918996129155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41485183809319210501510613 972308995530918996129155)
                    ·
                      rfl

theorem cell23_5680695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_5680695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680695 prefixEnd_5680695 := by exact prefixLift 5680695
  have htrace : WordTrace (prefixWord ++ tailWord_5680695) baseStart_5680695 baseEnd_5680695 := by
    simpa [prefixWord, tailWord_5680695, baseEnd_5680695] using wordTrace_append hprefix tailTrace_5680695
  have hstable : (prefixWord ++ tailWord_5680695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680695).length < 2 ^ (prefixWord ++ tailWord_5680695).sum := by decide
  have hdescent : baseEnd_5680695 < baseStart_5680695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680715 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4]
def baseStart_5680715 : Nat := 118140960795 + 5680715 * 2 ^ 59
def prefixEnd_5680715 : Nat := 4983230072969 + 3 ^ 40 * 5680715 * 2
def baseEnd_5680715 : Nat := 2916937256205846910137373

theorem tailTrace_5680715 : CollatzResearch.WordTrace tailWord_5680715 prefixEnd_5680715 2916937256205846910137373 := by
  unfold tailWord_5680715
  simp only [CollatzResearch.WordTrace]
  refine ⟨207192697614747218726427599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138128465076498145817618399 207192697614747218726427599)
  ·
    refine ⟨310789046422120828089641399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207192697614747218726427599 310789046422120828089641399)
    ·
      refine ⟨466183569633181242134462099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310789046422120828089641399 466183569633181242134462099)
      ·
        refine ⟨699275354449771863201693149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466183569633181242134462099 699275354449771863201693149)
        ·
          refine ⟨262228257918664448700634931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 699275354449771863201693149 262228257918664448700634931)
          ·
            refine ⟨393342386877996673050952397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262228257918664448700634931 393342386877996673050952397)
            ·
              refine ⟨147503395079248752394107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393342386877996673050952397 147503395079248752394107149)
              ·
                refine ⟨55313773154718282147790181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147503395079248752394107149 55313773154718282147790181)
                ·
                  refine ⟨10371332466509677902710659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55313773154718282147790181 10371332466509677902710659)
                  ·
                    refine ⟨15556998699764516854065989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10371332466509677902710659 15556998699764516854065989)
                    ·
                      refine ⟨2916937256205846910137373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15556998699764516854065989 2916937256205846910137373)
                      ·
                        rfl

theorem cell23_5680715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 4].length) (baseStart_5680715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680715 prefixEnd_5680715 := by exact prefixLift 5680715
  have htrace : WordTrace (prefixWord ++ tailWord_5680715) baseStart_5680715 baseEnd_5680715 := by
    simpa [prefixWord, tailWord_5680715, baseEnd_5680715] using wordTrace_append hprefix tailTrace_5680715
  have hstable : (prefixWord ++ tailWord_5680715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680715).length < 2 ^ (prefixWord ++ tailWord_5680715).sum := by decide
  have hdescent : baseEnd_5680715 < baseStart_5680715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680732 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_5680732 : Nat := 118140960795 + 5680732 * 2 ^ 59
def prefixEnd_5680732 : Nat := 4983230072969 + 3 ^ 40 * 5680732 * 2
def baseEnd_5680732 : Nat := 2916945985376973343624795

theorem tailTrace_5680732 : CollatzResearch.WordTrace tailWord_5680732 prefixEnd_5680732 2916945985376973343624795 := by
  unfold tailWord_5680732
  simp only [CollatzResearch.WordTrace]
  refine ⟨103596658827842815314898225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138128878437123753753197633 103596658827842815314898225)
  ·
    refine ⟨77697494120882111486173669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103596658827842815314898225 77697494120882111486173669)
    ·
      refine ⟨14568280147665395903657563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77697494120882111486173669 14568280147665395903657563)
      ·
        refine ⟨21852420221498093855486345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14568280147665395903657563 21852420221498093855486345)
        ·
          refine ⟨16389315166123570391614759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21852420221498093855486345 16389315166123570391614759)
          ·
            refine ⟨24583972749185355587422139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16389315166123570391614759 24583972749185355587422139)
            ·
              refine ⟨36875959123778033381133209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24583972749185355587422139 36875959123778033381133209)
              ·
                refine ⟨27656969342833525035849907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36875959123778033381133209 27656969342833525035849907)
                ·
                  refine ⟨41485454014250287553774861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27656969342833525035849907 41485454014250287553774861)
                  ·
                    refine ⟨15557045255343857832665573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41485454014250287553774861 15557045255343857832665573)
                    ·
                      refine ⟨2916945985376973343624795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15557045255343857832665573 2916945985376973343624795)
                      ·
                        rfl

theorem cell23_5680732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_5680732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680732 prefixEnd_5680732 := by exact prefixLift 5680732
  have htrace : WordTrace (prefixWord ++ tailWord_5680732) baseStart_5680732 baseEnd_5680732 := by
    simpa [prefixWord, tailWord_5680732, baseEnd_5680732] using wordTrace_append hprefix tailTrace_5680732
  have hstable : (prefixWord ++ tailWord_5680732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680732).length < 2 ^ (prefixWord ++ tailWord_5680732).sum := by decide
  have hdescent : baseEnd_5680732 < baseStart_5680732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680752 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_5680752 : Nat := 118140960795 + 5680752 * 2 ^ 59
def prefixEnd_5680752 : Nat := 4983230072969 + 3 ^ 40 * 5680752 * 2
def baseEnd_5680752 : Nat := 2916956254990063265374703

theorem tailTrace_5680752 : CollatzResearch.WordTrace tailWord_5680752 prefixEnd_5680752 2916956254990063265374703 := by
  unfold tailWord_5680752
  simp only [CollatzResearch.WordTrace]
  refine ⟨103597023557806587022762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138129364743742116030349673 103597023557806587022762255)
  ·
    refine ⟨155395535336709880534143383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103597023557806587022762255 155395535336709880534143383)
    ·
      refine ⟨233093303005064820801215075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155395535336709880534143383 233093303005064820801215075)
      ·
        refine ⟨349639954507597231201822613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233093303005064820801215075 349639954507597231201822613)
        ·
          refine ⟨16389372867543620212585435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 349639954507597231201822613 16389372867543620212585435)
          ·
            refine ⟨24584059301315430318878153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16389372867543620212585435 24584059301315430318878153)
            ·
              refine ⟨18438044475986572739158615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24584059301315430318878153 18438044475986572739158615)
              ·
                refine ⟨27657066713979859108737923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18438044475986572739158615 27657066713979859108737923)
                ·
                  refine ⟨41485600070969788663106885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27657066713979859108737923 41485600070969788663106885)
                  ·
                    refine ⟨7778550013306835374332541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41485600070969788663106885 7778550013306835374332541)
                    ·
                      refine ⟨2916956254990063265374703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778550013306835374332541 2916956254990063265374703)
                      ·
                        rfl

theorem cell23_5680752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_5680752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680752 prefixEnd_5680752 := by exact prefixLift 5680752
  have htrace : WordTrace (prefixWord ++ tailWord_5680752) baseStart_5680752 baseEnd_5680752 := by
    simpa [prefixWord, tailWord_5680752, baseEnd_5680752] using wordTrace_append hprefix tailTrace_5680752
  have hstable : (prefixWord ++ tailWord_5680752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680752).length < 2 ^ (prefixWord ++ tailWord_5680752).sum := by decide
  have hdescent : baseEnd_5680752 < baseStart_5680752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680769 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 3]
def baseStart_5680769 : Nat := 118140960795 + 5680769 * 2 ^ 59
def prefixEnd_5680769 : Nat := 4983230072969 + 3 ^ 40 * 5680769 * 2
def baseEnd_5680769 : Nat := 2916964984161189698862125

theorem tailTrace_5680769 : CollatzResearch.WordTrace tailWord_5680769 prefixEnd_5680769 2916964984161189698862125 := by
  unfold tailWord_5680769
  simp only [CollatzResearch.WordTrace]
  refine ⟨207194667156551585948893361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138129778104367723965928907 207194667156551585948893361)
  ·
    refine ⟨155396000367413689461670021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207194667156551585948893361 155396000367413689461670021)
    ·
      refine ⟨29136750068890066774063129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155396000367413689461670021 29136750068890066774063129)
      ·
        refine ⟨21852562551667550080547347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29136750068890066774063129 21852562551667550080547347)
        ·
          refine ⟨32778843827501325120821021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21852562551667550080547347 32778843827501325120821021)
          ·
            refine ⟨12292066435312996920307883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32778843827501325120821021 12292066435312996920307883)
            ·
              refine ⟨18438099652969495380461825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12292066435312996920307883 18438099652969495380461825)
              ·
                refine ⟨13828574739727121535346369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18438099652969495380461825 13828574739727121535346369)
                ·
                  refine ⟨10371431054795341151509777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13828574739727121535346369 10371431054795341151509777)
                  ·
                    refine ⟨7778573291096505863632333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10371431054795341151509777 7778573291096505863632333)
                    ·
                      refine ⟨2916964984161189698862125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778573291096505863632333 2916964984161189698862125)
                      ·
                        rfl

theorem cell23_5680769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_5680769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680769 prefixEnd_5680769 := by exact prefixLift 5680769
  have htrace : WordTrace (prefixWord ++ tailWord_5680769) baseStart_5680769 baseEnd_5680769 := by
    simpa [prefixWord, tailWord_5680769, baseEnd_5680769] using wordTrace_append hprefix tailTrace_5680769
  have hstable : (prefixWord ++ tailWord_5680769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680769).length < 2 ^ (prefixWord ++ tailWord_5680769).sum := by decide
  have hdescent : baseEnd_5680769 < baseStart_5680769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680819 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 1, 5]
def baseStart_5680819 : Nat := 118140960795 + 5680819 * 2 ^ 59
def prefixEnd_5680819 : Nat := 4983230072969 + 3 ^ 40 * 5680819 * 2
def baseEnd_5680819 : Nat := 972330219397971501078965

theorem tailTrace_5680819 : CollatzResearch.WordTrace tailWord_5680819 prefixEnd_5680819 972330219397971501078965 := by
  unfold tailWord_5680819
  simp only [CollatzResearch.WordTrace]
  refine ⟨207196490806370444488213511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138130993870913629658809007 207196490806370444488213511)
  ·
    refine ⟨310794736209555666732320267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207196490806370444488213511 310794736209555666732320267)
    ·
      refine ⟨466192104314333500098480401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310794736209555666732320267 466192104314333500098480401)
      ·
        refine ⟨349644078235750125073860301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466192104314333500098480401 349644078235750125073860301)
        ·
          refine ⟨131116529338406296902697613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349644078235750125073860301 131116529338406296902697613)
          ·
            refine ⟨49168698501902361338511605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131116529338406296902697613 49168698501902361338511605)
            ·
              refine ⟨4609565484553346375485463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49168698501902361338511605 4609565484553346375485463)
              ·
                refine ⟨6914348226830019563228195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609565484553346375485463 6914348226830019563228195)
                ·
                  refine ⟨10371522340245029344842293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914348226830019563228195 10371522340245029344842293)
                  ·
                    refine ⟨972330219397971501078965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10371522340245029344842293 972330219397971501078965)
                    ·
                      rfl

theorem cell23_5680819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 5].length) (baseStart_5680819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680819 prefixEnd_5680819 := by exact prefixLift 5680819
  have htrace : WordTrace (prefixWord ++ tailWord_5680819) baseStart_5680819 baseEnd_5680819 := by
    simpa [prefixWord, tailWord_5680819, baseEnd_5680819] using wordTrace_append hprefix tailTrace_5680819
  have hstable : (prefixWord ++ tailWord_5680819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680819).length < 2 ^ (prefixWord ++ tailWord_5680819).sum := by decide
  have hdescent : baseEnd_5680819 < baseStart_5680819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680849 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_5680849 : Nat := 118140960795 + 5680849 * 2 ^ 59
def prefixEnd_5680849 : Nat := 4983230072969 + 3 ^ 40 * 5680849 * 2
def baseEnd_5680849 : Nat := 972335354204516461953919

theorem tailTrace_5680849 : CollatzResearch.WordTrace tailWord_5680849 prefixEnd_5680849 972335354204516461953919 := by
  unfold tailWord_5680849
  simp only [CollatzResearch.WordTrace]
  refine ⟨207197584996261759611805601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138131723330841173074537067 207197584996261759611805601)
  ·
    refine ⟨155398188747196319708854201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207197584996261759611805601 155398188747196319708854201)
    ·
      refine ⟨116548641560397239781640651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155398188747196319708854201 116548641560397239781640651)
      ·
        refine ⟨174822962340595859672460977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116548641560397239781640651 174822962340595859672460977)
        ·
          refine ⟨131117221755446894754345733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174822962340595859672460977 131117221755446894754345733)
          ·
            refine ⟨24584479079146292766439825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131117221755446894754345733 24584479079146292766439825)
            ·
              refine ⟨18438359309359719574829869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24584479079146292766439825 18438359309359719574829869)
              ·
                refine ⟨6914384741009894840561201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18438359309359719574829869 6914384741009894840561201)
                ·
                  refine ⟨5185788555757421130420901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6914384741009894840561201 5185788555757421130420901)
                  ·
                    refine ⟨972335354204516461953919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5185788555757421130420901 972335354204516461953919)
                    ·
                      rfl

theorem cell23_5680849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_5680849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680849 prefixEnd_5680849 := by exact prefixLift 5680849
  have htrace : WordTrace (prefixWord ++ tailWord_5680849) baseStart_5680849 baseEnd_5680849 := by
    simpa [prefixWord, tailWord_5680849, baseEnd_5680849] using wordTrace_append hprefix tailTrace_5680849
  have hstable : (prefixWord ++ tailWord_5680849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680849).length < 2 ^ (prefixWord ++ tailWord_5680849).sum := by decide
  have hdescent : baseEnd_5680849 < baseStart_5680849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680856 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2]
def baseStart_5680856 : Nat := 118140960795 + 5680856 * 2 ^ 59
def prefixEnd_5680856 : Nat := 4983230072969 + 3 ^ 40 * 5680856 * 2
def baseEnd_5680856 : Nat := 2917009656978130858474225

theorem tailTrace_5680856 : CollatzResearch.WordTrace tailWord_5680856 prefixEnd_5680856 2917009656978130858474225 := by
  unfold tailWord_5680856
  simp only [CollatzResearch.WordTrace]
  refine ⟨103598920153618199903655211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138131893538157599871540281 103598920153618199903655211)
  ·
    refine ⟨155398380230427299855482817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103598920153618199903655211 155398380230427299855482817)
    ·
      refine ⟨116548785172820474891612113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155398380230427299855482817 116548785172820474891612113)
      ·
        refine ⟨87411588879615356168709085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116548785172820474891612113 87411588879615356168709085)
        ·
          refine ⟨32779345829855758563265907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87411588879615356168709085 32779345829855758563265907)
          ·
            refine ⟨49169018744783637844898861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32779345829855758563265907 49169018744783637844898861)
            ·
              refine ⟨18438382029293864191837073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49169018744783637844898861 18438382029293864191837073)
              ·
                refine ⟨13828786521970398143877805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18438382029293864191837073 13828786521970398143877805)
                ·
                  refine ⟨5185794945738899303954177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13828786521970398143877805 5185794945738899303954177)
                  ·
                    refine ⟨3889346209304174477965633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185794945738899303954177 3889346209304174477965633)
                    ·
                      refine ⟨2917009656978130858474225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889346209304174477965633 2917009656978130858474225)
                      ·
                        rfl

theorem cell23_5680856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_5680856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680856 prefixEnd_5680856 := by exact prefixLift 5680856
  have htrace : WordTrace (prefixWord ++ tailWord_5680856) baseStart_5680856 baseEnd_5680856 := by
    simpa [prefixWord, tailWord_5680856, baseEnd_5680856] using wordTrace_append hprefix tailTrace_5680856
  have hstable : (prefixWord ++ tailWord_5680856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680856).length < 2 ^ (prefixWord ++ tailWord_5680856).sum := by decide
  have hdescent : baseEnd_5680856 < baseStart_5680856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680860 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_5680860 : Nat := 118140960795 + 5680860 * 2 ^ 59
def prefixEnd_5680860 : Nat := 4983230072969 + 3 ^ 40 * 5680860 * 2
def baseEnd_5680860 : Nat := 2917011710900748842824207

theorem tailTrace_5680860 : CollatzResearch.WordTrace tailWord_5680860 prefixEnd_5680860 2917011710900748842824207 := by
  unfold tailWord_5680860
  simp only [CollatzResearch.WordTrace]
  refine ⟨103598993099610954245228017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138131990799481272326970689 103598993099610954245228017)
  ·
    refine ⟨77699244824708215683921013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103598993099610954245228017 77699244824708215683921013)
    ·
      refine ⟨7284304202316395220367595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77699244824708215683921013 7284304202316395220367595)
      ·
        refine ⟨10926456303474592830551393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7284304202316395220367595 10926456303474592830551393)
        ·
          refine ⟨8194842227605944622913545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10926456303474592830551393 8194842227605944622913545)
          ·
            refine ⟨6146131670704458467185159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8194842227605944622913545 6146131670704458467185159)
            ·
              refine ⟨9219197506056687700777739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146131670704458467185159 9219197506056687700777739)
              ·
                refine ⟨13828796259085031551166609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9219197506056687700777739 13828796259085031551166609)
                ·
                  refine ⟨10371597194313773663374957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13828796259085031551166609 10371597194313773663374957)
                  ·
                    refine ⟨3889348947867665123765609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10371597194313773663374957 3889348947867665123765609)
                    ·
                      refine ⟨2917011710900748842824207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889348947867665123765609 2917011710900748842824207)
                      ·
                        rfl

theorem cell23_5680860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_5680860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680860 prefixEnd_5680860 := by exact prefixLift 5680860
  have htrace : WordTrace (prefixWord ++ tailWord_5680860) baseStart_5680860 baseEnd_5680860 := by
    simpa [prefixWord, tailWord_5680860, baseEnd_5680860] using wordTrace_append hprefix tailTrace_5680860
  have hstable : (prefixWord ++ tailWord_5680860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680860).length < 2 ^ (prefixWord ++ tailWord_5680860).sum := by decide
  have hdescent : baseEnd_5680860 < baseStart_5680860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680876 : List Nat := [2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 3]
def baseStart_5680876 : Nat := 118140960795 + 5680876 * 2 ^ 59
def prefixEnd_5680876 : Nat := 4983230072969 + 3 ^ 40 * 5680876 * 2
def baseEnd_5680876 : Nat := 2917019926591220780224133

theorem tailTrace_5680876 : CollatzResearch.WordTrace tailWord_5680876 prefixEnd_5680876 2917019926591220780224133 := by
  unfold tailWord_5680876
  simp only [CollatzResearch.WordTrace]
  refine ⟨103599284883581971611519241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138132379844775962148692321 103599284883581971611519241)
  ·
    refine ⟨77699463662686478708639431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103599284883581971611519241 77699463662686478708639431)
    ·
      refine ⟨116549195494029718062959147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77699463662686478708639431 116549195494029718062959147)
      ·
        refine ⟨174823793241044577094438721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116549195494029718062959147 174823793241044577094438721)
        ·
          refine ⟨131117844930783432820829041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174823793241044577094438721 131117844930783432820829041)
          ·
            refine ⟨98338383698087574615621781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131117844930783432820829041 98338383698087574615621781)
            ·
              refine ⟨4609611735847855060107271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98338383698087574615621781 4609611735847855060107271)
              ·
                refine ⟨6914417603771782590160907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609611735847855060107271 6914417603771782590160907)
                ·
                  refine ⟨10371626405657673885241361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914417603771782590160907 10371626405657673885241361)
                  ·
                    refine ⟨7778719804243255413931021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10371626405657673885241361 7778719804243255413931021)
                    ·
                      refine ⟨2917019926591220780224133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778719804243255413931021 2917019926591220780224133)
                      ·
                        rfl

theorem cell23_5680876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 3].length) (baseStart_5680876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680876 prefixEnd_5680876 := by exact prefixLift 5680876
  have htrace : WordTrace (prefixWord ++ tailWord_5680876) baseStart_5680876 baseEnd_5680876 := by
    simpa [prefixWord, tailWord_5680876, baseEnd_5680876] using wordTrace_append hprefix tailTrace_5680876
  have hstable : (prefixWord ++ tailWord_5680876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680876).length < 2 ^ (prefixWord ++ tailWord_5680876).sum := by decide
  have hdescent : baseEnd_5680876 < baseStart_5680876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680899 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 5, 3, 2]
def baseStart_5680899 : Nat := 118140960795 + 5680899 * 2 ^ 59
def prefixEnd_5680899 : Nat := 4983230072969 + 3 ^ 40 * 5680899 * 2
def baseEnd_5680899 : Nat := 2917031736646274190236527

theorem tailTrace_5680899 : CollatzResearch.WordTrace tailWord_5680899 prefixEnd_5680899 2917031736646274190236527 := by
  unfold tailWord_5680899
  simp only [CollatzResearch.WordTrace]
  refine ⟨207199408646080618151125751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138132939097387078767417167 207199408646080618151125751)
  ·
    refine ⟨310799112969120927226688627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207199408646080618151125751 310799112969120927226688627)
    ·
      refine ⟨466198669453681390840032941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310799112969120927226688627 466198669453681390840032941)
      ·
        refine ⟨174824501045130521565012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466198669453681390840032941 174824501045130521565012353)
        ·
          refine ⟨131118375783847891173759265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174824501045130521565012353 131118375783847891173759265)
          ·
            refine ⟨98338781837885918380319449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131118375783847891173759265 98338781837885918380319449)
            ·
              refine ⟨73754086378414438785239587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98338781837885918380319449 73754086378414438785239587)
              ·
                refine ⟨110631129567621658177859381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73754086378414438785239587 110631129567621658177859381)
                ·
                  refine ⟨10371668396964530454174317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110631129567621658177859381 10371668396964530454174317)
                  ·
                    refine ⟨3889375648861698920315369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10371668396964530454174317 3889375648861698920315369)
                    ·
                      refine ⟨2917031736646274190236527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889375648861698920315369 2917031736646274190236527)
                      ·
                        rfl

theorem cell23_5680899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_5680899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680899 prefixEnd_5680899 := by exact prefixLift 5680899
  have htrace : WordTrace (prefixWord ++ tailWord_5680899) baseStart_5680899 baseEnd_5680899 := by
    simpa [prefixWord, tailWord_5680899, baseEnd_5680899] using wordTrace_append hprefix tailTrace_5680899
  have hstable : (prefixWord ++ tailWord_5680899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680899).length < 2 ^ (prefixWord ++ tailWord_5680899).sum := by decide
  have hdescent : baseEnd_5680899 < baseStart_5680899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680903 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 1, 2, 4]
def baseStart_5680903 : Nat := 118140960795 + 5680903 * 2 ^ 59
def prefixEnd_5680903 : Nat := 4983230072969 + 3 ^ 40 * 5680903 * 2
def baseEnd_5680903 : Nat := 2917033790568892174586509

theorem tailTrace_5680903 : CollatzResearch.WordTrace tailWord_5680903 prefixEnd_5680903 2917033790568892174586509 := by
  unfold tailWord_5680903
  simp only [CollatzResearch.WordTrace]
  refine ⟨207199554538066126834271363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138133036358710751222847575 207199554538066126834271363)
  ·
    refine ⟨310799331807099190251407045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207199554538066126834271363 310799331807099190251407045)
    ·
      refine ⟨58274874713831098172138821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310799331807099190251407045 58274874713831098172138821)
      ·
        refine ⟨10926539008843330907276029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58274874713831098172138821 10926539008843330907276029)
        ·
          refine ⟨4097452128316249090228511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10926539008843330907276029 4097452128316249090228511)
          ·
            refine ⟨6146178192474373635342767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097452128316249090228511 6146178192474373635342767)
            ·
              refine ⟨9219267288711560453014151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146178192474373635342767 9219267288711560453014151)
              ·
                refine ⟨13828900933067340679521227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9219267288711560453014151 13828900933067340679521227)
                ·
                  refine ⟨20743351399601011019281841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13828900933067340679521227 20743351399601011019281841)
                  ·
                    refine ⟨15557513549700758264461381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20743351399601011019281841 15557513549700758264461381)
                    ·
                      refine ⟨2917033790568892174586509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15557513549700758264461381 2917033790568892174586509)
                      ·
                        rfl

theorem cell23_5680903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_5680903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680903 prefixEnd_5680903 := by exact prefixLift 5680903
  have htrace : WordTrace (prefixWord ++ tailWord_5680903) baseStart_5680903 baseEnd_5680903 := by
    simpa [prefixWord, tailWord_5680903, baseEnd_5680903] using wordTrace_append hprefix tailTrace_5680903
  have hstable : (prefixWord ++ tailWord_5680903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680903).length < 2 ^ (prefixWord ++ tailWord_5680903).sum := by decide
  have hdescent : baseEnd_5680903 < baseStart_5680903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680906 : List Nat := [3, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_5680906 : Nat := 118140960795 + 5680906 * 2 ^ 59
def prefixEnd_5680906 : Nat := 4983230072969 + 3 ^ 40 * 5680906 * 2
def baseEnd_5680906 : Nat := 2917035331010855662848995

theorem tailTrace_5680906 : CollatzResearch.WordTrace tailWord_5680906 prefixEnd_5680906 2917035331010855662848995 := by
  unfold tailWord_5680906
  simp only [CollatzResearch.WordTrace]
  refine ⟨51799915989263814586657643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138133109304703505564420381 51799915989263814586657643)
  ·
    refine ⟨77699873983895721879986465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51799915989263814586657643 77699873983895721879986465)
    ·
      refine ⟨58274905487921791409989849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77699873983895721879986465 58274905487921791409989849)
      ·
        refine ⟨43706179115941343557492387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58274905487921791409989849 43706179115941343557492387)
        ·
          refine ⟨65559268673912015336238581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43706179115941343557492387 65559268673912015336238581)
          ·
            refine ⟨6146181438179251437772367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65559268673912015336238581 6146181438179251437772367)
            ·
              refine ⟨9219272157268877156658551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146181438179251437772367 9219272157268877156658551)
              ·
                refine ⟨13828908235903315734987827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9219272157268877156658551 13828908235903315734987827)
                ·
                  refine ⟨20743362353854973602481741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13828908235903315734987827 20743362353854973602481741)
                  ·
                    refine ⟨7778760882695615100930653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20743362353854973602481741 7778760882695615100930653)
                    ·
                      refine ⟨2917035331010855662848995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7778760882695615100930653 2917035331010855662848995)
                      ·
                        rfl

theorem cell23_5680906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_5680906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680906 prefixEnd_5680906 := by exact prefixLift 5680906
  have htrace : WordTrace (prefixWord ++ tailWord_5680906) baseStart_5680906 baseEnd_5680906 := by
    simpa [prefixWord, tailWord_5680906, baseEnd_5680906] using wordTrace_append hprefix tailTrace_5680906
  have hstable : (prefixWord ++ tailWord_5680906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680906).length < 2 ^ (prefixWord ++ tailWord_5680906).sum := by decide
  have hdescent : baseEnd_5680906 < baseStart_5680906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680963 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 2, 2, 2]
def baseStart_5680963 : Nat := 118140960795 + 5680963 * 2 ^ 59
def prefixEnd_5680963 : Nat := 4983230072969 + 3 ^ 40 * 5680963 * 2
def baseEnd_5680963 : Nat := 2917064599408161939836233

theorem tailTrace_5680963 : CollatzResearch.WordTrace tailWord_5680963 prefixEnd_5680963 2917064599408161939836233 := by
  unfold tailWord_5680963
  simp only [CollatzResearch.WordTrace]
  refine ⟨207201742917848757081455543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138134495278565838054303695 207201742917848757081455543)
  ·
    refine ⟨310802614376773135622183315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207201742917848757081455543 310802614376773135622183315)
    ·
      refine ⟨466203921565159703433274973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310802614376773135622183315 466203921565159703433274973)
      ·
        refine ⟨174826470586934888787478115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466203921565159703433274973 174826470586934888787478115)
        ·
          refine ⟨262239705880402333181217173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174826470586934888787478115 262239705880402333181217173)
          ·
            refine ⟨12292486213143859367869555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262239705880402333181217173 12292486213143859367869555)
            ·
              refine ⟨18438729319715789051804333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12292486213143859367869555 18438729319715789051804333)
              ·
                refine ⟨6914523494893420894426625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18438729319715789051804333 6914523494893420894426625)
                ·
                  refine ⟨5185892621170065670819969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6914523494893420894426625 5185892621170065670819969)
                  ·
                    refine ⟨3889419465877549253114977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5185892621170065670819969 3889419465877549253114977)
                    ·
                      refine ⟨2917064599408161939836233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889419465877549253114977 2917064599408161939836233)
                      ·
                        rfl

theorem cell23_5680963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_5680963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680963 prefixEnd_5680963 := by exact prefixLift 5680963
  have htrace : WordTrace (prefixWord ++ tailWord_5680963) baseStart_5680963 baseEnd_5680963 := by
    simpa [prefixWord, tailWord_5680963, baseEnd_5680963] using wordTrace_append hprefix tailTrace_5680963
  have hstable : (prefixWord ++ tailWord_5680963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680963).length < 2 ^ (prefixWord ++ tailWord_5680963).sum := by decide
  have hdescent : baseEnd_5680963 < baseStart_5680963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5680999 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 2, 5]
def baseStart_5680999 : Nat := 118140960795 + 5680999 * 2 ^ 59
def prefixEnd_5680999 : Nat := 4983230072969 + 3 ^ 40 * 5680999 * 2
def baseEnd_5680999 : Nat := 972361028237241266328689

theorem tailTrace_5680999 : CollatzResearch.WordTrace tailWord_5680999 prefixEnd_5680999 972361028237241266328689 := by
  unfold tailWord_5680999
  simp only [CollatzResearch.WordTrace]
  refine ⟨207203055945718335229766051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138135370630478890153177367 207203055945718335229766051)
  ·
    refine ⟨310804583918577502844649077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207203055945718335229766051 310804583918577502844649077)
    ·
      refine ⟨29137929742366640891685851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310804583918577502844649077 29137929742366640891685851)
      ·
        refine ⟨43706894613549961337528777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29137929742366640891685851 43706894613549961337528777)
        ·
          refine ⟨32780170960162471003146583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43706894613549961337528777 32780170960162471003146583)
          ·
            refine ⟨49170256440243706504719875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32780170960162471003146583 49170256440243706504719875)
            ·
              refine ⟨73755384660365559757079813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49170256440243706504719875 73755384660365559757079813)
              ·
                refine ⟨13829134623818542454452465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73755384660365559757079813 13829134623818542454452465)
                ·
                  refine ⟨10371850967863906840839349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13829134623818542454452465 10371850967863906840839349)
                  ·
                    refine ⟨972361028237241266328689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10371850967863906840839349 972361028237241266328689)
                    ·
                      rfl

theorem cell23_5680999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_5680999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5680999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5680999 prefixEnd_5680999 := by exact prefixLift 5680999
  have htrace : WordTrace (prefixWord ++ tailWord_5680999) baseStart_5680999 baseEnd_5680999 := by
    simpa [prefixWord, tailWord_5680999, baseEnd_5680999] using wordTrace_append hprefix tailTrace_5680999
  have hstable : (prefixWord ++ tailWord_5680999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5680999).length < 2 ^ (prefixWord ++ tailWord_5680999).sum := by decide
  have hdescent : baseEnd_5680999 < baseStart_5680999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5680999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681063 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 3, 4]
def baseStart_5681063 : Nat := 118140960795 + 5681063 * 2 ^ 59
def prefixEnd_5681063 : Nat := 4983230072969 + 3 ^ 40 * 5681063 * 2
def baseEnd_5681063 : Nat := 972371982491203849528591

theorem tailTrace_5681063 : CollatzResearch.WordTrace tailWord_5681063 prefixEnd_5681063 972371982491203849528591 := by
  unfold tailWord_5681063
  simp only [CollatzResearch.WordTrace]
  refine ⟨207205390217486474160095843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138136926811657649440063895 207205390217486474160095843)
  ·
    refine ⟨310808085326229711240143765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207205390217486474160095843 310808085326229711240143765)
    ·
      refine ⟨14569128999667017714381739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 310808085326229711240143765 14569128999667017714381739)
      ·
        refine ⟨21853693499500526571572609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14569128999667017714381739 21853693499500526571572609)
        ·
          refine ⟨16390270124625394928679457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21853693499500526571572609 16390270124625394928679457)
          ·
            refine ⟨12292702593469046196509593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16390270124625394928679457 12292702593469046196509593)
            ·
              refine ⟨9219526945101784647382195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12292702593469046196509593 9219526945101784647382195)
              ·
                refine ⟨13829290417652676971073293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9219526945101784647382195 13829290417652676971073293)
                ·
                  refine ⟨5185983906619753864152485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13829290417652676971073293 5185983906619753864152485)
                  ·
                    refine ⟨972371982491203849528591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5185983906619753864152485 972371982491203849528591)
                    ·
                      rfl

theorem cell23_5681063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_5681063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681063 prefixEnd_5681063 := by exact prefixLift 5681063
  have htrace : WordTrace (prefixWord ++ tailWord_5681063) baseStart_5681063 baseEnd_5681063 := by
    simpa [prefixWord, tailWord_5681063, baseEnd_5681063] using wordTrace_append hprefix tailTrace_5681063
  have hstable : (prefixWord ++ tailWord_5681063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681063).length < 2 ^ (prefixWord ++ tailWord_5681063).sum := by decide
  have hdescent : baseEnd_5681063 < baseStart_5681063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681139 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4]
def baseStart_5681139 : Nat := 118140960795 + 5681139 * 2 ^ 59
def prefixEnd_5681139 : Nat := 4983230072969 + 3 ^ 40 * 5681139 * 2
def baseEnd_5681139 : Nat := 2917154972003353251235423

theorem tailTrace_5681139 : CollatzResearch.WordTrace tailWord_5681139 prefixEnd_5681139 2917154972003353251235423 := by
  unfold tailWord_5681139
  simp only [CollatzResearch.WordTrace]
  refine ⟨207208162165211139139862471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138138774776807426093241647 207208162165211139139862471)
  ·
    refine ⟨310812243247816708709793707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207208162165211139139862471 310812243247816708709793707)
    ·
      refine ⟨466218364871725063064690561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310812243247816708709793707 466218364871725063064690561)
      ·
        refine ⟨349663773653793797298517921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466218364871725063064690561 349663773653793797298517921)
        ·
          refine ⟨262247830240345347973888441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349663773653793797298517921 262247830240345347973888441)
          ·
            refine ⟨196685872680259010980416331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262247830240345347973888441 196685872680259010980416331)
            ·
              refine ⟨295028809020388516470624497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196685872680259010980416331 295028809020388516470624497)
              ·
                refine ⟨221271606765291387352968373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295028809020388516470624497 221271606765291387352968373)
                ·
                  refine ⟨20744213134246067564340785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221271606765291387352968373 20744213134246067564340785)
                  ·
                    refine ⟨15558159850684550673255589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20744213134246067564340785 15558159850684550673255589)
                    ·
                      refine ⟨2917154972003353251235423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15558159850684550673255589 2917154972003353251235423)
                      ·
                        rfl

theorem cell23_5681139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 4].length) (baseStart_5681139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681139 prefixEnd_5681139 := by exact prefixLift 5681139
  have htrace : WordTrace (prefixWord ++ tailWord_5681139) baseStart_5681139 baseEnd_5681139 := by
    simpa [prefixWord, tailWord_5681139, baseEnd_5681139] using wordTrace_append hprefix tailTrace_5681139
  have hstable : (prefixWord ++ tailWord_5681139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681139).length < 2 ^ (prefixWord ++ tailWord_5681139).sum := by decide
  have hdescent : baseEnd_5681139 < baseStart_5681139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681149 : List Nat := [1, 4, 1, 1, 1, 2, 4, 9]
def baseStart_5681149 : Nat := 118140960795 + 5681149 * 2 ^ 59
def prefixEnd_5681149 : Nat := 4983230072969 + 3 ^ 40 * 5681149 * 2
def baseEnd_5681149 : Nat := 108042966918885118967051

theorem tailTrace_5681149 : CollatzResearch.WordTrace tailWord_5681149 prefixEnd_5681149 108042966918885118967051 := by
  unfold tailWord_5681149
  simp only [CollatzResearch.WordTrace]
  refine ⟨207208526895174910847726501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138139017930116607231817667 207208526895174910847726501)
  ·
    refine ⟨38851598792845295783948719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207208526895174910847726501 38851598792845295783948719)
    ·
      refine ⟨58277398189267943675923079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38851598792845295783948719 58277398189267943675923079)
      ·
        refine ⟨87416097283901915513884619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58277398189267943675923079 87416097283901915513884619)
        ·
          refine ⟨131124145925852873270826929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87416097283901915513884619 131124145925852873270826929)
          ·
            refine ⟨98343109444389654953120197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131124145925852873270826929 98343109444389654953120197)
            ·
              refine ⟨18439333020823060303710037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98343109444389654953120197 18439333020823060303710037)
              ·
                refine ⟨108042966918885118967051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18439333020823060303710037 108042966918885118967051)
                ·
                  rfl

theorem cell23_5681149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 9].length) (baseStart_5681149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681149 prefixEnd_5681149 := by exact prefixLift 5681149
  have htrace : WordTrace (prefixWord ++ tailWord_5681149) baseStart_5681149 baseEnd_5681149 := by
    simpa [prefixWord, tailWord_5681149, baseEnd_5681149] using wordTrace_append hprefix tailTrace_5681149
  have hstable : (prefixWord ++ tailWord_5681149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681149).length < 2 ^ (prefixWord ++ tailWord_5681149).sum := by decide
  have hdescent : baseEnd_5681149 < baseStart_5681149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681176 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_5681176 : Nat := 118140960795 + 5681176 * 2 ^ 59
def prefixEnd_5681176 : Nat := 4983230072969 + 3 ^ 40 * 5681176 * 2
def baseEnd_5681176 : Nat := 2917173970787569606472753

theorem tailTrace_5681176 : CollatzResearch.WordTrace tailWord_5681176 prefixEnd_5681176 2917173970787569606472753 := by
  unfold tailWord_5681176
  simp only [CollatzResearch.WordTrace]
  refine ⟨103604755833038547229479691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138139674444051396305972921 103604755833038547229479691)
  ·
    refine ⟨155407133749557820844219537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103604755833038547229479691 155407133749557820844219537)
    ·
      refine ⟨116555350312168365633164653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155407133749557820844219537 116555350312168365633164653)
      ·
        refine ⟨43708256367063137112436745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116555350312168365633164653 43708256367063137112436745)
        ·
          refine ⟨32781192275297352834327559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43708256367063137112436745 32781192275297352834327559)
          ·
            refine ⟨49171788412946029251491339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32781192275297352834327559 49171788412946029251491339)
            ·
              refine ⟨73757682619419043877237009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49171788412946029251491339 73757682619419043877237009)
              ·
                refine ⟨55318261964564282907927757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73757682619419043877237009 55318261964564282907927757)
                ·
                  refine ⟨20744348236711606090472909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55318261964564282907927757 20744348236711606090472909)
                  ·
                    refine ⟨7779130588766852283927341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20744348236711606090472909 7779130588766852283927341)
                    ·
                      refine ⟨2917173970787569606472753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779130588766852283927341 2917173970787569606472753)
                      ·
                        rfl

theorem cell23_5681176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_5681176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681176 prefixEnd_5681176 := by exact prefixLift 5681176
  have htrace : WordTrace (prefixWord ++ tailWord_5681176) baseStart_5681176 baseEnd_5681176 := by
    simpa [prefixWord, tailWord_5681176, baseEnd_5681176] using wordTrace_append hprefix tailTrace_5681176
  have hstable : (prefixWord ++ tailWord_5681176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681176).length < 2 ^ (prefixWord ++ tailWord_5681176).sum := by decide
  have hdescent : baseEnd_5681176 < baseStart_5681176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681203 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 3, 3, 2]
def baseStart_5681203 : Nat := 118140960795 + 5681203 * 2 ^ 59
def prefixEnd_5681203 : Nat := 4983230072969 + 3 ^ 40 * 5681203 * 2
def baseEnd_5681203 : Nat := 2917187834765241000835129

theorem tailTrace_5681203 : CollatzResearch.WordTrace tailWord_5681203 prefixEnd_5681203 2917187834765241000835129 := by
  unfold tailWord_5681203
  simp only [CollatzResearch.WordTrace]
  refine ⟨207210496436979278070192263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138140330957986185380128175 207210496436979278070192263)
  ·
    refine ⟨310815744655468917105288395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207210496436979278070192263 310815744655468917105288395)
    ·
      refine ⟨466223616983203375657932593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310815744655468917105288395 466223616983203375657932593)
      ·
        refine ⟨349667712737402531743449445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466223616983203375657932593 349667712737402531743449445)
        ·
          refine ⟨65562696138262974701896771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349667712737402531743449445 65562696138262974701896771)
          ·
            refine ⟨98344044207394462052845157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65562696138262974701896771 98344044207394462052845157)
            ·
              refine ⟨18439508288886461634908467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98344044207394462052845157 18439508288886461634908467)
              ·
                refine ⟨27659262433329692452362701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18439508288886461634908467 27659262433329692452362701)
                ·
                  refine ⟨10372223412498634669636013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27659262433329692452362701 10372223412498634669636013)
                  ·
                    refine ⟨3889583779686988001113505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10372223412498634669636013 3889583779686988001113505)
                    ·
                      refine ⟨2917187834765241000835129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889583779686988001113505 2917187834765241000835129)
                      ·
                        rfl

theorem cell23_5681203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 3, 2].length) (baseStart_5681203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681203 prefixEnd_5681203 := by exact prefixLift 5681203
  have htrace : WordTrace (prefixWord ++ tailWord_5681203) baseStart_5681203 baseEnd_5681203 := by
    simpa [prefixWord, tailWord_5681203, baseEnd_5681203] using wordTrace_append hprefix tailTrace_5681203
  have hstable : (prefixWord ++ tailWord_5681203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681203).length < 2 ^ (prefixWord ++ tailWord_5681203).sum := by decide
  have hdescent : baseEnd_5681203 < baseStart_5681203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681214 : List Nat := [4, 2, 1, 3, 2, 2, 2, 1, 1, 2, 3]
def baseStart_5681214 : Nat := 118140960795 + 5681214 * 2 ^ 59
def prefixEnd_5681214 : Nat := 4983230072969 + 3 ^ 40 * 5681214 * 2
def baseEnd_5681214 : Nat := 2917193483052440457797579

theorem tailTrace_5681214 : CollatzResearch.WordTrace tailWord_5681214 prefixEnd_5681214 2917193483052440457797579 := by
  unfold tailWord_5681214
  simp only [CollatzResearch.WordTrace]
  refine ⟨25901362204992428368605337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138140598426626284632561797 25901362204992428368605337)
  ·
    refine ⟨19426021653744321276454003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25901362204992428368605337 19426021653744321276454003)
    ·
      refine ⟨29139032480616481914681005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19426021653744321276454003 29139032480616481914681005)
      ·
        refine ⟨10927137180231180718005377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29139032480616481914681005 10927137180231180718005377)
        ·
          refine ⟨8195352885173385538504033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10927137180231180718005377 8195352885173385538504033)
          ·
            refine ⟨6146514663880039153878025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8195352885173385538504033 6146514663880039153878025)
            ·
              refine ⟨4609885997910029365408519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6146514663880039153878025 4609885997910029365408519)
              ·
                refine ⟨6914828996865044048112779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4609885997910029365408519 6914828996865044048112779)
                ·
                  refine ⟨10372243495297566072169169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6914828996865044048112779 10372243495297566072169169)
                  ·
                    refine ⟨7779182621473174554126877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10372243495297566072169169 7779182621473174554126877)
                    ·
                      refine ⟨2917193483052440457797579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779182621473174554126877 2917193483052440457797579)
                      ·
                        rfl

theorem cell23_5681214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_5681214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681214 prefixEnd_5681214 := by exact prefixLift 5681214
  have htrace : WordTrace (prefixWord ++ tailWord_5681214) baseStart_5681214 baseEnd_5681214 := by
    simpa [prefixWord, tailWord_5681214, baseEnd_5681214] using wordTrace_append hprefix tailTrace_5681214
  have hstable : (prefixWord ++ tailWord_5681214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681214).length < 2 ^ (prefixWord ++ tailWord_5681214).sum := by decide
  have hdescent : baseEnd_5681214 < baseStart_5681214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681236 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_5681236 : Nat := 118140960795 + 5681236 * 2 ^ 59
def prefixEnd_5681236 : Nat := 4983230072969 + 3 ^ 40 * 5681236 * 2
def baseEnd_5681236 : Nat := 2917204779626839371722477

theorem tailTrace_5681236 : CollatzResearch.WordTrace tailWord_5681236 prefixEnd_5681236 2917204779626839371722477 := by
  unfold tailWord_5681236
  simp only [CollatzResearch.WordTrace]
  refine ⟨103605850022929862353071781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138141133363906483137429041 103605850022929862353071781)
  ·
    refine ⟨19426096879299349191200959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103605850022929862353071781 19426096879299349191200959)
    ·
      refine ⟨29139145318949023786801439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19426096879299349191200959 29139145318949023786801439)
      ·
        refine ⟨43708717978423535680202159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29139145318949023786801439 43708717978423535680202159)
        ·
          refine ⟨65563076967635303520303239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43708717978423535680202159 65563076967635303520303239)
          ·
            refine ⟨98344615451452955280454859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65563076967635303520303239 98344615451452955280454859)
            ·
              refine ⟨147516923177179432920682289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98344615451452955280454859 147516923177179432920682289)
              ·
                refine ⟨110637692382884574690511717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147516923177179432920682289 110637692382884574690511717)
                ·
                  refine ⟨20744567321790857754470947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110637692382884574690511717 20744567321790857754470947)
                  ·
                    refine ⟨31116850982686286631706421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20744567321790857754470947 31116850982686286631706421)
                    ·
                      refine ⟨2917204779626839371722477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31116850982686286631706421 2917204779626839371722477)
                      ·
                        rfl

theorem cell23_5681236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_5681236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681236 prefixEnd_5681236 := by exact prefixLift 5681236
  have htrace : WordTrace (prefixWord ++ tailWord_5681236) baseStart_5681236 baseEnd_5681236 := by
    simpa [prefixWord, tailWord_5681236, baseEnd_5681236] using wordTrace_append hprefix tailTrace_5681236
  have hstable : (prefixWord ++ tailWord_5681236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681236).length < 2 ^ (prefixWord ++ tailWord_5681236).sum := by decide
  have hdescent : baseEnd_5681236 < baseStart_5681236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681296 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_5681296 : Nat := 118140960795 + 5681296 * 2 ^ 59
def prefixEnd_5681296 : Nat := 4983230072969 + 3 ^ 40 * 5681296 * 2
def baseEnd_5681296 : Nat := 2917235588466109136972201

theorem tailTrace_5681296 : CollatzResearch.WordTrace tailWord_5681296 prefixEnd_5681296 2917235588466109136972201 := by
  unfold tailWord_5681296
  simp only [CollatzResearch.WordTrace]
  refine ⟨103606944212821177476663871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138142592283761569968885161 103606944212821177476663871)
  ·
    refine ⟨155410416319231766214995807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103606944212821177476663871 155410416319231766214995807)
    ·
      refine ⟨233115624478847649322493711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155410416319231766214995807 233115624478847649322493711)
      ·
        refine ⟨349673436718271473983740567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233115624478847649322493711 349673436718271473983740567)
        ·
          refine ⟨524510155077407210975610851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349673436718271473983740567 524510155077407210975610851)
          ·
            refine ⟨786765232616110816463416277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524510155077407210975610851 786765232616110816463416277)
            ·
              refine ⟨18439810139440097260861319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 786765232616110816463416277 18439810139440097260861319)
              ·
                refine ⟨27659715209160145891291979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18439810139440097260861319 27659715209160145891291979)
                ·
                  refine ⟨41489572813740218836937969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27659715209160145891291979 41489572813740218836937969)
                  ·
                    refine ⟨31117179610305164127703477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41489572813740218836937969 31117179610305164127703477)
                    ·
                      refine ⟨2917235588466109136972201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31117179610305164127703477 2917235588466109136972201)
                      ·
                        rfl

theorem cell23_5681296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_5681296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681296 prefixEnd_5681296 := by exact prefixLift 5681296
  have htrace : WordTrace (prefixWord ++ tailWord_5681296) baseStart_5681296 baseEnd_5681296 := by
    simpa [prefixWord, tailWord_5681296, baseEnd_5681296] using wordTrace_append hprefix tailTrace_5681296
  have hstable : (prefixWord ++ tailWord_5681296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681296).length < 2 ^ (prefixWord ++ tailWord_5681296).sum := by decide
  have hdescent : baseEnd_5681296 < baseStart_5681296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681336 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_5681336 : Nat := 118140960795 + 5681336 * 2 ^ 59
def prefixEnd_5681336 : Nat := 4983230072969 + 3 ^ 40 * 5681336 * 2
def baseEnd_5681336 : Nat := 2917256127692288980472017

theorem tailTrace_5681336 : CollatzResearch.WordTrace tailWord_5681336 prefixEnd_5681336 2917256127692288980472017 := by
  unfold tailWord_5681336
  simp only [CollatzResearch.WordTrace]
  refine ⟨103607673672748720892391931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138143564896998294523189241 103607673672748720892391931)
  ·
    refine ⟨155411510509123081338587897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103607673672748720892391931 155411510509123081338587897)
    ·
      refine ⟨116558632881842311003940923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155411510509123081338587897 116558632881842311003940923)
      ·
        refine ⟨174837949322763466505911385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116558632881842311003940923 174837949322763466505911385)
        ·
          refine ⟨131128461992072599879433539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174837949322763466505911385 131128461992072599879433539)
          ·
            refine ⟨196692692988108899819150309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131128461992072599879433539 196692692988108899819150309)
            ·
              refine ⟨36879879935270418716090683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196692692988108899819150309 36879879935270418716090683)
              ·
                refine ⟨55319819902905628074136025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36879879935270418716090683 55319819902905628074136025)
                ·
                  refine ⟨41489864927179221055602019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55319819902905628074136025 41489864927179221055602019)
                  ·
                    refine ⟨62234797390768831583403029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41489864927179221055602019 62234797390768831583403029)
                    ·
                      refine ⟨2917256127692288980472017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62234797390768831583403029 2917256127692288980472017)
                      ·
                        rfl

theorem cell23_5681336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_5681336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681336 prefixEnd_5681336 := by exact prefixLift 5681336
  have htrace : WordTrace (prefixWord ++ tailWord_5681336) baseStart_5681336 baseEnd_5681336 := by
    simpa [prefixWord, tailWord_5681336, baseEnd_5681336] using wordTrace_append hprefix tailTrace_5681336
  have hstable : (prefixWord ++ tailWord_5681336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681336).length < 2 ^ (prefixWord ++ tailWord_5681336).sum := by decide
  have hdescent : baseEnd_5681336 < baseStart_5681336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681390 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_5681390 : Nat := 118140960795 + 5681390 * 2 ^ 59
def prefixEnd_5681390 : Nat := 4983230072969 + 3 ^ 40 * 5681390 * 2
def baseEnd_5681390 : Nat := 2917283855647631769196769

theorem tailTrace_5681390 : CollatzResearch.WordTrace tailWord_5681390 prefixEnd_5681390 2917283855647631769196769 := by
  unfold tailWord_5681390
  simp only [CollatzResearch.WordTrace]
  refine ⟨25902164610912726125906203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138144877924867872671499749 25902164610912726125906203)
  ·
    refine ⟨38853246916369089188859305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25902164610912726125906203 38853246916369089188859305)
    ·
      refine ⟨29139935187276816891644479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38853246916369089188859305 29139935187276816891644479)
      ·
        refine ⟨43709902780915225337466719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29139935187276816891644479 43709902780915225337466719)
        ·
          refine ⟨65564854171372838006200079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43709902780915225337466719 65564854171372838006200079)
          ·
            refine ⟨98347281257059257009300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65564854171372838006200079 98347281257059257009300119)
            ·
              refine ⟨147520921885588885513950179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98347281257059257009300119 147520921885588885513950179)
              ·
                refine ⟨221281382828383328270925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147520921885588885513950179 221281382828383328270925269)
                ·
                  refine ⟨5186282410040234256349811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 221281382828383328270925269 5186282410040234256349811)
                  ·
                    refine ⟨7779423615060351384524717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5186282410040234256349811 7779423615060351384524717)
                    ·
                      refine ⟨2917283855647631769196769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779423615060351384524717 2917283855647631769196769)
                      ·
                        rfl

theorem cell23_5681390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_5681390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681390 prefixEnd_5681390 := by exact prefixLift 5681390
  have htrace : WordTrace (prefixWord ++ tailWord_5681390) baseStart_5681390 baseEnd_5681390 := by
    simpa [prefixWord, tailWord_5681390, baseEnd_5681390] using wordTrace_append hprefix tailTrace_5681390
  have hstable : (prefixWord ++ tailWord_5681390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681390).length < 2 ^ (prefixWord ++ tailWord_5681390).sum := by decide
  have hdescent : baseEnd_5681390 < baseStart_5681390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681400 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2]
def baseStart_5681400 : Nat := 118140960795 + 5681400 * 2 ^ 59
def prefixEnd_5681400 : Nat := 4983230072969 + 3 ^ 40 * 5681400 * 2
def baseEnd_5681400 : Nat := 2917288990454176730071723

theorem tailTrace_5681400 : CollatzResearch.WordTrace tailWord_5681400 prefixEnd_5681400 2917288990454176730071723 := by
  unfold tailWord_5681400
  simp only [CollatzResearch.WordTrace]
  refine ⟨103608840808632790357556827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138145121078177053810075769 103608840808632790357556827)
  ·
    refine ⟨155413261212949185536335241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103608840808632790357556827 155413261212949185536335241)
    ·
      refine ⟨116559945909711889152251431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155413261212949185536335241 116559945909711889152251431)
      ·
        refine ⟨174839918864567833728377147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116559945909711889152251431 174839918864567833728377147)
        ·
          refine ⟨262259878296851750592565721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174839918864567833728377147 262259878296851750592565721)
          ·
            refine ⟨196694908722638812944424291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262259878296851750592565721 196694908722638812944424291)
            ·
              refine ⟨295042363083958219416636437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196694908722638812944424291 295042363083958219416636437)
              ·
                refine ⟨13830110769560541535154833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295042363083958219416636437 13830110769560541535154833)
                ·
                  refine ⟨10372583077170406151366125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13830110769560541535154833 10372583077170406151366125)
                  ·
                    refine ⟨3889718653938902306762297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10372583077170406151366125 3889718653938902306762297)
                    ·
                      refine ⟨2917288990454176730071723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889718653938902306762297 2917288990454176730071723)
                      ·
                        rfl

theorem cell23_5681400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_5681400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681400 prefixEnd_5681400 := by exact prefixLift 5681400
  have htrace : WordTrace (prefixWord ++ tailWord_5681400) baseStart_5681400 baseEnd_5681400 := by
    simpa [prefixWord, tailWord_5681400, baseEnd_5681400] using wordTrace_append hprefix tailTrace_5681400
  have hstable : (prefixWord ++ tailWord_5681400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681400).length < 2 ^ (prefixWord ++ tailWord_5681400).sum := by decide
  have hdescent : baseEnd_5681400 < baseStart_5681400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681407 : List Nat := [1, 1, 2, 2, 1, 4, 1, 6, 1, 1, 3]
def baseStart_5681407 : Nat := 118140960795 + 5681407 * 2 ^ 59
def prefixEnd_5681407 : Nat := 4983230072969 + 3 ^ 40 * 5681407 * 2
def baseEnd_5681407 : Nat := 2917292584818758202684191

theorem tailTrace_5681407 : CollatzResearch.WordTrace tailWord_5681407 prefixEnd_5681407 2917292584818758202684191 := by
  unfold tailWord_5681407
  simp only [CollatzResearch.WordTrace]
  refine ⟨207217936928240220910618475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138145291285493480607078983 207217936928240220910618475)
  ·
    refine ⟨310826905392360331365927713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207217936928240220910618475 310826905392360331365927713)
    ·
      refine ⟨233120179044270248524445785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310826905392360331365927713 233120179044270248524445785)
      ·
        refine ⟨174840134283202686393334339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233120179044270248524445785 174840134283202686393334339)
        ·
          refine ⟨262260201424804029590001509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174840134283202686393334339 262260201424804029590001509)
          ·
            refine ⟨49173787767150755548125283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262260201424804029590001509 49173787767150755548125283)
            ·
              refine ⟨73760681650726133322187925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49173787767150755548125283 73760681650726133322187925)
              ·
                refine ⟨3457531952377787499477559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73760681650726133322187925 3457531952377787499477559)
                ·
                  refine ⟨5186297928566681249216339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457531952377787499477559 5186297928566681249216339)
                  ·
                    refine ⟨7779446892850021873824509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5186297928566681249216339 7779446892850021873824509)
                    ·
                      refine ⟨2917292584818758202684191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779446892850021873824509 2917292584818758202684191)
                      ·
                        rfl

theorem cell23_5681407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_5681407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681407 prefixEnd_5681407 := by exact prefixLift 5681407
  have htrace : WordTrace (prefixWord ++ tailWord_5681407) baseStart_5681407 baseEnd_5681407 := by
    simpa [prefixWord, tailWord_5681407, baseEnd_5681407] using wordTrace_append hprefix tailTrace_5681407
  have hstable : (prefixWord ++ tailWord_5681407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681407).length < 2 ^ (prefixWord ++ tailWord_5681407).sum := by decide
  have hdescent : baseEnd_5681407 < baseStart_5681407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681413 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_5681413 : Nat := 118140960795 + 5681413 * 2 ^ 59
def prefixEnd_5681413 : Nat := 4983230072969 + 3 ^ 40 * 5681413 * 2
def baseEnd_5681413 : Nat := 2917295665702685179209163

theorem tailTrace_5681413 : CollatzResearch.WordTrace tailWord_5681413 prefixEnd_5681413 2917295665702685179209163 := by
  unfold tailWord_5681413
  simp only [CollatzResearch.WordTrace]
  refine ⟨207218155766218483935336893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138145437177478989290224595 207218155766218483935336893)
  ·
    refine ⟨77706808412331931475751335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207218155766218483935336893 77706808412331931475751335)
    ·
      refine ⟨116560212618497897213627003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77706808412331931475751335 116560212618497897213627003)
      ·
        refine ⟨174840318927746845820440505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116560212618497897213627003 174840318927746845820440505)
        ·
          refine ⟨131130239195810134365330379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174840318927746845820440505 131130239195810134365330379)
          ·
            refine ⟨196695358793715201547995569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131130239195810134365330379 196695358793715201547995569)
            ·
              refine ⟨147521519095286401160996677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196695358793715201547995569 147521519095286401160996677)
              ·
                refine ⟨27660284830366200217686877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147521519095286401160996677 27660284830366200217686877)
                ·
                  refine ⟨10372606811387325081632579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27660284830366200217686877 10372606811387325081632579)
                  ·
                    refine ⟨15558910217080987622448869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10372606811387325081632579 15558910217080987622448869)
                    ·
                      refine ⟨2917295665702685179209163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15558910217080987622448869 2917295665702685179209163)
                      ·
                        rfl

theorem cell23_5681413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_5681413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681413 prefixEnd_5681413 := by exact prefixLift 5681413
  have htrace : WordTrace (prefixWord ++ tailWord_5681413) baseStart_5681413 baseEnd_5681413 := by
    simpa [prefixWord, tailWord_5681413, baseEnd_5681413] using wordTrace_append hprefix tailTrace_5681413
  have hstable : (prefixWord ++ tailWord_5681413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681413).length < 2 ^ (prefixWord ++ tailWord_5681413).sum := by decide
  have hdescent : baseEnd_5681413 < baseStart_5681413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681440 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_5681440 : Nat := 118140960795 + 5681440 * 2 ^ 59
def prefixEnd_5681440 : Nat := 4983230072969 + 3 ^ 40 * 5681440 * 2
def baseEnd_5681440 : Nat := 972436509893452191190513

theorem tailTrace_5681440 : CollatzResearch.WordTrace tailWord_5681440 prefixEnd_5681440 972436509893452191190513 := by
  unfold tailWord_5681440
  simp only [CollatzResearch.WordTrace]
  refine ⟨103609570268560333773284887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138146093691413778364379849 103609570268560333773284887)
  ·
    refine ⟨155414355402840500659927331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103609570268560333773284887 155414355402840500659927331)
    ·
      refine ⟨233121533104260750989890997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155414355402840500659927331 233121533104260750989890997)
      ·
        refine ⟨21855143728524445405302281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233121533104260750989890997 21855143728524445405302281)
        ·
          refine ⟨16391357796393334053976711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21855143728524445405302281 16391357796393334053976711)
          ·
            refine ⟨24587036694590001080965067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16391357796393334053976711 24587036694590001080965067)
            ·
              refine ⟨36880555041885001621447601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587036694590001080965067 36880555041885001621447601)
              ·
                refine ⟨27660416281413751216085701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36880555041885001621447601 27660416281413751216085701)
                ·
                  refine ⟨5186328052765078353016069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27660416281413751216085701 5186328052765078353016069)
                  ·
                    refine ⟨972436509893452191190513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186328052765078353016069 972436509893452191190513)
                    ·
                      rfl

theorem cell23_5681440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_5681440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681440 prefixEnd_5681440 := by exact prefixLift 5681440
  have htrace : WordTrace (prefixWord ++ tailWord_5681440) baseStart_5681440 baseEnd_5681440 := by
    simpa [prefixWord, tailWord_5681440, baseEnd_5681440] using wordTrace_append hprefix tailTrace_5681440
  have hstable : (prefixWord ++ tailWord_5681440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681440).length < 2 ^ (prefixWord ++ tailWord_5681440).sum := by decide
  have hdescent : baseEnd_5681440 < baseStart_5681440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681443 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4]
def baseStart_5681443 : Nat := 118140960795 + 5681443 * 2 ^ 59
def prefixEnd_5681443 : Nat := 4983230072969 + 3 ^ 40 * 5681443 * 2
def baseEnd_5681443 : Nat := 2917311070122320061834025

theorem tailTrace_5681443 : CollatzResearch.WordTrace tailWord_5681443 prefixEnd_5681443 2917311070122320061834025 := by
  unfold tailWord_5681443
  simp only [CollatzResearch.WordTrace]
  refine ⟨207219249956109799058928983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138146166637406532705952655 207219249956109799058928983)
  ·
    refine ⟨310828874934164698588393475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207219249956109799058928983 310828874934164698588393475)
    ·
      refine ⟨466243312401247047882590213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310828874934164698588393475 466243312401247047882590213)
      ·
        refine ⟨87420621075233821477985665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466243312401247047882590213 87420621075233821477985665)
        ·
          refine ⟨65565465806425366108489249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87420621075233821477985665 65565465806425366108489249)
          ·
            refine ⟨49174099354819024581366937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65565465806425366108489249 49174099354819024581366937)
            ·
              refine ⟨36880574516114268436025203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49174099354819024581366937 36880574516114268436025203)
              ·
                refine ⟨55320861774171402654037805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36880574516114268436025203 55320861774171402654037805)
                ·
                  refine ⟨20745323165314275995264177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55320861774171402654037805 20745323165314275995264177)
                  ·
                    refine ⟨15558992373985706996448133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20745323165314275995264177 15558992373985706996448133)
                    ·
                      refine ⟨2917311070122320061834025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15558992373985706996448133 2917311070122320061834025)
                      ·
                        rfl

theorem cell23_5681443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_5681443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681443 prefixEnd_5681443 := by exact prefixLift 5681443
  have htrace : WordTrace (prefixWord ++ tailWord_5681443) baseStart_5681443 baseEnd_5681443 := by
    simpa [prefixWord, tailWord_5681443, baseEnd_5681443] using wordTrace_append hprefix tailTrace_5681443
  have hstable : (prefixWord ++ tailWord_5681443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681443).length < 2 ^ (prefixWord ++ tailWord_5681443).sum := by decide
  have hdescent : baseEnd_5681443 < baseStart_5681443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681460 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_5681460 : Nat := 118140960795 + 5681460 * 2 ^ 59
def prefixEnd_5681460 : Nat := 4983230072969 + 3 ^ 40 * 5681460 * 2
def baseEnd_5681460 : Nat := 2917319799293446495321447

theorem tailTrace_5681460 : CollatzResearch.WordTrace tailWord_5681460 prefixEnd_5681460 2917319799293446495321447 := by
  unfold tailWord_5681460
  simp only [CollatzResearch.WordTrace]
  refine ⟨103609934998524105481148917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138146579998032140641531889 103609934998524105481148917)
  ·
    refine ⟨9713431406111634888857711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103609934998524105481148917 9713431406111634888857711)
    ·
      refine ⟨14570147109167452333286567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9713431406111634888857711 14570147109167452333286567)
      ·
        refine ⟨21855220663751178499929851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14570147109167452333286567 21855220663751178499929851)
        ·
          refine ⟨32782830995626767749894777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21855220663751178499929851 32782830995626767749894777)
          ·
            refine ⟨24587123246720075812421083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32782830995626767749894777 24587123246720075812421083)
            ·
              refine ⟨36880684870080113718631625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587123246720075812421083 36880684870080113718631625)
              ·
                refine ⟨27660513652560085288973719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36880684870080113718631625 27660513652560085288973719)
                ·
                  refine ⟨41490770478840127933460579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27660513652560085288973719 41490770478840127933460579)
                  ·
                    refine ⟨62236155718260191900190869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41490770478840127933460579 62236155718260191900190869)
                    ·
                      refine ⟨2917319799293446495321447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62236155718260191900190869 2917319799293446495321447)
                      ·
                        rfl

theorem cell23_5681460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_5681460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681460 prefixEnd_5681460 := by exact prefixLift 5681460
  have htrace : WordTrace (prefixWord ++ tailWord_5681460) baseStart_5681460 baseEnd_5681460 := by
    simpa [prefixWord, tailWord_5681460, baseEnd_5681460] using wordTrace_append hprefix tailTrace_5681460
  have hstable : (prefixWord ++ tailWord_5681460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681460).length < 2 ^ (prefixWord ++ tailWord_5681460).sum := by decide
  have hdescent : baseEnd_5681460 < baseStart_5681460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681464 : List Nat := [2, 1, 2, 1, 3, 1, 2, 6, 1, 2, 2]
def baseStart_5681464 : Nat := 118140960795 + 5681464 * 2 ^ 59
def prefixEnd_5681464 : Nat := 4983230072969 + 3 ^ 40 * 5681464 * 2
def baseEnd_5681464 : Nat := 2917321853216064479671429

theorem tailTrace_5681464 : CollatzResearch.WordTrace tailWord_5681464 prefixEnd_5681464 2917321853216064479671429 := by
  unfold tailWord_5681464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103610007944516859822721723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138146677259355813096962297 103610007944516859822721723)
  ·
    refine ⟨155415011916775289734082585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103610007944516859822721723 155415011916775289734082585)
    ·
      refine ⟨116561258937581467300561939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155415011916775289734082585 116561258937581467300561939)
      ·
        refine ⟨174841888406372200950842909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116561258937581467300561939 174841888406372200950842909)
        ·
          refine ⟨65565708152389575356566091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174841888406372200950842909 65565708152389575356566091)
          ·
            refine ⟨98348562228584363034849137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65565708152389575356566091 98348562228584363034849137)
            ·
              refine ⟨73761421671438272276136853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98348562228584363034849137 73761421671438272276136853)
              ·
                refine ⟨3457566640848669012943915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73761421671438272276136853 3457566640848669012943915)
                ·
                  refine ⟨5186349961273003519415873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457566640848669012943915 5186349961273003519415873)
                  ·
                    refine ⟨3889762470954752639561905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186349961273003519415873 3889762470954752639561905)
                    ·
                      refine ⟨2917321853216064479671429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889762470954752639561905 2917321853216064479671429)
                      ·
                        rfl

theorem cell23_5681464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_5681464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681464 prefixEnd_5681464 := by exact prefixLift 5681464
  have htrace : WordTrace (prefixWord ++ tailWord_5681464) baseStart_5681464 baseEnd_5681464 := by
    simpa [prefixWord, tailWord_5681464, baseEnd_5681464] using wordTrace_append hprefix tailTrace_5681464
  have hstable : (prefixWord ++ tailWord_5681464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681464).length < 2 ^ (prefixWord ++ tailWord_5681464).sum := by decide
  have hdescent : baseEnd_5681464 < baseStart_5681464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681470 : List Nat := [4, 2, 1, 2, 1, 3, 2, 8]
def baseStart_5681470 : Nat := 118140960795 + 5681470 * 2 ^ 59
def prefixEnd_5681470 : Nat := 4983230072969 + 3 ^ 40 * 5681470 * 2
def baseEnd_5681470 : Nat := 108049071633333016896163

theorem tailTrace_5681470 : CollatzResearch.WordTrace tailWord_5681470 prefixEnd_5681470 108049071633333016896163 := by
  unfold tailWord_5681470
  simp only [CollatzResearch.WordTrace]
  refine ⟨25902529340876497833770233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138146823151341321780107909 25902529340876497833770233)
  ·
    refine ⟨19426897005657373375327675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25902529340876497833770233 19426897005657373375327675)
    ·
      refine ⟨29140345508486060062991513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19426897005657373375327675 29140345508486060062991513)
      ·
        refine ⟨21855259131364545047243635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29140345508486060062991513 21855259131364545047243635)
        ·
          refine ⟨32782888697046817570865453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21855259131364545047243635 32782888697046817570865453)
          ·
            refine ⟨12293583261392556589074545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32782888697046817570865453 12293583261392556589074545)
            ·
              refine ⟨9220187446044417441805909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12293583261392556589074545 9220187446044417441805909)
              ·
                refine ⟨108049071633333016896163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9220187446044417441805909 108049071633333016896163)
                ·
                  rfl

theorem cell23_5681470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_5681470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681470 prefixEnd_5681470 := by exact prefixLift 5681470
  have htrace : WordTrace (prefixWord ++ tailWord_5681470) baseStart_5681470 baseEnd_5681470 := by
    simpa [prefixWord, tailWord_5681470, baseEnd_5681470] using wordTrace_append hprefix tailTrace_5681470
  have hstable : (prefixWord ++ tailWord_5681470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681470).length < 2 ^ (prefixWord ++ tailWord_5681470).sum := by decide
  have hdescent : baseEnd_5681470 < baseStart_5681470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681513 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 6]
def baseStart_5681513 : Nat := 118140960795 + 5681513 * 2 ^ 59
def prefixEnd_5681513 : Nat := 4983230072969 + 3 ^ 40 * 5681513 * 2
def baseEnd_5681513 : Nat := 972449004589378262652901

theorem tailTrace_5681513 : CollatzResearch.WordTrace tailWord_5681513 prefixEnd_5681513 972449004589378262652901 := by
  unfold tailWord_5681513
  simp only [CollatzResearch.WordTrace]
  refine ⟨207221803065856201013977193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138147868710570800675984795 207221803065856201013977193)
  ·
    refine ⟨155416352299392150760482895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207221803065856201013977193 155416352299392150760482895)
    ·
      refine ⟨233124528449088226140724343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155416352299392150760482895 233124528449088226140724343)
      ·
        refine ⟨349686792673632339211086515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233124528449088226140724343 349686792673632339211086515)
        ·
          refine ⟨524530189010448508816629773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349686792673632339211086515 524530189010448508816629773)
          ·
            refine ⟨196698820878918190806236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524530189010448508816629773 196698820878918190806236165)
            ·
              refine ⟨36881028914797160776169281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196698820878918190806236165 36881028914797160776169281)
              ·
                refine ⟨27660771686097870582126961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36881028914797160776169281 27660771686097870582126961)
                ·
                  refine ⟨20745578764573402936595221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27660771686097870582126961 20745578764573402936595221)
                  ·
                    refine ⟨972449004589378262652901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20745578764573402936595221 972449004589378262652901)
                    ·
                      rfl

theorem cell23_5681513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 6].length) (baseStart_5681513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681513 prefixEnd_5681513 := by exact prefixLift 5681513
  have htrace : WordTrace (prefixWord ++ tailWord_5681513) baseStart_5681513 baseEnd_5681513 := by
    simpa [prefixWord, tailWord_5681513, baseEnd_5681513] using wordTrace_append hprefix tailTrace_5681513
  have hstable : (prefixWord ++ tailWord_5681513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681513).length < 2 ^ (prefixWord ++ tailWord_5681513).sum := by decide
  have hdescent : baseEnd_5681513 < baseStart_5681513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681514 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_5681514 : Nat := 118140960795 + 5681514 * 2 ^ 59
def prefixEnd_5681514 : Nat := 4983230072969 + 3 ^ 40 * 5681514 * 2
def baseEnd_5681514 : Nat := 2917347527248789284046199

theorem tailTrace_5681514 : CollatzResearch.WordTrace tailWord_5681514 prefixEnd_5681514 2917347527248789284046199 := by
  unfold tailWord_5681514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51805459884713144546190899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138147893025901718789842397 51805459884713144546190899)
  ·
    refine ⟨77708189827069716819286349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51805459884713144546190899 77708189827069716819286349)
    ·
      refine ⟨29140571185151143807232381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77708189827069716819286349 29140571185151143807232381)
      ·
        refine ⟨10927714194431678927712143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29140571185151143807232381 10927714194431678927712143)
        ·
          refine ⟨16391571291647518391568215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10927714194431678927712143 16391571291647518391568215)
          ·
            refine ⟨24587356937471277587352323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16391571291647518391568215 24587356937471277587352323)
            ·
              refine ⟨36881035406206916381028485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24587356937471277587352323 36881035406206916381028485)
              ·
                refine ⟨6915194138663796821442841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36881035406206916381028485 6915194138663796821442841)
                ·
                  refine ⟨5186395603997847616082131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6915194138663796821442841 5186395603997847616082131)
                  ·
                    refine ⟨7779593405996771424123197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5186395603997847616082131 7779593405996771424123197)
                    ·
                      refine ⟨2917347527248789284046199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779593405996771424123197 2917347527248789284046199)
                      ·
                        rfl

theorem cell23_5681514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_5681514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681514 prefixEnd_5681514 := by exact prefixLift 5681514
  have htrace : WordTrace (prefixWord ++ tailWord_5681514) baseStart_5681514 baseEnd_5681514 := by
    simpa [prefixWord, tailWord_5681514, baseEnd_5681514] using wordTrace_append hprefix tailTrace_5681514
  have hstable : (prefixWord ++ tailWord_5681514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681514).length < 2 ^ (prefixWord ++ tailWord_5681514).sum := by decide
  have hdescent : baseEnd_5681514 < baseStart_5681514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681540 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_5681540 : Nat := 118140960795 + 5681540 * 2 ^ 59
def prefixEnd_5681540 : Nat := 4983230072969 + 3 ^ 40 * 5681540 * 2
def baseEnd_5681540 : Nat := 2917360877745806182321079

theorem tailTrace_5681540 : CollatzResearch.WordTrace tailWord_5681540 prefixEnd_5681540 2917360877745806182321079 := by
  unfold tailWord_5681540
  simp only [CollatzResearch.WordTrace]
  refine ⟨103611393918379192312605037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138148525224505589750140049 103611393918379192312605037)
  ·
    refine ⟨38854272719392197117226889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103611393918379192312605037 38854272719392197117226889)
    ·
      refine ⟨29140704539544147837920167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38854272719392197117226889 29140704539544147837920167)
      ·
        refine ⟨43711056809316221756880251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29140704539544147837920167 43711056809316221756880251)
        ·
          refine ⟨65566585213974332635320377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43711056809316221756880251 65566585213974332635320377)
          ·
            refine ⟨49174938910480749476490283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65566585213974332635320377 49174938910480749476490283)
            ·
              refine ⟨73762408365721124214735425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49174938910480749476490283 73762408365721124214735425)
              ·
                refine ⟨55321806274290843161051569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73762408365721124214735425 55321806274290843161051569)
                ·
                  refine ⟨41491354705718132370788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55321806274290843161051569 41491354705718132370788677)
                  ·
                    refine ⟨7779629007322149819522877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41491354705718132370788677 7779629007322149819522877)
                    ·
                      refine ⟨2917360877745806182321079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7779629007322149819522877 2917360877745806182321079)
                      ·
                        rfl

theorem cell23_5681540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_5681540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681540 prefixEnd_5681540 := by exact prefixLift 5681540
  have htrace : WordTrace (prefixWord ++ tailWord_5681540) baseStart_5681540 baseEnd_5681540 := by
    simpa [prefixWord, tailWord_5681540, baseEnd_5681540] using wordTrace_append hprefix tailTrace_5681540
  have hstable : (prefixWord ++ tailWord_5681540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681540).length < 2 ^ (prefixWord ++ tailWord_5681540).sum := by decide
  have hdescent : baseEnd_5681540 < baseStart_5681540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681571 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 2, 2, 2]
def baseStart_5681571 : Nat := 118140960795 + 5681571 * 2 ^ 59
def prefixEnd_5681571 : Nat := 4983230072969 + 3 ^ 40 * 5681571 * 2
def baseEnd_5681571 : Nat := 2917376795646095561033437

theorem tailTrace_5681571 : CollatzResearch.WordTrace tailWord_5681571 prefixEnd_5681571 2917376795646095561033437 := by
  unfold tailWord_5681571
  simp only [CollatzResearch.WordTrace]
  refine ⟨207223918499646076919588567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138149278999764051279725711 207223918499646076919588567)
  ·
    refine ⟨310835877749469115379382851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207223918499646076919588567 310835877749469115379382851)
    ·
      refine ⟨466253816624203673069074277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310835877749469115379382851 466253816624203673069074277)
      ·
        refine ⟨87422590617038188700451427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466253816624203673069074277 87422590617038188700451427)
        ·
          refine ⟨131133885925557283050677141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87422590617038188700451427 131133885925557283050677141)
          ·
            refine ⟨6146900902760497643000491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131133885925557283050677141 6146900902760497643000491)
            ·
              refine ⟨9220351354140746464500737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6146900902760497643000491 9220351354140746464500737)
              ·
                refine ⟨6915263515605559848375553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9220351354140746464500737 6915263515605559848375553)
                ·
                  refine ⟨5186447636704169886281665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6915263515605559848375553 5186447636704169886281665)
                  ·
                    refine ⟨3889835727528127414711249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186447636704169886281665 3889835727528127414711249)
                    ·
                      refine ⟨2917376795646095561033437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889835727528127414711249 2917376795646095561033437)
                      ·
                        rfl

theorem cell23_5681571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 2, 2].length) (baseStart_5681571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681571 prefixEnd_5681571 := by exact prefixLift 5681571
  have htrace : WordTrace (prefixWord ++ tailWord_5681571) baseStart_5681571 baseEnd_5681571 := by
    simpa [prefixWord, tailWord_5681571, baseEnd_5681571] using wordTrace_append hprefix tailTrace_5681571
  have hstable : (prefixWord ++ tailWord_5681571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681571).length < 2 ^ (prefixWord ++ tailWord_5681571).sum := by decide
  have hdescent : baseEnd_5681571 < baseStart_5681571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681603 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 10]
def baseStart_5681603 : Nat := 118140960795 + 5681603 * 2 ^ 59
def prefixEnd_5681603 : Nat := 4983230072969 + 3 ^ 40 * 5681603 * 2
def baseEnd_5681603 : Nat := 972464409009013145277763

theorem tailTrace_5681603 : CollatzResearch.WordTrace tailWord_5681603 prefixEnd_5681603 972464409009013145277763 := by
  unfold tailWord_5681603
  simp only [CollatzResearch.WordTrace]
  refine ⟨207225085635530146384753463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138150057090353430923168975 207225085635530146384753463)
  ·
    refine ⟨310837628453295219577130195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207225085635530146384753463 310837628453295219577130195)
    ·
      refine ⟨466256442679942829365695293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310837628453295219577130195 466256442679942829365695293)
      ·
        refine ⟨174846166004978561012135735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466256442679942829365695293 174846166004978561012135735)
        ·
          refine ⟨262269249007467841518203603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174846166004978561012135735 262269249007467841518203603)
          ·
            refine ⟨393403873511201762277305405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262269249007467841518203603 393403873511201762277305405)
            ·
              refine ⟨147526452566700660853989527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393403873511201762277305405 147526452566700660853989527)
              ·
                refine ⟨221289678850050991280984291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147526452566700660853989527 221289678850050991280984291)
                ·
                  refine ⟨331934518275076486921476437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221289678850050991280984291 331934518275076486921476437)
                  ·
                    refine ⟨972464409009013145277763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 331934518275076486921476437 972464409009013145277763)
                    ·
                      rfl

theorem cell23_5681603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 10].length) (baseStart_5681603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681603 prefixEnd_5681603 := by exact prefixLift 5681603
  have htrace : WordTrace (prefixWord ++ tailWord_5681603) baseStart_5681603 baseEnd_5681603 := by
    simpa [prefixWord, tailWord_5681603, baseEnd_5681603] using wordTrace_append hprefix tailTrace_5681603
  have hstable : (prefixWord ++ tailWord_5681603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681603).length < 2 ^ (prefixWord ++ tailWord_5681603).sum := by decide
  have hdescent : baseEnd_5681603 < baseStart_5681603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681610 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_5681610 : Nat := 118140960795 + 5681610 * 2 ^ 59
def prefixEnd_5681610 : Nat := 4983230072969 + 3 ^ 40 * 5681610 * 2
def baseEnd_5681610 : Nat := 2917396821391620908445757

theorem tailTrace_5681610 : CollatzResearch.WordTrace tailWord_5681610 prefixEnd_5681610 2917396821391620908445757 := by
  unfold tailWord_5681610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51806335236626196645064571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138150227297669857720172189 51806335236626196645064571)
  ·
    refine ⟨77709502854939294967596857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51806335236626196645064571 77709502854939294967596857)
    ·
      refine ⟨58282127141204471225697643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77709502854939294967596857 58282127141204471225697643)
      ·
        refine ⟨87423190711806706838546465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58282127141204471225697643 87423190711806706838546465)
        ·
          refine ⟨65567393033855030128909849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87423190711806706838546465 65567393033855030128909849)
          ·
            refine ⟨49175544775391272596682387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65567393033855030128909849 49175544775391272596682387)
            ·
              refine ⟨73763317163086908895023581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49175544775391272596682387 73763317163086908895023581)
              ·
                refine ⟨27661243936157590835633843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73763317163086908895023581 27661243936157590835633843)
                ·
                  refine ⟨41491865904236386253450765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27661243936157590835633843 41491865904236386253450765)
                  ·
                    refine ⟨15559449714088644845044037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41491865904236386253450765 15559449714088644845044037)
                    ·
                      refine ⟨2917396821391620908445757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15559449714088644845044037 2917396821391620908445757)
                      ·
                        rfl

theorem cell23_5681610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_5681610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681610 prefixEnd_5681610 := by exact prefixLift 5681610
  have htrace : WordTrace (prefixWord ++ tailWord_5681610) baseStart_5681610 baseEnd_5681610 := by
    simpa [prefixWord, tailWord_5681610, baseEnd_5681610] using wordTrace_append hprefix tailTrace_5681610
  have hstable : (prefixWord ++ tailWord_5681610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681610).length < 2 ^ (prefixWord ++ tailWord_5681610).sum := by decide
  have hdescent : baseEnd_5681610 < baseStart_5681610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681684 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 6]
def baseStart_5681684 : Nat := 118140960795 + 5681684 * 2 ^ 59
def prefixEnd_5681684 : Nat := 4983230072969 + 3 ^ 40 * 5681684 * 2
def baseEnd_5681684 : Nat := 324159424328894846546713

theorem tailTrace_5681684 : CollatzResearch.WordTrace tailWord_5681684 prefixEnd_5681684 324159424328894846546713 := by
  unfold tailWord_5681684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103614019974118348609226053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138152026632157798145634737 103614019974118348609226053)
  ·
    refine ⟨19427628745147190364229885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103614019974118348609226053 19427628745147190364229885)
    ·
      refine ⟨7285360779430196386586207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19427628745147190364229885 7285360779430196386586207)
      ·
        refine ⟨10928041169145294579879311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7285360779430196386586207 10928041169145294579879311)
        ·
          refine ⟨16392061753717941869818967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928041169145294579879311 16392061753717941869818967)
          ·
            refine ⟨24588092630576912804728451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16392061753717941869818967 24588092630576912804728451)
            ·
              refine ⟨36882138945865369207092677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24588092630576912804728451 36882138945865369207092677)
              ·
                refine ⟨6915401052349756726329877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36882138945865369207092677 6915401052349756726329877)
                ·
                  refine ⟨324159424328894846546713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6915401052349756726329877 324159424328894846546713)
                  ·
                    rfl

theorem cell23_5681684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_5681684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681684 prefixEnd_5681684 := by exact prefixLift 5681684
  have htrace : WordTrace (prefixWord ++ tailWord_5681684) baseStart_5681684 baseEnd_5681684 := by
    simpa [prefixWord, tailWord_5681684, baseEnd_5681684] using wordTrace_append hprefix tailTrace_5681684
  have hstable : (prefixWord ++ tailWord_5681684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681684).length < 2 ^ (prefixWord ++ tailWord_5681684).sum := by decide
  have hdescent : baseEnd_5681684 < baseStart_5681684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681688 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 1, 4]
def baseStart_5681688 : Nat := 118140960795 + 5681688 * 2 ^ 59
def prefixEnd_5681688 : Nat := 4983230072969 + 3 ^ 40 * 5681688 * 2
def baseEnd_5681688 : Nat := 972478957627557201090133

theorem tailTrace_5681688 : CollatzResearch.WordTrace tailWord_5681688 prefixEnd_5681688 972478957627557201090133 := by
  unfold tailWord_5681688
  simp only [CollatzResearch.WordTrace]
  refine ⟨103614092920111102950798859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138152123893481470601065145 103614092920111102950798859)
  ·
    refine ⟨155421139380166654426198289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103614092920111102950798859 155421139380166654426198289)
    ·
      refine ⟨116565854535124990819648717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155421139380166654426198289 116565854535124990819648717)
      ·
        refine ⟨43712195450671871557368269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116565854535124990819648717 43712195450671871557368269)
        ·
          refine ⟨16392073294001951834013101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43712195450671871557368269 16392073294001951834013101)
          ·
            refine ⟨6147027485250731937754913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16392073294001951834013101 6147027485250731937754913)
            ·
              refine ⟨4610270613938048953316185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147027485250731937754913 4610270613938048953316185)
              ·
                refine ⟨3457702960453536714987139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610270613938048953316185 3457702960453536714987139)
                ·
                  refine ⟨5186554440680305072480709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457702960453536714987139 5186554440680305072480709)
                  ·
                    refine ⟨972478957627557201090133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186554440680305072480709 972478957627557201090133)
                    ·
                      rfl

theorem cell23_5681688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_5681688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681688 prefixEnd_5681688 := by exact prefixLift 5681688
  have htrace : WordTrace (prefixWord ++ tailWord_5681688) baseStart_5681688 baseEnd_5681688 := by
    simpa [prefixWord, tailWord_5681688, baseEnd_5681688] using wordTrace_append hprefix tailTrace_5681688
  have hstable : (prefixWord ++ tailWord_5681688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681688).length < 2 ^ (prefixWord ++ tailWord_5681688).sum := by decide
  have hdescent : baseEnd_5681688 < baseStart_5681688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681717 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_5681717 : Nat := 118140960795 + 5681717 * 2 ^ 59
def prefixEnd_5681717 : Nat := 4983230072969 + 3 ^ 40 * 5681717 * 2
def baseEnd_5681717 : Nat := 2917451763821651989807765

theorem tailTrace_5681717 : CollatzResearch.WordTrace tailWord_5681717 prefixEnd_5681717 2917451763821651989807765 := by
  unfold tailWord_5681717
  simp only [CollatzResearch.WordTrace]
  refine ⟨207229243557117143854403405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138152829038078095902935603 207229243557117143854403405)
  ·
    refine ⟨77710966333918928945401277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207229243557117143854403405 77710966333918928945401277)
    ·
      refine ⟨29141612375219598354525479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77710966333918928945401277 29141612375219598354525479)
      ·
        refine ⟨43712418562829397531788219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29141612375219598354525479 43712418562829397531788219)
        ·
          refine ⟨65568627844244096297682329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43712418562829397531788219 65568627844244096297682329)
          ·
            refine ⟨49176470883183072223261747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65568627844244096297682329 49176470883183072223261747)
            ·
              refine ⟨73764706324774608334892621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49176470883183072223261747 73764706324774608334892621)
              ·
                refine ⟨27661764871790478125584733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73764706324774608334892621 27661764871790478125584733)
                ·
                  refine ⟨10373161826921429297094275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27661764871790478125584733 10373161826921429297094275)
                  ·
                    refine ⟨15559742740382143945641413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373161826921429297094275 15559742740382143945641413)
                    ·
                      refine ⟨2917451763821651989807765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15559742740382143945641413 2917451763821651989807765)
                      ·
                        rfl

theorem cell23_5681717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_5681717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681717 prefixEnd_5681717 := by exact prefixLift 5681717
  have htrace : WordTrace (prefixWord ++ tailWord_5681717) baseStart_5681717 baseEnd_5681717 := by
    simpa [prefixWord, tailWord_5681717, baseEnd_5681717] using wordTrace_append hprefix tailTrace_5681717
  have hstable : (prefixWord ++ tailWord_5681717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681717).length < 2 ^ (prefixWord ++ tailWord_5681717).sum := by decide
  have hdescent : baseEnd_5681717 < baseStart_5681717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681727 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 4, 4]
def baseStart_5681727 : Nat := 118140960795 + 5681727 * 2 ^ 59
def prefixEnd_5681727 : Nat := 4983230072969 + 3 ^ 40 * 5681727 * 2
def baseEnd_5681727 : Nat := 972485632876065650227573

theorem tailTrace_5681727 : CollatzResearch.WordTrace tailWord_5681727 prefixEnd_5681727 972485632876065650227573 := by
  unfold tailWord_5681727
  simp only [CollatzResearch.WordTrace]
  refine ⟨207229608287080915562267435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138153072191387277041511623 207229608287080915562267435)
  ·
    refine ⟨310844412430621373343401153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207229608287080915562267435 310844412430621373343401153)
    ·
      refine ⟨233133309322966030007550865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310844412430621373343401153 233133309322966030007550865)
      ·
        refine ⟨174849981992224522505663149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233133309322966030007550865 174849981992224522505663149)
        ·
          refine ⟨65568743247084195939623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174849981992224522505663149 65568743247084195939623681)
          ·
            refine ⟨49176557435313146954717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65568743247084195939623681 49176557435313146954717761)
            ·
              refine ⟨36882418076484860216038321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49176557435313146954717761 36882418076484860216038321)
              ·
                refine ⟨27661813557363645162028741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36882418076484860216038321 27661813557363645162028741)
                ·
                  refine ⟨5186590042005683467880389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27661813557363645162028741 5186590042005683467880389)
                  ·
                    refine ⟨972485632876065650227573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186590042005683467880389 972485632876065650227573)
                    ·
                      rfl

theorem cell23_5681727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_5681727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681727 prefixEnd_5681727 := by exact prefixLift 5681727
  have htrace : WordTrace (prefixWord ++ tailWord_5681727) baseStart_5681727 baseEnd_5681727 := by
    simpa [prefixWord, tailWord_5681727, baseEnd_5681727] using wordTrace_append hprefix tailTrace_5681727
  have hstable : (prefixWord ++ tailWord_5681727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681727).length < 2 ^ (prefixWord ++ tailWord_5681727).sum := by decide
  have hdescent : baseEnd_5681727 < baseStart_5681727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681740 : List Nat := [2, 2, 1, 3, 1, 2, 12]
def baseStart_5681740 : Nat := 118140960795 + 5681740 * 2 ^ 59
def prefixEnd_5681740 : Nat := 4983230072969 + 3 ^ 40 * 5681740 * 2
def baseEnd_5681740 : Nat := 36018068813292659257039

theorem tailTrace_5681740 : CollatzResearch.WordTrace tailWord_5681740 prefixEnd_5681740 36018068813292659257039 := by
  unfold tailWord_5681740
  simp only [CollatzResearch.WordTrace]
  refine ⟨103615041218016909391245337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138153388290689212521660449 103615041218016909391245337)
  ·
    refine ⟨77711280913512682043434003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103615041218016909391245337 77711280913512682043434003)
    ·
      refine ⟨116566921370269023065151005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77711280913512682043434003 116566921370269023065151005)
      ·
        refine ⟨43712595513850883649431627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116566921370269023065151005 43712595513850883649431627)
        ·
          refine ⟨65568893270776325474147441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43712595513850883649431627 65568893270776325474147441)
          ·
            refine ⟨49176669953082244105610581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65568893270776325474147441 49176669953082244105610581)
            ·
              refine ⟨36018068813292659257039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49176669953082244105610581 36018068813292659257039)
              ·
                rfl

theorem cell23_5681740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 12].length) (baseStart_5681740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681740 prefixEnd_5681740 := by exact prefixLift 5681740
  have htrace : WordTrace (prefixWord ++ tailWord_5681740) baseStart_5681740 baseEnd_5681740 := by
    simpa [prefixWord, tailWord_5681740, baseEnd_5681740] using wordTrace_append hprefix tailTrace_5681740
  have hstable : (prefixWord ++ tailWord_5681740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681740).length < 2 ^ (prefixWord ++ tailWord_5681740).sum := by decide
  have hdescent : baseEnd_5681740 < baseStart_5681740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681751 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 3, 2, 2]
def baseStart_5681751 : Nat := 118140960795 + 5681751 * 2 ^ 59
def prefixEnd_5681751 : Nat := 4983230072969 + 3 ^ 40 * 5681751 * 2
def baseEnd_5681751 : Nat := 2917469222163904856782609

theorem tailTrace_5681751 : CollatzResearch.WordTrace tailWord_5681751 prefixEnd_5681751 2917469222163904856782609 := by
  unfold tailWord_5681751
  simp only [CollatzResearch.WordTrace]
  refine ⟨207230483638993967661141107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138153655759329311774094071 207230483638993967661141107)
  ·
    refine ⟨310845725458490951491711661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207230483638993967661141107 310845725458490951491711661)
    ·
      refine ⟨116567147046934106809391873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310845725458490951491711661 116567147046934106809391873)
      ·
        refine ⟨87425360285200580107043905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116567147046934106809391873 87425360285200580107043905)
        ·
          refine ⟨65569020213900435080282929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87425360285200580107043905 65569020213900435080282929)
          ·
            refine ⟨49176765160425326310212197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65569020213900435080282929 49176765160425326310212197)
            ·
              refine ⟨9220643467579748683164787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49176765160425326310212197 9220643467579748683164787)
              ·
                refine ⟨13830965201369623024747181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9220643467579748683164787 13830965201369623024747181)
                ·
                  refine ⟨5186611950513608634280193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13830965201369623024747181 5186611950513608634280193)
                  ·
                    refine ⟨3889958962885206475710145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186611950513608634280193 3889958962885206475710145)
                    ·
                      refine ⟨2917469222163904856782609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889958962885206475710145 2917469222163904856782609)
                      ·
                        rfl

theorem cell23_5681751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_5681751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681751 prefixEnd_5681751 := by exact prefixLift 5681751
  have htrace : WordTrace (prefixWord ++ tailWord_5681751) baseStart_5681751 baseEnd_5681751 := by
    simpa [prefixWord, tailWord_5681751, baseEnd_5681751] using wordTrace_append hprefix tailTrace_5681751
  have hstable : (prefixWord ++ tailWord_5681751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681751).length < 2 ^ (prefixWord ++ tailWord_5681751).sum := by decide
  have hdescent : baseEnd_5681751 < baseStart_5681751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681761 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_5681761 : Nat := 118140960795 + 5681761 * 2 ^ 59
def prefixEnd_5681761 : Nat := 4983230072969 + 3 ^ 40 * 5681761 * 2
def baseEnd_5681761 : Nat := 972491452323483272552521

theorem tailTrace_5681761 : CollatzResearch.WordTrace tailWord_5681761 prefixEnd_5681761 972491452323483272552521 := by
  unfold tailWord_5681761
  simp only [CollatzResearch.WordTrace]
  refine ⟨207230848368957739369005137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138153898912638492912670091 207230848368957739369005137)
  ·
    refine ⟨155423136276718304526753853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207230848368957739369005137 155423136276718304526753853)
    ·
      refine ⟨58283676103769364197532695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155423136276718304526753853 58283676103769364197532695)
      ·
        refine ⟨87425514155654046296299043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58283676103769364197532695 87425514155654046296299043)
        ·
          refine ⟨131138271233481069444448565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87425514155654046296299043 131138271233481069444448565)
          ·
            refine ⟨12294212928138850260417053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131138271233481069444448565 12294212928138850260417053)
            ·
              refine ⟨4610329848052068847656395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12294212928138850260417053 4610329848052068847656395)
              ·
                refine ⟨6915494772078103271484593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610329848052068847656395 6915494772078103271484593)
                ·
                  refine ⟨5186621079058577453613445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6915494772078103271484593 5186621079058577453613445)
                  ·
                    refine ⟨972491452323483272552521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5186621079058577453613445 972491452323483272552521)
                    ·
                      rfl

theorem cell23_5681761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_5681761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681761 prefixEnd_5681761 := by exact prefixLift 5681761
  have htrace : WordTrace (prefixWord ++ tailWord_5681761) baseStart_5681761 baseEnd_5681761 := by
    simpa [prefixWord, tailWord_5681761, baseEnd_5681761] using wordTrace_append hprefix tailTrace_5681761
  have hstable : (prefixWord ++ tailWord_5681761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681761).length < 2 ^ (prefixWord ++ tailWord_5681761).sum := by decide
  have hdescent : baseEnd_5681761 < baseStart_5681761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681774 : List Nat := [4, 1, 2, 2, 2, 1, 4, 7]
def baseStart_5681774 : Nat := 118140960795 + 5681774 * 2 ^ 59
def prefixEnd_5681774 : Nat := 4983230072969 + 3 ^ 40 * 5681774 * 2
def baseEnd_5681774 : Nat := 108054853045146602473889

theorem tailTrace_5681774 : CollatzResearch.WordTrace tailWord_5681774 prefixEnd_5681774 108054853045146602473889 := by
  unfold tailWord_5681774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25903915314738830323653547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138154215011940428392818917 25903915314738830323653547)
  ·
    refine ⟨38855872972108245485480321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25903915314738830323653547 38855872972108245485480321)
    ·
      refine ⟨29141904729081184114110241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38855872972108245485480321 29141904729081184114110241)
      ·
        refine ⟨21856428546810888085582681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29141904729081184114110241 21856428546810888085582681)
        ·
          refine ⟨16392321410108166064187011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21856428546810888085582681 16392321410108166064187011)
          ·
            refine ⟨24588482115162249096280517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16392321410108166064187011 24588482115162249096280517)
            ·
              refine ⟨4610340396592921705552597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24588482115162249096280517 4610340396592921705552597)
              ·
                refine ⟨108054853045146602473889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4610340396592921705552597 108054853045146602473889)
                ·
                  rfl

theorem cell23_5681774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_5681774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681774 prefixEnd_5681774 := by exact prefixLift 5681774
  have htrace : WordTrace (prefixWord ++ tailWord_5681774) baseStart_5681774 baseEnd_5681774 := by
    simpa [prefixWord, tailWord_5681774, baseEnd_5681774] using wordTrace_append hprefix tailTrace_5681774
  have hstable : (prefixWord ++ tailWord_5681774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681774).length < 2 ^ (prefixWord ++ tailWord_5681774).sum := by decide
  have hdescent : baseEnd_5681774 < baseStart_5681774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681785 : List Nat := [1, 2, 1, 3, 3, 4, 1, 3, 1, 2, 2]
def baseStart_5681785 : Nat := 118140960795 + 5681785 * 2 ^ 59
def prefixEnd_5681785 : Nat := 4983230072969 + 3 ^ 40 * 5681785 * 2
def baseEnd_5681785 : Nat := 2917486680506157723757453

theorem tailTrace_5681785 : CollatzResearch.WordTrace tailWord_5681785 prefixEnd_5681785 2917486680506157723757453 := by
  unfold tailWord_5681785
  simp only [CollatzResearch.WordTrace]
  refine ⟨207231723720870791467878809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138154482480580527645252539 207231723720870791467878809)
  ·
    refine ⟨155423792790653093600909107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207231723720870791467878809 155423792790653093600909107)
    ·
      refine ⟨233135689185979640401363661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155423792790653093600909107 233135689185979640401363661)
      ·
        refine ⟨87425883444742365150511373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233135689185979640401363661 87425883444742365150511373)
        ·
          refine ⟨32784706291778386931441765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87425883444742365150511373 32784706291778386931441765)
          ·
            refine ⟨6147132429708447549645331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32784706291778386931441765 6147132429708447549645331)
            ·
              refine ⟨9220698644562671324467997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147132429708447549645331 9220698644562671324467997)
              ·
                refine ⟨3457761991711001746675499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9220698644562671324467997 3457761991711001746675499)
                ·
                  refine ⟨5186642987566502620013249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457761991711001746675499 5186642987566502620013249)
                  ·
                    refine ⟨3889982240674876965009937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186642987566502620013249 3889982240674876965009937)
                    ·
                      refine ⟨2917486680506157723757453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889982240674876965009937 2917486680506157723757453)
                      ·
                        rfl

theorem cell23_5681785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_5681785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681785 prefixEnd_5681785 := by exact prefixLift 5681785
  have htrace : WordTrace (prefixWord ++ tailWord_5681785) baseStart_5681785 baseEnd_5681785 := by
    simpa [prefixWord, tailWord_5681785, baseEnd_5681785] using wordTrace_append hprefix tailTrace_5681785
  have hstable : (prefixWord ++ tailWord_5681785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681785).length < 2 ^ (prefixWord ++ tailWord_5681785).sum := by decide
  have hdescent : baseEnd_5681785 < baseStart_5681785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681802 : List Nat := [3, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2]
def baseStart_5681802 : Nat := 118140960795 + 5681802 * 2 ^ 59
def prefixEnd_5681802 : Nat := 4983230072969 + 3 ^ 40 * 5681802 * 2
def baseEnd_5681802 : Nat := 2917495409677284157244875

theorem tailTrace_5681802 : CollatzResearch.WordTrace tailWord_5681802 prefixEnd_5681802 2917495409677284157244875 := by
  unfold tailWord_5681802
  simp only [CollatzResearch.WordTrace]
  refine ⟨51808085940452300842811915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138154895841206135580831773 51808085940452300842811915)
  ·
    refine ⟨77712128910678451264217873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51808085940452300842811915 77712128910678451264217873)
    ·
      refine ⟨58284096683008838448163405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77712128910678451264217873 58284096683008838448163405)
      ·
        refine ⟨21856536256128314418061277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58284096683008838448163405 21856536256128314418061277)
        ·
          refine ⟨8196201096048117906772979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21856536256128314418061277 8196201096048117906772979)
          ·
            refine ⟨12294301644072176860159469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196201096048117906772979 12294301644072176860159469)
            ·
              refine ⟨4610363116527066322559801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12294301644072176860159469 4610363116527066322559801)
              ·
                refine ⟨3457772337395299741919851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610363116527066322559801 3457772337395299741919851)
                ·
                  refine ⟨5186658506092949612879777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3457772337395299741919851 5186658506092949612879777)
                  ·
                    refine ⟨3889993879569712209659833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186658506092949612879777 3889993879569712209659833)
                    ·
                      refine ⟨2917495409677284157244875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3889993879569712209659833 2917495409677284157244875)
                      ·
                        rfl

theorem cell23_5681802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_5681802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681802 prefixEnd_5681802 := by exact prefixLift 5681802
  have htrace : WordTrace (prefixWord ++ tailWord_5681802) baseStart_5681802 baseEnd_5681802 := by
    simpa [prefixWord, tailWord_5681802, baseEnd_5681802] using wordTrace_append hprefix tailTrace_5681802
  have hstable : (prefixWord ++ tailWord_5681802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681802).length < 2 ^ (prefixWord ++ tailWord_5681802).sum := by decide
  have hdescent : baseEnd_5681802 < baseStart_5681802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681827 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3]
def baseStart_5681827 : Nat := 118140960795 + 5681827 * 2 ^ 59
def prefixEnd_5681827 : Nat := 4983230072969 + 3 ^ 40 * 5681827 * 2
def baseEnd_5681827 : Nat := 2917508246693646559432259

theorem tailTrace_5681827 : CollatzResearch.WordTrace tailWord_5681827 prefixEnd_5681827 2917508246693646559432259 := by
  unfold tailWord_5681827
  simp only [CollatzResearch.WordTrace]
  refine ⟨207233255586718632640907735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138155503724479088427271823 207233255586718632640907735)
  ·
    refine ⟨310849883380077948961361603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207233255586718632640907735 310849883380077948961361603)
    ·
      refine ⟨466274825070116923442042405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310849883380077948961361603 466274825070116923442042405)
      ·
        refine ⟨87426529700646923145382951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466274825070116923442042405 87426529700646923145382951)
        ·
          refine ⟨131139794550970384718074427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87426529700646923145382951 131139794550970384718074427)
          ·
            refine ⟨196709691826455577077111641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131139794550970384718074427 196709691826455577077111641)
            ·
              refine ⟨147532268869841682807833731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196709691826455577077111641 147532268869841682807833731)
              ·
                refine ⟨221298403304762524211750597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147532268869841682807833731 221298403304762524211750597)
                ·
                  refine ⟨41493450619642973289703237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221298403304762524211750597 41493450619642973289703237)
                  ·
                    refine ⟨7780021991183057491819357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41493450619642973289703237 7780021991183057491819357)
                    ·
                      refine ⟨2917508246693646559432259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780021991183057491819357 2917508246693646559432259)
                      ·
                        rfl

theorem cell23_5681827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_5681827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681827 prefixEnd_5681827 := by exact prefixLift 5681827
  have htrace : WordTrace (prefixWord ++ tailWord_5681827) baseStart_5681827 baseEnd_5681827 := by
    simpa [prefixWord, tailWord_5681827, baseEnd_5681827] using wordTrace_append hprefix tailTrace_5681827
  have hstable : (prefixWord ++ tailWord_5681827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681827).length < 2 ^ (prefixWord ++ tailWord_5681827).sum := by decide
  have hdescent : baseEnd_5681827 < baseStart_5681827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681845 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5681845 : Nat := 118140960795 + 5681845 * 2 ^ 59
def prefixEnd_5681845 : Nat := 4983230072969 + 3 ^ 40 * 5681845 * 2
def baseEnd_5681845 : Nat := 2917517489345427489007177

theorem tailTrace_5681845 : CollatzResearch.WordTrace tailWord_5681845 prefixEnd_5681845 2917517489345427489007177 := by
  unfold tailWord_5681845
  simp only [CollatzResearch.WordTrace]
  refine ⟨207233912100653421715062989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138155941400435614476708659 207233912100653421715062989)
  ·
    refine ⟨77712717037745033143148621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207233912100653421715062989 77712717037745033143148621)
    ·
      refine ⟨29142268889154387428680733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77712717037745033143148621 29142268889154387428680733)
      ·
        refine ⟨10928350833432895285755275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29142268889154387428680733 10928350833432895285755275)
        ·
          refine ⟨16392526250149342928632913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928350833432895285755275 16392526250149342928632913)
          ·
            refine ⟨12294394687612007196474685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16392526250149342928632913 12294394687612007196474685)
            ·
              refine ⟨4610398007854502698678007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12294394687612007196474685 4610398007854502698678007)
              ·
                refine ⟨6915597011781754048017011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610398007854502698678007 6915597011781754048017011)
                ·
                  refine ⟨10373395517672631072025517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6915597011781754048017011 10373395517672631072025517)
                  ·
                    refine ⟨3890023319127236652009569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10373395517672631072025517 3890023319127236652009569)
                    ·
                      refine ⟨2917517489345427489007177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890023319127236652009569 2917517489345427489007177)
                      ·
                        rfl

theorem cell23_5681845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5681845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681845 prefixEnd_5681845 := by exact prefixLift 5681845
  have htrace : WordTrace (prefixWord ++ tailWord_5681845) baseStart_5681845 baseEnd_5681845 := by
    simpa [prefixWord, tailWord_5681845, baseEnd_5681845] using wordTrace_append hprefix tailTrace_5681845
  have hstable : (prefixWord ++ tailWord_5681845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681845).length < 2 ^ (prefixWord ++ tailWord_5681845).sum := by decide
  have hdescent : baseEnd_5681845 < baseStart_5681845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681854 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4]
def baseStart_5681854 : Nat := 118140960795 + 5681854 * 2 ^ 59
def prefixEnd_5681854 : Nat := 4983230072969 + 3 ^ 40 * 5681854 * 2
def baseEnd_5681854 : Nat := 2917522110671317953794635

theorem tailTrace_5681854 : CollatzResearch.WordTrace tailWord_5681854 prefixEnd_5681854 2917522110671317953794635 := by
  unfold tailWord_5681854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25904280044702602031517577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138156160238413877501427077 25904280044702602031517577)
  ·
    refine ⟨19428210033526951523638183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25904280044702602031517577 19428210033526951523638183)
    ·
      refine ⟨29142315050290427285457275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428210033526951523638183 29142315050290427285457275)
      ·
        refine ⟨43713472575435640928185913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29142315050290427285457275 43713472575435640928185913)
        ·
          refine ⟨32785104431576730696139435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43713472575435640928185913 32785104431576730696139435)
          ·
            refine ⟨49177656647365096044209153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32785104431576730696139435 49177656647365096044209153)
            ·
              refine ⟨36883242485523822033156865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49177656647365096044209153 36883242485523822033156865)
              ·
                refine ⟨27662431864142866524867649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36883242485523822033156865 27662431864142866524867649)
                ·
                  refine ⟨20746823898107149893650737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27662431864142866524867649 20746823898107149893650737)
                  ·
                    refine ⟨15560117923580362420238053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20746823898107149893650737 15560117923580362420238053)
                    ·
                      refine ⟨2917522110671317953794635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560117923580362420238053 2917522110671317953794635)
                      ·
                        rfl

theorem cell23_5681854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_5681854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681854 prefixEnd_5681854 := by exact prefixLift 5681854
  have htrace : WordTrace (prefixWord ++ tailWord_5681854) baseStart_5681854 baseEnd_5681854 := by
    simpa [prefixWord, tailWord_5681854, baseEnd_5681854] using wordTrace_append hprefix tailTrace_5681854
  have hstable : (prefixWord ++ tailWord_5681854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681854).length < 2 ^ (prefixWord ++ tailWord_5681854).sum := by decide
  have hdescent : baseEnd_5681854 < baseStart_5681854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681914 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_5681914 : Nat := 118140960795 + 5681914 * 2 ^ 59
def prefixEnd_5681914 : Nat := 4983230072969 + 3 ^ 40 * 5681914 * 2
def baseEnd_5681914 : Nat := 2917552919510587719044359

theorem tailTrace_5681914 : CollatzResearch.WordTrace tailWord_5681914 prefixEnd_5681914 2917552919510587719044359 := by
  unfold tailWord_5681914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809107184350861624831199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138157619158268964332883197 51809107184350861624831199)
  ·
    refine ⟨77713660776526292437246799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51809107184350861624831199 77713660776526292437246799)
    ·
      refine ⟨116570491164789438655870199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77713660776526292437246799 116570491164789438655870199)
      ·
        refine ⟨174855736747184157983805299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116570491164789438655870199 174855736747184157983805299)
        ·
          refine ⟨262283605120776236975707949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174855736747184157983805299 262283605120776236975707949)
          ·
            refine ⟨98356351920291088865890481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262283605120776236975707949 98356351920291088865890481)
            ·
              refine ⟨73767263940218316649417861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98356351920291088865890481 73767263940218316649417861)
              ·
                refine ⟨13831361988790934371765849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73767263940218316649417861 13831361988790934371765849)
                ·
                  refine ⟨10373521491593200778824387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13831361988790934371765849 10373521491593200778824387)
                  ·
                    refine ⟨15560282237389801168236581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373521491593200778824387 15560282237389801168236581)
                    ·
                      refine ⟨2917552919510587719044359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560282237389801168236581 2917552919510587719044359)
                      ·
                        rfl

theorem cell23_5681914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_5681914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681914 prefixEnd_5681914 := by exact prefixLift 5681914
  have htrace : WordTrace (prefixWord ++ tailWord_5681914) baseStart_5681914 baseEnd_5681914 := by
    simpa [prefixWord, tailWord_5681914, baseEnd_5681914] using wordTrace_append hprefix tailTrace_5681914
  have hstable : (prefixWord ++ tailWord_5681914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681914).length < 2 ^ (prefixWord ++ tailWord_5681914).sum := by decide
  have hdescent : baseEnd_5681914 < baseStart_5681914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681954 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 8]
def baseStart_5681954 : Nat := 118140960795 + 5681954 * 2 ^ 59
def prefixEnd_5681954 : Nat := 4983230072969 + 3 ^ 40 * 5681954 * 2
def baseEnd_5681954 : Nat := 324174828748529729171575

theorem tailTrace_5681954 : CollatzResearch.WordTrace tailWord_5681954 prefixEnd_5681954 324174828748529729171575 := by
  unfold tailWord_5681954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51809471914314633332695229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138158591771505688887187277 51809471914314633332695229)
  ·
    refine ⟨19428551967867987499760711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51809471914314633332695229 19428551967867987499760711)
    ·
      refine ⟨29142827951801981249641067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428551967867987499760711 29142827951801981249641067)
      ·
        refine ⟨43714241927702971874461601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29142827951801981249641067 43714241927702971874461601)
        ·
          refine ⟨32785681445777228905846201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43714241927702971874461601 32785681445777228905846201)
          ·
            refine ⟨24589261084332921679384651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32785681445777228905846201 24589261084332921679384651)
            ·
              refine ⟨36883891626499382519076977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24589261084332921679384651 36883891626499382519076977)
              ·
                refine ⟨27662918719874536889307733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36883891626499382519076977 27662918719874536889307733)
                ·
                  refine ⟨324174828748529729171575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27662918719874536889307733 324174828748529729171575)
                  ·
                    rfl

theorem cell23_5681954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_5681954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681954 prefixEnd_5681954 := by exact prefixLift 5681954
  have htrace : WordTrace (prefixWord ++ tailWord_5681954) baseStart_5681954 baseEnd_5681954 := by
    simpa [prefixWord, tailWord_5681954, baseEnd_5681954] using wordTrace_append hprefix tailTrace_5681954
  have hstable : (prefixWord ++ tailWord_5681954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681954).length < 2 ^ (prefixWord ++ tailWord_5681954).sum := by decide
  have hdescent : baseEnd_5681954 < baseStart_5681954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681965 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5681965 : Nat := 118140960795 + 5681965 * 2 ^ 59
def prefixEnd_5681965 : Nat := 4983230072969 + 3 ^ 40 * 5681965 * 2
def baseEnd_5681965 : Nat := 2917579107023967019506625

theorem tailTrace_5681965 : CollatzResearch.WordTrace tailWord_5681965 prefixEnd_5681965 2917579107023967019506625 := by
  unfold tailWord_5681965
  simp only [CollatzResearch.WordTrace]
  refine ⟨207238288860218682209431349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138158859240145788139620899 207238288860218682209431349)
  ·
    refine ⟨19428589580645501457134189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207238288860218682209431349 19428589580645501457134189)
    ·
      refine ⟨7285721092742063046425321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19428589580645501457134189 7285721092742063046425321)
      ·
        refine ⟨5464290819556547284818991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7285721092742063046425321 5464290819556547284818991)
        ·
          refine ⟨8196436229334820927228487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464290819556547284818991 8196436229334820927228487)
          ·
            refine ⟨12294654344002231390842731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196436229334820927228487 12294654344002231390842731)
            ·
              refine ⟨18441981516003347086264097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12294654344002231390842731 18441981516003347086264097)
              ·
                refine ⟨13831486137002510314698073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18441981516003347086264097 13831486137002510314698073)
                ·
                  refine ⟨10373614602751882736023555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13831486137002510314698073 10373614602751882736023555)
                  ·
                    refine ⟨15560421904127824104035333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373614602751882736023555 15560421904127824104035333)
                    ·
                      refine ⟨2917579107023967019506625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560421904127824104035333 2917579107023967019506625)
                      ·
                        rfl

theorem cell23_5681965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5681965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681965 prefixEnd_5681965 := by exact prefixLift 5681965
  have htrace : WordTrace (prefixWord ++ tailWord_5681965) baseStart_5681965 baseEnd_5681965 := by
    simpa [prefixWord, tailWord_5681965, baseEnd_5681965] using wordTrace_append hprefix tailTrace_5681965
  have hstable : (prefixWord ++ tailWord_5681965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681965).length < 2 ^ (prefixWord ++ tailWord_5681965).sum := by decide
  have hdescent : baseEnd_5681965 < baseStart_5681965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5681991 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 6, 3, 2]
def baseStart_5681991 : Nat := 118140960795 + 5681991 * 2 ^ 59
def prefixEnd_5681991 : Nat := 4983230072969 + 3 ^ 40 * 5681991 * 2
def baseEnd_5681991 : Nat := 2917592457520983917781505

theorem tailTrace_5681991 : CollatzResearch.WordTrace tailWord_5681991 prefixEnd_5681991 2917592457520983917781505 := by
  unfold tailWord_5681991
  simp only [CollatzResearch.WordTrace]
  refine ⟨207239237158124488649877827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138159491438749659099918551 207239237158124488649877827)
  ·
    refine ⟨310858855737186732974816741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207239237158124488649877827 310858855737186732974816741)
    ·
      refine ⟨58286035450722512432778139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310858855737186732974816741 58286035450722512432778139)
      ·
        refine ⟨87429053176083768649167209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58286035450722512432778139 87429053176083768649167209)
        ·
          refine ⟨65571789882062826486875407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87429053176083768649167209 65571789882062826486875407)
          ·
            refine ⟨98357684823094239730313111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65571789882062826486875407 98357684823094239730313111)
            ·
              refine ⟨147536527234641359595469667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98357684823094239730313111 147536527234641359595469667)
              ·
                refine ⟨221304790851962039393204501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147536527234641359595469667 221304790851962039393204501)
                ·
                  refine ⟨10373662071185720596556461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221304790851962039393204501 10373662071185720596556461)
                  ·
                    refine ⟨3890123276694645223708673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10373662071185720596556461 3890123276694645223708673)
                    ·
                      refine ⟨2917592457520983917781505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890123276694645223708673 2917592457520983917781505)
                      ·
                        rfl

theorem cell23_5681991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 3, 2].length) (baseStart_5681991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5681991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5681991 prefixEnd_5681991 := by exact prefixLift 5681991
  have htrace : WordTrace (prefixWord ++ tailWord_5681991) baseStart_5681991 baseEnd_5681991 := by
    simpa [prefixWord, tailWord_5681991, baseEnd_5681991] using wordTrace_append hprefix tailTrace_5681991
  have hstable : (prefixWord ++ tailWord_5681991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5681991).length < 2 ^ (prefixWord ++ tailWord_5681991).sum := by decide
  have hdescent : baseEnd_5681991 < baseStart_5681991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5681991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682001 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_5682001 : Nat := 118140960795 + 5682001 * 2 ^ 59
def prefixEnd_5682001 : Nat := 4983230072969 + 3 ^ 40 * 5682001 * 2
def baseEnd_5682001 : Nat := 972532530775842959552153

theorem tailTrace_5682001 : CollatzResearch.WordTrace tailWord_5682001 prefixEnd_5682001 972532530775842959552153 := by
  unfold tailWord_5682001
  simp only [CollatzResearch.WordTrace]
  refine ⟨207239601888088260357741857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138159734592058840238494571 207239601888088260357741857)
  ·
    refine ⟨155429701416066195268306393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207239601888088260357741857 155429701416066195268306393)
    ·
      refine ⟨116572276062049646451229795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155429701416066195268306393 116572276062049646451229795)
      ·
        refine ⟨174858414093074469676844693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116572276062049646451229795 174858414093074469676844693)
        ·
          refine ⟨8196488160612865766102095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174858414093074469676844693 8196488160612865766102095)
          ·
            refine ⟨12294732240919298649153143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196488160612865766102095 12294732240919298649153143)
            ·
              refine ⟨18442098361378947973729715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12294732240919298649153143 18442098361378947973729715)
              ·
                refine ⟨27663147542068421960594573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442098361378947973729715 27663147542068421960594573)
                ·
                  refine ⟨10373680328275658235222965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27663147542068421960594573 10373680328275658235222965)
                  ·
                    refine ⟨972532530775842959552153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10373680328275658235222965 972532530775842959552153)
                    ·
                      rfl

theorem cell23_5682001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_5682001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682001 prefixEnd_5682001 := by exact prefixLift 5682001
  have htrace : WordTrace (prefixWord ++ tailWord_5682001) baseStart_5682001 baseEnd_5682001 := by
    simpa [prefixWord, tailWord_5682001, baseEnd_5682001] using wordTrace_append hprefix tailTrace_5682001
  have hstable : (prefixWord ++ tailWord_5682001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682001).length < 2 ^ (prefixWord ++ tailWord_5682001).sum := by decide
  have hdescent : baseEnd_5682001 < baseStart_5682001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682021 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_5682021 : Nat := 118140960795 + 5682021 * 2 ^ 59
def prefixEnd_5682021 : Nat := 4983230072969 + 3 ^ 40 * 5682021 * 2
def baseEnd_5682021 : Nat := 2917607861940618800406367

theorem tailTrace_5682021 : CollatzResearch.WordTrace tailWord_5682021 prefixEnd_5682021 2917607861940618800406367 := by
  unfold tailWord_5682021
  simp only [CollatzResearch.WordTrace]
  refine ⟨207240331348015803773469917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138160220898677202515646611 207240331348015803773469917)
  ·
    refine ⟨77715124255505926415051219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207240331348015803773469917 77715124255505926415051219)
    ·
      refine ⟨116572686383258889622576829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77715124255505926415051219 116572686383258889622576829)
      ·
        refine ⟨43714757393722083608466311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116572686383258889622576829 43714757393722083608466311)
        ·
          refine ⟨65572136090583125412699467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43714757393722083608466311 65572136090583125412699467)
          ·
            refine ⟨98358204135874688119049201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65572136090583125412699467 98358204135874688119049201)
            ·
              refine ⟨73768653101906016089286901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98358204135874688119049201 73768653101906016089286901)
              ·
                refine ⟨6915811228303689008370647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73768653101906016089286901 6915811228303689008370647)
                ·
                  refine ⟨10373716842455533512555971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6915811228303689008370647 10373716842455533512555971)
                  ·
                    refine ⟨15560575263683300268833957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373716842455533512555971 15560575263683300268833957)
                    ·
                      refine ⟨2917607861940618800406367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560575263683300268833957 2917607861940618800406367)
                      ·
                        rfl

theorem cell23_5682021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_5682021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682021 prefixEnd_5682021 := by exact prefixLift 5682021
  have htrace : WordTrace (prefixWord ++ tailWord_5682021) baseStart_5682021 baseEnd_5682021 := by
    simpa [prefixWord, tailWord_5682021, baseEnd_5682021] using wordTrace_append hprefix tailTrace_5682021
  have hstable : (prefixWord ++ tailWord_5682021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682021).length < 2 ^ (prefixWord ++ tailWord_5682021).sum := by decide
  have hdescent : baseEnd_5682021 < baseStart_5682021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682034 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5682034 : Nat := 118140960795 + 5682034 * 2 ^ 59
def prefixEnd_5682034 : Nat := 4983230072969 + 3 ^ 40 * 5682034 * 2
def baseEnd_5682034 : Nat := 2917614537189127249543807

theorem tailTrace_5682034 : CollatzResearch.WordTrace tailWord_5682034 prefixEnd_5682034 2917614537189127249543807 := by
  unfold tailWord_5682034
  simp only [CollatzResearch.WordTrace]
  refine ⟨51810201374242176748423289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138160536997979137995795437 51810201374242176748423289)
  ·
    refine ⟨38857651030681632561317467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51810201374242176748423289 38857651030681632561317467)
    ·
      refine ⟨58286476546022448841976201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38857651030681632561317467 58286476546022448841976201)
      ·
        refine ⟨43714857409516836631482151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58286476546022448841976201 43714857409516836631482151)
        ·
          refine ⟨65572286114275254947223227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43714857409516836631482151 65572286114275254947223227)
          ·
            refine ⟨98358429171412882420834841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65572286114275254947223227 98358429171412882420834841)
            ·
              refine ⟨73768821878559661815626131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98358429171412882420834841 73768821878559661815626131)
              ·
                refine ⟨110653232817839492723439197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73768821878559661815626131 110653232817839492723439197)
                ·
                  refine ⟨41494962306689809771289699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110653232817839492723439197 41494962306689809771289699)
                  ·
                    refine ⟨62242443460034714656934549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41494962306689809771289699 62242443460034714656934549)
                    ·
                      refine ⟨2917614537189127249543807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62242443460034714656934549 2917614537189127249543807)
                      ·
                        rfl

theorem cell23_5682034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5682034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682034 prefixEnd_5682034 := by exact prefixLift 5682034
  have htrace : WordTrace (prefixWord ++ tailWord_5682034) baseStart_5682034 baseEnd_5682034 := by
    simpa [prefixWord, tailWord_5682034, baseEnd_5682034] using wordTrace_append hprefix tailTrace_5682034
  have hstable : (prefixWord ++ tailWord_5682034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682034).length < 2 ^ (prefixWord ++ tailWord_5682034).sum := by decide
  have hdescent : baseEnd_5682034 < baseStart_5682034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682038 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_5682038 : Nat := 118140960795 + 5682038 * 2 ^ 59
def prefixEnd_5682038 : Nat := 4983230072969 + 3 ^ 40 * 5682038 * 2
def baseEnd_5682038 : Nat := 2917616591111745233893789

theorem tailTrace_5682038 : CollatzResearch.WordTrace tailWord_5682038 prefixEnd_5682038 2917616591111745233893789 := by
  unfold tailWord_5682038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952559461809638479802423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138160634259302810451225845 12952559461809638479802423)
  ·
    refine ⟨19428839192714457719703635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952559461809638479802423 19428839192714457719703635)
    ·
      refine ⟨29143258789071686579555453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19428839192714457719703635 29143258789071686579555453)
      ·
        refine ⟨10928722045901882467333295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29143258789071686579555453 10928722045901882467333295)
        ·
          refine ⟨16393083068852823700999943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928722045901882467333295 16393083068852823700999943)
          ·
            refine ⟨24589624603279235551499915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393083068852823700999943 24589624603279235551499915)
            ·
              refine ⟨36884436904918853327249873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24589624603279235551499915 36884436904918853327249873)
              ·
                refine ⟨27663327678689139995437405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36884436904918853327249873 27663327678689139995437405)
                ·
                  refine ⟨10373747879508427498289027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27663327678689139995437405 10373747879508427498289027)
                  ·
                    refine ⟨15560621819262641247433541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10373747879508427498289027 15560621819262641247433541)
                    ·
                      refine ⟨2917616591111745233893789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560621819262641247433541 2917616591111745233893789)
                      ·
                        rfl

theorem cell23_5682038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_5682038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682038 prefixEnd_5682038 := by exact prefixLift 5682038
  have htrace : WordTrace (prefixWord ++ tailWord_5682038) baseStart_5682038 baseEnd_5682038 := by
    simpa [prefixWord, tailWord_5682038, baseEnd_5682038] using wordTrace_append hprefix tailTrace_5682038
  have hstable : (prefixWord ++ tailWord_5682038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682038).length < 2 ^ (prefixWord ++ tailWord_5682038).sum := by decide
  have hdescent : baseEnd_5682038 < baseStart_5682038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682041 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 3]
def baseStart_5682041 : Nat := 118140960795 + 5682041 * 2 ^ 59
def prefixEnd_5682041 : Nat := 4983230072969 + 3 ^ 40 * 5682041 * 2
def baseEnd_5682041 : Nat := 2917618131553708722156275

theorem tailTrace_5682041 : CollatzResearch.WordTrace tailWord_5682041 prefixEnd_5682041 2917618131553708722156275 := by
  unfold tailWord_5682041
  simp only [CollatzResearch.WordTrace]
  refine ⟨207241060807943347189197977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138160707205295564792798651 207241060807943347189197977)
  ·
    refine ⟨155430795605957510391898483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207241060807943347189197977 155430795605957510391898483)
    ·
      refine ⟨233146193408936265587847725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155430795605957510391898483 233146193408936265587847725)
      ·
        refine ⟨87429822528351099595442897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233146193408936265587847725 87429822528351099595442897)
        ·
          refine ⟨65572366896263324696582173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87429822528351099595442897 65572366896263324696582173)
          ·
            refine ⟨24589637586098746761218315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65572366896263324696582173 24589637586098746761218315)
            ·
              refine ⟨36884456379148120141827473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24589637586098746761218315 36884456379148120141827473)
              ·
                refine ⟨27663342284361090106370605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36884456379148120141827473 27663342284361090106370605)
                ·
                  refine ⟨10373753356635408789888977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27663342284361090106370605 10373753356635408789888977)
                  ·
                    refine ⟨7780315017476556592416733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10373753356635408789888977 7780315017476556592416733)
                    ·
                      refine ⟨2917618131553708722156275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780315017476556592416733 2917618131553708722156275)
                      ·
                        rfl

theorem cell23_5682041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_5682041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682041 prefixEnd_5682041 := by exact prefixLift 5682041
  have htrace : WordTrace (prefixWord ++ tailWord_5682041) baseStart_5682041 baseEnd_5682041 := by
    simpa [prefixWord, tailWord_5682041, baseEnd_5682041] using wordTrace_append hprefix tailTrace_5682041
  have hstable : (prefixWord ++ tailWord_5682041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682041).length < 2 ^ (prefixWord ++ tailWord_5682041).sum := by decide
  have hdescent : baseEnd_5682041 < baseStart_5682041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682051 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4]
def baseStart_5682051 : Nat := 118140960795 + 5682051 * 2 ^ 59
def prefixEnd_5682051 : Nat := 4983230072969 + 3 ^ 40 * 5682051 * 2
def baseEnd_5682051 : Nat := 2917623266360253683031229

theorem tailTrace_5682051 : CollatzResearch.WordTrace tailWord_5682051 prefixEnd_5682051 2917623266360253683031229 := by
  unfold tailWord_5682051
  simp only [CollatzResearch.WordTrace]
  refine ⟨207241425537907118897062007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138160950358604745931374671 207241425537907118897062007)
  ·
    refine ⟨310862138306860678345593011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207241425537907118897062007 310862138306860678345593011)
    ·
      refine ⟨466293207460291017518389517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310862138306860678345593011 466293207460291017518389517)
      ·
        refine ⟨174859952797609131569396069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466293207460291017518389517 174859952797609131569396069)
        ·
          refine ⟨32786241149551712169261763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174859952797609131569396069 32786241149551712169261763)
          ·
            refine ⟨49179361724327568253892645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32786241149551712169261763 49179361724327568253892645)
            ·
              refine ⟨9221130323311419047604871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49179361724327568253892645 9221130323311419047604871)
              ·
                refine ⟨13831695484967128571407307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221130323311419047604871 13831695484967128571407307)
                ·
                  refine ⟨20747543227450692857110961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13831695484967128571407307 20747543227450692857110961)
                  ·
                    refine ⟨15560657420588019642833221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20747543227450692857110961 15560657420588019642833221)
                    ·
                      refine ⟨2917623266360253683031229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15560657420588019642833221 2917623266360253683031229)
                      ·
                        rfl

theorem cell23_5682051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_5682051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682051 prefixEnd_5682051 := by exact prefixLift 5682051
  have htrace : WordTrace (prefixWord ++ tailWord_5682051) baseStart_5682051 baseEnd_5682051 := by
    simpa [prefixWord, tailWord_5682051, baseEnd_5682051] using wordTrace_append hprefix tailTrace_5682051
  have hstable : (prefixWord ++ tailWord_5682051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682051).length < 2 ^ (prefixWord ++ tailWord_5682051).sum := by decide
  have hdescent : baseEnd_5682051 < baseStart_5682051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682055 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 3, 2, 2]
def baseStart_5682055 : Nat := 118140960795 + 5682055 * 2 ^ 59
def prefixEnd_5682055 : Nat := 4983230072969 + 3 ^ 40 * 5682055 * 2
def baseEnd_5682055 : Nat := 2917625320282871667381211

theorem tailTrace_5682055 : CollatzResearch.WordTrace tailWord_5682055 prefixEnd_5682055 2917625320282871667381211 := by
  unfold tailWord_5682055
  simp only [CollatzResearch.WordTrace]
  refine ⟨207241571429892627580207619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138161047619928418386805079 207241571429892627580207619)
  ·
    refine ⟨310862357144838941370311429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207241571429892627580207619 310862357144838941370311429)
    ·
      refine ⟨58286691964657301506933393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310862357144838941370311429 58286691964657301506933393)
      ·
        refine ⟨43715018973492976130200045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58286691964657301506933393 43715018973492976130200045)
        ·
          refine ⟨16393132115059866048825017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43715018973492976130200045 16393132115059866048825017)
          ·
            refine ⟨12294849086294899536618763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16393132115059866048825017 12294849086294899536618763)
            ·
              refine ⟨18442273629442349304928145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12294849086294899536618763 18442273629442349304928145)
              ·
                refine ⟨13831705222081761978696109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18442273629442349304928145 13831705222081761978696109)
                ·
                  refine ⟨5186889458280660742011041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13831705222081761978696109 5186889458280660742011041)
                  ·
                    refine ⟨3890167093710495556508281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186889458280660742011041 3890167093710495556508281)
                    ·
                      refine ⟨2917625320282871667381211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890167093710495556508281 2917625320282871667381211)
                      ·
                        rfl

theorem cell23_5682055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_5682055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682055 prefixEnd_5682055 := by exact prefixLift 5682055
  have htrace : WordTrace (prefixWord ++ tailWord_5682055) baseStart_5682055 baseEnd_5682055 := by
    simpa [prefixWord, tailWord_5682055, baseEnd_5682055] using wordTrace_append hprefix tailTrace_5682055
  have hstable : (prefixWord ++ tailWord_5682055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682055).length < 2 ^ (prefixWord ++ tailWord_5682055).sum := by decide
  have hdescent : baseEnd_5682055 < baseStart_5682055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682058 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_5682058 : Nat := 118140960795 + 5682058 * 2 ^ 59
def prefixEnd_5682058 : Nat := 4983230072969 + 3 ^ 40 * 5682058 * 2
def baseEnd_5682058 : Nat := 2917626860724835155643697

theorem tailTrace_5682058 : CollatzResearch.WordTrace tailWord_5682058 prefixEnd_5682058 2917626860724835155643697 := by
  unfold tailWord_5682058
  simp only [CollatzResearch.WordTrace]
  refine ⟨51810420212220439773141707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138161120565921172728377885 51810420212220439773141707)
  ·
    refine ⟨77715630318330659659712561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51810420212220439773141707 77715630318330659659712561)
    ·
      refine ⟨58286722738747994744784421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77715630318330659659712561 58286722738747994744784421)
      ·
        refine ⟨10928760513515249014647079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58286722738747994744784421 10928760513515249014647079)
        ·
          refine ⟨16393140770272873521970619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10928760513515249014647079 16393140770272873521970619)
          ·
            refine ⟨24589711155409310282955929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393140770272873521970619 24589711155409310282955929)
            ·
              refine ⟨18442283366556982712216947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24589711155409310282955929 18442283366556982712216947)
              ·
                refine ⟨27663425049835474068325421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442283366556982712216947 27663425049835474068325421)
                ·
                  refine ⟨10373784393688302775622033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27663425049835474068325421 10373784393688302775622033)
                  ·
                    refine ⟨7780338295266227081716525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10373784393688302775622033 7780338295266227081716525)
                    ·
                      refine ⟨2917626860724835155643697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780338295266227081716525 2917626860724835155643697)
                      ·
                        rfl

theorem cell23_5682058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_5682058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682058 prefixEnd_5682058 := by exact prefixLift 5682058
  have htrace : WordTrace (prefixWord ++ tailWord_5682058) baseStart_5682058 baseEnd_5682058 := by
    simpa [prefixWord, tailWord_5682058, baseEnd_5682058] using wordTrace_append hprefix tailTrace_5682058
  have hstable : (prefixWord ++ tailWord_5682058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682058).length < 2 ^ (prefixWord ++ tailWord_5682058).sum := by decide
  have hdescent : baseEnd_5682058 < baseStart_5682058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682071 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3]
def baseStart_5682071 : Nat := 118140960795 + 5682071 * 2 ^ 59
def prefixEnd_5682071 : Nat := 4983230072969 + 3 ^ 40 * 5682071 * 2
def baseEnd_5682071 : Nat := 2917633535973343604781137

theorem tailTrace_5682071 : CollatzResearch.WordTrace tailWord_5682071 prefixEnd_5682071 2917633535973343604781137 := by
  unfold tailWord_5682071
  simp only [CollatzResearch.WordTrace]
  refine ⟨207242154997834662312790067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138161436665223108208526711 207242154997834662312790067)
  ·
    refine ⟨310863232496751993469185101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207242154997834662312790067 310863232496751993469185101)
    ·
      refine ⟨116573712186281997550944413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310863232496751993469185101 116573712186281997550944413)
      ·
        refine ⟨43715142069855749081604155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116573712186281997550944413 43715142069855749081604155)
        ·
          refine ⟨65572713104783623622406233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43715142069855749081604155 65572713104783623622406233)
          ·
            refine ⟨49179534828587717716804675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65572713104783623622406233 49179534828587717716804675)
            ·
              refine ⟨73769302242881576575207013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49179534828587717716804675 73769302242881576575207013)
              ·
                refine ⟨13831744170540295607851315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73769302242881576575207013 13831744170540295607851315)
                ·
                  refine ⟨20747616255810443411776973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13831744170540295607851315 20747616255810443411776973)
                  ·
                    refine ⟨7780356095928916279416365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20747616255810443411776973 7780356095928916279416365)
                    ·
                      refine ⟨2917633535973343604781137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780356095928916279416365 2917633535973343604781137)
                      ·
                        rfl

theorem cell23_5682071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_5682071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682071 prefixEnd_5682071 := by exact prefixLift 5682071
  have htrace : WordTrace (prefixWord ++ tailWord_5682071) baseStart_5682071 baseEnd_5682071 := by
    simpa [prefixWord, tailWord_5682071, baseEnd_5682071] using wordTrace_append hprefix tailTrace_5682071
  have hstable : (prefixWord ++ tailWord_5682071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682071).length < 2 ^ (prefixWord ++ tailWord_5682071).sum := by decide
  have hdescent : baseEnd_5682071 < baseStart_5682071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682102 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5682102 : Nat := 118140960795 + 5682102 * 2 ^ 59
def prefixEnd_5682102 : Nat := 4983230072969 + 3 ^ 40 * 5682102 * 2
def baseEnd_5682102 : Nat := 2917649453873632983493495

theorem tailTrace_5682102 : CollatzResearch.WordTrace tailWord_5682102 prefixEnd_5682102 2917649453873632983493495 := by
  unfold tailWord_5682102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12952705353795147162948035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138162190440481569738112373 12952705353795147162948035)
  ·
    refine ⟨19429058030692720744422053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12952705353795147162948035 19429058030692720744422053)
    ·
      refine ⟨3642948380754885139579135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19429058030692720744422053 3642948380754885139579135)
      ·
        refine ⟨5464422571132327709368703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642948380754885139579135 5464422571132327709368703)
        ·
          refine ⟨8196633856698491564053055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5464422571132327709368703 8196633856698491564053055)
          ·
            refine ⟨12294950785047737346079583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8196633856698491564053055 12294950785047737346079583)
            ·
              refine ⟨18442426177571606019119375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12294950785047737346079583 18442426177571606019119375)
              ·
                refine ⟨27663639266357409028679063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442426177571606019119375 27663639266357409028679063)
                ·
                  refine ⟨41495458899536113543018595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27663639266357409028679063 41495458899536113543018595)
                  ·
                    refine ⟨62243188349304170314527893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41495458899536113543018595 62243188349304170314527893)
                    ·
                      refine ⟨2917649453873632983493495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62243188349304170314527893 2917649453873632983493495)
                      ·
                        rfl

theorem cell23_5682102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5682102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682102 prefixEnd_5682102 := by exact prefixLift 5682102
  have htrace : WordTrace (prefixWord ++ tailWord_5682102) baseStart_5682102 baseEnd_5682102 := by
    simpa [prefixWord, tailWord_5682102, baseEnd_5682102] using wordTrace_append hprefix tailTrace_5682102
  have hstable : (prefixWord ++ tailWord_5682102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682102).length < 2 ^ (prefixWord ++ tailWord_5682102).sum := by decide
  have hdescent : baseEnd_5682102 < baseStart_5682102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682145 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 2, 2, 2]
def baseStart_5682145 : Nat := 118140960795 + 5682145 * 2 ^ 59
def prefixEnd_5682145 : Nat := 4983230072969 + 3 ^ 40 * 5682145 * 2
def baseEnd_5682145 : Nat := 2917671533541776315255797

theorem tailTrace_5682145 : CollatzResearch.WordTrace tailWord_5682145 prefixEnd_5682145 2917671533541776315255797 := by
  unfold tailWord_5682145
  simp only [CollatzResearch.WordTrace]
  refine ⟨207244853999566572950983889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138163235999711048633989259 207244853999566572950983889)
  ·
    refine ⟨155433640499674929713237917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207244853999566572950983889 155433640499674929713237917)
    ·
      refine ⟨58287615187378098642464219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155433640499674929713237917 58287615187378098642464219)
      ·
        refine ⟨87431422781067147963696329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58287615187378098642464219 87431422781067147963696329)
        ·
          refine ⟨65573567085800360972772247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87431422781067147963696329 65573567085800360972772247)
          ·
            refine ⟨98360350628700541459158371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65573567085800360972772247 98360350628700541459158371)
            ·
              refine ⟨147540525943050812188737557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98360350628700541459158371 147540525943050812188737557)
              ·
                refine ⟨6915962153580506821347073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147540525943050812188737557 6915962153580506821347073)
                ·
                  refine ⟨5186971615185380116010305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6915962153580506821347073 5186971615185380116010305)
                  ·
                    refine ⟨3890228711389035087007729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5186971615185380116010305 3890228711389035087007729)
                    ·
                      refine ⟨2917671533541776315255797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890228711389035087007729 2917671533541776315255797)
                      ·
                        rfl

theorem cell23_5682145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 2, 2].length) (baseStart_5682145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682145 prefixEnd_5682145 := by exact prefixLift 5682145
  have htrace : WordTrace (prefixWord ++ tailWord_5682145) baseStart_5682145 baseEnd_5682145 := by
    simpa [prefixWord, tailWord_5682145, baseEnd_5682145] using wordTrace_append hprefix tailTrace_5682145
  have hstable : (prefixWord ++ tailWord_5682145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682145).length < 2 ^ (prefixWord ++ tailWord_5682145).sum := by decide
  have hdescent : baseEnd_5682145 < baseStart_5682145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682245 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 1, 4]
def baseStart_5682245 : Nat := 118140960795 + 5682245 * 2 ^ 59
def prefixEnd_5682245 : Nat := 4983230072969 + 3 ^ 40 * 5682245 * 2
def baseEnd_5682245 : Nat := 972574293869075308001779

theorem tailTrace_5682245 : CollatzResearch.WordTrace tailWord_5682245 prefixEnd_5682245 972574293869075308001779 := by
  unfold tailWord_5682245
  simp only [CollatzResearch.WordTrace]
  refine ⟨207248501299204290029624189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138165667532802860019749459 207248501299204290029624189)
  ·
    refine ⟨77718187987201608761109071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207248501299204290029624189 77718187987201608761109071)
    ·
      refine ⟨116577281980802413141663607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77718187987201608761109071 116577281980802413141663607)
      ·
        refine ⟨174865922971203619712495411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116577281980802413141663607 174865922971203619712495411)
        ·
          refine ⟨262298884456805429568743117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174865922971203619712495411 262298884456805429568743117)
          ·
            refine ⟨98362081671302036088278669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262298884456805429568743117 98362081671302036088278669)
            ·
              refine ⟨36885780626738263533104501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98362081671302036088278669 36885780626738263533104501)
              ·
                refine ⟨3458041933756712206228547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36885780626738263533104501 3458041933756712206228547)
                ·
                  refine ⟨5187062900635068309342821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458041933756712206228547 5187062900635068309342821)
                  ·
                    refine ⟨972574293869075308001779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187062900635068309342821 972574293869075308001779)
                    ·
                      rfl

theorem cell23_5682245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 4].length) (baseStart_5682245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682245 prefixEnd_5682245 := by exact prefixLift 5682245
  have htrace : WordTrace (prefixWord ++ tailWord_5682245) baseStart_5682245 baseEnd_5682245 := by
    simpa [prefixWord, tailWord_5682245, baseEnd_5682245] using wordTrace_append hprefix tailTrace_5682245
  have hstable : (prefixWord ++ tailWord_5682245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682245).length < 2 ^ (prefixWord ++ tailWord_5682245).sum := by decide
  have hdescent : baseEnd_5682245 < baseStart_5682245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682258 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_5682258 : Nat := 118140960795 + 5682258 * 2 ^ 59
def prefixEnd_5682258 : Nat := 4983230072969 + 3 ^ 40 * 5682258 * 2
def baseEnd_5682258 : Nat := 324192172983970485904753

theorem tailTrace_5682258 : CollatzResearch.WordTrace tailWord_5682258 prefixEnd_5682258 324192172983970485904753 := by
  unfold tailWord_5682258
  simp only [CollatzResearch.WordTrace]
  refine ⟨51812243862039298312461857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138165983632104795499898285 51812243862039298312461857)
  ·
    refine ⟨38859182896529473734346393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51812243862039298312461857 38859182896529473734346393)
    ·
      refine ⟨29144387172397105300759795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38859182896529473734346393 29144387172397105300759795)
      ·
        refine ⟨43716580758595657951139693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29144387172397105300759795 43716580758595657951139693)
        ·
          refine ⟨16393717784473371731677385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43716580758595657951139693 16393717784473371731677385)
          ·
            refine ⟨12295288338355028798758039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16393717784473371731677385 12295288338355028798758039)
            ·
              refine ⟨18442932507532543198137059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12295288338355028798758039 18442932507532543198137059)
              ·
                refine ⟨27664398761298814797205589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18442932507532543198137059 27664398761298814797205589)
                ·
                  refine ⟨324192172983970485904753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27664398761298814797205589 324192172983970485904753)
                  ·
                    rfl

theorem cell23_5682258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_5682258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682258 prefixEnd_5682258 := by exact prefixLift 5682258
  have htrace : WordTrace (prefixWord ++ tailWord_5682258) baseStart_5682258 baseEnd_5682258 := by
    simpa [prefixWord, tailWord_5682258, baseEnd_5682258] using wordTrace_append hprefix tailTrace_5682258
  have hstable : (prefixWord ++ tailWord_5682258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682258).length < 2 ^ (prefixWord ++ tailWord_5682258).sum := by decide
  have hdescent : baseEnd_5682258 < baseStart_5682258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682261 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_5682261 : Nat := 118140960795 + 5682261 * 2 ^ 59
def prefixEnd_5682261 : Nat := 4983230072969 + 3 ^ 40 * 5682261 * 2
def baseEnd_5682261 : Nat := 2917731097297697861405263

theorem tailTrace_5682261 : CollatzResearch.WordTrace tailWord_5682261 prefixEnd_5682261 2917731097297697861405263 := by
  unfold tailWord_5682261
  simp only [CollatzResearch.WordTrace]
  refine ⟨207249084867146324762206637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138166056578097549841471091 207249084867146324762206637)
  ·
    refine ⟨77718406825179871785827489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207249084867146324762206637 77718406825179871785827489)
    ·
      refine ⟨58288805118884903839370617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77718406825179871785827489 58288805118884903839370617)
      ·
        refine ⟨43716603839163677879527963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58288805118884903839370617 43716603839163677879527963)
        ·
          refine ⟨65574905758745516819291945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43716603839163677879527963 65574905758745516819291945)
          ·
            refine ⟨49181179319059137614468959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65574905758745516819291945 49181179319059137614468959)
            ·
              refine ⟨73771768978588706421703439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49181179319059137614468959 73771768978588706421703439)
              ·
                refine ⟨110657653467883059632555159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73771768978588706421703439 110657653467883059632555159)
                ·
                  refine ⟨165986480201824589448832739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110657653467883059632555159 165986480201824589448832739)
                  ·
                    refine ⟨248979720302736884173249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165986480201824589448832739 248979720302736884173249109)
                    ·
                      refine ⟨2917731097297697861405263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 248979720302736884173249109 2917731097297697861405263)
                      ·
                        rfl

theorem cell23_5682261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_5682261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682261 prefixEnd_5682261 := by exact prefixLift 5682261
  have htrace : WordTrace (prefixWord ++ tailWord_5682261) baseStart_5682261 baseEnd_5682261 := by
    simpa [prefixWord, tailWord_5682261, baseEnd_5682261] using wordTrace_append hprefix tailTrace_5682261
  have hstable : (prefixWord ++ tailWord_5682261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682261).length < 2 ^ (prefixWord ++ tailWord_5682261).sum := by decide
  have hdescent : baseEnd_5682261 < baseStart_5682261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682291 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_5682291 : Nat := 118140960795 + 5682291 * 2 ^ 59
def prefixEnd_5682291 : Nat := 4983230072969 + 3 ^ 40 * 5682291 * 2
def baseEnd_5682291 : Nat := 2917746501717332744030125

theorem tailTrace_5682291 : CollatzResearch.WordTrace tailWord_5682291 prefixEnd_5682291 2917746501717332744030125 := by
  unfold tailWord_5682291
  simp only [CollatzResearch.WordTrace]
  refine ⟨207250179057037639885798727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138166786038025093257199151 207250179057037639885798727)
  ·
    refine ⟨310875268585556459828698091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207250179057037639885798727 310875268585556459828698091)
    ·
      refine ⟨466312902878334689743047137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310875268585556459828698091 466312902878334689743047137)
      ·
        refine ⟨349734677158751017307285353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466312902878334689743047137 349734677158751017307285353)
        ·
          refine ⟨262301007869063262980464015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349734677158751017307285353 262301007869063262980464015)
          ·
            refine ⟨393451511803594894470696023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262301007869063262980464015 393451511803594894470696023)
            ·
              refine ⟨590177267705392341706044035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393451511803594894470696023 590177267705392341706044035)
              ·
                refine ⟨885265901558088512559066053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590177267705392341706044035 885265901558088512559066053)
                ·
                  refine ⟨165987356542141596104824885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 885265901558088512559066053 165987356542141596104824885)
                  ·
                    refine ⟨15561314675825774634827333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165987356542141596104824885 15561314675825774634827333)
                    ·
                      refine ⟨2917746501717332744030125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15561314675825774634827333 2917746501717332744030125)
                      ·
                        rfl

theorem cell23_5682291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_5682291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682291 prefixEnd_5682291 := by exact prefixLift 5682291
  have htrace : WordTrace (prefixWord ++ tailWord_5682291) baseStart_5682291 baseEnd_5682291 := by
    simpa [prefixWord, tailWord_5682291, baseEnd_5682291] using wordTrace_append hprefix tailTrace_5682291
  have hstable : (prefixWord ++ tailWord_5682291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682291).length < 2 ^ (prefixWord ++ tailWord_5682291).sum := by decide
  have hdescent : baseEnd_5682291 < baseStart_5682291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682295 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 2, 3, 2]
def baseStart_5682295 : Nat := 118140960795 + 5682295 * 2 ^ 59
def prefixEnd_5682295 : Nat := 4983230072969 + 3 ^ 40 * 5682295 * 2
def baseEnd_5682295 : Nat := 2917748555639950728380107

theorem tailTrace_5682295 : CollatzResearch.WordTrace tailWord_5682295 prefixEnd_5682295 2917748555639950728380107 := by
  unfold tailWord_5682295
  simp only [CollatzResearch.WordTrace]
  refine ⟨207250324949023148568944339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138166883299348765712629559 207250324949023148568944339)
  ·
    refine ⟨310875487423534722853416509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207250324949023148568944339 310875487423534722853416509)
    ·
      refine ⟨116578307783825521070031191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310875487423534722853416509 116578307783825521070031191)
      ·
        refine ⟨174867461675738281605046787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116578307783825521070031191 174867461675738281605046787)
        ·
          refine ⟨262301192513607422407570181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174867461675738281605046787 262301192513607422407570181)
          ·
            refine ⟨49181473596301391701419409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262301192513607422407570181 49181473596301391701419409)
            ·
              refine ⟨36886105197226043776064557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49181473596301391701419409 36886105197226043776064557)
              ·
                refine ⟨13832289448959766416024209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36886105197226043776064557 13832289448959766416024209)
                ·
                  refine ⟨10374217086719824812018157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13832289448959766416024209 10374217086719824812018157)
                  ·
                    refine ⟨3890331407519934304506809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10374217086719824812018157 3890331407519934304506809)
                    ·
                      refine ⟨2917748555639950728380107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890331407519934304506809 2917748555639950728380107)
                      ·
                        rfl

theorem cell23_5682295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_5682295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682295 prefixEnd_5682295 := by exact prefixLift 5682295
  have htrace : WordTrace (prefixWord ++ tailWord_5682295) baseStart_5682295 baseEnd_5682295 := by
    simpa [prefixWord, tailWord_5682295, baseEnd_5682295] using wordTrace_append hprefix tailTrace_5682295
  have hstable : (prefixWord ++ tailWord_5682295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682295).length < 2 ^ (prefixWord ++ tailWord_5682295).sum := by decide
  have hdescent : baseEnd_5682295 < baseStart_5682295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682305 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 1, 5]
def baseStart_5682305 : Nat := 118140960795 + 5682305 * 2 ^ 59
def prefixEnd_5682305 : Nat := 4983230072969 + 3 ^ 40 * 5682305 * 2
def baseEnd_5682305 : Nat := 972584563482165229751687

theorem tailTrace_5682305 : CollatzResearch.WordTrace tailWord_5682305 prefixEnd_5682305 972584563482165229751687 := by
  unfold tailWord_5682305
  simp only [CollatzResearch.WordTrace]
  refine ⟨207250689678986920276808369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138167126452657946851205579 207250689678986920276808369)
  ·
    refine ⟨155438017259240190207606277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207250689678986920276808369 155438017259240190207606277)
    ·
      refine ⟨29144628236107535663926177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155438017259240190207606277 29144628236107535663926177)
      ·
        refine ⟨21858471177080651747944633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29144628236107535663926177 21858471177080651747944633)
        ·
          refine ⟨16393853382810488810958475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21858471177080651747944633 16393853382810488810958475)
          ·
            refine ⟨24590780074215733216437713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16393853382810488810958475 24590780074215733216437713)
            ·
              refine ⟨18443085055661799912328285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24590780074215733216437713 18443085055661799912328285)
              ·
                refine ⟨6916156895873174967123107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18443085055661799912328285 6916156895873174967123107)
                ·
                  refine ⟨10374235343809762450684661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916156895873174967123107 10374235343809762450684661)
                  ·
                    refine ⟨972584563482165229751687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10374235343809762450684661 972584563482165229751687)
                    ·
                      rfl

theorem cell23_5682305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_5682305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682305 prefixEnd_5682305 := by exact prefixLift 5682305
  have htrace : WordTrace (prefixWord ++ tailWord_5682305) baseStart_5682305 baseEnd_5682305 := by
    simpa [prefixWord, tailWord_5682305, baseEnd_5682305] using wordTrace_append hprefix tailTrace_5682305
  have hstable : (prefixWord ++ tailWord_5682305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682305).length < 2 ^ (prefixWord ++ tailWord_5682305).sum := by decide
  have hdescent : baseEnd_5682305 < baseStart_5682305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682359 : List Nat := [1, 1, 3, 1, 4, 1, 2, 5, 1, 2, 2]
def baseStart_5682359 : Nat := 118140960795 + 5682359 * 2 ^ 59
def prefixEnd_5682359 : Nat := 4983230072969 + 3 ^ 40 * 5682359 * 2
def baseEnd_5682359 : Nat := 2917781418401838477979813

theorem tailTrace_5682359 : CollatzResearch.WordTrace tailWord_5682359 prefixEnd_5682359 2917781418401838477979813 := by
  unfold tailWord_5682359
  simp only [CollatzResearch.WordTrace]
  refine ⟨207252659220791287499274131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138168439480527524999516087 207252659220791287499274131)
  ·
    refine ⟨310878988831186931248911197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207252659220791287499274131 310878988831186931248911197)
    ·
      refine ⟨116579620811695099218341699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310878988831186931248911197 116579620811695099218341699)
      ·
        refine ⟨174869431217542648827512549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116579620811695099218341699 174869431217542648827512549)
        ·
          refine ⟨32788018353289246655158603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174869431217542648827512549 32788018353289246655158603)
          ·
            refine ⟨49182027529933869982737905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32788018353289246655158603 49182027529933869982737905)
            ·
              refine ⟨36886520647450402487053429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49182027529933869982737905 36886520647450402487053429)
              ·
                refine ⟨3458111310698475233161259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36886520647450402487053429 3458111310698475233161259)
                ·
                  refine ⟨5187166966047712849741889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458111310698475233161259 5187166966047712849741889)
                  ·
                    refine ⟨3890375224535784637306417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187166966047712849741889 3890375224535784637306417)
                    ·
                      refine ⟨2917781418401838477979813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890375224535784637306417 2917781418401838477979813)
                      ·
                        rfl

theorem cell23_5682359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_5682359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682359 prefixEnd_5682359 := by exact prefixLift 5682359
  have htrace : WordTrace (prefixWord ++ tailWord_5682359) baseStart_5682359 baseEnd_5682359 := by
    simpa [prefixWord, tailWord_5682359, baseEnd_5682359] using wordTrace_append hprefix tailTrace_5682359
  have hstable : (prefixWord ++ tailWord_5682359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682359).length < 2 ^ (prefixWord ++ tailWord_5682359).sum := by decide
  have hdescent : baseEnd_5682359 < baseStart_5682359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682369 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5682369 : Nat := 118140960795 + 5682369 * 2 ^ 59
def prefixEnd_5682369 : Nat := 4983230072969 + 3 ^ 40 * 5682369 * 2
def baseEnd_5682369 : Nat := 972595517736127812951589

theorem tailTrace_5682369 : CollatzResearch.WordTrace tailWord_5682369 prefixEnd_5682369 972595517736127812951589 := by
  unfold tailWord_5682369
  simp only [CollatzResearch.WordTrace]
  refine ⟨207253023950755059207138161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138168682633836706138092107 207253023950755059207138161)
  ·
    refine ⟨155439767963066294405353621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207253023950755059207138161 155439767963066294405353621)
    ·
      refine ⟨7286239123268732550250951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155439767963066294405353621 7286239123268732550250951)
      ·
        refine ⟨10929358684903098825376427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7286239123268732550250951 10929358684903098825376427)
        ·
          refine ⟨16394038027354648238064641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929358684903098825376427 16394038027354648238064641)
          ·
            refine ⟨12295528520515986178548481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16394038027354648238064641 12295528520515986178548481)
            ·
              refine ⟨9221646390386989633911361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12295528520515986178548481 9221646390386989633911361)
              ·
                refine ⟨6916234792790242225433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221646390386989633911361 6916234792790242225433521)
                ·
                  refine ⟨5187176094592681669075141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916234792790242225433521 5187176094592681669075141)
                  ·
                    refine ⟨972595517736127812951589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187176094592681669075141 972595517736127812951589)
                    ·
                      rfl

theorem cell23_5682369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5682369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682369 prefixEnd_5682369 := by exact prefixLift 5682369
  have htrace : WordTrace (prefixWord ++ tailWord_5682369) baseStart_5682369 baseEnd_5682369 := by
    simpa [prefixWord, tailWord_5682369, baseEnd_5682369] using wordTrace_append hprefix tailTrace_5682369
  have hstable : (prefixWord ++ tailWord_5682369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682369).length < 2 ^ (prefixWord ++ tailWord_5682369).sum := by decide
  have hdescent : baseEnd_5682369 < baseStart_5682369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682375 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 3]
def baseStart_5682375 : Nat := 118140960795 + 5682375 * 2 ^ 59
def prefixEnd_5682375 : Nat := 4983230072969 + 3 ^ 40 * 5682375 * 2
def baseEnd_5682375 : Nat := 2917789634092310415379739

theorem tailTrace_5682375 : CollatzResearch.WordTrace tailWord_5682375 prefixEnd_5682375 2917789634092310415379739 := by
  unfold tailWord_5682375
  simp only [CollatzResearch.WordTrace]
  refine ⟨207253242788733322231856579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138168828525822214821237719 207253242788733322231856579)
  ·
    refine ⟨310879864183099983347784869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207253242788733322231856579 310879864183099983347784869)
    ·
      refine ⟨58289974534331246877709663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310879864183099983347784869 58289974534331246877709663)
      ·
        refine ⟨87434961801496870316564495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58289974534331246877709663 87434961801496870316564495)
        ·
          refine ⟨131152442702245305474846743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87434961801496870316564495 131152442702245305474846743)
          ·
            refine ⟨196728664053367958212270115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131152442702245305474846743 196728664053367958212270115)
            ·
              refine ⟨295092996080051937318405173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196728664053367958212270115 295092996080051937318405173)
              ·
                refine ⟨27664968382504869123600485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295092996080051937318405173 27664968382504869123600485)
                ·
                  refine ⟨5187181571719662960675091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27664968382504869123600485 5187181571719662960675091)
                  ·
                    refine ⟨7780772357579494441012637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5187181571719662960675091 7780772357579494441012637)
                    ·
                      refine ⟨2917789634092310415379739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780772357579494441012637 2917789634092310415379739)
                      ·
                        rfl

theorem cell23_5682375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 1, 3].length) (baseStart_5682375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682375 prefixEnd_5682375 := by exact prefixLift 5682375
  have htrace : WordTrace (prefixWord ++ tailWord_5682375) baseStart_5682375 baseEnd_5682375 := by
    simpa [prefixWord, tailWord_5682375, baseEnd_5682375] using wordTrace_append hprefix tailTrace_5682375
  have hstable : (prefixWord ++ tailWord_5682375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682375).length < 2 ^ (prefixWord ++ tailWord_5682375).sum := by decide
  have hdescent : baseEnd_5682375 < baseStart_5682375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682376 : List Nat := [2, 1, 3, 1, 2, 1, 6, 2, 1, 2, 2]
def baseStart_5682376 : Nat := 118140960795 + 5682376 * 2 ^ 59
def prefixEnd_5682376 : Nat := 4983230072969 + 3 ^ 40 * 5682376 * 2
def baseEnd_5682376 : Nat := 2917790147572964911467235

theorem tailTrace_5682376 : CollatzResearch.WordTrace tailWord_5682376 prefixEnd_5682376 2917790147572964911467235 := by
  unfold tailWord_5682376
  simp only [CollatzResearch.WordTrace]
  refine ⟨103626639630864849701321491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138168852841153132935095321 103626639630864849701321491)
  ·
    refine ⟨155439959446297274551982237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103626639630864849701321491 155439959446297274551982237)
    ·
      refine ⟨58289984792361477956993339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155439959446297274551982237 58289984792361477956993339)
      ·
        refine ⟨87434977188542216935490009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58289984792361477956993339 87434977188542216935490009)
        ·
          refine ⟨65576232891406662701617507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87434977188542216935490009 65576232891406662701617507)
          ·
            refine ⟨98364349337109994052426261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65576232891406662701617507 98364349337109994052426261)
            ·
              refine ⟨4610828875177030971207481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98364349337109994052426261 4610828875177030971207481)
              ·
                refine ⟨3458121656382773228405611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4610828875177030971207481 3458121656382773228405611)
                ·
                  refine ⟨5187182484574159842608417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458121656382773228405611 5187182484574159842608417)
                  ·
                    refine ⟨3890386863430619881956313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187182484574159842608417 3890386863430619881956313)
                    ·
                      refine ⟨2917790147572964911467235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890386863430619881956313 2917790147572964911467235)
                      ·
                        rfl

theorem cell23_5682376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_5682376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682376 prefixEnd_5682376 := by exact prefixLift 5682376
  have htrace : WordTrace (prefixWord ++ tailWord_5682376) baseStart_5682376 baseEnd_5682376 := by
    simpa [prefixWord, tailWord_5682376, baseEnd_5682376] using wordTrace_append hprefix tailTrace_5682376
  have hstable : (prefixWord ++ tailWord_5682376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682376).length < 2 ^ (prefixWord ++ tailWord_5682376).sum := by decide
  have hdescent : baseEnd_5682376 < baseStart_5682376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682378 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_5682378 : Nat := 118140960795 + 5682378 * 2 ^ 59
def prefixEnd_5682378 : Nat := 4983230072969 + 3 ^ 40 * 5682378 * 2
def baseEnd_5682378 : Nat := 972597058178091301214075

theorem tailTrace_5682378 : CollatzResearch.WordTrace tailWord_5682378 prefixEnd_5682378 972597058178091301214075 := by
  unfold tailWord_5682378
  simp only [CollatzResearch.WordTrace]
  refine ⟨51813338051930613436053947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138168901471814969162810525 51813338051930613436053947)
  ·
    refine ⟨77720007077895920154080921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51813338051930613436053947 77720007077895920154080921)
    ·
      refine ⟨58290005308421940115560691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77720007077895920154080921 58290005308421940115560691)
      ·
        refine ⟨87435007962632910173341037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58290005308421940115560691 87435007962632910173341037)
        ·
          refine ⟨32788127985987341315002889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87435007962632910173341037 32788127985987341315002889)
          ·
            refine ⟨24591095989490505986252167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32788127985987341315002889 24591095989490505986252167)
            ·
              refine ⟨36886643984235758979378251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24591095989490505986252167 36886643984235758979378251)
              ·
                refine ⟨55329965976353638469067377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36886643984235758979378251 55329965976353638469067377)
                ·
                  refine ⟨41497474482265228851800533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55329965976353638469067377 41497474482265228851800533)
                  ·
                    refine ⟨972597058178091301214075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41497474482265228851800533 972597058178091301214075)
                    ·
                      rfl

theorem cell23_5682378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_5682378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682378 prefixEnd_5682378 := by exact prefixLift 5682378
  have htrace : WordTrace (prefixWord ++ tailWord_5682378) baseStart_5682378 baseEnd_5682378 := by
    simpa [prefixWord, tailWord_5682378, baseEnd_5682378] using wordTrace_append hprefix tailTrace_5682378
  have hstable : (prefixWord ++ tailWord_5682378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682378).length < 2 ^ (prefixWord ++ tailWord_5682378).sum := by decide
  have hdescent : baseEnd_5682378 < baseStart_5682378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682382 : List Nat := [4, 1, 1, 1, 6, 1, 1, 8]
def baseStart_5682382 : Nat := 118140960795 + 5682382 * 2 ^ 59
def prefixEnd_5682382 : Nat := 4983230072969 + 3 ^ 40 * 5682382 * 2
def baseEnd_5682382 : Nat := 108066415868773773629341

theorem tailTrace_5682382 : CollatzResearch.WordTrace tailWord_5682382 prefixEnd_5682382 108066415868773773629341 := by
  unfold tailWord_5682382
  simp only [CollatzResearch.WordTrace]
  refine ⟨25906687262463495303420175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138168998733138641618240933 25906687262463495303420175)
  ·
    refine ⟨38860030893695242955130263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25906687262463495303420175 38860030893695242955130263)
    ·
      refine ⟨58290046340542864432695395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38860030893695242955130263 58290046340542864432695395)
      ·
        refine ⟨87435069510814296649043093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58290046340542864432695395 87435069510814296649043093)
        ·
          refine ⟨4098518883319420155423895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87435069510814296649043093 4098518883319420155423895)
          ·
            refine ⟨6147778324979130233135843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098518883319420155423895 6147778324979130233135843)
            ·
              refine ⟨9221667487468695349703765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147778324979130233135843 9221667487468695349703765)
              ·
                refine ⟨108066415868773773629341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9221667487468695349703765 108066415868773773629341)
                ·
                  rfl

theorem cell23_5682382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_5682382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682382 prefixEnd_5682382 := by exact prefixLift 5682382
  have htrace : WordTrace (prefixWord ++ tailWord_5682382) baseStart_5682382 baseEnd_5682382 := by
    simpa [prefixWord, tailWord_5682382, baseEnd_5682382] using wordTrace_append hprefix tailTrace_5682382
  have hstable : (prefixWord ++ tailWord_5682382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682382).length < 2 ^ (prefixWord ++ tailWord_5682382).sum := by decide
  have hdescent : baseEnd_5682382 < baseStart_5682382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682392 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3]
def baseStart_5682392 : Nat := 118140960795 + 5682392 * 2 ^ 59
def prefixEnd_5682392 : Nat := 4983230072969 + 3 ^ 40 * 5682392 * 2
def baseEnd_5682392 : Nat := 2917798363263436848867161

theorem tailTrace_5682392 : CollatzResearch.WordTrace tailWord_5682392 prefixEnd_5682392 2917798363263436848867161 := by
  unfold tailWord_5682392
  simp only [CollatzResearch.WordTrace]
  refine ⟨103626931414835867067612715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138169241886447822756816953 103626931414835867067612715)
  ·
    refine ⟨155440397122253800601419073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103626931414835867067612715 155440397122253800601419073)
    ·
      refine ⟨116580297841690350451064305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155440397122253800601419073 116580297841690350451064305)
      ·
        refine ⟨87435223381267762838298229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116580297841690350451064305 87435223381267762838298229)
        ·
          refine ⟨8197052191993852766090459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87435223381267762838298229 8197052191993852766090459)
          ·
            refine ⟨12295578287990779149135689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197052191993852766090459 12295578287990779149135689)
            ·
              refine ⟨9221683715993084361851767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12295578287990779149135689 9221683715993084361851767)
              ·
                refine ⟨13832525573989626542777651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221683715993084361851767 13832525573989626542777651)
                ·
                  refine ⟨20748788360984439814166477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13832525573989626542777651 20748788360984439814166477)
                  ·
                    refine ⟨7780795635369164930312429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20748788360984439814166477 7780795635369164930312429)
                    ·
                      refine ⟨2917798363263436848867161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7780795635369164930312429 2917798363263436848867161)
                      ·
                        rfl

theorem cell23_5682392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_5682392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682392 prefixEnd_5682392 := by exact prefixLift 5682392
  have htrace : WordTrace (prefixWord ++ tailWord_5682392) baseStart_5682392 baseEnd_5682392 := by
    simpa [prefixWord, tailWord_5682392, baseEnd_5682392] using wordTrace_append hprefix tailTrace_5682392
  have hstable : (prefixWord ++ tailWord_5682392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682392).length < 2 ^ (prefixWord ++ tailWord_5682392).sum := by decide
  have hdescent : baseEnd_5682392 < baseStart_5682392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682408 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_5682408 : Nat := 118140960795 + 5682408 * 2 ^ 59
def prefixEnd_5682408 : Nat := 4983230072969 + 3 ^ 40 * 5682408 * 2
def baseEnd_5682408 : Nat := 972602192984636262089029

theorem tailTrace_5682408 : CollatzResearch.WordTrace tailWord_5682408 prefixEnd_5682408 972602192984636262089029 := by
  unfold tailWord_5682408
  simp only [CollatzResearch.WordTrace]
  refine ⟨103627223198806884433903939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138169630931742512578538585 103627223198806884433903939)
  ·
    refine ⟨155440834798210326650855909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103627223198806884433903939 155440834798210326650855909)
    ·
      refine ⟨29145156524664436247035483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155440834798210326650855909 29145156524664436247035483)
      ·
        refine ⟨43717734786996654370553225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29145156524664436247035483 43717734786996654370553225)
        ·
          refine ⟨32788301090247490777914919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43717734786996654370553225 32788301090247490777914919)
          ·
            refine ⟨49182451635371236166872379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32788301090247490777914919 49182451635371236166872379)
            ·
              refine ⟨73773677453056854250308569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49182451635371236166872379 73773677453056854250308569)
              ·
                refine ⟨55330258089792640687731427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73773677453056854250308569 55330258089792640687731427)
                ·
                  refine ⟨82995387134688961031597141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55330258089792640687731427 82995387134688961031597141)
                  ·
                    refine ⟨972602192984636262089029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82995387134688961031597141 972602192984636262089029)
                    ·
                      rfl

theorem cell23_5682408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_5682408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682408 prefixEnd_5682408 := by exact prefixLift 5682408
  have htrace : WordTrace (prefixWord ++ tailWord_5682408) baseStart_5682408 baseEnd_5682408 := by
    simpa [prefixWord, tailWord_5682408, baseEnd_5682408] using wordTrace_append hprefix tailTrace_5682408
  have hstable : (prefixWord ++ tailWord_5682408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682408).length < 2 ^ (prefixWord ++ tailWord_5682408).sum := by decide
  have hdescent : baseEnd_5682408 < baseStart_5682408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682419 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 1, 3, 2]
def baseStart_5682419 : Nat := 118140960795 + 5682419 * 2 ^ 59
def prefixEnd_5682419 : Nat := 4983230072969 + 3 ^ 40 * 5682419 * 2
def baseEnd_5682419 : Nat := 2917812227241108243229537

theorem tailTrace_5682419 : CollatzResearch.WordTrace tailWord_5682419 prefixEnd_5682419 2917812227241108243229537 := by
  unfold tailWord_5682419
  simp only [CollatzResearch.WordTrace]
  refine ⟨207254847600573917746458311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138169898400382611830972207 207254847600573917746458311)
  ·
    refine ⟨310882271400860876619687467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207254847600573917746458311 310882271400860876619687467)
    ·
      refine ⟨466323407101291314929531201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310882271400860876619687467 466323407101291314929531201)
      ·
        refine ⟨349742555325968486197148401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466323407101291314929531201 349742555325968486197148401)
        ·
          refine ⟨262306916494476364647861301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349742555325968486197148401 262306916494476364647861301)
          ·
            refine ⟨24591273421357159185736997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262306916494476364647861301 24591273421357159185736997)
            ·
              refine ⟨4610863766504467347325687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24591273421357159185736997 4610863766504467347325687)
              ·
                refine ⟨6916295649756701020988531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610863766504467347325687 6916295649756701020988531)
                ·
                  refine ⟨10374443474635051531482797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916295649756701020988531 10374443474635051531482797)
                  ·
                    refine ⟨3890416302988144324306049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10374443474635051531482797 3890416302988144324306049)
                    ·
                      refine ⟨2917812227241108243229537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890416302988144324306049 2917812227241108243229537)
                      ·
                        rfl

theorem cell23_5682419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 1, 3, 2].length) (baseStart_5682419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682419 prefixEnd_5682419 := by exact prefixLift 5682419
  have htrace : WordTrace (prefixWord ++ tailWord_5682419) baseStart_5682419 baseEnd_5682419 := by
    simpa [prefixWord, tailWord_5682419, baseEnd_5682419] using wordTrace_append hprefix tailTrace_5682419
  have hstable : (prefixWord ++ tailWord_5682419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682419).length < 2 ^ (prefixWord ++ tailWord_5682419).sum := by decide
  have hdescent : baseEnd_5682419 < baseStart_5682419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682420 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_5682420 : Nat := 118140960795 + 5682420 * 2 ^ 59
def prefixEnd_5682420 : Nat := 4983230072969 + 3 ^ 40 * 5682420 * 2
def baseEnd_5682420 : Nat := 972604246907254246439011

theorem tailTrace_5682420 : CollatzResearch.WordTrace tailWord_5682420 prefixEnd_5682420 972604246907254246439011 := by
  unfold tailWord_5682420
  simp only [CollatzResearch.WordTrace]
  refine ⟨103627442036785147458622357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138169922715713529944829809 103627442036785147458622357)
  ·
    refine ⟨4857536345474303787122923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103627442036785147458622357 4857536345474303787122923)
    ·
      refine ⟨7286304518211455680684385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4857536345474303787122923 7286304518211455680684385)
      ·
        refine ⟨5464728388658591760513289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7286304518211455680684385 5464728388658591760513289)
        ·
          refine ⟨4098546291493943820384967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5464728388658591760513289 4098546291493943820384967)
          ·
            refine ⟨6147819437240915730577451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098546291493943820384967 6147819437240915730577451)
            ·
              refine ⟨9221729155861373595866177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147819437240915730577451 9221729155861373595866177)
              ·
                refine ⟨6916296866896030196899633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9221729155861373595866177 6916296866896030196899633)
                ·
                  refine ⟨5187222650172022647674725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916296866896030196899633 5187222650172022647674725)
                  ·
                    refine ⟨972604246907254246439011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187222650172022647674725 972604246907254246439011)
                    ·
                      rfl

theorem cell23_5682420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_5682420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682420 prefixEnd_5682420 := by exact prefixLift 5682420
  have htrace : WordTrace (prefixWord ++ tailWord_5682420) baseStart_5682420 baseEnd_5682420 := by
    simpa [prefixWord, tailWord_5682420, baseEnd_5682420] using wordTrace_append hprefix tailTrace_5682420
  have hstable : (prefixWord ++ tailWord_5682420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682420).length < 2 ^ (prefixWord ++ tailWord_5682420).sum := by decide
  have hdescent : baseEnd_5682420 < baseStart_5682420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682475 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 5, 2]
def baseStart_5682475 : Nat := 118140960795 + 5682475 * 2 ^ 59
def prefixEnd_5682475 : Nat := 4983230072969 + 3 ^ 40 * 5682475 * 2
def baseEnd_5682475 : Nat := 2917840982157760024129279

theorem tailTrace_5682475 : CollatzResearch.WordTrace tailWord_5682475 prefixEnd_5682475 2917840982157760024129279 := by
  unfold tailWord_5682475
  simp only [CollatzResearch.WordTrace]
  refine ⟨207256890088371039310496879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138171260058914026206997919 207256890088371039310496879)
  ·
    refine ⟨310885335132556558965745319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207256890088371039310496879 310885335132556558965745319)
    ·
      refine ⟨466328002698834838448617979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310885335132556558965745319 466328002698834838448617979)
      ·
        refine ⟨699492004048252257672926969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466328002698834838448617979 699492004048252257672926969)
        ·
          refine ⟨524619003036189193254695227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699492004048252257672926969 524619003036189193254695227)
          ·
            refine ⟨786928504554283789882042841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524619003036189193254695227 786928504554283789882042841)
            ·
              refine ⟨590196378415712842411532131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786928504554283789882042841 590196378415712842411532131)
              ·
                refine ⟨885294567623569263617298197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590196378415712842411532131 885294567623569263617298197)
                ·
                  refine ⟨41498182857354809232060853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 885294567623569263617298197 41498182857354809232060853)
                  ·
                    refine ⟨3890454642877013365505705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41498182857354809232060853 3890454642877013365505705)
                    ·
                      refine ⟨2917840982157760024129279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890454642877013365505705 2917840982157760024129279)
                      ·
                        rfl

theorem cell23_5682475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 5, 2].length) (baseStart_5682475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682475 prefixEnd_5682475 := by exact prefixLift 5682475
  have htrace : WordTrace (prefixWord ++ tailWord_5682475) baseStart_5682475 baseEnd_5682475 := by
    simpa [prefixWord, tailWord_5682475, baseEnd_5682475] using wordTrace_append hprefix tailTrace_5682475
  have hstable : (prefixWord ++ tailWord_5682475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682475).length < 2 ^ (prefixWord ++ tailWord_5682475).sum := by decide
  have hdescent : baseEnd_5682475 < baseStart_5682475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682485 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_5682485 : Nat := 118140960795 + 5682485 * 2 ^ 59
def prefixEnd_5682485 : Nat := 4983230072969 + 3 ^ 40 * 5682485 * 2
def baseEnd_5682485 : Nat := 972615372321434995001411

theorem tailTrace_5682485 : CollatzResearch.WordTrace tailWord_5682485 prefixEnd_5682485 972615372321434995001411 := by
  unfold tailWord_5682485
  simp only [CollatzResearch.WordTrace]
  refine ⟨207257254818334811018360909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138171503212223207345573939 207257254818334811018360909)
  ·
    refine ⟨77721470556875554131885341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207257254818334811018360909 77721470556875554131885341)
    ·
      refine ⟨29145551458828332799457003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77721470556875554131885341 29145551458828332799457003)
      ·
        refine ⟨43718327188242499199185505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29145551458828332799457003 43718327188242499199185505)
        ·
          refine ⟨32788745391181874399389129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43718327188242499199185505 32788745391181874399389129)
          ·
            refine ⟨24591559043386405799541847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32788745391181874399389129 24591559043386405799541847)
            ·
              refine ⟨36887338565079608699312771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24591559043386405799541847 36887338565079608699312771)
              ·
                refine ⟨55331007847619413048969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36887338565079608699312771 55331007847619413048969157)
                ·
                  refine ⟨10374563971428639946681717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55331007847619413048969157 10374563971428639946681717)
                  ·
                    refine ⟨972615372321434995001411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10374563971428639946681717 972615372321434995001411)
                    ·
                      rfl

theorem cell23_5682485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_5682485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682485 prefixEnd_5682485 := by exact prefixLift 5682485
  have htrace : WordTrace (prefixWord ++ tailWord_5682485) baseStart_5682485 baseEnd_5682485 := by
    simpa [prefixWord, tailWord_5682485, baseEnd_5682485] using wordTrace_append hprefix tailTrace_5682485
  have hstable : (prefixWord ++ tailWord_5682485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682485).length < 2 ^ (prefixWord ++ tailWord_5682485).sum := by decide
  have hdescent : baseEnd_5682485 < baseStart_5682485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682489 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 7]
def baseStart_5682489 : Nat := 118140960795 + 5682489 * 2 ^ 59
def prefixEnd_5682489 : Nat := 4983230072969 + 3 ^ 40 * 5682489 * 2
def baseEnd_5682489 : Nat := 324205352320769218817135

theorem tailTrace_5682489 : CollatzResearch.WordTrace tailWord_5682489 prefixEnd_5682489 324205352320769218817135 := by
  unfold tailWord_5682489
  simp only [CollatzResearch.WordTrace]
  refine ⟨207257400710320319701506521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138171600473546879801004347 207257400710320319701506521)
  ·
    refine ⟨155443050532740239776129891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207257400710320319701506521 155443050532740239776129891)
    ·
      refine ⟨233164575799110359664194837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155443050532740239776129891 233164575799110359664194837)
      ·
        refine ⟨10929589490583298109259133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233164575799110359664194837 10929589490583298109259133)
        ·
          refine ⟨4098596058968736790972175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10929589490583298109259133 4098596058968736790972175)
          ·
            refine ⟨6147894088453105186458263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4098596058968736790972175 6147894088453105186458263)
            ·
              refine ⟨9221841132679657779687395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6147894088453105186458263 9221841132679657779687395)
              ·
                refine ⟨13832761699019486669531093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9221841132679657779687395 13832761699019486669531093)
                ·
                  refine ⟨324205352320769218817135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13832761699019486669531093 324205352320769218817135)
                  ·
                    rfl

theorem cell23_5682489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 7].length) (baseStart_5682489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682489 prefixEnd_5682489 := by exact prefixLift 5682489
  have htrace : WordTrace (prefixWord ++ tailWord_5682489) baseStart_5682489 baseEnd_5682489 := by
    simpa [prefixWord, tailWord_5682489, baseEnd_5682489] using wordTrace_append hprefix tailTrace_5682489
  have hstable : (prefixWord ++ tailWord_5682489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682489).length < 2 ^ (prefixWord ++ tailWord_5682489).sum := by decide
  have hdescent : baseEnd_5682489 < baseStart_5682489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682495 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5]
def baseStart_5682495 : Nat := 118140960795 + 5682495 * 2 ^ 59
def prefixEnd_5682495 : Nat := 4983230072969 + 3 ^ 40 * 5682495 * 2
def baseEnd_5682495 : Nat := 2917851251770849945879187

theorem tailTrace_5682495 : CollatzResearch.WordTrace tailWord_5682495 prefixEnd_5682495 2917851251770849945879187 := by
  unfold tailWord_5682495
  simp only [CollatzResearch.WordTrace]
  refine ⟨207257619548298582726224939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138171746365532388484149959 207257619548298582726224939)
  ·
    refine ⟨310886429322447874089337409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207257619548298582726224939 310886429322447874089337409)
    ·
      refine ⟨233164821991835905567003057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310886429322447874089337409 233164821991835905567003057)
      ·
        refine ⟨174873616493876929175252293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233164821991835905567003057 174873616493876929175252293)
        ·
          refine ⟨32788803092601924220359805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174873616493876929175252293 32788803092601924220359805)
          ·
            refine ⟨12295801159725721582634927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32788803092601924220359805 12295801159725721582634927)
            ·
              refine ⟨18443701739588582373952391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12295801159725721582634927 18443701739588582373952391)
              ·
                refine ⟨27665552609382873560928587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18443701739588582373952391 27665552609382873560928587)
                ·
                  refine ⟨41498328914074310341392881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27665552609382873560928587 41498328914074310341392881)
                  ·
                    refine ⟨31123746685555732756044661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41498328914074310341392881 31123746685555732756044661)
                    ·
                      refine ⟨2917851251770849945879187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31123746685555732756044661 2917851251770849945879187)
                      ·
                        rfl

theorem cell23_5682495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_5682495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682495 prefixEnd_5682495 := by exact prefixLift 5682495
  have htrace : WordTrace (prefixWord ++ tailWord_5682495) baseStart_5682495 baseEnd_5682495 := by
    simpa [prefixWord, tailWord_5682495, baseEnd_5682495] using wordTrace_append hprefix tailTrace_5682495
  have hstable : (prefixWord ++ tailWord_5682495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682495).length < 2 ^ (prefixWord ++ tailWord_5682495).sum := by decide
  have hdescent : baseEnd_5682495 < baseStart_5682495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682500 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_5682500 : Nat := 118140960795 + 5682500 * 2 ^ 59
def prefixEnd_5682500 : Nat := 4983230072969 + 3 ^ 40 * 5682500 * 2
def baseEnd_5682500 : Nat := 2917853819174122426316665

theorem tailTrace_5682500 : CollatzResearch.WordTrace tailWord_5682500 prefixEnd_5682500 2917853819174122426316665 := by
  unfold tailWord_5682500
  simp only [CollatzResearch.WordTrace]
  refine ⟨103628900956640234290078477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138171867942186979053437969 103628900956640234290078477)
  ·
    refine ⟨38860837858740087858779429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103628900956640234290078477 38860837858740087858779429)
    ·
      refine ⟨7286407098513766473521143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38860837858740087858779429 7286407098513766473521143)
      ·
        refine ⟨10929610647770649710281715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7286407098513766473521143 10929610647770649710281715)
        ·
          refine ⟨16394415971655974565422573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929610647770649710281715 16394415971655974565422573)
          ·
            refine ⟨6147905989370990462033465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16394415971655974565422573 6147905989370990462033465)
            ·
              refine ⟨4610929492028242846525099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6147905989370990462033465 4610929492028242846525099)
              ·
                refine ⟨6916394238042364269787649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4610929492028242846525099 6916394238042364269787649)
                ·
                  refine ⟨5187295678531773202340737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916394238042364269787649 5187295678531773202340737)
                  ·
                    refine ⟨3890471758898829901755553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187295678531773202340737 3890471758898829901755553)
                    ·
                      refine ⟨2917853819174122426316665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890471758898829901755553 2917853819174122426316665)
                      ·
                        rfl

theorem cell23_5682500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_5682500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682500 prefixEnd_5682500 := by exact prefixLift 5682500
  have htrace : WordTrace (prefixWord ++ tailWord_5682500) baseStart_5682500 baseEnd_5682500 := by
    simpa [prefixWord, tailWord_5682500, baseEnd_5682500] using wordTrace_append hprefix tailTrace_5682500
  have hstable : (prefixWord ++ tailWord_5682500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682500).length < 2 ^ (prefixWord ++ tailWord_5682500).sum := by decide
  have hdescent : baseEnd_5682500 < baseStart_5682500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682515 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 5, 4]
def baseStart_5682515 : Nat := 118140960795 + 5682515 * 2 ^ 59
def prefixEnd_5682515 : Nat := 4983230072969 + 3 ^ 40 * 5682515 * 2
def baseEnd_5682515 : Nat := 972620507127979955876365

theorem tailTrace_5682515 : CollatzResearch.WordTrace tailWord_5682515 prefixEnd_5682515 972620507127979955876365 := by
  unfold tailWord_5682515
  simp only [CollatzResearch.WordTrace]
  refine ⟨207258349008226126141952999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138172232672150750761301999 207258349008226126141952999)
  ·
    refine ⟨310887523512339189212929499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207258349008226126141952999 310887523512339189212929499)
    ·
      refine ⟨466331285268508783819394249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310887523512339189212929499 466331285268508783819394249)
      ·
        refine ⟨349748463951381587864545687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466331285268508783819394249 349748463951381587864545687)
        ·
          refine ⟨524622695927072381796818531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349748463951381587864545687 524622695927072381796818531)
          ·
            refine ⟨786934043890608572695227797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524622695927072381796818531 786934043890608572695227797)
            ·
              refine ⟨36887533307372276845088803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 786934043890608572695227797 36887533307372276845088803)
              ·
                refine ⟨55331299961058415267633205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36887533307372276845088803 55331299961058415267633205)
                ·
                  refine ⟨5187309371349226431340613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55331299961058415267633205 5187309371349226431340613)
                  ·
                    refine ⟨972620507127979955876365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187309371349226431340613 972620507127979955876365)
                    ·
                      rfl

theorem cell23_5682515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 4].length) (baseStart_5682515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682515 prefixEnd_5682515 := by exact prefixLift 5682515
  have htrace : WordTrace (prefixWord ++ tailWord_5682515) baseStart_5682515 baseEnd_5682515 := by
    simpa [prefixWord, tailWord_5682515, baseEnd_5682515] using wordTrace_append hprefix tailTrace_5682515
  have hstable : (prefixWord ++ tailWord_5682515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682515).length < 2 ^ (prefixWord ++ tailWord_5682515).sum := by decide
  have hdescent : baseEnd_5682515 < baseStart_5682515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682545 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 6]
def baseStart_5682545 : Nat := 118140960795 + 5682545 * 2 ^ 59
def prefixEnd_5682545 : Nat := 4983230072969 + 3 ^ 40 * 5682545 * 2
def baseEnd_5682545 : Nat := 324208547311508305583773

theorem tailTrace_5682545 : CollatzResearch.WordTrace tailWord_5682545 prefixEnd_5682545 324208547311508305583773 := by
  unfold tailWord_5682545
  simp only [CollatzResearch.WordTrace]
  refine ⟨207259443198117441265545089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138172962132078294177030059 207259443198117441265545089)
  ·
    refine ⟨155444582398588080949158817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207259443198117441265545089 155444582398588080949158817)
    ·
      refine ⟨116583436798941060711869113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155444582398588080949158817 116583436798941060711869113)
      ·
        refine ⟨87437577599205795533901835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116583436798941060711869113 87437577599205795533901835)
        ·
          refine ⟨131156366398808693300852753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87437577599205795533901835 131156366398808693300852753)
          ·
            refine ⟨98367274799106519975639565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131156366398808693300852753 98367274799106519975639565)
            ·
              refine ⟨36887728049664944990864837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98367274799106519975639565 36887728049664944990864837)
              ·
                refine ⟨6916449009312177185787157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36887728049664944990864837 6916449009312177185787157)
                ·
                  refine ⟨324208547311508305583773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6916449009312177185787157 324208547311508305583773)
                  ·
                    rfl

theorem cell23_5682545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 6].length) (baseStart_5682545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682545 prefixEnd_5682545 := by exact prefixLift 5682545
  have htrace : WordTrace (prefixWord ++ tailWord_5682545) baseStart_5682545 baseEnd_5682545 := by
    simpa [prefixWord, tailWord_5682545, baseEnd_5682545] using wordTrace_append hprefix tailTrace_5682545
  have hstable : (prefixWord ++ tailWord_5682545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682545).length < 2 ^ (prefixWord ++ tailWord_5682545).sum := by decide
  have hdescent : baseEnd_5682545 < baseStart_5682545 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682592 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 1, 5]
def baseStart_5682592 : Nat := 118140960795 + 5682592 * 2 ^ 59
def prefixEnd_5682592 : Nat := 4983230072969 + 3 ^ 40 * 5682592 * 2
def baseEnd_5682592 : Nat := 972633686464778688788747

theorem tailTrace_5682592 : CollatzResearch.WordTrace tailWord_5682592 prefixEnd_5682592 972633686464778688788747 := by
  unfold tailWord_5682592
  simp only [CollatzResearch.WordTrace]
  refine ⟨103630578714473584146253015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138174104952631445528337353 103630578714473584146253015)
  ·
    refine ⟨155445868071710376219379523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103630578714473584146253015 155445868071710376219379523)
    ·
      refine ⟨233168802107565564329069285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155445868071710376219379523 233168802107565564329069285)
      ·
        refine ⟨43719150395168543311700491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233168802107565564329069285 43719150395168543311700491)
        ·
          refine ⟨65578725592752814967550737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43719150395168543311700491 65578725592752814967550737)
          ·
            refine ⟨49184044194564611225663053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65578725592752814967550737 49184044194564611225663053)
            ·
              refine ⟨18444016572961729209623645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49184044194564611225663053 18444016572961729209623645)
              ·
                refine ⟨6916506214860648453608867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18444016572961729209623645 6916506214860648453608867)
                ·
                  refine ⟨10374759322290972680413301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916506214860648453608867 10374759322290972680413301)
                  ·
                    refine ⟨972633686464778688788747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10374759322290972680413301 972633686464778688788747)
                    ·
                      rfl

theorem cell23_5682592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 5].length) (baseStart_5682592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682592 prefixEnd_5682592 := by exact prefixLift 5682592
  have htrace : WordTrace (prefixWord ++ tailWord_5682592) baseStart_5682592 baseEnd_5682592 := by
    simpa [prefixWord, tailWord_5682592, baseEnd_5682592] using wordTrace_append hprefix tailTrace_5682592
  have hstable : (prefixWord ++ tailWord_5682592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682592).length < 2 ^ (prefixWord ++ tailWord_5682592).sum := by decide
  have hdescent : baseEnd_5682592 < baseStart_5682592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682599 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_5682599 : Nat := 118140960795 + 5682599 * 2 ^ 59
def prefixEnd_5682599 : Nat := 4983230072969 + 3 ^ 40 * 5682599 * 2
def baseEnd_5682599 : Nat := 2917904653758917538978709

theorem tailTrace_5682599 : CollatzResearch.WordTrace tailWord_5682599 prefixEnd_5682599 2917904653758917538978709 := by
  unfold tailWord_5682599
  simp only [CollatzResearch.WordTrace]
  refine ⟨207261412739921808488010851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138174275159947872325340567 207261412739921808488010851)
  ·
    refine ⟨310892119109882712732016277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207261412739921808488010851 310892119109882712732016277)
    ·
      refine ⟨14573068083275752159313263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 310892119109882712732016277 14573068083275752159313263)
      ·
        refine ⟨21859602124913628238969895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573068083275752159313263 21859602124913628238969895)
        ·
          refine ⟨32789403187370442358454843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21859602124913628238969895 32789403187370442358454843)
          ·
            refine ⟨49184104781055663537682265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32789403187370442358454843 49184104781055663537682265)
            ·
              refine ⟨36888078585791747653261699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49184104781055663537682265 36888078585791747653261699)
              ·
                refine ⟨55332117878687621479892549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36888078585791747653261699 55332117878687621479892549)
                ·
                  refine ⟨10374772102253929027479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55332117878687621479892549 10374772102253929027479853)
                  ·
                    refine ⟨3890539538345223385304945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10374772102253929027479853 3890539538345223385304945)
                    ·
                      refine ⟨2917904653758917538978709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890539538345223385304945 2917904653758917538978709)
                      ·
                        rfl

theorem cell23_5682599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_5682599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682599 prefixEnd_5682599 := by exact prefixLift 5682599
  have htrace : WordTrace (prefixWord ++ tailWord_5682599) baseStart_5682599 baseEnd_5682599 := by
    simpa [prefixWord, tailWord_5682599, baseEnd_5682599] using wordTrace_append hprefix tailTrace_5682599
  have hstable : (prefixWord ++ tailWord_5682599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682599).length < 2 ^ (prefixWord ++ tailWord_5682599).sum := by decide
  have hdescent : baseEnd_5682599 < baseStart_5682599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682646 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_5682646 : Nat := 118140960795 + 5682646 * 2 ^ 59
def prefixEnd_5682646 : Nat := 4983230072969 + 3 ^ 40 * 5682646 * 2
def baseEnd_5682646 : Nat := 2917928787349678855090993

theorem tailTrace_5682646 : CollatzResearch.WordTrace tailWord_5682646 prefixEnd_5682646 2917928787349678855090993 := by
  unfold tailWord_5682646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953945435671970969685737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138175417980501023676647861 12953945435671970969685737)
  ·
    refine ⟨9715459076753978227264303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12953945435671970969685737 9715459076753978227264303)
    ·
      refine ⟨14573188615130967340896455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9715459076753978227264303 14573188615130967340896455)
      ·
        refine ⟨21859782922696451011344683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573188615130967340896455 21859782922696451011344683)
        ·
          refine ⟨32789674384044676517017025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21859782922696451011344683 32789674384044676517017025)
          ·
            refine ⟨24592255788033507387762769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32789674384044676517017025 24592255788033507387762769)
            ·
              refine ⟨18444191841025130540822077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24592255788033507387762769 18444191841025130540822077)
              ·
                refine ⟨6916571940384423952808279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18444191841025130540822077 6916571940384423952808279)
                ·
                  refine ⟨10374857910576635929212419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916571940384423952808279 10374857910576635929212419)
                  ·
                    refine ⟨15562286865864953893818629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10374857910576635929212419 15562286865864953893818629)
                    ·
                      refine ⟨2917928787349678855090993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15562286865864953893818629 2917928787349678855090993)
                      ·
                        rfl

theorem cell23_5682646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_5682646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682646 prefixEnd_5682646 := by exact prefixLift 5682646
  have htrace : WordTrace (prefixWord ++ tailWord_5682646) baseStart_5682646 baseEnd_5682646 := by
    simpa [prefixWord, tailWord_5682646, baseEnd_5682646] using wordTrace_append hprefix tailTrace_5682646
  have hstable : (prefixWord ++ tailWord_5682646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682646).length < 2 ^ (prefixWord ++ tailWord_5682646).sum := by decide
  have hdescent : baseEnd_5682646 < baseStart_5682646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682649 : List Nat := [1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 3]
def baseStart_5682649 : Nat := 118140960795 + 5682649 * 2 ^ 59
def prefixEnd_5682649 : Nat := 4983230072969 + 3 ^ 40 * 5682649 * 2
def baseEnd_5682649 : Nat := 2917930327791642343353479

theorem tailTrace_5682649 : CollatzResearch.WordTrace tailWord_5682649 prefixEnd_5682649 2917930327791642343353479 := by
  unfold tailWord_5682649
  simp only [CollatzResearch.WordTrace]
  refine ⟨207263236389740667027331001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138175490926493778018220667 207263236389740667027331001)
  ·
    refine ⟨155447427292305500270498251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207263236389740667027331001 155447427292305500270498251)
    ·
      refine ⟨233171140938458250405747377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155447427292305500270498251 233171140938458250405747377)
      ·
        refine ⟨174878355703843687804310533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233171140938458250405747377 174878355703843687804310533)
        ·
          refine ⟨32789691694470691463308225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174878355703843687804310533 32789691694470691463308225)
          ·
            refine ⟨24592268770853018597481169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32789691694470691463308225 24592268770853018597481169)
            ·
              refine ⟨18444201578139763948110877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24592268770853018597481169 18444201578139763948110877)
              ·
                refine ⟨6916575591802411480541579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18444201578139763948110877 6916575591802411480541579)
                ·
                  refine ⟨10374863387703617220812369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916575591802411480541579 10374863387703617220812369)
                  ·
                    refine ⟨7781147540777712915609277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10374863387703617220812369 7781147540777712915609277)
                    ·
                      refine ⟨2917930327791642343353479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781147540777712915609277 2917930327791642343353479)
                      ·
                        rfl

theorem cell23_5682649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_5682649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682649 prefixEnd_5682649 := by exact prefixLift 5682649
  have htrace : WordTrace (prefixWord ++ tailWord_5682649) baseStart_5682649 baseEnd_5682649 := by
    simpa [prefixWord, tailWord_5682649, baseEnd_5682649] using wordTrace_append hprefix tailTrace_5682649
  have hstable : (prefixWord ++ tailWord_5682649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682649).length < 2 ^ (prefixWord ++ tailWord_5682649).sum := by decide
  have hdescent : baseEnd_5682649 < baseStart_5682649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682663 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_5682663 : Nat := 118140960795 + 5682663 * 2 ^ 59
def prefixEnd_5682663 : Nat := 4983230072969 + 3 ^ 40 * 5682663 * 2
def baseEnd_5682663 : Nat := 2917937516520805288578415

theorem tailTrace_5682663 : CollatzResearch.WordTrace tailWord_5682663 prefixEnd_5682663 2917937516520805288578415 := by
  unfold tailWord_5682663
  simp only [CollatzResearch.WordTrace]
  refine ⟨207263747011689947418340643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138175831341126631612227095 207263747011689947418340643)
  ·
    refine ⟨310895620517534921127510965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207263747011689947418340643 310895620517534921127510965)
    ·
      refine ⟨29146464423518898855704153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310895620517534921127510965 29146464423518898855704153)
      ·
        refine ⟨21859848317639174141778115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29146464423518898855704153 21859848317639174141778115)
        ·
          refine ⟨32789772476458761212667173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21859848317639174141778115 32789772476458761212667173)
          ·
            refine ⟨6148082339336017727375095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32789772476458761212667173 6148082339336017727375095)
            ·
              refine ⟨9222123509004026591062643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6148082339336017727375095 9222123509004026591062643)
              ·
                refine ⟨13833185263506039886593965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9222123509004026591062643 13833185263506039886593965)
                ·
                  refine ⟨5187444473814764957472737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13833185263506039886593965 5187444473814764957472737)
                  ·
                    refine ⟨3890583355361073718104553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187444473814764957472737 3890583355361073718104553)
                    ·
                      refine ⟨2917937516520805288578415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890583355361073718104553 2917937516520805288578415)
                      ·
                        rfl

theorem cell23_5682663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_5682663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682663 prefixEnd_5682663 := by exact prefixLift 5682663
  have htrace : WordTrace (prefixWord ++ tailWord_5682663) baseStart_5682663 baseEnd_5682663 := by
    simpa [prefixWord, tailWord_5682663, baseEnd_5682663] using wordTrace_append hprefix tailTrace_5682663
  have hstable : (prefixWord ++ tailWord_5682663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682663).length < 2 ^ (prefixWord ++ tailWord_5682663).sum := by decide
  have hdescent : baseEnd_5682663 < baseStart_5682663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682669 : List Nat := [1, 5, 1, 3, 2, 1, 2, 8]
def baseStart_5682669 : Nat := 118140960795 + 5682669 * 2 ^ 59
def prefixEnd_5682669 : Nat := 4983230072969 + 3 ^ 40 * 5682669 * 2
def baseEnd_5682669 : Nat := 108071873977953046855681

theorem tailTrace_5682669 : CollatzResearch.WordTrace tailWord_5682669 prefixEnd_5682669 108071873977953046855681 := by
  unfold tailWord_5682669
  simp only [CollatzResearch.WordTrace]
  refine ⟨207263965849668210443059061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138175977233112140295372707 207263965849668210443059061)
  ·
    refine ⟨19430996798406394729036787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207263965849668210443059061 19430996798406394729036787)
    ·
      refine ⟨29146495197609592093555181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19430996798406394729036787 29146495197609592093555181)
      ·
        refine ⟨10929935699103597035083193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29146495197609592093555181 10929935699103597035083193)
        ·
          refine ⟨8197451774327697776312395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10929935699103597035083193 8197451774327697776312395)
          ·
            refine ⟨12296177661491546664468593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197451774327697776312395 12296177661491546664468593)
            ·
              refine ⟨9222133246118659998351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12296177661491546664468593 9222133246118659998351445)
              ·
                refine ⟨108071873977953046855681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9222133246118659998351445 108071873977953046855681)
                ·
                  rfl

theorem cell23_5682669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 8].length) (baseStart_5682669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682669 prefixEnd_5682669 := by exact prefixLift 5682669
  have htrace : WordTrace (prefixWord ++ tailWord_5682669) baseStart_5682669 baseEnd_5682669 := by
    simpa [prefixWord, tailWord_5682669, baseEnd_5682669] using wordTrace_append hprefix tailTrace_5682669
  have hstable : (prefixWord ++ tailWord_5682669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682669).length < 2 ^ (prefixWord ++ tailWord_5682669).sum := by decide
  have hdescent : baseEnd_5682669 < baseStart_5682669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682675 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_5682675 : Nat := 118140960795 + 5682675 * 2 ^ 59
def prefixEnd_5682675 : Nat := 4983230072969 + 3 ^ 40 * 5682675 * 2
def baseEnd_5682675 : Nat := 2917943678288659241628359

theorem tailTrace_5682675 : CollatzResearch.WordTrace tailWord_5682675 prefixEnd_5682675 2917943678288659241628359 := by
  unfold tailWord_5682675
  simp only [CollatzResearch.WordTrace]
  refine ⟨207264184687646473467777479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138176123125097648978518319 207264184687646473467777479)
  ·
    refine ⟨310896277031469710201666219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207264184687646473467777479 310896277031469710201666219)
    ·
      refine ⟨466344415547204565302499329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310896277031469710201666219 466344415547204565302499329)
      ·
        refine ⟨349758311660403423976874497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466344415547204565302499329 349758311660403423976874497)
        ·
          refine ⟨262318733745302567982655873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349758311660403423976874497 262318733745302567982655873)
          ·
            refine ⟨196739050308976925986991905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262318733745302567982655873 196739050308976925986991905)
            ·
              refine ⟨147554287731732694490243929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196739050308976925986991905 147554287731732694490243929)
              ·
                refine ⟨110665715798799520867682947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147554287731732694490243929 110665715798799520867682947)
                ·
                  refine ⟨165998573698199281301524421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110665715798799520867682947 165998573698199281301524421)
                  ·
                    refine ⟨31124732568412365244035829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165998573698199281301524421 31124732568412365244035829)
                    ·
                      refine ⟨2917943678288659241628359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31124732568412365244035829 2917943678288659241628359)
                      ·
                        rfl

theorem cell23_5682675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_5682675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682675 prefixEnd_5682675 := by exact prefixLift 5682675
  have htrace : WordTrace (prefixWord ++ tailWord_5682675) baseStart_5682675 baseEnd_5682675 := by
    simpa [prefixWord, tailWord_5682675, baseEnd_5682675] using wordTrace_append hprefix tailTrace_5682675
  have hstable : (prefixWord ++ tailWord_5682675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682675).length < 2 ^ (prefixWord ++ tailWord_5682675).sum := by decide
  have hdescent : baseEnd_5682675 < baseStart_5682675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682722 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_5682722 : Nat := 118140960795 + 5682722 * 2 ^ 59
def prefixEnd_5682722 : Nat := 4983230072969 + 3 ^ 40 * 5682722 * 2
def baseEnd_5682722 : Nat := 2917967811879420557740643

theorem tailTrace_5682722 : CollatzResearch.WordTrace tailWord_5682722 prefixEnd_5682722 2917967811879420557740643 := by
  unfold tailWord_5682722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51816474729619050123684605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138177265945650800329825613 51816474729619050123684605)
  ·
    refine ⟨19431178023607143796381727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51816474729619050123684605 19431178023607143796381727)
    ·
      refine ⟨29146767035410715694572591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19431178023607143796381727 29146767035410715694572591)
      ·
        refine ⟨43720150553116073541858887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29146767035410715694572591 43720150553116073541858887)
        ·
          refine ⟨65580225829674110312788331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43720150553116073541858887 65580225829674110312788331)
          ·
            refine ⟨98370338744511165469182497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65580225829674110312788331 98370338744511165469182497)
            ·
              refine ⟨73777754058383374101886873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98370338744511165469182497 73777754058383374101886873)
              ·
                refine ⟨55333315543787530576415155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73777754058383374101886873 55333315543787530576415155)
                ·
                  refine ⟨82999973315681295864622733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55333315543787530576415155 82999973315681295864622733)
                  ·
                    refine ⟨31124989993380485949233525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82999973315681295864622733 31124989993380485949233525)
                    ·
                      refine ⟨2917967811879420557740643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31124989993380485949233525 2917967811879420557740643)
                      ·
                        rfl

theorem cell23_5682722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_5682722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682722 prefixEnd_5682722 := by exact prefixLift 5682722
  have htrace : WordTrace (prefixWord ++ tailWord_5682722) baseStart_5682722 baseEnd_5682722 := by
    simpa [prefixWord, tailWord_5682722, baseEnd_5682722] using wordTrace_append hprefix tailTrace_5682722
  have hstable : (prefixWord ++ tailWord_5682722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682722).length < 2 ^ (prefixWord ++ tailWord_5682722).sum := by decide
  have hdescent : baseEnd_5682722 < baseStart_5682722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682752 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3]
def baseStart_5682752 : Nat := 118140960795 + 5682752 * 2 ^ 59
def prefixEnd_5682752 : Nat := 4983230072969 + 3 ^ 40 * 5682752 * 2
def baseEnd_5682752 : Nat := 2917983216299055440365505

theorem tailTrace_5682752 : CollatzResearch.WordTrace tailWord_5682752 prefixEnd_5682752 2917983216299055440365505 := by
  unfold tailWord_5682752
  simp only [CollatzResearch.WordTrace]
  refine ⟨103633496554183757809165255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138177995405578343745553673 103633496554183757809165255)
  ·
    refine ⟨155450244831275636713747883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103633496554183757809165255 155450244831275636713747883)
    ·
      refine ⟨233175367246913455070621825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155450244831275636713747883 233175367246913455070621825)
      ·
        refine ⟨174881525435185091302966369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233175367246913455070621825 174881525435185091302966369)
        ·
          refine ⟨131161144076388818477224777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174881525435185091302966369 131161144076388818477224777)
          ·
            refine ⟨98370858057291613857918583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131161144076388818477224777 98370858057291613857918583)
            ·
              refine ⟨147556287085937420786877875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98370858057291613857918583 147556287085937420786877875)
              ·
                refine ⟨221334430628906131180316813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147556287085937420786877875 221334430628906131180316813)
                ·
                  refine ⟨83000411485839799192618805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221334430628906131180316813 83000411485839799192618805)
                  ·
                    refine ⟨7781288576797481174308013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83000411485839799192618805 7781288576797481174308013)
                    ·
                      refine ⟨2917983216299055440365505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781288576797481174308013 2917983216299055440365505)
                      ·
                        rfl

theorem cell23_5682752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_5682752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682752 prefixEnd_5682752 := by exact prefixLift 5682752
  have htrace : WordTrace (prefixWord ++ tailWord_5682752) baseStart_5682752 baseEnd_5682752 := by
    simpa [prefixWord, tailWord_5682752, baseEnd_5682752] using wordTrace_append hprefix tailTrace_5682752
  have hstable : (prefixWord ++ tailWord_5682752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682752).length < 2 ^ (prefixWord ++ tailWord_5682752).sum := by decide
  have hdescent : baseEnd_5682752 < baseStart_5682752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682770 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 2, 2, 2]
def baseStart_5682770 : Nat := 118140960795 + 5682770 * 2 ^ 59
def prefixEnd_5682770 : Nat := 4983230072969 + 3 ^ 40 * 5682770 * 2
def baseEnd_5682770 : Nat := 2917992458950836369940423

theorem tailTrace_5682770 : CollatzResearch.WordTrace tailWord_5682770 prefixEnd_5682770 2917992458950836369940423 := by
  unfold tailWord_5682770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51816912405575576173121441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138178433081534869794990509 51816912405575576173121441)
  ·
    refine ⟨38862684304181682129841081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51816912405575576173121441 38862684304181682129841081)
    ·
      refine ⟨29147013228136261597380811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38862684304181682129841081 29147013228136261597380811)
      ·
        refine ⟨43720519842204392396071217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29147013228136261597380811 43720519842204392396071217)
        ·
          refine ⟨32790389881653294297053413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43720519842204392396071217 32790389881653294297053413)
          ·
            refine ⟨6148198102809992680697515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32790389881653294297053413 6148198102809992680697515)
            ·
              refine ⟨9222297154214989021046273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6148198102809992680697515 9222297154214989021046273)
              ·
                refine ⟨6916722865661241765784705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9222297154214989021046273 6916722865661241765784705)
                ·
                  refine ⟨5187542149245931324338529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6916722865661241765784705 5187542149245931324338529)
                  ·
                    refine ⟨3890656611934448493253897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187542149245931324338529 3890656611934448493253897)
                    ·
                      refine ⟨2917992458950836369940423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890656611934448493253897 2917992458950836369940423)
                      ·
                        rfl

theorem cell23_5682770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_5682770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682770 prefixEnd_5682770 := by exact prefixLift 5682770
  have htrace : WordTrace (prefixWord ++ tailWord_5682770) baseStart_5682770 baseEnd_5682770 := by
    simpa [prefixWord, tailWord_5682770, baseEnd_5682770] using wordTrace_append hprefix tailTrace_5682770
  have hstable : (prefixWord ++ tailWord_5682770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682770).length < 2 ^ (prefixWord ++ tailWord_5682770).sum := by decide
  have hdescent : baseEnd_5682770 < baseStart_5682770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682809 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 4]
def baseStart_5682809 : Nat := 118140960795 + 5682809 * 2 ^ 59
def prefixEnd_5682809 : Nat := 4983230072969 + 3 ^ 40 * 5682809 * 2
def baseEnd_5682809 : Nat := 2918012484696361717352743

theorem tailTrace_5682809 : CollatzResearch.WordTrace tailWord_5682809 prefixEnd_5682809 2918012484696361717352743 := by
  unfold tailWord_5682809
  simp only [CollatzResearch.WordTrace]
  refine ⟨207269072069161014353155481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138179381379440676235436987 207269072069161014353155481)
  ·
    refine ⟨155451804051870760764866611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207269072069161014353155481 155451804051870760764866611)
    ·
      refine ⟨233177706077806141147299917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155451804051870760764866611 233177706077806141147299917)
      ·
        refine ⟨87441639779177302930237469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233177706077806141147299917 87441639779177302930237469)
        ·
          refine ⟨32790614917191488598839051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87441639779177302930237469 32790614917191488598839051)
          ·
            refine ⟨49185922375787232898258577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32790614917191488598839051 49185922375787232898258577)
            ·
              refine ⟨36889441781840424673693933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49185922375787232898258577 36889441781840424673693933)
              ·
                refine ⟨13833540668190159252635225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36889441781840424673693933 13833540668190159252635225)
                ·
                  refine ⟨10375155501142619439476419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13833540668190159252635225 10375155501142619439476419)
                  ·
                    refine ⟨15562733251713929159214629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10375155501142619439476419 15562733251713929159214629)
                    ·
                      refine ⟨2918012484696361717352743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15562733251713929159214629 2918012484696361717352743)
                      ·
                        rfl

theorem cell23_5682809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_5682809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682809 prefixEnd_5682809 := by exact prefixLift 5682809
  have htrace : WordTrace (prefixWord ++ tailWord_5682809) baseStart_5682809 baseEnd_5682809 := by
    simpa [prefixWord, tailWord_5682809, baseEnd_5682809] using wordTrace_append hprefix tailTrace_5682809
  have hstable : (prefixWord ++ tailWord_5682809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682809).length < 2 ^ (prefixWord ++ tailWord_5682809).sum := by decide
  have hdescent : baseEnd_5682809 < baseStart_5682809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682812 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_5682812 : Nat := 118140960795 + 5682812 * 2 ^ 59
def prefixEnd_5682812 : Nat := 4983230072969 + 3 ^ 40 * 5682812 * 2
def baseEnd_5682812 : Nat := 2918014025138325205615229

theorem tailTrace_5682812 : CollatzResearch.WordTrace tailWord_5682812 prefixEnd_5682812 2918014025138325205615229 := by
  unfold tailWord_5682812
  simp only [CollatzResearch.WordTrace]
  refine ⟨103634590744075072932757345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138179454325433430577009793 103634590744075072932757345)
  ·
    refine ⟨77725943058056304699568009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103634590744075072932757345 77725943058056304699568009)
    ·
      refine ⟨58294457293542228524676007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77725943058056304699568009 58294457293542228524676007)
      ·
        refine ⟨87441685940313342787014011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58294457293542228524676007 87441685940313342787014011)
        ·
          refine ⟨131162528910470014180521017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87441685940313342787014011 131162528910470014180521017)
          ·
            refine ⟨98371896682852510635390763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131162528910470014180521017 98371896682852510635390763)
            ·
              refine ⟨147557845024278765953086145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98371896682852510635390763 147557845024278765953086145)
              ·
                refine ⟨110668383768209074464814609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147557845024278765953086145 110668383768209074464814609)
                ·
                  refine ⟨83001287826156805848610957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110668383768209074464814609 83001287826156805848610957)
                  ·
                    refine ⟨31125482934808802193229109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83001287826156805848610957 31125482934808802193229109)
                    ·
                      refine ⟨2918014025138325205615229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31125482934808802193229109 2918014025138325205615229)
                      ·
                        rfl

theorem cell23_5682812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_5682812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682812 prefixEnd_5682812 := by exact prefixLift 5682812
  have htrace : WordTrace (prefixWord ++ tailWord_5682812) baseStart_5682812 baseEnd_5682812 := by
    simpa [prefixWord, tailWord_5682812, baseEnd_5682812] using wordTrace_append hprefix tailTrace_5682812
  have hstable : (prefixWord ++ tailWord_5682812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682812).length < 2 ^ (prefixWord ++ tailWord_5682812).sum := by decide
  have hdescent : baseEnd_5682812 < baseStart_5682812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682826 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_5682826 : Nat := 118140960795 + 5682826 * 2 ^ 59
def prefixEnd_5682826 : Nat := 4983230072969 + 3 ^ 40 * 5682826 * 2
def baseEnd_5682826 : Nat := 2918021213867488150840165

theorem tailTrace_5682826 : CollatzResearch.WordTrace tailWord_5682826 prefixEnd_5682826 2918021213867488150840165 := by
  unfold tailWord_5682826
  simp only [CollatzResearch.WordTrace]
  refine ⟨51817423027524856564131083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138179794740066284171016221 51817423027524856564131083)
  ·
    refine ⟨77726134541287284846196625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51817423027524856564131083 77726134541287284846196625)
    ·
      refine ⟨58294600905965463634647469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77726134541287284846196625 58294600905965463634647469)
      ·
        refine ⟨21860475339737048862992801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58294600905965463634647469 21860475339737048862992801)
        ·
          refine ⟨16395356504802786647244601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21860475339737048862992801 16395356504802786647244601)
          ·
            refine ⟨12296517378602089985433451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16395356504802786647244601 12296517378602089985433451)
            ·
              refine ⟨18444776067903134978150177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12296517378602089985433451 18444776067903134978150177)
              ·
                refine ⟨13833582050927351233612633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18444776067903134978150177 13833582050927351233612633)
                ·
                  refine ⟨10375186538195513425209475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13833582050927351233612633 10375186538195513425209475)
                  ·
                    refine ⟨15562779807293270137814213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10375186538195513425209475 15562779807293270137814213)
                    ·
                      refine ⟨2918021213867488150840165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15562779807293270137814213 2918021213867488150840165)
                      ·
                        rfl

theorem cell23_5682826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_5682826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682826 prefixEnd_5682826 := by exact prefixLift 5682826
  have htrace : WordTrace (prefixWord ++ tailWord_5682826) baseStart_5682826 baseEnd_5682826 := by
    simpa [prefixWord, tailWord_5682826, baseEnd_5682826] using wordTrace_append hprefix tailTrace_5682826
  have hstable : (prefixWord ++ tailWord_5682826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682826).length < 2 ^ (prefixWord ++ tailWord_5682826).sum := by decide
  have hdescent : baseEnd_5682826 < baseStart_5682826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682872 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7]
def baseStart_5682872 : Nat := 118140960795 + 5682872 * 2 ^ 59
def prefixEnd_5682872 : Nat := 4983230072969 + 3 ^ 40 * 5682872 * 2
def baseEnd_5682872 : Nat := 2918044833977594970864953

theorem tailTrace_5682872 : CollatzResearch.WordTrace tailWord_5682872 prefixEnd_5682872 2918044833977594970864953 := by
  unfold tailWord_5682872
  simp only [CollatzResearch.WordTrace]
  refine ⟨103635684933966388056349435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138180913245288517408465913 103635684933966388056349435)
  ·
    refine ⟨155453527400949582084524153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103635684933966388056349435 155453527400949582084524153)
    ·
      refine ⟨116590145550712186563393115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155453527400949582084524153 116590145550712186563393115)
      ·
        refine ⟨174885218326068279845089673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116590145550712186563393115 174885218326068279845089673)
        ·
          refine ⟨131163913744551209883817255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174885218326068279845089673 131163913744551209883817255)
          ·
            refine ⟨196745870616826814825725883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131163913744551209883817255 196745870616826814825725883)
            ·
              refine ⟨295118805925240222238588825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196745870616826814825725883 295118805925240222238588825)
              ·
                refine ⟨221339104443930166678941619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295118805925240222238588825 221339104443930166678941619)
                ·
                  refine ⟨332008656665895250018412429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221339104443930166678941619 332008656665895250018412429)
                  ·
                    refine ⟨124503246249710718756904661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332008656665895250018412429 124503246249710718756904661)
                    ·
                      refine ⟨2918044833977594970864953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124503246249710718756904661 2918044833977594970864953)
                      ·
                        rfl

theorem cell23_5682872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_5682872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682872 prefixEnd_5682872 := by exact prefixLift 5682872
  have htrace : WordTrace (prefixWord ++ tailWord_5682872) baseStart_5682872 baseEnd_5682872 := by
    simpa [prefixWord, tailWord_5682872, baseEnd_5682872] using wordTrace_append hprefix tailTrace_5682872
  have hstable : (prefixWord ++ tailWord_5682872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682872).length < 2 ^ (prefixWord ++ tailWord_5682872).sum := by decide
  have hdescent : baseEnd_5682872 < baseStart_5682872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682916 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 1, 1, 4]
def baseStart_5682916 : Nat := 118140960795 + 5682916 * 2 ^ 59
def prefixEnd_5682916 : Nat := 4983230072969 + 3 ^ 40 * 5682916 * 2
def baseEnd_5682916 : Nat := 2918067427126392798714751

theorem tailTrace_5682916 : CollatzResearch.WordTrace tailWord_5682916 prefixEnd_5682916 2918067427126392798714751 := by
  unfold tailWord_5682916
  simp only [CollatzResearch.WordTrace]
  refine ⟨103636487339886685813650301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138181983119848914418200401 103636487339886685813650301)
  ·
    refine ⟨38863682752457507180118863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103636487339886685813650301 38863682752457507180118863)
    ·
      refine ⟨58295524128686260770178295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38863682752457507180118863 58295524128686260770178295)
      ·
        refine ⟨87443286193029391155267443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58295524128686260770178295 87443286193029391155267443)
        ·
          refine ⟨131164929289544086732901165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87443286193029391155267443 131164929289544086732901165)
          ·
            refine ⟨49186848483579032524837937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131164929289544086732901165 49186848483579032524837937)
            ·
              refine ⟨36890136362684274393628453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49186848483579032524837937 36890136362684274393628453)
              ·
                refine ⟨6916900568003301448805335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36890136362684274393628453 6916900568003301448805335)
                ·
                  refine ⟨10375350852004952173208003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6916900568003301448805335 10375350852004952173208003)
                  ·
                    refine ⟨15563026278007428259812005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10375350852004952173208003 15563026278007428259812005)
                    ·
                      refine ⟨2918067427126392798714751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15563026278007428259812005 2918067427126392798714751)
                      ·
                        rfl

theorem cell23_5682916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_5682916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682916 prefixEnd_5682916 := by exact prefixLift 5682916
  have htrace : WordTrace (prefixWord ++ tailWord_5682916) baseStart_5682916 baseEnd_5682916 := by
    simpa [prefixWord, tailWord_5682916, baseEnd_5682916] using wordTrace_append hprefix tailTrace_5682916
  have hstable : (prefixWord ++ tailWord_5682916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682916).length < 2 ^ (prefixWord ++ tailWord_5682916).sum := by decide
  have hdescent : baseEnd_5682916 < baseStart_5682916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682920 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_5682920 : Nat := 118140960795 + 5682920 * 2 ^ 59
def prefixEnd_5682920 : Nat := 4983230072969 + 3 ^ 40 * 5682920 * 2
def baseEnd_5682920 : Nat := 2918069481049010783064733

theorem tailTrace_5682920 : CollatzResearch.WordTrace tailWord_5682920 prefixEnd_5682920 2918069481049010783064733 := by
  unfold tailWord_5682920
  simp only [CollatzResearch.WordTrace]
  refine ⟨103636560285879440155223107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138182080381172586873630809 103636560285879440155223107)
  ·
    refine ⟨155454840428819160232834661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103636560285879440155223107 155454840428819160232834661)
    ·
      refine ⟨29147782580403592543656499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155454840428819160232834661 29147782580403592543656499)
      ·
        refine ⟨43721673870605388815484749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29147782580403592543656499 43721673870605388815484749)
        ·
          refine ⟨16395627701477020805806781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43721673870605388815484749 16395627701477020805806781)
          ·
            refine ⟨6148360388053882802177543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16395627701477020805806781 6148360388053882802177543)
            ·
              refine ⟨9222540582080824203266315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6148360388053882802177543 9222540582080824203266315)
              ·
                refine ⟨13833810873121236304899473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9222540582080824203266315 13833810873121236304899473)
                ·
                  refine ⟨10375358154840927228674605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13833810873121236304899473 10375358154840927228674605)
                  ·
                    refine ⟨3890759308065347710752977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10375358154840927228674605 3890759308065347710752977)
                    ·
                      refine ⟨2918069481049010783064733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890759308065347710752977 2918069481049010783064733)
                      ·
                        rfl

theorem cell23_5682920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_5682920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682920 prefixEnd_5682920 := by exact prefixLift 5682920
  have htrace : WordTrace (prefixWord ++ tailWord_5682920) baseStart_5682920 baseEnd_5682920 := by
    simpa [prefixWord, tailWord_5682920, baseEnd_5682920] using wordTrace_append hprefix tailTrace_5682920
  have hstable : (prefixWord ++ tailWord_5682920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682920).length < 2 ^ (prefixWord ++ tailWord_5682920).sum := by decide
  have hdescent : baseEnd_5682920 < baseStart_5682920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682926 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_5682926 : Nat := 118140960795 + 5682926 * 2 ^ 59
def prefixEnd_5682926 : Nat := 4983230072969 + 3 ^ 40 * 5682926 * 2
def baseEnd_5682926 : Nat := 972690853977645919863235

theorem tailTrace_5682926 : CollatzResearch.WordTrace tailWord_5682926 prefixEnd_5682926 972690853977645919863235 := by
  unfold tailWord_5682926
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909167426217142916895579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138182226273158095556776421 25909167426217142916895579)
  ·
    refine ⟨38863751139325714375343369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25909167426217142916895579 38863751139325714375343369)
    ·
      refine ⟨29147813354494285781507527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38863751139325714375343369 29147813354494285781507527)
      ·
        refine ⟨43721720031741428672261291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29147813354494285781507527 43721720031741428672261291)
        ·
          refine ⟨65582580047612143008391937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43721720031741428672261291 65582580047612143008391937)
          ·
            refine ⟨49186935035709107256293953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65582580047612143008391937 49186935035709107256293953)
            ·
              refine ⟨36890201276781830442220465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49186935035709107256293953 36890201276781830442220465)
              ·
                refine ⟨27667650957586372831665349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36890201276781830442220465 27667650957586372831665349)
                ·
                  refine ⟨5187684554547444905937253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27667650957586372831665349 5187684554547444905937253)
                  ·
                    refine ⟨972690853977645919863235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187684554547444905937253 972690853977645919863235)
                    ·
                      rfl

theorem cell23_5682926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_5682926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682926 prefixEnd_5682926 := by exact prefixLift 5682926
  have htrace : WordTrace (prefixWord ++ tailWord_5682926) baseStart_5682926 baseEnd_5682926 := by
    simpa [prefixWord, tailWord_5682926, baseEnd_5682926] using wordTrace_append hprefix tailTrace_5682926
  have hstable : (prefixWord ++ tailWord_5682926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682926).length < 2 ^ (prefixWord ++ tailWord_5682926).sum := by decide
  have hdescent : baseEnd_5682926 < baseStart_5682926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682946 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_5682946 : Nat := 118140960795 + 5682946 * 2 ^ 59
def prefixEnd_5682946 : Nat := 4983230072969 + 3 ^ 40 * 5682946 * 2
def baseEnd_5682946 : Nat := 2918082831546027681339613

theorem tailTrace_5682946 : CollatzResearch.WordTrace tailWord_5682946 prefixEnd_5682946 2918082831546027681339613 := by
  unfold tailWord_5682946
  simp only [CollatzResearch.WordTrace]
  refine ⟨51818517217416171687723173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138182712579776457833928461 51818517217416171687723173)
  ·
    refine ⟨9715971978265532191448095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51818517217416171687723173 9715971978265532191448095)
    ·
      refine ⟨14573957967398298287172143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9715971978265532191448095 14573957967398298287172143)
      ·
        refine ⟨21860936951097447430758215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573957967398298287172143 21860936951097447430758215)
        ·
          refine ⟨32791405426646171146137323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21860936951097447430758215 32791405426646171146137323)
          ·
            refine ⟨49187108139969256719205985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32791405426646171146137323 49187108139969256719205985)
            ·
              refine ⟨36890331104976942539404489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49187108139969256719205985 36890331104976942539404489)
              ·
                refine ⟨27667748328732706904553367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36890331104976942539404489 27667748328732706904553367)
                ·
                  refine ⟨41501622493099060356830051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27667748328732706904553367 41501622493099060356830051)
                  ·
                    refine ⟨62252433739648590535245077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41501622493099060356830051 62252433739648590535245077)
                    ·
                      refine ⟨2918082831546027681339613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62252433739648590535245077 2918082831546027681339613)
                      ·
                        rfl

theorem cell23_5682946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_5682946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682946 prefixEnd_5682946 := by exact prefixLift 5682946
  have htrace : WordTrace (prefixWord ++ tailWord_5682946) baseStart_5682946 baseEnd_5682946 := by
    simpa [prefixWord, tailWord_5682946, baseEnd_5682946] using wordTrace_append hprefix tailTrace_5682946
  have hstable : (prefixWord ++ tailWord_5682946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682946).length < 2 ^ (prefixWord ++ tailWord_5682946).sum := by decide
  have hdescent : baseEnd_5682946 < baseStart_5682946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682949 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_5682949 : Nat := 118140960795 + 5682949 * 2 ^ 59
def prefixEnd_5682949 : Nat := 4983230072969 + 3 ^ 40 * 5682949 * 2
def baseEnd_5682949 : Nat := 2918084371987991169602099

theorem tailTrace_5682949 : CollatzResearch.WordTrace tailWord_5682949 prefixEnd_5682949 2918084371987991169602099 := by
  unfold tailWord_5682949
  simp only [CollatzResearch.WordTrace]
  refine ⟨207274178288653818263251901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138182785525769212175501267 207274178288653818263251901)
  ·
    refine ⟨77727816858245181848719463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207274178288653818263251901 77727816858245181848719463)
    ·
      refine ⟨116591725287367772773079195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77727816858245181848719463 116591725287367772773079195)
      ·
        refine ⟨174887587931051659159618793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116591725287367772773079195 174887587931051659159618793)
        ·
          refine ⟨131165690948288744369714095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174887587931051659159618793 131165690948288744369714095)
          ·
            refine ⟨196748536422433116554571143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131165690948288744369714095 196748536422433116554571143)
            ·
              refine ⟨295122804633649674831856715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196748536422433116554571143 295122804633649674831856715)
              ·
                refine ⟨442684206950474512247785073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295122804633649674831856715 442684206950474512247785073)
                ·
                  refine ⟨332013155212855884185838805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442684206950474512247785073 332013155212855884185838805)
                  ·
                    refine ⟨7781558325301309785605597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 332013155212855884185838805 7781558325301309785605597)
                    ·
                      refine ⟨2918084371987991169602099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781558325301309785605597 2918084371987991169602099)
                      ·
                        rfl

theorem cell23_5682949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_5682949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682949 prefixEnd_5682949 := by exact prefixLift 5682949
  have htrace : WordTrace (prefixWord ++ tailWord_5682949) baseStart_5682949 baseEnd_5682949 := by
    simpa [prefixWord, tailWord_5682949, baseEnd_5682949] using wordTrace_append hprefix tailTrace_5682949
  have hstable : (prefixWord ++ tailWord_5682949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682949).length < 2 ^ (prefixWord ++ tailWord_5682949).sum := by decide
  have hdescent : baseEnd_5682949 < baseStart_5682949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682979 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5682979 : Nat := 118140960795 + 5682979 * 2 ^ 59
def prefixEnd_5682979 : Nat := 4983230072969 + 3 ^ 40 * 5682979 * 2
def baseEnd_5682979 : Nat := 2918099776407626052226961

theorem tailTrace_5682979 : CollatzResearch.WordTrace tailWord_5682979 prefixEnd_5682979 2918099776407626052226961 := by
  unfold tailWord_5682979
  simp only [CollatzResearch.WordTrace]
  refine ⟨207275272478545133386843991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138183514985696755591229327 207275272478545133386843991)
  ·
    refine ⟨310912908717817700080265987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207275272478545133386843991 310912908717817700080265987)
    ·
      refine ⟨466369363076726550120398981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310912908717817700080265987 466369363076726550120398981)
      ·
        refine ⟨87444255576886228147574809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 466369363076726550120398981 87444255576886228147574809)
        ·
          refine ⟨65583191682664671110681107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87444255576886228147574809 65583191682664671110681107)
          ·
            refine ⟨98374787523997006666021661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65583191682664671110681107 98374787523997006666021661)
            ·
              refine ⟨36890545321498877499758123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98374787523997006666021661 36890545321498877499758123)
              ·
                refine ⟨55335817982248316249637185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36890545321498877499758123 55335817982248316249637185)
                ·
                  refine ⟨41501863486686237187227889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55335817982248316249637185 41501863486686237187227889)
                  ·
                    refine ⟨31126397615014677890420917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41501863486686237187227889 31126397615014677890420917)
                    ·
                      refine ⟨2918099776407626052226961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31126397615014677890420917 2918099776407626052226961)
                      ·
                        rfl

theorem cell23_5682979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5682979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682979 prefixEnd_5682979 := by exact prefixLift 5682979
  have htrace : WordTrace (prefixWord ++ tailWord_5682979) baseStart_5682979 baseEnd_5682979 := by
    simpa [prefixWord, tailWord_5682979, baseEnd_5682979] using wordTrace_append hprefix tailTrace_5682979
  have hstable : (prefixWord ++ tailWord_5682979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682979).length < 2 ^ (prefixWord ++ tailWord_5682979).sum := by decide
  have hdescent : baseEnd_5682979 < baseStart_5682979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682984 : List Nat := [2, 1, 5, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_5682984 : Nat := 118140960795 + 5682984 * 2 ^ 59
def prefixEnd_5682984 : Nat := 4983230072969 + 3 ^ 40 * 5682984 * 2
def baseEnd_5682984 : Nat := 2918102343810898532664439

theorem tailTrace_5682984 : CollatzResearch.WordTrace tailWord_5682984 prefixEnd_5682984 2918102343810898532664439 := by
  unfold tailWord_5682984
  simp only [CollatzResearch.WordTrace]
  refine ⟨103637727421763509620388003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138183636562351346160517337 103637727421763509620388003)
  ·
    refine ⟨155456591132645264430582005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103637727421763509620388003 155456591132645264430582005)
    ·
      refine ⟨14574055418685493540367063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155456591132645264430582005 14574055418685493540367063)
      ·
        refine ⟨21861083128028240310550595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574055418685493540367063 21861083128028240310550595)
        ·
          refine ⟨32791624692042360465825893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861083128028240310550595 32791624692042360465825893)
          ·
            refine ⟨6148429629757942587342355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32791624692042360465825893 6148429629757942587342355)
            ·
              refine ⟨9222644444636913881013533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6148429629757942587342355 9222644444636913881013533)
              ·
                refine ⟨3458491666738842705380075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9222644444636913881013533 3458491666738842705380075)
                ·
                  refine ⟨5187737500108264058070113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458491666738842705380075 5187737500108264058070113)
                  ·
                    refine ⟨3890803125081198043552585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187737500108264058070113 3890803125081198043552585)
                    ·
                      refine ⟨2918102343810898532664439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890803125081198043552585 2918102343810898532664439)
                      ·
                        rfl

theorem cell23_5682984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_5682984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682984 prefixEnd_5682984 := by exact prefixLift 5682984
  have htrace : WordTrace (prefixWord ++ tailWord_5682984) baseStart_5682984 baseEnd_5682984 := by
    simpa [prefixWord, tailWord_5682984, baseEnd_5682984] using wordTrace_append hprefix tailTrace_5682984
  have hstable : (prefixWord ++ tailWord_5682984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682984).length < 2 ^ (prefixWord ++ tailWord_5682984).sum := by decide
  have hdescent : baseEnd_5682984 < baseStart_5682984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5682999 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 6]
def baseStart_5682999 : Nat := 118140960795 + 5682999 * 2 ^ 59
def prefixEnd_5682999 : Nat := 4983230072969 + 3 ^ 40 * 5682999 * 2
def baseEnd_5682999 : Nat := 972703348673571991325623

theorem tailTrace_5682999 : CollatzResearch.WordTrace tailWord_5682999 prefixEnd_5682999 972703348673571991325623 := by
  unfold tailWord_5682999
  simp only [CollatzResearch.WordTrace]
  refine ⟨207276001938472676802572051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138184001292315117868381367 207276001938472676802572051)
  ·
    refine ⟨310914002907709015203858077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207276001938472676802572051 310914002907709015203858077)
    ·
      refine ⟨116592751090390880701446779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310914002907709015203858077 116592751090390880701446779)
      ·
        refine ⟨174889126635586321052170169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116592751090390880701446779 174889126635586321052170169)
        ·
          refine ⟨131166844976689740789127627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174889126635586321052170169 131166844976689740789127627)
          ·
            refine ⟨196750267465034611183691441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131166844976689740789127627 196750267465034611183691441)
            ·
              refine ⟨147562700598775958387768581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196750267465034611183691441 147562700598775958387768581)
              ·
                refine ⟨27668006362270492197706609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147562700598775958387768581 27668006362270492197706609)
                ·
                  refine ⟨20751004771702869148279957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27668006362270492197706609 20751004771702869148279957)
                  ·
                    refine ⟨972703348673571991325623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20751004771702869148279957 972703348673571991325623)
                    ·
                      rfl

theorem cell23_5682999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_5682999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5682999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5682999 prefixEnd_5682999 := by exact prefixLift 5682999
  have htrace : WordTrace (prefixWord ++ tailWord_5682999) baseStart_5682999 baseEnd_5682999 := by
    simpa [prefixWord, tailWord_5682999, baseEnd_5682999] using wordTrace_append hprefix tailTrace_5682999
  have hstable : (prefixWord ++ tailWord_5682999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5682999).length < 2 ^ (prefixWord ++ tailWord_5682999).sum := by decide
  have hdescent : baseEnd_5682999 < baseStart_5682999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5682999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683001 : List Nat := [1, 2, 1, 7, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5683001 : Nat := 118140960795 + 5683001 * 2 ^ 59
def prefixEnd_5683001 : Nat := 4983230072969 + 3 ^ 40 * 5683001 * 2
def baseEnd_5683001 : Nat := 2918111072982024966151861

theorem tailTrace_5683001 : CollatzResearch.WordTrace tailWord_5683001 prefixEnd_5683001 2918111072982024966151861 := by
  unfold tailWord_5683001
  simp only [CollatzResearch.WordTrace]
  refine ⟨207276074884465431144144857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138184049922976954096096571 207276074884465431144144857)
  ·
    refine ⟨155457056163349073358108643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207276074884465431144144857 155457056163349073358108643)
    ·
      refine ⟨233185584245023610037162965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155457056163349073358108643 233185584245023610037162965)
      ·
        refine ⟨5465287130742740860246007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 233185584245023610037162965 5465287130742740860246007)
        ·
          refine ⟨8197930696114111290369011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465287130742740860246007 8197930696114111290369011)
          ·
            refine ⟨12296896044171166935553517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8197930696114111290369011 12296896044171166935553517)
            ·
              refine ⟨4611336016564187600832569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12296896044171166935553517 4611336016564187600832569)
              ·
                refine ⟨3458502012423140700624427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4611336016564187600832569 3458502012423140700624427)
                ·
                  refine ⟨5187753018634711050936641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458502012423140700624427 5187753018634711050936641)
                  ·
                    refine ⟨3890814763976033288202481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187753018634711050936641 3890814763976033288202481)
                    ·
                      refine ⟨2918111072982024966151861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890814763976033288202481 2918111072982024966151861)
                      ·
                        rfl

theorem cell23_5683001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5683001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683001 prefixEnd_5683001 := by exact prefixLift 5683001
  have htrace : WordTrace (prefixWord ++ tailWord_5683001) baseStart_5683001 baseEnd_5683001 := by
    simpa [prefixWord, tailWord_5683001, baseEnd_5683001] using wordTrace_append hprefix tailTrace_5683001
  have hstable : (prefixWord ++ tailWord_5683001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683001).length < 2 ^ (prefixWord ++ tailWord_5683001).sum := by decide
  have hdescent : baseEnd_5683001 < baseStart_5683001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683026 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5]
def baseStart_5683026 : Nat := 118140960795 + 5683026 * 2 ^ 59
def prefixEnd_5683026 : Nat := 4983230072969 + 3 ^ 40 * 5683026 * 2
def baseEnd_5683026 : Nat := 2918123909998387368339245

theorem tailTrace_5683026 : CollatzResearch.WordTrace tailWord_5683026 prefixEnd_5683026 2918123909998387368339245 := by
  unfold tailWord_5683026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51819246677343715103451233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138184657806249906942536621 51819246677343715103451233)
  ·
    refine ⟨38864435008007786327588425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51819246677343715103451233 38864435008007786327588425)
    ·
      refine ⟨29148326256005839745691319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38864435008007786327588425 29148326256005839745691319)
      ·
        refine ⟨43722489384008759618536979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29148326256005839745691319 43722489384008759618536979)
        ·
          refine ⟨65583734076013139427805469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43722489384008759618536979 65583734076013139427805469)
          ·
            refine ⟨24593900278504927285427051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65583734076013139427805469 24593900278504927285427051)
            ·
              refine ⟨36890850417757390928140577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24593900278504927285427051 36890850417757390928140577)
              ·
                refine ⟨27668137813318043196105433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36890850417757390928140577 27668137813318043196105433)
                ·
                  refine ⟨20751103359988532397079075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27668137813318043196105433 20751103359988532397079075)
                  ·
                    refine ⟨31126655039982798595618613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20751103359988532397079075 31126655039982798595618613)
                    ·
                      refine ⟨2918123909998387368339245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31126655039982798595618613 2918123909998387368339245)
                      ·
                        rfl

theorem cell23_5683026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_5683026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683026 prefixEnd_5683026 := by exact prefixLift 5683026
  have htrace : WordTrace (prefixWord ++ tailWord_5683026) baseStart_5683026 baseEnd_5683026 := by
    simpa [prefixWord, tailWord_5683026, baseEnd_5683026] using wordTrace_append hprefix tailTrace_5683026
  have hstable : (prefixWord ++ tailWord_5683026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683026).length < 2 ^ (prefixWord ++ tailWord_5683026).sum := by decide
  have hdescent : baseEnd_5683026 < baseStart_5683026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683056 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3]
def baseStart_5683056 : Nat := 118140960795 + 5683056 * 2 ^ 59
def prefixEnd_5683056 : Nat := 4983230072969 + 3 ^ 40 * 5683056 * 2
def baseEnd_5683056 : Nat := 2918139314418022250964107

theorem tailTrace_5683056 : CollatzResearch.WordTrace tailWord_5683056 prefixEnd_5683056 2918139314418022250964107 := by
  unfold tailWord_5683056
  simp only [CollatzResearch.WordTrace]
  refine ⟨103639040449633087768698511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138185387266177450358264681 103639040449633087768698511)
  ·
    refine ⟨155458560674449631653047767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103639040449633087768698511 155458560674449631653047767)
    ·
      refine ⟨233187841011674447479571651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155458560674449631653047767 233187841011674447479571651)
      ·
        refine ⟨349781761517511671219357477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233187841011674447479571651 349781761517511671219357477)
        ·
          refine ⟨65584080284533438353629527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349781761517511671219357477 65584080284533438353629527)
          ·
            refine ⟨98376120426800157530444291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65584080284533438353629527 98376120426800157530444291)
            ·
              refine ⟨147564180640200236295666437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98376120426800157530444291 147564180640200236295666437)
              ·
                refine ⟨27668283870037544305437457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147564180640200236295666437 27668283870037544305437457)
                ·
                  refine ⟨20751212902528158229078093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27668283870037544305437457 20751212902528158229078093)
                  ·
                    refine ⟨7781704838448059335904285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20751212902528158229078093 7781704838448059335904285)
                    ·
                      refine ⟨2918139314418022250964107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781704838448059335904285 2918139314418022250964107)
                      ·
                        rfl

theorem cell23_5683056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_5683056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683056 prefixEnd_5683056 := by exact prefixLift 5683056
  have htrace : WordTrace (prefixWord ++ tailWord_5683056) baseStart_5683056 baseEnd_5683056 := by
    simpa [prefixWord, tailWord_5683056, baseEnd_5683056] using wordTrace_append hprefix tailTrace_5683056
  have hstable : (prefixWord ++ tailWord_5683056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683056).length < 2 ^ (prefixWord ++ tailWord_5683056).sum := by decide
  have hdescent : baseEnd_5683056 < baseStart_5683056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683059 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 7]
def baseStart_5683059 : Nat := 118140960795 + 5683059 * 2 ^ 59
def prefixEnd_5683059 : Nat := 4983230072969 + 3 ^ 40 * 5683059 * 2
def baseEnd_5683059 : Nat := 972713618286661913075531

theorem tailTrace_5683059 : CollatzResearch.WordTrace tailWord_5683059 prefixEnd_5683059 972713618286661913075531 := by
  unfold tailWord_5683059
  simp only [CollatzResearch.WordTrace]
  refine ⟨207278190318255307049756231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138185460212170204699837487 207278190318255307049756231)
  ·
    refine ⟨310917285477382960574634347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207278190318255307049756231 310917285477382960574634347)
    ·
      refine ⟨466375928216074440861951521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310917285477382960574634347 466375928216074440861951521)
      ·
        refine ⟨349781946162055830646463641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466375928216074440861951521 349781946162055830646463641)
        ·
          refine ⟨262336459621541872984847731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349781946162055830646463641 262336459621541872984847731)
          ·
            refine ⟨393504689432312809477271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262336459621541872984847731 393504689432312809477271597)
            ·
              refine ⟨147564258537117303553976849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393504689432312809477271597 147564258537117303553976849)
              ·
                refine ⟨110673193902837977665482637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147564258537117303553976849 110673193902837977665482637)
                ·
                  refine ⟨41502447713564241624555989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110673193902837977665482637 41502447713564241624555989)
                  ·
                    refine ⟨972713618286661913075531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41502447713564241624555989 972713618286661913075531)
                    ·
                      rfl

theorem cell23_5683059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_5683059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683059 prefixEnd_5683059 := by exact prefixLift 5683059
  have htrace : WordTrace (prefixWord ++ tailWord_5683059) baseStart_5683059 baseEnd_5683059 := by
    simpa [prefixWord, tailWord_5683059, baseEnd_5683059] using wordTrace_append hprefix tailTrace_5683059
  have hstable : (prefixWord ++ tailWord_5683059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683059).length < 2 ^ (prefixWord ++ tailWord_5683059).sum := by decide
  have hdescent : baseEnd_5683059 < baseStart_5683059 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683070 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_5683070 : Nat := 118140960795 + 5683070 * 2 ^ 59
def prefixEnd_5683070 : Nat := 4983230072969 + 3 ^ 40 * 5683070 * 2
def baseEnd_5683070 : Nat := 2918146503147185196189043

theorem tailTrace_5683070 : CollatzResearch.WordTrace tailWord_5683070 prefixEnd_5683070 2918146503147185196189043 := by
  unfold tailWord_5683070
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909823940151931991050833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138185727680810303952271109 25909823940151931991050833)
  ·
    refine ⟨19432367955113948993288125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25909823940151931991050833 19432367955113948993288125)
    ·
      refine ⟨7287137983167730872483047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19432367955113948993288125 7287137983167730872483047)
      ·
        refine ⟨10930706974751596308724571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7287137983167730872483047 10930706974751596308724571)
        ·
          refine ⟨16396060462127394463086857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10930706974751596308724571 16396060462127394463086857)
          ·
            refine ⟨12297045346595545847315143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16396060462127394463086857 12297045346595545847315143)
            ·
              refine ⟨18445568019893318770972715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12297045346595545847315143 18445568019893318770972715)
              ·
                refine ⟨27668352029839978156459073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18445568019893318770972715 27668352029839978156459073)
                ·
                  refine ⟨20751264022379983617344305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27668352029839978156459073 20751264022379983617344305)
                  ·
                    refine ⟨15563448016784987713008229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20751264022379983617344305 15563448016784987713008229)
                    ·
                      refine ⟨2918146503147185196189043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15563448016784987713008229 2918146503147185196189043)
                      ·
                        rfl

theorem cell23_5683070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_5683070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683070 prefixEnd_5683070 := by exact prefixLift 5683070
  have htrace : WordTrace (prefixWord ++ tailWord_5683070) baseStart_5683070 baseEnd_5683070 := by
    simpa [prefixWord, tailWord_5683070, baseEnd_5683070] using wordTrace_append hprefix tailTrace_5683070
  have hstable : (prefixWord ++ tailWord_5683070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683070).length < 2 ^ (prefixWord ++ tailWord_5683070).sum := by decide
  have hdescent : baseEnd_5683070 < baseStart_5683070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683076 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 4, 5]
def baseStart_5683076 : Nat := 118140960795 + 5683076 * 2 ^ 59
def prefixEnd_5683076 : Nat := 4983230072969 + 3 ^ 40 * 5683076 * 2
def baseEnd_5683076 : Nat := 972716528010370724238005

theorem tailTrace_5683076 : CollatzResearch.WordTrace tailWord_5683076 prefixEnd_5683076 972716528010370724238005 := by
  unfold tailWord_5683076
  simp only [CollatzResearch.WordTrace]
  refine ⟨103639405179596859476562541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138185873572795812635416721 103639405179596859476562541)
  ·
    refine ⟨38864776942348822303710953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103639405179596859476562541 38864776942348822303710953)
    ·
      refine ⟨29148582706761616727783215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38864776942348822303710953 29148582706761616727783215)
      ·
        refine ⟨43722874060142425091674823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29148582706761616727783215 43722874060142425091674823)
        ·
          refine ⟨65584311090213637637512235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43722874060142425091674823 65584311090213637637512235)
          ·
            refine ⟨98376466635320456456268353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65584311090213637637512235 98376466635320456456268353)
            ·
              refine ⟨73782349976490342342201265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98376466635320456456268353 73782349976490342342201265)
              ·
                refine ⟨55336762482367756756650949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73782349976490342342201265 55336762482367756756650949)
                ·
                  refine ⟨10375642965443954391872053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55336762482367756756650949 10375642965443954391872053)
                  ·
                    refine ⟨972716528010370724238005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10375642965443954391872053 972716528010370724238005)
                    ·
                      rfl

theorem cell23_5683076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_5683076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683076 prefixEnd_5683076 := by exact prefixLift 5683076
  have htrace : WordTrace (prefixWord ++ tailWord_5683076) baseStart_5683076 baseEnd_5683076 := by
    simpa [prefixWord, tailWord_5683076, baseEnd_5683076] using wordTrace_append hprefix tailTrace_5683076
  have hstable : (prefixWord ++ tailWord_5683076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683076).length < 2 ^ (prefixWord ++ tailWord_5683076).sum := by decide
  have hdescent : baseEnd_5683076 < baseStart_5683076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683116 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_5683116 : Nat := 118140960795 + 5683116 * 2 ^ 59
def prefixEnd_5683116 : Nat := 4983230072969 + 3 ^ 40 * 5683116 * 2
def baseEnd_5683116 : Nat := 2918170123257292016213831

theorem tailTrace_5683116 : CollatzResearch.WordTrace tailWord_5683116 prefixEnd_5683116 2918170123257292016213831 := by
  unfold tailWord_5683116
  simp only [CollatzResearch.WordTrace]
  refine ⟨103640134639524402892290601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138186846186032537189720801 103640134639524402892290601)
  ·
    refine ⟨77730100979643302169217951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103640134639524402892290601 77730100979643302169217951)
    ·
      refine ⟨116595151469464953253826927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77730100979643302169217951 116595151469464953253826927)
      ·
        refine ⟨174892727204197429880740391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116595151469464953253826927 174892727204197429880740391)
        ·
          refine ⟨262339090806296144821110587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174892727204197429880740391 262339090806296144821110587)
          ·
            refine ⟨393508636209444217231665881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262339090806296144821110587 393508636209444217231665881)
            ·
              refine ⟨295131477157083162923749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393508636209444217231665881 295131477157083162923749411)
              ·
                refine ⟨442697215735624744385624117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295131477157083162923749411 442697215735624744385624117)
                ·
                  refine ⟨41502863975214819786152261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442697215735624744385624117 41502863975214819786152261)
                  ·
                    refine ⟨7781786995352778709903549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41502863975214819786152261 7781786995352778709903549)
                    ·
                      refine ⟨2918170123257292016213831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781786995352778709903549 2918170123257292016213831)
                      ·
                        rfl

theorem cell23_5683116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_5683116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683116 prefixEnd_5683116 := by exact prefixLift 5683116
  have htrace : WordTrace (prefixWord ++ tailWord_5683116) baseStart_5683116 baseEnd_5683116 := by
    simpa [prefixWord, tailWord_5683116, baseEnd_5683116] using wordTrace_append hprefix tailTrace_5683116
  have hstable : (prefixWord ++ tailWord_5683116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683116).length < 2 ^ (prefixWord ++ tailWord_5683116).sum := by decide
  have hdescent : baseEnd_5683116 < baseStart_5683116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683123 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 3, 4]
def baseStart_5683123 : Nat := 118140960795 + 5683123 * 2 ^ 59
def prefixEnd_5683123 : Nat := 4983230072969 + 3 ^ 40 * 5683123 * 2
def baseEnd_5683123 : Nat := 972724572540624496275433

theorem tailTrace_5683123 : CollatzResearch.WordTrace tailWord_5683123 prefixEnd_5683123 972724572540624496275433 := by
  unfold tailWord_5683123
  simp only [CollatzResearch.WordTrace]
  refine ⟨207280524590023445980086023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138187016393348963986724015 207280524590023445980086023)
  ·
    refine ⟨310920786885035168970129035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207280524590023445980086023 310920786885035168970129035)
    ·
      refine ⟨466381180327552753455193553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310920786885035168970129035 466381180327552753455193553)
      ·
        refine ⟨349785885245664565091395165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466381180327552753455193553 349785885245664565091395165)
        ·
          refine ⟨131169706967124211909273187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349785885245664565091395165 131169706967124211909273187)
          ·
            refine ⟨196754560450686317863909781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131169706967124211909273187 196754560450686317863909781)
            ·
              refine ⟨9222870021125921149870771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196754560450686317863909781 9222870021125921149870771)
              ·
                refine ⟨13834305031688881724806157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9222870021125921149870771 13834305031688881724806157)
                ·
                  refine ⟨5187864386883330646802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13834305031688881724806157 5187864386883330646802309)
                  ·
                    refine ⟨972724572540624496275433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187864386883330646802309 972724572540624496275433)
                    ·
                      rfl

theorem cell23_5683123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 4].length) (baseStart_5683123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683123 prefixEnd_5683123 := by exact prefixLift 5683123
  have htrace : WordTrace (prefixWord ++ tailWord_5683123) baseStart_5683123 baseEnd_5683123 := by
    simpa [prefixWord, tailWord_5683123, baseEnd_5683123] using wordTrace_append hprefix tailTrace_5683123
  have hstable : (prefixWord ++ tailWord_5683123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683123).length < 2 ^ (prefixWord ++ tailWord_5683123).sum := by decide
  have hdescent : baseEnd_5683123 < baseStart_5683123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683133 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_5683133 : Nat := 118140960795 + 5683133 * 2 ^ 59
def prefixEnd_5683133 : Nat := 4983230072969 + 3 ^ 40 * 5683133 * 2
def baseEnd_5683133 : Nat := 2918178852428418449701253

theorem tailTrace_5683133 : CollatzResearch.WordTrace tailWord_5683133 prefixEnd_5683133 2918178852428418449701253 := by
  unfold tailWord_5683133
  simp only [CollatzResearch.WordTrace]
  refine ⟨207280889319987217687950053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138187259546658145125300035 207280889319987217687950053)
  ·
    refine ⟨38865166747497603316490635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207280889319987217687950053 38865166747497603316490635)
    ·
      refine ⟨58297750121246404974735953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38865166747497603316490635 58297750121246404974735953)
      ·
        refine ⟨43723312590934803731051965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58297750121246404974735953 43723312590934803731051965)
        ·
          refine ⟨16396242221600551399144487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43723312590934803731051965 16396242221600551399144487)
          ·
            refine ⟨24594363332400827098716731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16396242221600551399144487 24594363332400827098716731)
            ·
              refine ⟨36891544998601240648075097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24594363332400827098716731 36891544998601240648075097)
              ·
                refine ⟨27668658748950930486056323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36891544998601240648075097 27668658748950930486056323)
                ·
                  refine ⟨41502988123426395729084485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27668658748950930486056323 41502988123426395729084485)
                  ·
                    refine ⟨7781810273142449199203341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41502988123426395729084485 7781810273142449199203341)
                    ·
                      refine ⟨2918178852428418449701253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7781810273142449199203341 2918178852428418449701253)
                      ·
                        rfl

theorem cell23_5683133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_5683133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683133 prefixEnd_5683133 := by exact prefixLift 5683133
  have htrace : WordTrace (prefixWord ++ tailWord_5683133) baseStart_5683133 baseEnd_5683133 := by
    simpa [prefixWord, tailWord_5683133, baseEnd_5683133] using wordTrace_append hprefix tailTrace_5683133
  have hstable : (prefixWord ++ tailWord_5683133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683133).length < 2 ^ (prefixWord ++ tailWord_5683133).sum := by decide
  have hdescent : baseEnd_5683133 < baseStart_5683133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683157 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_5683157 : Nat := 118140960795 + 5683157 * 2 ^ 59
def prefixEnd_5683157 : Nat := 4983230072969 + 3 ^ 40 * 5683157 * 2
def baseEnd_5683157 : Nat := 972730391988042118600381

theorem tailTrace_5683157 : CollatzResearch.WordTrace tailWord_5683157 prefixEnd_5683157 972730391988042118600381 := by
  unfold tailWord_5683157
  simp only [CollatzResearch.WordTrace]
  refine ⟨207281764671900269786823725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138187843114600179857882483 207281764671900269786823725)
  ·
    refine ⟨77730661751962601170058897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207281764671900269786823725 77730661751962601170058897)
    ·
      refine ⟨58297996313971950877544173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77730661751962601170058897 58297996313971950877544173)
      ·
        refine ⟨21861748617739481579079065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58297996313971950877544173 21861748617739481579079065)
        ·
          refine ⟨16396311463304611184309299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21861748617739481579079065 16396311463304611184309299)
          ·
            refine ⟨24594467194956916776463949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16396311463304611184309299 24594467194956916776463949)
            ·
              refine ⟨9222925198108843791173981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24594467194956916776463949 9222925198108843791173981)
              ·
                refine ⟨3458596949290816421690243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9222925198108843791173981 3458596949290816421690243)
                ·
                  refine ⟨5187895423936224632535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458596949290816421690243 5187895423936224632535365)
                  ·
                    refine ⟨972730391988042118600381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5187895423936224632535365 972730391988042118600381)
                    ·
                      rfl

theorem cell23_5683157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_5683157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683157 prefixEnd_5683157 := by exact prefixLift 5683157
  have htrace : WordTrace (prefixWord ++ tailWord_5683157) baseStart_5683157 baseEnd_5683157 := by
    simpa [prefixWord, tailWord_5683157, baseEnd_5683157] using wordTrace_append hprefix tailTrace_5683157
  have hstable : (prefixWord ++ tailWord_5683157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683157).length < 2 ^ (prefixWord ++ tailWord_5683157).sum := by decide
  have hdescent : baseEnd_5683157 < baseStart_5683157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683164 : List Nat := [2, 2, 6, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_5683164 : Nat := 118140960795 + 5683164 * 2 ^ 59
def prefixEnd_5683164 : Nat := 4983230072969 + 3 ^ 40 * 5683164 * 2
def baseEnd_5683164 : Nat := 2918194770328707828413611

theorem tailTrace_5683164 : CollatzResearch.WordTrace tailWord_5683164 prefixEnd_5683164 2918194770328707828413611 := by
  unfold tailWord_5683164
  simp only [CollatzResearch.WordTrace]
  refine ⟨103641009991437454991164273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138188013321916606654885697 103641009991437454991164273)
  ·
    refine ⟨77730757493578091243373205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103641009991437454991164273 77730757493578091243373205)
    ·
      refine ⟨3643629257511473027033119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77730757493578091243373205 3643629257511473027033119)
      ·
        refine ⟨5465443886267209540549679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3643629257511473027033119 5465443886267209540549679)
        ·
          refine ⟨8198165829400814310824519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5465443886267209540549679 8198165829400814310824519)
          ·
            refine ⟨12297248744101221466236779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8198165829400814310824519 12297248744101221466236779)
            ·
              refine ⟨18445873116151832199355169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12297248744101221466236779 18445873116151832199355169)
              ·
                refine ⟨13834404837113874149516377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18445873116151832199355169 13834404837113874149516377)
                ·
                  refine ⟨10375803627835405612137283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13834404837113874149516377 10375803627835405612137283)
                  ·
                    refine ⟨15563705441753108418205925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10375803627835405612137283 15563705441753108418205925)
                    ·
                      refine ⟨2918194770328707828413611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15563705441753108418205925 2918194770328707828413611)
                      ·
                        rfl

theorem cell23_5683164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_5683164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683164 prefixEnd_5683164 := by exact prefixLift 5683164
  have htrace : WordTrace (prefixWord ++ tailWord_5683164) baseStart_5683164 baseEnd_5683164 := by
    simpa [prefixWord, tailWord_5683164, baseEnd_5683164] using wordTrace_append hprefix tailTrace_5683164
  have hstable : (prefixWord ++ tailWord_5683164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683164).length < 2 ^ (prefixWord ++ tailWord_5683164).sum := by decide
  have hdescent : baseEnd_5683164 < baseStart_5683164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683176 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_5683176 : Nat := 118140960795 + 5683176 * 2 ^ 59
def prefixEnd_5683176 : Nat := 4983230072969 + 3 ^ 40 * 5683176 * 2
def baseEnd_5683176 : Nat := 2918200932096561781463555

theorem tailTrace_5683176 : CollatzResearch.WordTrace tailWord_5683176 prefixEnd_5683176 2918200932096561781463555 := by
  unfold tailWord_5683176
  simp only [CollatzResearch.WordTrace]
  refine ⟨103641228829415718015882691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138188305105887624021176921 103641228829415718015882691)
  ·
    refine ⟨155461843244123577023824037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103641228829415718015882691 155461843244123577023824037)
    ·
      refine ⟨29149095608273170691967007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155461843244123577023824037 29149095608273170691967007)
      ·
        refine ⟨43723643412409756037950511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149095608273170691967007 43723643412409756037950511)
        ·
          refine ⟨65585465118614634056925767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43723643412409756037950511 65585465118614634056925767)
          ·
            refine ⟨98378197677921951085388651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65585465118614634056925767 98378197677921951085388651)
            ·
              refine ⟨147567296516882926628082977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98378197677921951085388651 147567296516882926628082977)
              ·
                refine ⟨110675472387662194971062233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147567296516882926628082977 110675472387662194971062233)
                ·
                  refine ⟨83006604290746646228296675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110675472387662194971062233 83006604290746646228296675)
                  ·
                    refine ⟨124509906436119969342445013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83006604290746646228296675 124509906436119969342445013)
                    ·
                      refine ⟨2918200932096561781463555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124509906436119969342445013 2918200932096561781463555)
                      ·
                        rfl

theorem cell23_5683176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_5683176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683176 prefixEnd_5683176 := by exact prefixLift 5683176
  have htrace : WordTrace (prefixWord ++ tailWord_5683176) baseStart_5683176 baseEnd_5683176 := by
    simpa [prefixWord, tailWord_5683176, baseEnd_5683176] using wordTrace_append hprefix tailTrace_5683176
  have hstable : (prefixWord ++ tailWord_5683176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683176).length < 2 ^ (prefixWord ++ tailWord_5683176).sum := by decide
  have hdescent : baseEnd_5683176 < baseStart_5683176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683203 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 6, 2]
def baseStart_5683203 : Nat := 118140960795 + 5683203 * 2 ^ 59
def prefixEnd_5683203 : Nat := 4983230072969 + 3 ^ 40 * 5683203 * 2
def baseEnd_5683203 : Nat := 2918214796074233175825931

theorem tailTrace_5683203 : CollatzResearch.WordTrace tailWord_5683203 prefixEnd_5683203 2918214796074233175825931 := by
  unfold tailWord_5683203
  simp only [CollatzResearch.WordTrace]
  refine ⟨207283442429733619642998263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138188961619822413095332175 207283442429733619642998263)
  ·
    refine ⟨310925163644600429464497395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207283442429733619642998263 310925163644600429464497395)
    ·
      refine ⟨466387745466900644196746093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310925163644600429464497395 466387745466900644196746093)
      ·
        refine ⟨174895404550087741573779785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466387745466900644196746093 174895404550087741573779785)
        ·
          refine ⟨131171553412565806180334839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174895404550087741573779785 131171553412565806180334839)
          ·
            refine ⟨196757330118848709270502259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131171553412565806180334839 196757330118848709270502259)
            ·
              refine ⟨295135995178273063905753389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196757330118848709270502259 295135995178273063905753389)
              ·
                refine ⟨110675998191852398964657521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295135995178273063905753389 110675998191852398964657521)
                ·
                  refine ⟨83006998643889299223493141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110675998191852398964657521 83006998643889299223493141)
                  ·
                    refine ⟨3890953061432310901101241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83006998643889299223493141 3890953061432310901101241)
                    ·
                      refine ⟨2918214796074233175825931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890953061432310901101241 2918214796074233175825931)
                      ·
                        rfl

theorem cell23_5683203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_5683203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683203 prefixEnd_5683203 := by exact prefixLift 5683203
  have htrace : WordTrace (prefixWord ++ tailWord_5683203) baseStart_5683203 baseEnd_5683203 := by
    simpa [prefixWord, tailWord_5683203, baseEnd_5683203] using wordTrace_append hprefix tailTrace_5683203
  have hstable : (prefixWord ++ tailWord_5683203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683203).length < 2 ^ (prefixWord ++ tailWord_5683203).sum := by decide
  have hdescent : baseEnd_5683203 < baseStart_5683203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683207 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_5683207 : Nat := 118140960795 + 5683207 * 2 ^ 59
def prefixEnd_5683207 : Nat := 4983230072969 + 3 ^ 40 * 5683207 * 2
def baseEnd_5683207 : Nat := 2918216849996851160175913

theorem tailTrace_5683207 : CollatzResearch.WordTrace tailWord_5683207 prefixEnd_5683207 2918216849996851160175913 := by
  unfold tailWord_5683207
  simp only [CollatzResearch.WordTrace]
  refine ⟨207283588321719128326143875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138189058881146085550762583 207283588321719128326143875)
  ·
    refine ⟨310925382482578692489215813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207283588321719128326143875 310925382482578692489215813)
    ·
      refine ⟨58298509215483504841727965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310925382482578692489215813 58298509215483504841727965)
      ·
        refine ⟨21861940955806314315647987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58298509215483504841727965 21861940955806314315647987)
        ·
          refine ⟨32792911433709471473471981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21861940955806314315647987 32792911433709471473471981)
          ·
            refine ⟨12297341787641051802551993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32792911433709471473471981 12297341787641051802551993)
            ·
              refine ⟨9223006340730788851913995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12297341787641051802551993 9223006340730788851913995)
              ·
                refine ⟨13834509511096183277870993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9223006340730788851913995 13834509511096183277870993)
                ·
                  refine ⟨10375882133322137458403245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13834509511096183277870993 10375882133322137458403245)
                  ·
                    refine ⟨3890955799995801546901217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10375882133322137458403245 3890955799995801546901217)
                    ·
                      refine ⟨2918216849996851160175913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890955799995801546901217 2918216849996851160175913)
                      ·
                        rfl

theorem cell23_5683207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_5683207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683207 prefixEnd_5683207 := by exact prefixLift 5683207
  have htrace : WordTrace (prefixWord ++ tailWord_5683207) baseStart_5683207 baseEnd_5683207 := by
    simpa [prefixWord, tailWord_5683207, baseEnd_5683207] using wordTrace_append hprefix tailTrace_5683207
  have hstable : (prefixWord ++ tailWord_5683207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683207).length < 2 ^ (prefixWord ++ tailWord_5683207).sum := by decide
  have hdescent : baseEnd_5683207 < baseStart_5683207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683226 : List Nat := [3, 1, 1, 3, 1, 14]
def baseStart_5683226 : Nat := 118140960795 + 5683226 * 2 ^ 59
def prefixEnd_5683226 : Nat := 4983230072969 + 3 ^ 40 * 5683226 * 2
def baseEnd_5683226 : Nat := 12009162988186364550775

theorem tailTrace_5683226 : CollatzResearch.WordTrace tailWord_5683226 prefixEnd_5683226 12009162988186364550775 := by
  unfold tailWord_5683226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51821070327162573642771383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138189520872433529714057021 51821070327162573642771383)
  ·
    refine ⟨77731605490743860464157075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51821070327162573642771383 77731605490743860464157075)
    ·
      refine ⟨116597408236115790696235613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77731605490743860464157075 116597408236115790696235613)
      ·
        refine ⟨43724028088543421511088355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116597408236115790696235613 43724028088543421511088355)
        ·
          refine ⟨65586042132815132266632533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43724028088543421511088355 65586042132815132266632533)
          ·
            refine ⟨12009162988186364550775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 65586042132815132266632533 12009162988186364550775)
            ·
              rfl

theorem cell23_5683226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 14].length) (baseStart_5683226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683226 prefixEnd_5683226 := by exact prefixLift 5683226
  have htrace : WordTrace (prefixWord ++ tailWord_5683226) baseStart_5683226 baseEnd_5683226 := by
    simpa [prefixWord, tailWord_5683226, baseEnd_5683226] using wordTrace_append hprefix tailTrace_5683226
  have hstable : (prefixWord ++ tailWord_5683226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683226).length < 2 ^ (prefixWord ++ tailWord_5683226).sum := by decide
  have hdescent : baseEnd_5683226 < baseStart_5683226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683250 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4]
def baseStart_5683250 : Nat := 118140960795 + 5683250 * 2 ^ 59
def prefixEnd_5683250 : Nat := 4983230072969 + 3 ^ 40 * 5683250 * 2
def baseEnd_5683250 : Nat := 2918238929664994491938215

theorem tailTrace_5683250 : CollatzResearch.WordTrace tailWord_5683250 prefixEnd_5683250 2918238929664994491938215 := by
  unfold tailWord_5683250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51821289165140836667489801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138190104440375564446639469 51821289165140836667489801)
  ·
    refine ⟨38865966873855627500617351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51821289165140836667489801 38865966873855627500617351)
    ·
      refine ⟨58298950310783441250926027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38865966873855627500617351 58298950310783441250926027)
      ·
        refine ⟨87448425466175161876389041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58298950310783441250926027 87448425466175161876389041)
        ·
          refine ⟨65586319099631371407291781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87448425466175161876389041 65586319099631371407291781)
          ·
            refine ⟨12297434831180882138867209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65586319099631371407291781 12297434831180882138867209)
            ·
              refine ⟨9223076123385661604150407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12297434831180882138867209 9223076123385661604150407)
              ·
                refine ⟨13834614185078492406225611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9223076123385661604150407 13834614185078492406225611)
                ·
                  refine ⟨20751921277617738609338417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13834614185078492406225611 20751921277617738609338417)
                  ·
                    refine ⟨15563940958213303957003813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20751921277617738609338417 15563940958213303957003813)
                    ·
                      refine ⟨2918238929664994491938215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15563940958213303957003813 2918238929664994491938215)
                      ·
                        rfl

theorem cell23_5683250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_5683250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683250 prefixEnd_5683250 := by exact prefixLift 5683250
  have htrace : WordTrace (prefixWord ++ tailWord_5683250) baseStart_5683250 baseEnd_5683250 := by
    simpa [prefixWord, tailWord_5683250, baseEnd_5683250] using wordTrace_append hprefix tailTrace_5683250
  have hstable : (prefixWord ++ tailWord_5683250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683250).length < 2 ^ (prefixWord ++ tailWord_5683250).sum := by decide
  have hdescent : baseEnd_5683250 < baseStart_5683250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683254 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_5683254 : Nat := 118140960795 + 5683254 * 2 ^ 59
def prefixEnd_5683254 : Nat := 4983230072969 + 3 ^ 40 * 5683254 * 2
def baseEnd_5683254 : Nat := 2918240983587612476288197

theorem tailTrace_5683254 : CollatzResearch.WordTrace tailWord_5683254 prefixEnd_5683254 2918240983587612476288197 := by
  unfold tailWord_5683254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12955331409534303459569051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138190201701699236902069877 12955331409534303459569051)
  ·
    refine ⟨19432997114301455189353577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12955331409534303459569051 19432997114301455189353577)
    ·
      refine ⟨14574747835726091392015183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19432997114301455189353577 14574747835726091392015183)
      ·
        refine ⟨21862121753589137088022775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14574747835726091392015183 21862121753589137088022775)
        ·
          refine ⟨32793182630383705632034163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21862121753589137088022775 32793182630383705632034163)
          ·
            refine ⟨49189773945575558448051245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32793182630383705632034163 49189773945575558448051245)
            ·
              refine ⟨18446165229590834418019217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49189773945575558448051245 18446165229590834418019217)
              ·
                refine ⟨13834623922193125813514413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18446165229590834418019217 13834623922193125813514413)
                ·
                  refine ⟨5187983970822422180067905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13834623922193125813514413 5187983970822422180067905)
                  ·
                    refine ⟨3890987978116816635050929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5187983970822422180067905 3890987978116816635050929)
                    ·
                      refine ⟨2918240983587612476288197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3890987978116816635050929 2918240983587612476288197)
                      ·
                        rfl

theorem cell23_5683254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_5683254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683254 prefixEnd_5683254 := by exact prefixLift 5683254
  have htrace : WordTrace (prefixWord ++ tailWord_5683254) baseStart_5683254 baseEnd_5683254 := by
    simpa [prefixWord, tailWord_5683254, baseEnd_5683254] using wordTrace_append hprefix tailTrace_5683254
  have hstable : (prefixWord ++ tailWord_5683254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683254).length < 2 ^ (prefixWord ++ tailWord_5683254).sum := by decide
  have hdescent : baseEnd_5683254 < baseStart_5683254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683287 : List Nat := [1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_5683287 : Nat := 118140960795 + 5683287 * 2 ^ 59
def prefixEnd_5683287 : Nat := 4983230072969 + 3 ^ 40 * 5683287 * 2
def baseEnd_5683287 : Nat := 2918257928449210847175545

theorem tailTrace_5683287 : CollatzResearch.WordTrace tailWord_5683287 prefixEnd_5683287 2918257928449210847175545 := by
  unfold tailWord_5683287
  simp only [CollatzResearch.WordTrace]
  refine ⟨207286506161429301989056115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138191004107619534659370743 207286506161429301989056115)
  ·
    refine ⟨310929759242143952983584173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207286506161429301989056115 310929759242143952983584173)
    ·
      refine ⟨116598659715803982368844065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310929759242143952983584173 116598659715803982368844065)
      ·
        refine ⟨87448994786852986776633049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116598659715803982368844065 87448994786852986776633049)
        ·
          refine ⟨65586746090139740082474787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87448994786852986776633049 65586746090139740082474787)
          ·
            refine ⟨98380119135209610123712181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65586746090139740082474787 98380119135209610123712181)
            ·
              refine ⟨9223136168925900949098017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98380119135209610123712181 9223136168925900949098017)
              ·
                refine ⟨6917352126694425711823513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9223136168925900949098017 6917352126694425711823513)
                ·
                  refine ⟨5188014095020819283867635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6917352126694425711823513 5188014095020819283867635)
                  ·
                    refine ⟨7782021142531228925801453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5188014095020819283867635 7782021142531228925801453)
                    ·
                      refine ⟨2918257928449210847175545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7782021142531228925801453 2918257928449210847175545)
                      ·
                        rfl

theorem cell23_5683287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_5683287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683287 prefixEnd_5683287 := by exact prefixLift 5683287
  have htrace : WordTrace (prefixWord ++ tailWord_5683287) baseStart_5683287 baseEnd_5683287 := by
    simpa [prefixWord, tailWord_5683287, baseEnd_5683287] using wordTrace_append hprefix tailTrace_5683287
  have hstable : (prefixWord ++ tailWord_5683287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683287).length < 2 ^ (prefixWord ++ tailWord_5683287).sum := by decide
  have hdescent : baseEnd_5683287 < baseStart_5683287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683303 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5683303 : Nat := 118140960795 + 5683303 * 2 ^ 59
def prefixEnd_5683303 : Nat := 4983230072969 + 3 ^ 40 * 5683303 * 2
def baseEnd_5683303 : Nat := 972755381379894261525157

theorem tailTrace_5683303 : CollatzResearch.WordTrace tailWord_5683303 prefixEnd_5683303 972755381379894261525157 := by
  unfold tailWord_5683303
  simp only [CollatzResearch.WordTrace]
  refine ⟨207287089729371336721638563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138191393152914224481092375 207287089729371336721638563)
  ·
    refine ⟨310930634594057005082457845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207287089729371336721638563 310930634594057005082457845)
    ·
      refine ⟨29149746993192844226480423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310930634594057005082457845 29149746993192844226480423)
      ·
        refine ⟨43724620489789266339720635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29149746993192844226480423 43724620489789266339720635)
        ·
          refine ⟨65586930734683899509580953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43724620489789266339720635 65586930734683899509580953)
          ·
            refine ⟨49190198051012924632185715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65586930734683899509580953 49190198051012924632185715)
            ·
              refine ⟨73785297076519386948278573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49190198051012924632185715 73785297076519386948278573)
              ·
                refine ⟨27669486403694770105604465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73785297076519386948278573 27669486403694770105604465)
                ·
                  refine ⟨20752114802771077579203349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27669486403694770105604465 20752114802771077579203349)
                  ·
                    refine ⟨972755381379894261525157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20752114802771077579203349 972755381379894261525157)
                    ·
                      rfl

theorem cell23_5683303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5683303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683303 prefixEnd_5683303 := by exact prefixLift 5683303
  have htrace : WordTrace (prefixWord ++ tailWord_5683303) baseStart_5683303 baseEnd_5683303 := by
    simpa [prefixWord, tailWord_5683303, baseEnd_5683303] using wordTrace_append hprefix tailTrace_5683303
  have hstable : (prefixWord ++ tailWord_5683303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683303).length < 2 ^ (prefixWord ++ tailWord_5683303).sum := by decide
  have hdescent : baseEnd_5683303 < baseStart_5683303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683313 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 5]
def baseStart_5683313 : Nat := 118140960795 + 5683313 * 2 ^ 59
def prefixEnd_5683313 : Nat := 4983230072969 + 3 ^ 40 * 5683313 * 2
def baseEnd_5683313 : Nat := 2918271278946227745450425

theorem tailTrace_5683313 : CollatzResearch.WordTrace tailWord_5683313 prefixEnd_5683313 2918271278946227745450425 := by
  unfold tailWord_5683313
  simp only [CollatzResearch.WordTrace]
  refine ⟨207287454459335108429502593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138191636306223405619668395 207287454459335108429502593)
  ·
    refine ⟨155465590844501331322126945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207287454459335108429502593 155465590844501331322126945)
    ·
      refine ⟨116599193133375998491595209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155465590844501331322126945 116599193133375998491595209)
      ·
        refine ⟨87449394850031998868696407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116599193133375998491595209 87449394850031998868696407)
        ·
          refine ⟨131174092275047998303044611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87449394850031998868696407 131174092275047998303044611)
          ·
            refine ⟨196761138412571997454566917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131174092275047998303044611 196761138412571997454566917)
            ·
              refine ⟨36892713452357249522731297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196761138412571997454566917 36892713452357249522731297)
              ·
                refine ⟨27669535089267937142048473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36892713452357249522731297 27669535089267937142048473)
                ·
                  refine ⟨20752151316950952856536355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27669535089267937142048473 20752151316950952856536355)
                  ·
                    refine ⟨31128226975426429284804533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20752151316950952856536355 31128226975426429284804533)
                    ·
                      refine ⟨2918271278946227745450425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31128226975426429284804533 2918271278946227745450425)
                      ·
                        rfl

theorem cell23_5683313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_5683313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683313 prefixEnd_5683313 := by exact prefixLift 5683313
  have htrace : WordTrace (prefixWord ++ tailWord_5683313) baseStart_5683313 baseEnd_5683313 := by
    simpa [prefixWord, tailWord_5683313, baseEnd_5683313] using wordTrace_append hprefix tailTrace_5683313
  have hstable : (prefixWord ++ tailWord_5683313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683313).length < 2 ^ (prefixWord ++ tailWord_5683313).sum := by decide
  have hdescent : baseEnd_5683313 < baseStart_5683313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683314 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 1, 3, 2]
def baseStart_5683314 : Nat := 118140960795 + 5683314 * 2 ^ 59
def prefixEnd_5683314 : Nat := 4983230072969 + 3 ^ 40 * 5683314 * 2
def baseEnd_5683314 : Nat := 2918271792426882241537921

theorem tailTrace_5683314 : CollatzResearch.WordTrace tailWord_5683314 prefixEnd_5683314 2918271792426882241537921 := by
  unfold tailWord_5683314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51821872733082871400072249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138191660621554323733525997 51821872733082871400072249)
  ·
    refine ⟨38866404549812153550054187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51821872733082871400072249 38866404549812153550054187)
    ·
      refine ⟨58299606824718230325081281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38866404549812153550054187 58299606824718230325081281)
      ·
        refine ⟨43724705118538672743810961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58299606824718230325081281 43724705118538672743810961)
        ·
          refine ⟨32793528838904004557858221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43724705118538672743810961 32793528838904004557858221)
          ·
            refine ⟨12297573314589001709196833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32793528838904004557858221 12297573314589001709196833)
            ·
              refine ⟨9223179985941751281897625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12297573314589001709196833 9223179985941751281897625)
              ·
                refine ⟨6917384989456313461423219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9223179985941751281897625 6917384989456313461423219)
                ·
                  refine ⟨10376077484184470192134829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917384989456313461423219 10376077484184470192134829)
                  ·
                    refine ⟨3891029056569176322050561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10376077484184470192134829 3891029056569176322050561)
                    ·
                      refine ⟨2918271792426882241537921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891029056569176322050561 2918271792426882241537921)
                      ·
                        rfl

theorem cell23_5683314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_5683314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683314 prefixEnd_5683314 := by exact prefixLift 5683314
  have htrace : WordTrace (prefixWord ++ tailWord_5683314) baseStart_5683314 baseEnd_5683314 := by
    simpa [prefixWord, tailWord_5683314, baseEnd_5683314] using wordTrace_append hprefix tailTrace_5683314
  have hstable : (prefixWord ++ tailWord_5683314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683314).length < 2 ^ (prefixWord ++ tailWord_5683314).sum := by decide
  have hdescent : baseEnd_5683314 < baseStart_5683314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683361 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 2, 2, 2]
def baseStart_5683361 : Nat := 118140960795 + 5683361 * 2 ^ 59
def prefixEnd_5683361 : Nat := 4983230072969 + 3 ^ 40 * 5683361 * 2
def baseEnd_5683361 : Nat := 2918295926017643557650205

theorem tailTrace_5683361 : CollatzResearch.WordTrace tailWord_5683361 prefixEnd_5683361 2918295926017643557650205 := by
  unfold tailWord_5683361
  simp only [CollatzResearch.WordTrace]
  refine ⟨207289205163161212627249937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138192803442107475084833291 207289205163161212627249937)
  ·
    refine ⟨155466903872370909470437453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207289205163161212627249937 155466903872370909470437453)
    ·
      refine ⟨58300088952139091051414045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155466903872370909470437453 58300088952139091051414045)
      ·
        refine ⟨21862533357052159144280267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58300088952139091051414045 21862533357052159144280267)
        ·
          refine ⟨32793800035578238716420401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21862533357052159144280267 32793800035578238716420401)
          ·
            refine ⟨24595350026683679037315301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32793800035578238716420401 24595350026683679037315301)
            ·
              refine ⟨4611628130003189819496619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24595350026683679037315301 4611628130003189819496619)
              ·
                refine ⟨6917442195004784729244929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611628130003189819496619 6917442195004784729244929)
                ·
                  refine ⟨5188081646253588546933697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6917442195004784729244929 5188081646253588546933697)
                  ·
                    refine ⟨3891061234690191410200273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5188081646253588546933697 3891061234690191410200273)
                    ·
                      refine ⟨2918295926017643557650205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891061234690191410200273 2918295926017643557650205)
                      ·
                        rfl

theorem cell23_5683361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_5683361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683361 prefixEnd_5683361 := by exact prefixLift 5683361
  have htrace : WordTrace (prefixWord ++ tailWord_5683361) baseStart_5683361 baseEnd_5683361 := by
    simpa [prefixWord, tailWord_5683361, baseEnd_5683361] using wordTrace_append hprefix tailTrace_5683361
  have hstable : (prefixWord ++ tailWord_5683361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683361).length < 2 ^ (prefixWord ++ tailWord_5683361).sum := by decide
  have hdescent : baseEnd_5683361 < baseStart_5683361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683403 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_5683403 : Nat := 118140960795 + 5683403 * 2 ^ 59
def prefixEnd_5683403 : Nat := 4983230072969 + 3 ^ 40 * 5683403 * 2
def baseEnd_5683403 : Nat := 2918317492205132393325011

theorem tailTrace_5683403 : CollatzResearch.WordTrace tailWord_5683403 prefixEnd_5683403 2918317492205132393325011 := by
  unfold tailWord_5683403
  simp only [CollatzResearch.WordTrace]
  refine ⟨207290737029009053800278863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138193824686006035866852575 207290737029009053800278863)
  ·
    refine ⟨310936105543513580700418295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207290737029009053800278863 310936105543513580700418295)
    ·
      refine ⟨466404158315270371050627443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310936105543513580700418295 466404158315270371050627443)
      ·
        refine ⟨699606237472905556575941165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466404158315270371050627443 699606237472905556575941165)
        ·
          refine ⟨262352339052339583715977937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 699606237472905556575941165 262352339052339583715977937)
          ·
            refine ⟨196764254289254687786983453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262352339052339583715977937 196764254289254687786983453)
            ·
              refine ⟨73786595358470507920118795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196764254289254687786983453 73786595358470507920118795)
              ·
                refine ⟨110679893037705761880178193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73786595358470507920118795 110679893037705761880178193)
                ·
                  refine ⟨83009919778279321410133645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110679893037705761880178193 83009919778279321410133645)
                  ·
                    refine ⟨31128719916854745528800117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83009919778279321410133645 31128719916854745528800117)
                    ·
                      refine ⟨2918317492205132393325011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31128719916854745528800117 2918317492205132393325011)
                      ·
                        rfl

theorem cell23_5683403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_5683403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683403 prefixEnd_5683403 := by exact prefixLift 5683403
  have htrace : WordTrace (prefixWord ++ tailWord_5683403) baseStart_5683403 baseEnd_5683403 := by
    simpa [prefixWord, tailWord_5683403, baseEnd_5683403] using wordTrace_append hprefix tailTrace_5683403
  have hstable : (prefixWord ++ tailWord_5683403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683403).length < 2 ^ (prefixWord ++ tailWord_5683403).sum := by decide
  have hdescent : baseEnd_5683403 < baseStart_5683403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683423 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 10]
def baseStart_5683423 : Nat := 118140960795 + 5683423 * 2 ^ 59
def prefixEnd_5683423 : Nat := 4983230072969 + 3 ^ 40 * 5683423 * 2
def baseEnd_5683423 : Nat := 324258640202024701674991

theorem tailTrace_5683423 : CollatzResearch.WordTrace tailWord_5683423 prefixEnd_5683423 324258640202024701674991 := by
  unfold tailWord_5683423
  simp only [CollatzResearch.WordTrace]
  refine ⟨207291466488936597216006923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138194310992624398144004615 207291466488936597216006923)
  ·
    refine ⟨310937199733404895824010385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207291466488936597216006923 310937199733404895824010385)
    ·
      refine ⟨233202899800053671868007789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310937199733404895824010385 233202899800053671868007789)
      ·
        refine ⟨87451087425020126950502921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233202899800053671868007789 87451087425020126950502921)
        ·
          refine ⟨65588315568765095212877191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87451087425020126950502921 65588315568765095212877191)
          ·
            refine ⟨98382473353147642819315787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65588315568765095212877191 98382473353147642819315787)
            ·
              refine ⟨147573710029721464228973681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98382473353147642819315787 147573710029721464228973681)
              ·
                refine ⟨110680282522291098171730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147573710029721464228973681 110680282522291098171730261)
                ·
                  refine ⟨324258640202024701674991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110680282522291098171730261 324258640202024701674991)
                  ·
                    rfl

theorem cell23_5683423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 10].length) (baseStart_5683423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683423 prefixEnd_5683423 := by exact prefixLift 5683423
  have htrace : WordTrace (prefixWord ++ tailWord_5683423) baseStart_5683423 baseEnd_5683423 := by
    simpa [prefixWord, tailWord_5683423, baseEnd_5683423] using wordTrace_append hprefix tailTrace_5683423
  have hstable : (prefixWord ++ tailWord_5683423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683423).length < 2 ^ (prefixWord ++ tailWord_5683423).sum := by decide
  have hdescent : baseEnd_5683423 < baseStart_5683423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683477 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_5683477 : Nat := 118140960795 + 5683477 * 2 ^ 59
def prefixEnd_5683477 : Nat := 4983230072969 + 3 ^ 40 * 5683477 * 2
def baseEnd_5683477 : Nat := 2918355489773565103799671

theorem tailTrace_5683477 : CollatzResearch.WordTrace tailWord_5683477 prefixEnd_5683477 2918355489773565103799671 := by
  unfold tailWord_5683477
  simp only [CollatzResearch.WordTrace]
  refine ⟨207293436030740964438472685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138195624020493976292315123 207293436030740964438472685)
  ·
    refine ⟨77735038511527861664427257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207293436030740964438472685 77735038511527861664427257)
    ·
      refine ⟨58301278883645896248320443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77735038511527861664427257 58301278883645896248320443)
      ·
        refine ⟨87451918325468844372480665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58301278883645896248320443 87451918325468844372480665)
        ·
          refine ⟨65588938744101633279360499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87451918325468844372480665 65588938744101633279360499)
          ·
            refine ⟨98383408116152449919040749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65588938744101633279360499 98383408116152449919040749)
            ·
              refine ⟨36893778043557168719640281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98383408116152449919040749 36893778043557168719640281)
              ·
                refine ⟨27670333532667876539730211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36893778043557168719640281 27670333532667876539730211)
                ·
                  refine ⟨41505500299001814809595317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27670333532667876539730211 41505500299001814809595317)
                  ·
                    refine ⟨3891140653031420138399561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41505500299001814809595317 3891140653031420138399561)
                    ·
                      refine ⟨2918355489773565103799671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891140653031420138399561 2918355489773565103799671)
                      ·
                        rfl

theorem cell23_5683477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_5683477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683477 prefixEnd_5683477 := by exact prefixLift 5683477
  have htrace : WordTrace (prefixWord ++ tailWord_5683477) baseStart_5683477 baseEnd_5683477 := by
    simpa [prefixWord, tailWord_5683477, baseEnd_5683477] using wordTrace_append hprefix tailTrace_5683477
  have hstable : (prefixWord ++ tailWord_5683477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683477).length < 2 ^ (prefixWord ++ tailWord_5683477).sum := by decide
  have hdescent : baseEnd_5683477 < baseStart_5683477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683487 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 1, 5]
def baseStart_5683487 : Nat := 118140960795 + 5683487 * 2 ^ 59
def prefixEnd_5683487 : Nat := 4983230072969 + 3 ^ 40 * 5683487 * 2
def baseEnd_5683487 : Nat := 972786874860036688224875

theorem tailTrace_5683487 : CollatzResearch.WordTrace tailWord_5683487 prefixEnd_5683487 972786874860036688224875 := by
  unfold tailWord_5683487
  simp only [CollatzResearch.WordTrace]
  refine ⟨207293800760704736146336715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138195867173803157430891143 207293800760704736146336715)
  ·
    refine ⟨310940701141057104219505073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207293800760704736146336715 310940701141057104219505073)
    ·
      refine ⟨233205525855792828164628805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310940701141057104219505073 233205525855792828164628805)
      ·
        refine ⟨43726036097961155280867901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233205525855792828164628805 43726036097961155280867901)
        ·
          refine ⟨16397263536735433230325463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43726036097961155280867901 16397263536735433230325463)
          ·
            refine ⟨24595895305103149845488195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16397263536735433230325463 24595895305103149845488195)
            ·
              refine ⟨36893842957654724768232293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24595895305103149845488195 36893842957654724768232293)
              ·
                refine ⟨6917595554560260894043555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36893842957654724768232293 6917595554560260894043555)
                ·
                  refine ⟨10376393331840391341065333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917595554560260894043555 10376393331840391341065333)
                  ·
                    refine ⟨972786874860036688224875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10376393331840391341065333 972786874860036688224875)
                    ·
                      rfl

theorem cell23_5683487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_5683487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683487 prefixEnd_5683487 := by exact prefixLift 5683487
  have htrace : WordTrace (prefixWord ++ tailWord_5683487) baseStart_5683487 baseEnd_5683487 := by
    simpa [prefixWord, tailWord_5683487, baseEnd_5683487] using wordTrace_append hprefix tailTrace_5683487
  have hstable : (prefixWord ++ tailWord_5683487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683487).length < 2 ^ (prefixWord ++ tailWord_5683487).sum := by decide
  have hdescent : baseEnd_5683487 < baseStart_5683487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683500 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_5683500 : Nat := 118140960795 + 5683500 * 2 ^ 59
def prefixEnd_5683500 : Nat := 4983230072969 + 3 ^ 40 * 5683500 * 2
def baseEnd_5683500 : Nat := 972789099942872837937355

theorem tailTrace_5683500 : CollatzResearch.WordTrace tailWord_5683500 prefixEnd_5683500 972789099942872837937355 := by
  unfold tailWord_5683500
  simp only [CollatzResearch.WordTrace]
  refine ⟨103647137454828819683279977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138196183273105092911039969 103647137454828819683279977)
  ·
    refine ⟨77735353091121614762459983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103647137454828819683279977 77735353091121614762459983)
    ·
      refine ⟨116603029636682422143689975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77735353091121614762459983 116603029636682422143689975)
      ·
        refine ⟨174904544455023633215534963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116603029636682422143689975 174904544455023633215534963)
        ·
          refine ⟨262356816682535449823302445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174904544455023633215534963 262356816682535449823302445)
          ·
            refine ⟨98383806255950793683738417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262356816682535449823302445 98383806255950793683738417)
            ·
              refine ⟨73787854691963095262803813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98383806255950793683738417 73787854691963095262803813)
              ·
                refine ⟨13835222754743080361775715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73787854691963095262803813 13835222754743080361775715)
                ·
                  refine ⟨20752834132114620542663573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13835222754743080361775715 20752834132114620542663573)
                  ·
                    refine ⟨972789099942872837937355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20752834132114620542663573 972789099942872837937355)
                    ·
                      rfl

theorem cell23_5683500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_5683500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683500 prefixEnd_5683500 := by exact prefixLift 5683500
  have htrace : WordTrace (prefixWord ++ tailWord_5683500) baseStart_5683500 baseEnd_5683500 := by
    simpa [prefixWord, tailWord_5683500, baseEnd_5683500] using wordTrace_append hprefix tailTrace_5683500
  have hstable : (prefixWord ++ tailWord_5683500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683500).length < 2 ^ (prefixWord ++ tailWord_5683500).sum := by decide
  have hdescent : baseEnd_5683500 < baseStart_5683500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683507 : List Nat := [1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 4]
def baseStart_5683507 : Nat := 118140960795 + 5683507 * 2 ^ 59
def prefixEnd_5683507 : Nat := 4983230072969 + 3 ^ 40 * 5683507 * 2
def baseEnd_5683507 : Nat := 2918370894193199986424533

theorem tailTrace_5683507 : CollatzResearch.WordTrace tailWord_5683507 prefixEnd_5683507 2918370894193199986424533 := by
  unfold tailWord_5683507
  simp only [CollatzResearch.WordTrace]
  refine ⟨207294530220632279562064775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138196353480421519708043183 207294530220632279562064775)
  ·
    refine ⟨310941795330948419343097163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207294530220632279562064775 310941795330948419343097163)
    ·
      refine ⟨466412692996422629014645745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310941795330948419343097163 466412692996422629014645745)
      ·
        refine ⟨349809519747316971760984309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466412692996422629014645745 349809519747316971760984309)
        ·
          refine ⟨32794642476310966102592279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 349809519747316971760984309 32794642476310966102592279)
          ·
            refine ⟨49191963714466449153888419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32794642476310966102592279 49191963714466449153888419)
            ·
              refine ⟨73787945571699673730832629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49191963714466449153888419 73787945571699673730832629)
              ·
                refine ⟨6917619897346844412265559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73787945571699673730832629 6917619897346844412265559)
                ·
                  refine ⟨10376429846020266618398339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917619897346844412265559 10376429846020266618398339)
                  ·
                    refine ⟨15564644769030399927597509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10376429846020266618398339 15564644769030399927597509)
                    ·
                      refine ⟨2918370894193199986424533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15564644769030399927597509 2918370894193199986424533)
                      ·
                        rfl

theorem cell23_5683507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 5, 1, 1, 4].length) (baseStart_5683507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683507 prefixEnd_5683507 := by exact prefixLift 5683507
  have htrace : WordTrace (prefixWord ++ tailWord_5683507) baseStart_5683507 baseEnd_5683507 := by
    simpa [prefixWord, tailWord_5683507, baseEnd_5683507] using wordTrace_append hprefix tailTrace_5683507
  have hstable : (prefixWord ++ tailWord_5683507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683507).length < 2 ^ (prefixWord ++ tailWord_5683507).sum := by decide
  have hdescent : baseEnd_5683507 < baseStart_5683507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683520 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4]
def baseStart_5683520 : Nat := 118140960795 + 5683520 * 2 ^ 59
def prefixEnd_5683520 : Nat := 4983230072969 + 3 ^ 40 * 5683520 * 2
def baseEnd_5683520 : Nat := 2918377569441708435561973

theorem tailTrace_5683520 : CollatzResearch.WordTrace tailWord_5683520 prefixEnd_5683520 2918377569441708435561973 := by
  unfold tailWord_5683520
  simp only [CollatzResearch.WordTrace]
  refine ⟨103647502184792591391144007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138196669579723455188192009 103647502184792591391144007)
  ·
    refine ⟨155471253277188887086716011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103647502184792591391144007 155471253277188887086716011)
    ·
      refine ⟨233206879915783330630074017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155471253277188887086716011 233206879915783330630074017)
      ·
        refine ⟨174905159936837497972555513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233206879915783330630074017 174905159936837497972555513)
        ·
          refine ⟨131178869952628123479416635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174905159936837497972555513 131178869952628123479416635)
          ·
            refine ⟨196768304928942185219124953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131178869952628123479416635 196768304928942185219124953)
            ·
              refine ⟨147576228696706638914343715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196768304928942185219124953 147576228696706638914343715)
              ·
                refine ⟨221364343045059958371515573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147576228696706638914343715 221364343045059958371515573)
                ·
                  refine ⟨20752907160474371097329585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221364343045059958371515573 20752907160474371097329585)
                  ·
                    refine ⟨15564680370355778322997189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20752907160474371097329585 15564680370355778322997189)
                    ·
                      refine ⟨2918377569441708435561973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15564680370355778322997189 2918377569441708435561973)
                      ·
                        rfl

theorem cell23_5683520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_5683520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683520 prefixEnd_5683520 := by exact prefixLift 5683520
  have htrace : WordTrace (prefixWord ++ tailWord_5683520) baseStart_5683520 baseEnd_5683520 := by
    simpa [prefixWord, tailWord_5683520, baseEnd_5683520] using wordTrace_append hprefix tailTrace_5683520
  have hstable : (prefixWord ++ tailWord_5683520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683520).length < 2 ^ (prefixWord ++ tailWord_5683520).sum := by decide
  have hdescent : baseEnd_5683520 < baseStart_5683520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683527 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_5683527 : Nat := 118140960795 + 5683527 * 2 ^ 59
def prefixEnd_5683527 : Nat := 4983230072969 + 3 ^ 40 * 5683527 * 2
def baseEnd_5683527 : Nat := 2918381163806289908174441

theorem tailTrace_5683527 : CollatzResearch.WordTrace tailWord_5683527 prefixEnd_5683527 2918381163806289908174441 := by
  unfold tailWord_5683527
  simp only [CollatzResearch.WordTrace]
  refine ⟨207295259680559822977792835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138196839787039881985195223 207295259680559822977792835)
  ·
    refine ⟨310942889520839734466689253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207295259680559822977792835 310942889520839734466689253)
    ·
      refine ⟨58301791785157450212504235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310942889520839734466689253 58301791785157450212504235)
      ·
        refine ⟨87452687677736175318756353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58301791785157450212504235 87452687677736175318756353)
        ·
          refine ⟨65589515758302131489067265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87452687677736175318756353 65589515758302131489067265)
          ·
            refine ⟨49192136818726598616800449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65589515758302131489067265 49192136818726598616800449)
            ·
              refine ⟨36894102614044948962600337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49192136818726598616800449 36894102614044948962600337)
              ·
                refine ⟨27670576960533711721950253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36894102614044948962600337 27670576960533711721950253)
                ·
                  refine ⟨10376466360200141895731345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27670576960533711721950253 10376466360200141895731345)
                  ·
                    refine ⟨7782349770150106421798509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10376466360200141895731345 7782349770150106421798509)
                    ·
                      refine ⟨2918381163806289908174441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7782349770150106421798509 2918381163806289908174441)
                      ·
                        rfl

theorem cell23_5683527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_5683527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683527 prefixEnd_5683527 := by exact prefixLift 5683527
  have htrace : WordTrace (prefixWord ++ tailWord_5683527) baseStart_5683527 baseEnd_5683527 := by
    simpa [prefixWord, tailWord_5683527, baseEnd_5683527] using wordTrace_append hprefix tailTrace_5683527
  have hstable : (prefixWord ++ tailWord_5683527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683527).length < 2 ^ (prefixWord ++ tailWord_5683527).sum := by decide
  have hdescent : baseEnd_5683527 < baseStart_5683527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683541 : List Nat := [1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_5683541 : Nat := 118140960795 + 5683541 * 2 ^ 59
def prefixEnd_5683541 : Nat := 4983230072969 + 3 ^ 40 * 5683541 * 2
def baseEnd_5683541 : Nat := 2918388352535452853399377

theorem tailTrace_5683541 : CollatzResearch.WordTrace tailWord_5683541 prefixEnd_5683541 2918388352535452853399377 := by
  unfold tailWord_5683541
  simp only [CollatzResearch.WordTrace]
  refine ⟨207295770302509103368802477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138197180201672735579201651 207295770302509103368802477)
  ·
    refine ⟨77735913863440913763300929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207295770302509103368802477 77735913863440913763300929)
    ·
      refine ⟨58301935397580685322475697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77735913863440913763300929 58301935397580685322475697)
      ·
        refine ⟨43726451548185513991856773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58301935397580685322475697 43726451548185513991856773)
        ·
          refine ⟨8198709665284783873473145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43726451548185513991856773 8198709665284783873473145)
          ·
            refine ⟨6149032248963587905104859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8198709665284783873473145 6149032248963587905104859)
            ·
              refine ⟨9223548373445381857657289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149032248963587905104859 9223548373445381857657289)
              ·
                refine ⟨6917661280084036393242967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9223548373445381857657289 6917661280084036393242967)
                ·
                  refine ⟨10376491920126054589864451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917661280084036393242967 10376491920126054589864451)
                  ·
                    refine ⟨15564737880189081884796677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10376491920126054589864451 15564737880189081884796677)
                    ·
                      refine ⟨2918388352535452853399377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15564737880189081884796677 2918388352535452853399377)
                      ·
                        rfl

theorem cell23_5683541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_5683541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683541 prefixEnd_5683541 := by exact prefixLift 5683541
  have htrace : WordTrace (prefixWord ++ tailWord_5683541) baseStart_5683541 baseEnd_5683541 := by
    simpa [prefixWord, tailWord_5683541, baseEnd_5683541] using wordTrace_append hprefix tailTrace_5683541
  have hstable : (prefixWord ++ tailWord_5683541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683541).length < 2 ^ (prefixWord ++ tailWord_5683541).sum := by decide
  have hdescent : baseEnd_5683541 < baseStart_5683541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683554 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_5683554 : Nat := 118140960795 + 5683554 * 2 ^ 59
def prefixEnd_5683554 : Nat := 4983230072969 + 3 ^ 40 * 5683554 * 2
def baseEnd_5683554 : Nat := 2918395027783961302536817

theorem tailTrace_5683554 : CollatzResearch.WordTrace tailWord_5683554 prefixEnd_5683554 2918395027783961302536817 := by
  unfold tailWord_5683554
  simp only [CollatzResearch.WordTrace]
  refine ⟨51824061112865501647256429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138197496300974671059350477 51824061112865501647256429)
  ·
    refine ⟨19434022917324563117721161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51824061112865501647256429 19434022917324563117721161)
    ·
      refine ⟨14575517187993422338290871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19434022917324563117721161 14575517187993422338290871)
      ·
        refine ⟨21863275781990133507436307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14575517187993422338290871 21863275781990133507436307)
        ·
          refine ⟨32794913672985200261154461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21863275781990133507436307 32794913672985200261154461)
          ·
            refine ⟨12298092627369450097932923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32794913672985200261154461 12298092627369450097932923)
            ·
              refine ⟨18447138941054175146899385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298092627369450097932923 18447138941054175146899385)
              ·
                refine ⟨13835354205790631360174539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18447138941054175146899385 13835354205790631360174539)
                ·
                  refine ⟨20753031308685947040261809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13835354205790631360174539 20753031308685947040261809)
                  ·
                    refine ⟨15564773481514460280196357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20753031308685947040261809 15564773481514460280196357)
                    ·
                      refine ⟨2918395027783961302536817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15564773481514460280196357 2918395027783961302536817)
                      ·
                        rfl

theorem cell23_5683554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_5683554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683554 prefixEnd_5683554 := by exact prefixLift 5683554
  have htrace : WordTrace (prefixWord ++ tailWord_5683554) baseStart_5683554 baseEnd_5683554 := by
    simpa [prefixWord, tailWord_5683554, baseEnd_5683554] using wordTrace_append hprefix tailTrace_5683554
  have hstable : (prefixWord ++ tailWord_5683554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683554).length < 2 ^ (prefixWord ++ tailWord_5683554).sum := by decide
  have hdescent : baseEnd_5683554 < baseStart_5683554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683557 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_5683557 : Nat := 118140960795 + 5683557 * 2 ^ 59
def prefixEnd_5683557 : Nat := 4983230072969 + 3 ^ 40 * 5683557 * 2
def baseEnd_5683557 : Nat := 2918396568225924790799303

theorem tailTrace_5683557 : CollatzResearch.WordTrace tailWord_5683557 prefixEnd_5683557 2918396568225924790799303 := by
  unfold tailWord_5683557
  simp only [CollatzResearch.WordTrace]
  refine ⟨207296353870451138101384925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138197569246967425400923283 207296353870451138101384925)
  ·
    refine ⟨77736132701419176788019347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207296353870451138101384925 77736132701419176788019347)
    ·
      refine ⟨116604199052128765182029021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77736132701419176788019347 116604199052128765182029021)
      ·
        refine ⟨43726574644548286943260883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116604199052128765182029021 43726574644548286943260883)
        ·
          refine ⟨65589861966822430414891325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43726574644548286943260883 65589861966822430414891325)
          ·
            refine ⟨24596198237558411405584247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65589861966822430414891325 24596198237558411405584247)
            ·
              refine ⟨36894297356337617108376371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24596198237558411405584247 36894297356337617108376371)
              ·
                refine ⟨55341446034506425662564557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36894297356337617108376371 55341446034506425662564557)
                ·
                  refine ⟨20753042262939909623461709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55341446034506425662564557 20753042262939909623461709)
                  ·
                    refine ⟨7782390848602466108798141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20753042262939909623461709 7782390848602466108798141)
                    ·
                      refine ⟨2918396568225924790799303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7782390848602466108798141 2918396568225924790799303)
                      ·
                        rfl

theorem cell23_5683557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_5683557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683557 prefixEnd_5683557 := by exact prefixLift 5683557
  have htrace : WordTrace (prefixWord ++ tailWord_5683557) baseStart_5683557 baseEnd_5683557 := by
    simpa [prefixWord, tailWord_5683557, baseEnd_5683557] using wordTrace_append hprefix tailTrace_5683557
  have hstable : (prefixWord ++ tailWord_5683557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683557).length < 2 ^ (prefixWord ++ tailWord_5683557).sum := by decide
  have hdescent : baseEnd_5683557 < baseStart_5683557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683600 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5]
def baseStart_5683600 : Nat := 118140960795 + 5683600 * 2 ^ 59
def prefixEnd_5683600 : Nat := 4983230072969 + 3 ^ 40 * 5683600 * 2
def baseEnd_5683600 : Nat := 2918418647894068122561605

theorem tailTrace_5683600 : CollatzResearch.WordTrace tailWord_5683600 prefixEnd_5683600 2918418647894068122561605 := by
  unfold tailWord_5683600
  simp only [CollatzResearch.WordTrace]
  refine ⟨103648961104647678222600127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138198614806196904296800169 103648961104647678222600127)
  ·
    refine ⟨155473441656971517333900191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103648961104647678222600127 155473441656971517333900191)
    ·
      refine ⟨233210162485457276000850287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155473441656971517333900191 233210162485457276000850287)
      ·
        refine ⟨349815243728185914001275431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233210162485457276000850287 349815243728185914001275431)
        ·
          refine ⟨524722865592278871001913147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349815243728185914001275431 524722865592278871001913147)
          ·
            refine ⟨787084298388418306502869721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524722865592278871001913147 787084298388418306502869721)
            ·
              refine ⟨590313223791313729877152291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787084298388418306502869721 590313223791313729877152291)
              ·
                refine ⟨885469835686970594815728437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590313223791313729877152291 885469835686970594815728437)
                ·
                  refine ⟨83012797095653493263974541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 885469835686970594815728437 83012797095653493263974541)
                  ·
                    refine ⟨31129798910870059973990453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83012797095653493263974541 31129798910870059973990453)
                    ·
                      refine ⟨2918418647894068122561605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31129798910870059973990453 2918418647894068122561605)
                      ·
                        rfl

theorem cell23_5683600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_5683600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683600 prefixEnd_5683600 := by exact prefixLift 5683600
  have htrace : WordTrace (prefixWord ++ tailWord_5683600) baseStart_5683600 baseEnd_5683600 := by
    simpa [prefixWord, tailWord_5683600, baseEnd_5683600] using wordTrace_append hprefix tailTrace_5683600
  have hstable : (prefixWord ++ tailWord_5683600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683600).length < 2 ^ (prefixWord ++ tailWord_5683600).sum := by decide
  have hdescent : baseEnd_5683600 < baseStart_5683600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683624 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5683624 : Nat := 118140960795 + 5683624 * 2 ^ 59
def prefixEnd_5683624 : Nat := 4983230072969 + 3 ^ 40 * 5683624 * 2
def baseEnd_5683624 : Nat := 972810323809925342887165

theorem tailTrace_5683624 : CollatzResearch.WordTrace tailWord_5683624 prefixEnd_5683624 972810323809925342887165 := by
  unfold tailWord_5683624
  simp only [CollatzResearch.WordTrace]
  refine ⟨103649398780604204272036963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138199198374138939029382617 103649398780604204272036963)
  ·
    refine ⟨155474098170906306408055445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103649398780604204272036963 155474098170906306408055445)
    ·
      refine ⟨7287848351761233112877599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155474098170906306408055445 7287848351761233112877599)
      ·
        refine ⟨10931772527641849669316399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7287848351761233112877599 10931772527641849669316399)
        ·
          refine ⟨16397658791462774503974599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10931772527641849669316399 16397658791462774503974599)
          ·
            refine ⟨24596488187194161755961899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16397658791462774503974599 24596488187194161755961899)
            ·
              refine ⟨36894732280791242633942849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24596488187194161755961899 36894732280791242633942849)
              ·
                refine ⟨27671049210593431975457137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36894732280791242633942849 27671049210593431975457137)
                ·
                  refine ⟨20753286907945073981592853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27671049210593431975457137 20753286907945073981592853)
                  ·
                    refine ⟨972810323809925342887165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20753286907945073981592853 972810323809925342887165)
                    ·
                      rfl

theorem cell23_5683624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5683624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683624 prefixEnd_5683624 := by exact prefixLift 5683624
  have htrace : WordTrace (prefixWord ++ tailWord_5683624) baseStart_5683624 baseEnd_5683624 := by
    simpa [prefixWord, tailWord_5683624, baseEnd_5683624] using wordTrace_append hprefix tailTrace_5683624
  have hstable : (prefixWord ++ tailWord_5683624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683624).length < 2 ^ (prefixWord ++ tailWord_5683624).sum := by decide
  have hdescent : baseEnd_5683624 < baseStart_5683624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683644 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5683644 : Nat := 118140960795 + 5683644 * 2 ^ 59
def prefixEnd_5683644 : Nat := 4983230072969 + 3 ^ 40 * 5683644 * 2
def baseEnd_5683644 : Nat := 2918441241042865950411403

theorem tailTrace_5683644 : CollatzResearch.WordTrace tailWord_5683644 prefixEnd_5683644 2918441241042865950411403 := by
  unfold tailWord_5683644
  simp only [CollatzResearch.WordTrace]
  refine ⟨103649763510567975979900993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138199684680757301306534657 103649763510567975979900993)
  ·
    refine ⟨77737322632925981984925745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103649763510567975979900993 77737322632925981984925745)
    ·
      refine ⟨58302991974694486488694309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77737322632925981984925745 58302991974694486488694309)
      ·
        refine ⟨10931810995255216216630183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58302991974694486488694309 10931810995255216216630183)
        ·
          refine ⟨16397716492882824324945275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10931810995255216216630183 16397716492882824324945275)
          ·
            refine ⟨24596574739324236487417913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16397716492882824324945275 24596574739324236487417913)
            ·
              refine ⟨18447431054493177365563435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24596574739324236487417913 18447431054493177365563435)
              ·
                refine ⟨27671146581739766048345153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18447431054493177365563435 27671146581739766048345153)
                ·
                  refine ⟨20753359936304824536258865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27671146581739766048345153 20753359936304824536258865)
                  ·
                    refine ⟨15565019952228618402194149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20753359936304824536258865 15565019952228618402194149)
                    ·
                      refine ⟨2918441241042865950411403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15565019952228618402194149 2918441241042865950411403)
                      ·
                        rfl

theorem cell23_5683644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5683644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683644 prefixEnd_5683644 := by exact prefixLift 5683644
  have htrace : WordTrace (prefixWord ++ tailWord_5683644) baseStart_5683644 baseEnd_5683644 := by
    simpa [prefixWord, tailWord_5683644, baseEnd_5683644] using wordTrace_append hprefix tailTrace_5683644
  have hstable : (prefixWord ++ tailWord_5683644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683644).length < 2 ^ (prefixWord ++ tailWord_5683644).sum := by decide
  have hdescent : baseEnd_5683644 < baseStart_5683644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683694 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_5683694 : Nat := 118140960795 + 5683694 * 2 ^ 59
def prefixEnd_5683694 : Nat := 4983230072969 + 3 ^ 40 * 5683694 * 2
def baseEnd_5683694 : Nat := 2918466915075590754786173

theorem tailTrace_5683694 : CollatzResearch.WordTrace tailWord_5683694 prefixEnd_5683694 2918466915075590754786173 := by
  unfold tailWord_5683694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25912668833869351312390267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138200900447303206999414757 25912668833869351312390267)
  ·
    refine ⟨38869003250804026968585401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25912668833869351312390267 38869003250804026968585401)
    ·
      refine ⟨29151752438103020226439051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38869003250804026968585401 29151752438103020226439051)
      ·
        refine ⟨43727628657154530339658577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29151752438103020226439051 43727628657154530339658577)
        ·
          refine ⟨32795721492865897754743933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43727628657154530339658577 32795721492865897754743933)
          ·
            refine ⟨12298395559824711658028975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32795721492865897754743933 12298395559824711658028975)
            ·
              refine ⟨18447593339737067487043463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298395559824711658028975 18447593339737067487043463)
              ·
                refine ⟨27671390009605601230565195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18447593339737067487043463 27671390009605601230565195)
                ·
                  refine ⟨41507085014408401845847793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27671390009605601230565195 41507085014408401845847793)
                  ·
                    refine ⟨31130313760806301384385845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41507085014408401845847793 31130313760806301384385845)
                    ·
                      refine ⟨2918466915075590754786173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31130313760806301384385845 2918466915075590754786173)
                      ·
                        rfl

theorem cell23_5683694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_5683694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683694 prefixEnd_5683694 := by exact prefixLift 5683694
  have htrace : WordTrace (prefixWord ++ tailWord_5683694) baseStart_5683694 baseEnd_5683694 := by
    simpa [prefixWord, tailWord_5683694, baseEnd_5683694] using wordTrace_append hprefix tailTrace_5683694
  have hstable : (prefixWord ++ tailWord_5683694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683694).length < 2 ^ (prefixWord ++ tailWord_5683694).sum := by decide
  have hdescent : baseEnd_5683694 < baseStart_5683694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683704 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2]
def baseStart_5683704 : Nat := 118140960795 + 5683704 * 2 ^ 59
def prefixEnd_5683704 : Nat := 4983230072969 + 3 ^ 40 * 5683704 * 2
def baseEnd_5683704 : Nat := 2918472049882135715661127

theorem tailTrace_5683704 : CollatzResearch.WordTrace tailWord_5683704 prefixEnd_5683704 2918472049882135715661127 := by
  unfold tailWord_5683704
  simp only [CollatzResearch.WordTrace]
  refine ⟨103650857700459291103493083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138201143600612388137990777 103650857700459291103493083)
  ·
    refine ⟨155476286550688936655239625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103650857700459291103493083 155476286550688936655239625)
    ·
      refine ⟨116607214913016702491429719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155476286550688936655239625 116607214913016702491429719)
      ·
        refine ⟨174910822369525053737144579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116607214913016702491429719 174910822369525053737144579)
        ·
          refine ⟨262366233554287580605716869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174910822369525053737144579 262366233554287580605716869)
          ·
            refine ⟨49193668791428921363571913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262366233554287580605716869 49193668791428921363571913)
            ·
              refine ⟨36895251593571691022678935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49193668791428921363571913 36895251593571691022678935)
              ·
                refine ⟨55342877390357536534018403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36895251593571691022678935 55342877390357536534018403)
                ·
                  refine ⟨83014316085536304801027605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55342877390357536534018403 83014316085536304801027605)
                  ·
                    refine ⟨3891296066509514287548169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83014316085536304801027605 3891296066509514287548169)
                    ·
                      refine ⟨2918472049882135715661127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891296066509514287548169 2918472049882135715661127)
                      ·
                        rfl

theorem cell23_5683704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_5683704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683704 prefixEnd_5683704 := by exact prefixLift 5683704
  have htrace : WordTrace (prefixWord ++ tailWord_5683704) baseStart_5683704 baseEnd_5683704 := by
    simpa [prefixWord, tailWord_5683704, baseEnd_5683704] using wordTrace_append hprefix tailTrace_5683704
  have hstable : (prefixWord ++ tailWord_5683704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683704).length < 2 ^ (prefixWord ++ tailWord_5683704).sum := by decide
  have hdescent : baseEnd_5683704 < baseStart_5683704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683717 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_5683717 : Nat := 118140960795 + 5683717 * 2 ^ 59
def prefixEnd_5683717 : Nat := 4983230072969 + 3 ^ 40 * 5683717 * 2
def baseEnd_5683717 : Nat := 2918478725130644164798567

theorem tailTrace_5683717 : CollatzResearch.WordTrace tailWord_5683717 prefixEnd_5683717 2918478725130644164798567 := by
  unfold tailWord_5683717
  simp only [CollatzResearch.WordTrace]
  refine ⟨207302189549871485427209405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138201459699914323618139603 207302189549871485427209405)
  ·
    refine ⟨77738321081201807035203527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207302189549871485427209405 77738321081201807035203527)
    ·
      refine ⟨116607481621802710552805291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77738321081201807035203527 116607481621802710552805291)
      ·
        refine ⟨174911222432704065829207937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116607481621802710552805291 174911222432704065829207937)
        ·
          refine ⟨131183416824528049371905953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174911222432704065829207937 131183416824528049371905953)
          ·
            refine ⟨98387562618396037028929465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131183416824528049371905953 98387562618396037028929465)
            ·
              refine ⟨73790671963797027771697099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98387562618396037028929465 73790671963797027771697099)
              ·
                refine ⟨110686007945695541657545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73790671963797027771697099 110686007945695541657545649)
                ·
                  refine ⟨83014505959271656243159237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110686007945695541657545649 83014505959271656243159237)
                  ·
                    refine ⟨15565219867363435545592357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83014505959271656243159237 15565219867363435545592357)
                    ·
                      refine ⟨2918478725130644164798567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15565219867363435545592357 2918478725130644164798567)
                      ·
                        rfl

theorem cell23_5683717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_5683717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683717 prefixEnd_5683717 := by exact prefixLift 5683717
  have htrace : WordTrace (prefixWord ++ tailWord_5683717) baseStart_5683717 baseEnd_5683717 := by
    simpa [prefixWord, tailWord_5683717, baseEnd_5683717] using wordTrace_append hprefix tailTrace_5683717
  have hstable : (prefixWord ++ tailWord_5683717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683717).length < 2 ^ (prefixWord ++ tailWord_5683717).sum := by decide
  have hdescent : baseEnd_5683717 < baseStart_5683717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683731 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 1, 4]
def baseStart_5683731 : Nat := 118140960795 + 5683731 * 2 ^ 59
def prefixEnd_5683731 : Nat := 4983230072969 + 3 ^ 40 * 5683731 * 2
def baseEnd_5683731 : Nat := 972828637953269036674501

theorem tailTrace_5683731 : CollatzResearch.WordTrace tailWord_5683731 prefixEnd_5683731 972828637953269036674501 := by
  unfold tailWord_5683731
  simp only [CollatzResearch.WordTrace]
  refine ⟨207302700171820765818219047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138201800114547177212146031 207302700171820765818219047)
  ·
    refine ⟨310954050257731148727328571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207302700171820765818219047 310954050257731148727328571)
    ·
      refine ⟨466431075386596723090992857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310954050257731148727328571 466431075386596723090992857)
      ·
        refine ⟨349823306539947542318244643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466431075386596723090992857 349823306539947542318244643)
        ·
          refine ⟨524734959809921313477366965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349823306539947542318244643 524734959809921313477366965)
          ·
            refine ⟨49193902482180123138503153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 524734959809921313477366965 49193902482180123138503153)
            ·
              refine ⟨36895426861635092353877365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49193902482180123138503153 36895426861635092353877365)
              ·
                refine ⟨3458946268278289908176003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36895426861635092353877365 3458946268278289908176003)
                ·
                  refine ⟨5188419402417434862264005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458946268278289908176003 5188419402417434862264005)
                  ·
                    refine ⟨972828637953269036674501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188419402417434862264005 972828637953269036674501)
                    ·
                      rfl

theorem cell23_5683731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 4].length) (baseStart_5683731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683731 prefixEnd_5683731 := by exact prefixLift 5683731
  have htrace : WordTrace (prefixWord ++ tailWord_5683731) baseStart_5683731 baseEnd_5683731 := by
    simpa [prefixWord, tailWord_5683731, baseEnd_5683731] using wordTrace_append hprefix tailTrace_5683731
  have hstable : (prefixWord ++ tailWord_5683731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683731).length < 2 ^ (prefixWord ++ tailWord_5683731).sum := by decide
  have hdescent : baseEnd_5683731 < baseStart_5683731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683741 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_5683741 : Nat := 118140960795 + 5683741 * 2 ^ 59
def prefixEnd_5683741 : Nat := 4983230072969 + 3 ^ 40 * 5683741 * 2
def baseEnd_5683741 : Nat := 2918491048666352070898457

theorem tailTrace_5683741 : CollatzResearch.WordTrace tailWord_5683741 prefixEnd_5683741 2918491048666352070898457 := by
  unfold tailWord_5683741
  simp only [CollatzResearch.WordTrace]
  refine ⟨207303064901784537526083077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138202043267856358350722051 207303064901784537526083077)
  ·
    refine ⟨38869324669084600786140577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207303064901784537526083077 38869324669084600786140577)
    ·
      refine ⟨29151993501813450589605433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38869324669084600786140577 29151993501813450589605433)
      ·
        refine ⟨21863995126360087942204075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29151993501813450589605433 21863995126360087942204075)
        ·
          refine ⟨32795992689540131913306113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21863995126360087942204075 32795992689540131913306113)
          ·
            refine ⟨24596994517155098934979585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32795992689540131913306113 24596994517155098934979585)
            ·
              refine ⟨18447745887866324201234689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24596994517155098934979585 18447745887866324201234689)
              ·
                refine ⟨13835809415899743150926017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18447745887866324201234689 13835809415899743150926017)
                ·
                  refine ⟨10376857061924807363194513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13835809415899743150926017 10376857061924807363194513)
                  ·
                    refine ⟨7782642796443605522395885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10376857061924807363194513 7782642796443605522395885)
                    ·
                      refine ⟨2918491048666352070898457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7782642796443605522395885 2918491048666352070898457)
                      ·
                        rfl

theorem cell23_5683741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_5683741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683741 prefixEnd_5683741 := by exact prefixLift 5683741
  have htrace : WordTrace (prefixWord ++ tailWord_5683741) baseStart_5683741 baseEnd_5683741 := by
    simpa [prefixWord, tailWord_5683741, baseEnd_5683741] using wordTrace_append hprefix tailTrace_5683741
  have hstable : (prefixWord ++ tailWord_5683741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683741).length < 2 ^ (prefixWord ++ tailWord_5683741).sum := by decide
  have hdescent : baseEnd_5683741 < baseStart_5683741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683767 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_5683767 : Nat := 118140960795 + 5683767 * 2 ^ 59
def prefixEnd_5683767 : Nat := 4983230072969 + 3 ^ 40 * 5683767 * 2
def baseEnd_5683767 : Nat := 2918504399163368969173337

theorem tailTrace_5683767 : CollatzResearch.WordTrace tailWord_5683767 prefixEnd_5683767 2918504399163368969173337 := by
  unfold tailWord_5683767
  simp only [CollatzResearch.WordTrace]
  refine ⟨207304013199690343966529555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138202675466460229311019703 207304013199690343966529555)
  ·
    refine ⟨310956019799535515949794333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207304013199690343966529555 310956019799535515949794333)
    ·
      refine ⟨116608507424825818481172875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310956019799535515949794333 116608507424825818481172875)
      ·
        refine ⟨174912761137238727721759313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116608507424825818481172875 174912761137238727721759313)
        ·
          refine ⟨131184570852929045791319485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174912761137238727721759313 131184570852929045791319485)
          ·
            refine ⟨49194214069848392171744807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131184570852929045791319485 49194214069848392171744807)
            ·
              refine ⟨73791321104772588257617211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49194214069848392171744807 73791321104772588257617211)
              ·
                refine ⟨110686981657158882386425817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73791321104772588257617211 110686981657158882386425817)
                ·
                  refine ⟨83015236242869161789819363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110686981657158882386425817 83015236242869161789819363)
                  ·
                    refine ⟨124522854364303742684729045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83015236242869161789819363 124522854364303742684729045)
                    ·
                      refine ⟨2918504399163368969173337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124522854364303742684729045 2918504399163368969173337)
                      ·
                        rfl

theorem cell23_5683767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_5683767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683767 prefixEnd_5683767 := by exact prefixLift 5683767
  have htrace : WordTrace (prefixWord ++ tailWord_5683767) baseStart_5683767 baseEnd_5683767 := by
    simpa [prefixWord, tailWord_5683767, baseEnd_5683767] using wordTrace_append hprefix tailTrace_5683767
  have hstable : (prefixWord ++ tailWord_5683767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683767).length < 2 ^ (prefixWord ++ tailWord_5683767).sum := by decide
  have hdescent : baseEnd_5683767 < baseStart_5683767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
