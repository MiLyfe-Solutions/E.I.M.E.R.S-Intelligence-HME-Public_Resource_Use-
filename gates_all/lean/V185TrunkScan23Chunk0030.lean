import V185TrunkScan23Chunk0029

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_178174 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_178174 : Nat := 118140960795 + 178174 * 2 ^ 59
def prefixEnd_178174 : Nat := 4983230072969 + 3 ^ 40 * 178174 * 2
def baseEnd_178174 : Nat := 91488902134291127105599

theorem tailTrace_178174 : CollatzResearch.WordTrace tailWord_178174 prefixEnd_178174 91488902134291127105599 := by
  unfold tailWord_178174
  simp only [CollatzResearch.WordTrace]
  refine ⟨812317457064187817709697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4332359771009001694451717 812317457064187817709697)
  ·
    refine ⟨609238092798140863282273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 812317457064187817709697 609238092798140863282273)
    ·
      refine ⟨456928569598605647461705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 609238092798140863282273 456928569598605647461705)
      ·
        refine ⟨342696427198954235596279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456928569598605647461705 342696427198954235596279)
        ·
          refine ⟨514044640798431353394419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342696427198954235596279 514044640798431353394419)
          ·
            refine ⟨771066961197647030091629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514044640798431353394419 771066961197647030091629)
            ·
              refine ⟨289150110449117636284361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 771066961197647030091629 289150110449117636284361)
              ·
                refine ⟨216862582836838227213271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289150110449117636284361 216862582836838227213271)
                ·
                  refine ⟨325293874255257340819907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216862582836838227213271 325293874255257340819907)
                  ·
                    refine ⟨487940811382886011229861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325293874255257340819907 487940811382886011229861)
                    ·
                      refine ⟨91488902134291127105599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 487940811382886011229861 91488902134291127105599)
                      ·
                        rfl

theorem cell23_178174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_178174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178174 prefixEnd_178174 := by exact prefixLift 178174
  have htrace : WordTrace (prefixWord ++ tailWord_178174) baseStart_178174 baseEnd_178174 := by
    simpa [prefixWord, tailWord_178174, baseEnd_178174] using wordTrace_append hprefix tailTrace_178174
  have hstable : (prefixWord ++ tailWord_178174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178174).length < 2 ^ (prefixWord ++ tailWord_178174).sum := by decide
  have hdescent : baseEnd_178174 < baseStart_178174 := by decide
  rcases family_descends (prefixWord ++ tailWord_178174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178247 : List Nat := [1, 1, 4, 1, 3, 1, 1, 4, 1, 4, 2]
def baseStart_178247 : Nat := 118140960795 + 178247 * 2 ^ 59
def prefixEnd_178247 : Nat := 4983230072969 + 3 ^ 40 * 178247 * 2
def baseEnd_178247 : Nat := 91526386222069341492763

theorem tailTrace_178247 : CollatzResearch.WordTrace tailWord_178247 prefixEnd_178247 91526386222069341492763 := by
  unfold tailWord_178247
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501202185249036009084995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334134790166024006056663 6501202185249036009084995)
  ·
    refine ⟨9751803277873554013627493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501202185249036009084995 9751803277873554013627493)
    ·
      refine ⟨1828463114601291377555155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9751803277873554013627493 1828463114601291377555155)
      ·
        refine ⟨2742694671901937066332733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1828463114601291377555155 2742694671901937066332733)
        ·
          refine ⟨1028510501963226399874775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2742694671901937066332733 1028510501963226399874775)
          ·
            refine ⟨1542765752944839599812163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028510501963226399874775 1542765752944839599812163)
            ·
              refine ⟨2314148629417259399718245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542765752944839599812163 2314148629417259399718245)
              ·
                refine ⟨433902868015736137447171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2314148629417259399718245 433902868015736137447171)
                ·
                  refine ⟨650854302023604206170757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433902868015736137447171 650854302023604206170757)
                  ·
                    refine ⟨122035181629425788657017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 650854302023604206170757 122035181629425788657017)
                    ·
                      refine ⟨91526386222069341492763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122035181629425788657017 91526386222069341492763)
                      ·
                        rfl

theorem cell23_178247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_178247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178247 prefixEnd_178247 := by exact prefixLift 178247
  have htrace : WordTrace (prefixWord ++ tailWord_178247) baseStart_178247 baseEnd_178247 := by
    simpa [prefixWord, tailWord_178247, baseEnd_178247] using wordTrace_append hprefix tailTrace_178247
  have hstable : (prefixWord ++ tailWord_178247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178247).length < 2 ^ (prefixWord ++ tailWord_178247).sum := by decide
  have hdescent : baseEnd_178247 < baseStart_178247 := by decide
  rcases family_descends (prefixWord ++ tailWord_178247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178258 : List Nat := [3, 2, 2, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_178258 : Nat := 118140960795 + 178258 * 2 ^ 59
def prefixEnd_178258 : Nat := 4983230072969 + 3 ^ 40 * 178258 * 2
def baseEnd_178258 : Nat := 91532034509268798455213

theorem tailTrace_178258 : CollatzResearch.WordTrace tailWord_178258 prefixEnd_178258 91532034509268798455213 := by
  unfold tailWord_178258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625400847052296221933857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4334402258806123258490285 1625400847052296221933857)
  ·
    refine ⟨1219050635289222166450393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1625400847052296221933857 1219050635289222166450393)
    ·
      refine ⟨914287976466916624837795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1219050635289222166450393 914287976466916624837795)
      ·
        refine ⟨1371431964700374937256693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 914287976466916624837795 1371431964700374937256693)
        ·
          refine ⟨128571746690660150367815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1371431964700374937256693 128571746690660150367815)
          ·
            refine ⟨192857620035990225551723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128571746690660150367815 192857620035990225551723)
            ·
              refine ⟨289286430053985338327585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192857620035990225551723 289286430053985338327585)
              ·
                refine ⟨216964822540489003745689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 289286430053985338327585 216964822540489003745689)
                ·
                  refine ⟨162723616905366752809267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216964822540489003745689 162723616905366752809267)
                  ·
                    refine ⟨244085425358050129213901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162723616905366752809267 244085425358050129213901)
                    ·
                      refine ⟨91532034509268798455213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244085425358050129213901 91532034509268798455213)
                      ·
                        rfl

theorem cell23_178258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_178258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178258 prefixEnd_178258 := by exact prefixLift 178258
  have htrace : WordTrace (prefixWord ++ tailWord_178258) baseStart_178258 baseEnd_178258 := by
    simpa [prefixWord, tailWord_178258, baseEnd_178258] using wordTrace_append hprefix tailTrace_178258
  have hstable : (prefixWord ++ tailWord_178258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178258).length < 2 ^ (prefixWord ++ tailWord_178258).sum := by decide
  have hdescent : baseEnd_178258 < baseStart_178258 := by decide
  rcases family_descends (prefixWord ++ tailWord_178258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178264 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2]
def baseStart_178264 : Nat := 118140960795 + 178264 * 2 ^ 59
def prefixEnd_178264 : Nat := 4983230072969 + 3 ^ 40 * 178264 * 2
def baseEnd_178264 : Nat := 91535115393195774980185

theorem tailTrace_178264 : CollatzResearch.WordTrace tailWord_178264 prefixEnd_178264 91535115393195774980185 := by
  unfold tailWord_178264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250911113093723956226923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4334548150791631941635897 3250911113093723956226923)
  ·
    refine ⟨4876366669640585934340385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3250911113093723956226923 4876366669640585934340385)
    ·
      refine ⟨3657275002230439450755289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4876366669640585934340385 3657275002230439450755289)
      ·
        refine ⟨2742956251672829588066467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3657275002230439450755289 2742956251672829588066467)
        ·
          refine ⟨4114434377509244382099701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2742956251672829588066467 4114434377509244382099701)
          ·
            refine ⟨385728222891491660821847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4114434377509244382099701 385728222891491660821847)
            ·
              refine ⟨578592334337237491232771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385728222891491660821847 578592334337237491232771)
              ·
                refine ⟨867888501505856236849157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578592334337237491232771 867888501505856236849157)
                ·
                  refine ⟨162729094032348044409217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 867888501505856236849157 162729094032348044409217)
                  ·
                    refine ⟨122046820524261033306913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162729094032348044409217 122046820524261033306913)
                    ·
                      refine ⟨91535115393195774980185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122046820524261033306913 91535115393195774980185)
                      ·
                        rfl

theorem cell23_178264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_178264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178264 prefixEnd_178264 := by exact prefixLift 178264
  have htrace : WordTrace (prefixWord ++ tailWord_178264) baseStart_178264 baseEnd_178264 := by
    simpa [prefixWord, tailWord_178264, baseEnd_178264] using wordTrace_append hprefix tailTrace_178264
  have hstable : (prefixWord ++ tailWord_178264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178264).length < 2 ^ (prefixWord ++ tailWord_178264).sum := by decide
  have hdescent : baseEnd_178264 < baseStart_178264 := by decide
  rcases family_descends (prefixWord ++ tailWord_178264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178281 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 2, 2, 2]
def baseStart_178281 : Nat := 118140960795 + 178281 * 2 ^ 59
def prefixEnd_178281 : Nat := 4983230072969 + 3 ^ 40 * 178281 * 2
def baseEnd_178281 : Nat := 91543844564322208467607

theorem tailTrace_178281 : CollatzResearch.WordTrace tailWord_178281 prefixEnd_178281 91543844564322208467607 := by
  unfold tailWord_178281
  simp only [CollatzResearch.WordTrace]
  refine ⟨6502442267125859815822697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4334961511417239877215131 6502442267125859815822697)
  ·
    refine ⟨4876831700344394861867023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6502442267125859815822697 4876831700344394861867023)
    ·
      refine ⟨7315247550516592292800535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876831700344394861867023 7315247550516592292800535)
      ·
        refine ⟨10972871325774888439200803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315247550516592292800535 10972871325774888439200803)
        ·
          refine ⟨16459306988662332658801205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972871325774888439200803 16459306988662332658801205)
          ·
            refine ⟨1543060030187093686762613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16459306988662332658801205 1543060030187093686762613)
            ·
              refine ⟨144661877830040033133995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1543060030187093686762613 144661877830040033133995)
              ·
                refine ⟨216992816745060049700993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144661877830040033133995 216992816745060049700993)
                ·
                  refine ⟨162744612558795037275745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216992816745060049700993 162744612558795037275745)
                  ·
                    refine ⟨122058459419096277956809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162744612558795037275745 122058459419096277956809)
                    ·
                      refine ⟨91543844564322208467607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122058459419096277956809 91543844564322208467607)
                      ·
                        rfl

theorem cell23_178281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 2, 2, 2].length) (baseStart_178281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178281 prefixEnd_178281 := by exact prefixLift 178281
  have htrace : WordTrace (prefixWord ++ tailWord_178281) baseStart_178281 baseEnd_178281 := by
    simpa [prefixWord, tailWord_178281, baseEnd_178281] using wordTrace_append hprefix tailTrace_178281
  have hstable : (prefixWord ++ tailWord_178281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178281).length < 2 ^ (prefixWord ++ tailWord_178281).sum := by decide
  have hdescent : baseEnd_178281 < baseStart_178281 := by decide
  rcases family_descends (prefixWord ++ tailWord_178281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178300 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 1, 7]
def baseStart_178300 : Nat := 118140960795 + 178300 * 2 ^ 59
def prefixEnd_178300 : Nat := 4983230072969 + 3 ^ 40 * 178300 * 2
def baseEnd_178300 : Nat := 30517866898919211376673

theorem tailTrace_178300 : CollatzResearch.WordTrace tailWord_178300 prefixEnd_178300 30517866898919211376673 := by
  unfold tailWord_178300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251567627028513030382177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4335423502704684040509569 3251567627028513030382177)
  ·
    refine ⟨2438675720271384772786633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3251567627028513030382177 2438675720271384772786633)
    ·
      refine ⟨1829006790203538579589975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2438675720271384772786633 1829006790203538579589975)
      ·
        refine ⟨2743510185305307869384963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1829006790203538579589975 2743510185305307869384963)
        ·
          refine ⟨4115265277957961804077445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743510185305307869384963 4115265277957961804077445)
          ·
            refine ⟨771612239617117838264521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4115265277957961804077445 771612239617117838264521)
            ·
              refine ⟨578709179712838378698391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771612239617117838264521 578709179712838378698391)
              ·
                refine ⟨868063769569257568047587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578709179712838378698391 868063769569257568047587)
                ·
                  refine ⟨1302095654353886352071381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868063769569257568047587 1302095654353886352071381)
                  ·
                    refine ⟨30517866898919211376673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1302095654353886352071381 30517866898919211376673)
                    ·
                      rfl

theorem cell23_178300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_178300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178300 prefixEnd_178300 := by exact prefixLift 178300
  have htrace : WordTrace (prefixWord ++ tailWord_178300) baseStart_178300 baseEnd_178300 := by
    simpa [prefixWord, tailWord_178300, baseEnd_178300] using wordTrace_append hprefix tailTrace_178300
  have hstable : (prefixWord ++ tailWord_178300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178300).length < 2 ^ (prefixWord ++ tailWord_178300).sum := by decide
  have hdescent : baseEnd_178300 < baseStart_178300 := by decide
  rcases family_descends (prefixWord ++ tailWord_178300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178326 : List Nat := [5, 3, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_178326 : Nat := 118140960795 + 178326 * 2 ^ 59
def prefixEnd_178326 : Nat := 4983230072969 + 3 ^ 40 * 178326 * 2
def baseEnd_178326 : Nat := 91566951193774532404901

theorem tailTrace_178326 : CollatzResearch.WordTrace tailWord_178326 prefixEnd_178326 91566951193774532404901 := by
  unfold tailWord_178326
  simp only [CollatzResearch.WordTrace]
  refine ⟨406505221997677031325677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4336055701308555000807221 406505221997677031325677)
  ·
    refine ⟨152439458249128886747129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 406505221997677031325677 152439458249128886747129)
    ·
      refine ⟨114329593686846665060347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152439458249128886747129 114329593686846665060347)
      ·
        refine ⟨171494390530269997590521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114329593686846665060347 171494390530269997590521)
        ·
          refine ⟨128620792897702498192891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171494390530269997590521 128620792897702498192891)
          ·
            refine ⟨192931189346553747289337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128620792897702498192891 192931189346553747289337)
            ·
              refine ⟨144698392009915310467003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192931189346553747289337 144698392009915310467003)
              ·
                refine ⟨217047588014872965700505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144698392009915310467003 217047588014872965700505)
                ·
                  refine ⟨162785691011154724275379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217047588014872965700505 162785691011154724275379)
                  ·
                    refine ⟨244178536516732086413069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162785691011154724275379 244178536516732086413069)
                    ·
                      refine ⟨91566951193774532404901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244178536516732086413069 91566951193774532404901)
                      ·
                        rfl

theorem cell23_178326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_178326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178326 prefixEnd_178326 := by exact prefixLift 178326
  have htrace : WordTrace (prefixWord ++ tailWord_178326) baseStart_178326 baseEnd_178326 := by
    simpa [prefixWord, tailWord_178326, baseEnd_178326] using wordTrace_append hprefix tailTrace_178326
  have hstable : (prefixWord ++ tailWord_178326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178326).length < 2 ^ (prefixWord ++ tailWord_178326).sum := by decide
  have hdescent : baseEnd_178326 < baseStart_178326 := by decide
  rcases family_descends (prefixWord ++ tailWord_178326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178327 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5]
def baseStart_178327 : Nat := 118140960795 + 178327 * 2 ^ 59
def prefixEnd_178327 : Nat := 4983230072969 + 3 ^ 40 * 178327 * 2
def baseEnd_178327 : Nat := 91567464674429028492395

theorem tailTrace_178327 : CollatzResearch.WordTrace tailWord_178327 prefixEnd_178327 91567464674429028492395 := by
  unfold tailWord_178327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504120024959209671997235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4336080016639473114664823 6504120024959209671997235)
  ·
    refine ⟨9756180037438814507995853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6504120024959209671997235 9756180037438814507995853)
    ·
      refine ⟨3658567514039555440498445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9756180037438814507995853 3658567514039555440498445)
      ·
        refine ⟨1371962817764833290186917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3658567514039555440498445 1371962817764833290186917)
        ·
          refine ⟨257243028330906241910047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1371962817764833290186917 257243028330906241910047)
          ·
            refine ⟨385864542496359362865071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257243028330906241910047 385864542496359362865071)
            ·
              refine ⟨578796813744539044297607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 385864542496359362865071 578796813744539044297607)
              ·
                refine ⟨868195220616808566446411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578796813744539044297607 868195220616808566446411)
                ·
                  refine ⟨1302292830925212849669617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868195220616808566446411 1302292830925212849669617)
                  ·
                    refine ⟨976719623193909637252213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1302292830925212849669617 976719623193909637252213)
                    ·
                      refine ⟨91567464674429028492395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 976719623193909637252213 91567464674429028492395)
                      ·
                        rfl

theorem cell23_178327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_178327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178327 prefixEnd_178327 := by exact prefixLift 178327
  have htrace : WordTrace (prefixWord ++ tailWord_178327) baseStart_178327 baseEnd_178327 := by
    simpa [prefixWord, tailWord_178327, baseEnd_178327] using wordTrace_append hprefix tailTrace_178327
  have hstable : (prefixWord ++ tailWord_178327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178327).length < 2 ^ (prefixWord ++ tailWord_178327).sum := by decide
  have hdescent : baseEnd_178327 < baseStart_178327 := by decide
  rcases family_descends (prefixWord ++ tailWord_178327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178400 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_178400 : Nat := 118140960795 + 178400 * 2 ^ 59
def prefixEnd_178400 : Nat := 4983230072969 + 3 ^ 40 * 178400 * 2
def baseEnd_178400 : Nat := 91604948762207242879559

theorem tailTrace_178400 : CollatzResearch.WordTrace tailWord_178400 prefixEnd_178400 91604948762207242879559 := by
  unfold tailWord_178400
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253391276847371569702327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4337855035796495426269769 3253391276847371569702327)
  ·
    refine ⟨4880086915271057354553491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253391276847371569702327 4880086915271057354553491)
    ·
      refine ⟨7320130372906586031830237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880086915271057354553491 7320130372906586031830237)
      ·
        refine ⟨2745048889839969761936339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7320130372906586031830237 2745048889839969761936339)
        ·
          refine ⟨4117573334759954642904509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745048889839969761936339 4117573334759954642904509)
          ·
            refine ⟨1544090000534982991089191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4117573334759954642904509 1544090000534982991089191)
            ·
              refine ⟨2316135000802474486633787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544090000534982991089191 2316135000802474486633787)
              ·
                refine ⟨3474202501203711729950681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316135000802474486633787 3474202501203711729950681)
                ·
                  refine ⟨2605651875902783797463011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3474202501203711729950681 2605651875902783797463011)
                  ·
                    refine ⟨3908477813854175696194517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2605651875902783797463011 3908477813854175696194517)
                    ·
                      refine ⟨91604948762207242879559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3908477813854175696194517 91604948762207242879559)
                      ·
                        rfl

theorem cell23_178400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_178400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178400 prefixEnd_178400 := by exact prefixLift 178400
  have htrace : WordTrace (prefixWord ++ tailWord_178400) baseStart_178400 baseEnd_178400 := by
    simpa [prefixWord, tailWord_178400, baseEnd_178400] using wordTrace_append hprefix tailTrace_178400
  have hstable : (prefixWord ++ tailWord_178400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178400).length < 2 ^ (prefixWord ++ tailWord_178400).sum := by decide
  have hdescent : baseEnd_178400 < baseStart_178400 := by decide
  rcases family_descends (prefixWord ++ tailWord_178400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178427 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 8, 2]
def baseStart_178427 : Nat := 118140960795 + 178427 * 2 ^ 59
def prefixEnd_178427 : Nat := 4983230072969 + 3 ^ 40 * 178427 * 2
def baseEnd_178427 : Nat := 91618812739878637241935

theorem tailTrace_178427 : CollatzResearch.WordTrace tailWord_178427 prefixEnd_178427 91618812739878637241935 := by
  unfold tailWord_178427
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507767324596926750637535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4338511549731284500425023 6507767324596926750637535)
  ·
    refine ⟨9761650986895390125956303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6507767324596926750637535 9761650986895390125956303)
    ·
      refine ⟨14642476480343085188934455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9761650986895390125956303 14642476480343085188934455)
      ·
        refine ⟨21963714720514627783401683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14642476480343085188934455 21963714720514627783401683)
        ·
          refine ⟨32945572080771941675102525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21963714720514627783401683 32945572080771941675102525)
          ·
            refine ⟨12354589530289478128163447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32945572080771941675102525 12354589530289478128163447)
            ·
              refine ⟨18531884295434217192245171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12354589530289478128163447 18531884295434217192245171)
              ·
                refine ⟨27797826443151325788367757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18531884295434217192245171 27797826443151325788367757)
                ·
                  refine ⟨10424184916181747170637909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27797826443151325788367757 10424184916181747170637909)
                  ·
                    refine ⟨122158416986504849655913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10424184916181747170637909 122158416986504849655913)
                    ·
                      refine ⟨91618812739878637241935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122158416986504849655913 91618812739878637241935)
                      ·
                        rfl

theorem cell23_178427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 8, 2].length) (baseStart_178427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178427 prefixEnd_178427 := by exact prefixLift 178427
  have htrace : WordTrace (prefixWord ++ tailWord_178427) baseStart_178427 baseEnd_178427 := by
    simpa [prefixWord, tailWord_178427, baseEnd_178427] using wordTrace_append hprefix tailTrace_178427
  have hstable : (prefixWord ++ tailWord_178427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178427).length < 2 ^ (prefixWord ++ tailWord_178427).sum := by decide
  have hdescent : baseEnd_178427 < baseStart_178427 := by decide
  rcases family_descends (prefixWord ++ tailWord_178427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178447 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3]
def baseStart_178447 : Nat := 118140960795 + 178447 * 2 ^ 59
def prefixEnd_178447 : Nat := 4983230072969 + 3 ^ 40 * 178447 * 2
def baseEnd_178447 : Nat := 91629082352968558991843

theorem tailTrace_178447 : CollatzResearch.WordTrace tailWord_178447 prefixEnd_178447 91629082352968558991843 := by
  unfold tailWord_178447
  simp only [CollatzResearch.WordTrace]
  refine ⟨6508496784524470166365595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4338997856349646777577063 6508496784524470166365595)
  ·
    refine ⟨9762745176786705249548393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6508496784524470166365595 9762745176786705249548393)
    ·
      refine ⟨7322058882590028937161295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9762745176786705249548393 7322058882590028937161295)
      ·
        refine ⟨10983088323885043405741943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322058882590028937161295 10983088323885043405741943)
        ·
          refine ⟨16474632485827565108612915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10983088323885043405741943 16474632485827565108612915)
          ·
            refine ⟨24711948728741347662919373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16474632485827565108612915 24711948728741347662919373)
            ·
              refine ⟨9266980773278005373594765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24711948728741347662919373 9266980773278005373594765)
              ·
                refine ⟨3475117789979252015098037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9266980773278005373594765 3475117789979252015098037)
                ·
                  refine ⟨325792292810554876415441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3475117789979252015098037 325792292810554876415441)
                  ·
                    refine ⟨244344219607916157311581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 325792292810554876415441 244344219607916157311581)
                    ·
                      refine ⟨91629082352968558991843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244344219607916157311581 91629082352968558991843)
                      ·
                        rfl

theorem cell23_178447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 3].length) (baseStart_178447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178447 prefixEnd_178447 := by exact prefixLift 178447
  have htrace : WordTrace (prefixWord ++ tailWord_178447) baseStart_178447 baseEnd_178447 := by
    simpa [prefixWord, tailWord_178447, baseEnd_178447] using wordTrace_append hprefix tailTrace_178447
  have hstable : (prefixWord ++ tailWord_178447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178447).length < 2 ^ (prefixWord ++ tailWord_178447).sum := by decide
  have hdescent : baseEnd_178447 < baseStart_178447 := by decide
  rcases family_descends (prefixWord ++ tailWord_178447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178472 : List Nat := [2, 1, 5, 1, 4, 1, 1, 3, 1, 1, 3]
def baseStart_178472 : Nat := 118140960795 + 178472 * 2 ^ 59
def prefixEnd_178472 : Nat := 4983230072969 + 3 ^ 40 * 178472 * 2
def baseEnd_178472 : Nat := 91641919369330961179229

theorem tailTrace_178472 : CollatzResearch.WordTrace tailWord_178472 prefixEnd_178472 91641919369330961179229 := by
  unfold tailWord_178472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254704304716949718012835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4339605739622599624017113 3254704304716949718012835)
  ·
    refine ⟨4882056457075424577019253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3254704304716949718012835 4882056457075424577019253)
    ·
      refine ⟨457692792850821054095555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4882056457075424577019253 457692792850821054095555)
      ·
        refine ⟨686539189276231581143333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457692792850821054095555 686539189276231581143333)
        ·
          refine ⟨128726097989293421464375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 686539189276231581143333 128726097989293421464375)
          ·
            refine ⟨193089146983940132196563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128726097989293421464375 193089146983940132196563)
            ·
              refine ⟨289633720475910198294845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193089146983940132196563 289633720475910198294845)
              ·
                refine ⟨108612645178466324360567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289633720475910198294845 108612645178466324360567)
                ·
                  refine ⟨162918967767699486540851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108612645178466324360567 162918967767699486540851)
                  ·
                    refine ⟨244378451651549229811277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162918967767699486540851 244378451651549229811277)
                    ·
                      refine ⟨91641919369330961179229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244378451651549229811277 91641919369330961179229)
                      ·
                        rfl

theorem cell23_178472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_178472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178472 prefixEnd_178472 := by exact prefixLift 178472
  have htrace : WordTrace (prefixWord ++ tailWord_178472) baseStart_178472 baseEnd_178472 := by
    simpa [prefixWord, tailWord_178472, baseEnd_178472] using wordTrace_append hprefix tailTrace_178472
  have hstable : (prefixWord ++ tailWord_178472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178472).length < 2 ^ (prefixWord ++ tailWord_178472).sum := by decide
  have hdescent : baseEnd_178472 < baseStart_178472 := by decide
  rcases family_descends (prefixWord ++ tailWord_178472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178484 : List Nat := [2, 5, 1, 1, 1, 4, 9]
def baseStart_178484 : Nat := 118140960795 + 178484 * 2 ^ 59
def prefixEnd_178484 : Nat := 4983230072969 + 3 ^ 40 * 178484 * 2
def baseEnd_178484 : Nat := 1131457791817097706533

theorem tailTrace_178484 : CollatzResearch.WordTrace tailWord_178484 prefixEnd_178484 1131457791817097706533 := by
  unfold tailWord_178484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3254923142695212742731253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4339897523593616990308337 3254923142695212742731253)
  ·
    refine ⟨305149044627676194631055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3254923142695212742731253 305149044627676194631055)
    ·
      refine ⟨457723566941514291946583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305149044627676194631055 457723566941514291946583)
      ·
        refine ⟨686585350412271437919875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457723566941514291946583 686585350412271437919875)
        ·
          refine ⟨1029878025618407156879813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686585350412271437919875 1029878025618407156879813)
          ·
            refine ⟨193102129803451341914965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1029878025618407156879813 193102129803451341914965)
            ·
              refine ⟨1131457791817097706533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 193102129803451341914965 1131457791817097706533)
              ·
                rfl

theorem cell23_178484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 9].length) (baseStart_178484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178484 prefixEnd_178484 := by exact prefixLift 178484
  have htrace : WordTrace (prefixWord ++ tailWord_178484) baseStart_178484 baseEnd_178484 := by
    simpa [prefixWord, tailWord_178484, baseEnd_178484] using wordTrace_append hprefix tailTrace_178484
  have hstable : (prefixWord ++ tailWord_178484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178484).length < 2 ^ (prefixWord ++ tailWord_178484).sum := by decide
  have hdescent : baseEnd_178484 < baseStart_178484 := by decide
  rcases family_descends (prefixWord ++ tailWord_178484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178495 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 1, 2, 2]
def baseStart_178495 : Nat := 118140960795 + 178495 * 2 ^ 59
def prefixEnd_178495 : Nat := 4983230072969 + 3 ^ 40 * 178495 * 2
def baseEnd_178495 : Nat := 91653729424384371191623

theorem tailTrace_178495 : CollatzResearch.WordTrace tailWord_178495 prefixEnd_178495 91653729424384371191623 := by
  unfold tailWord_178495
  simp only [CollatzResearch.WordTrace]
  refine ⟨6510247488350574364112939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4340164992233716242741959 6510247488350574364112939)
  ·
    refine ⟨9765371232525861546169409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6510247488350574364112939 9765371232525861546169409)
    ·
      refine ⟨7324028424394396159627057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9765371232525861546169409 7324028424394396159627057)
      ·
        refine ⟨5493021318295797119720293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324028424394396159627057 5493021318295797119720293)
        ·
          refine ⟨1029941497180461959947555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5493021318295797119720293 1029941497180461959947555)
          ·
            refine ⟨1544912245770692939921333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029941497180461959947555 1544912245770692939921333)
            ·
              refine ⟨144835523041002463117625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1544912245770692939921333 144835523041002463117625)
              ·
                refine ⟨108626642280751847338219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144835523041002463117625 108626642280751847338219)
                ·
                  refine ⟨162939963421127771007329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108626642280751847338219 162939963421127771007329)
                  ·
                    refine ⟨122204972565845828255497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162939963421127771007329 122204972565845828255497)
                    ·
                      refine ⟨91653729424384371191623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122204972565845828255497 91653729424384371191623)
                      ·
                        rfl

theorem cell23_178495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 2, 2].length) (baseStart_178495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178495 prefixEnd_178495 := by exact prefixLift 178495
  have htrace : WordTrace (prefixWord ++ tailWord_178495) baseStart_178495 baseEnd_178495 := by
    simpa [prefixWord, tailWord_178495, baseEnd_178495] using wordTrace_append hprefix tailTrace_178495
  have hstable : (prefixWord ++ tailWord_178495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178495).length < 2 ^ (prefixWord ++ tailWord_178495).sum := by decide
  have hdescent : baseEnd_178495 < baseStart_178495 := by decide
  rcases family_descends (prefixWord ++ tailWord_178495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178537 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_178537 : Nat := 118140960795 + 178537 * 2 ^ 59
def prefixEnd_178537 : Nat := 4983230072969 + 3 ^ 40 * 178537 * 2
def baseEnd_178537 : Nat := 91675295611873206866429

theorem tailTrace_178537 : CollatzResearch.WordTrace tailWord_178537 prefixEnd_178537 91675295611873206866429 := by
  unfold tailWord_178537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511779354198415537141865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4341186236132277024761243 6511779354198415537141865)
  ·
    refine ⟨4883834515648811652856399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6511779354198415537141865 4883834515648811652856399)
    ·
      refine ⟨7325751773473217479284599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883834515648811652856399 7325751773473217479284599)
      ·
        refine ⟨10988627660209826218926899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325751773473217479284599 10988627660209826218926899)
        ·
          refine ⟨16482941490314739328390349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10988627660209826218926899 16482941490314739328390349)
          ·
            refine ⟨6181103058868027248146381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16482941490314739328390349 6181103058868027248146381)
            ·
              refine ⟨2317913647075510218054893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6181103058868027248146381 2317913647075510218054893)
              ·
                refine ⟨869217617653316331770585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2317913647075510218054893 869217617653316331770585)
                ·
                  refine ⟨651913213239987248827939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869217617653316331770585 651913213239987248827939)
                  ·
                    refine ⟨977869819859980873241909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 651913213239987248827939 977869819859980873241909)
                    ·
                      refine ⟨91675295611873206866429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 977869819859980873241909 91675295611873206866429)
                      ·
                        rfl

theorem cell23_178537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_178537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178537 prefixEnd_178537 := by exact prefixLift 178537
  have htrace : WordTrace (prefixWord ++ tailWord_178537) baseStart_178537 baseEnd_178537 := by
    simpa [prefixWord, tailWord_178537, baseEnd_178537] using wordTrace_append hprefix tailTrace_178537
  have hstable : (prefixWord ++ tailWord_178537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178537).length < 2 ^ (prefixWord ++ tailWord_178537).sum := by decide
  have hdescent : baseEnd_178537 < baseStart_178537 := by decide
  rcases family_descends (prefixWord ++ tailWord_178537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178547 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4]
def baseStart_178547 : Nat := 118140960795 + 178547 * 2 ^ 59
def prefixEnd_178547 : Nat := 4983230072969 + 3 ^ 40 * 178547 * 2
def baseEnd_178547 : Nat := 91680430418418167741383

theorem tailTrace_178547 : CollatzResearch.WordTrace tailWord_178547 prefixEnd_178547 91680430418418167741383 := by
  unfold tailWord_178547
  simp only [CollatzResearch.WordTrace]
  refine ⟨6512144084162187245005895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4341429389441458163337263 6512144084162187245005895)
  ·
    refine ⟨9768216126243280867508843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6512144084162187245005895 9768216126243280867508843)
    ·
      refine ⟨14652324189364921301263265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768216126243280867508843 14652324189364921301263265)
      ·
        refine ⟨10989243142023690975947449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14652324189364921301263265 10989243142023690975947449)
        ·
          refine ⟨8241932356517768231960587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10989243142023690975947449 8241932356517768231960587)
          ·
            refine ⟨12362898534776652347940881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241932356517768231960587 12362898534776652347940881)
            ·
              refine ⟨9272173901082489260955661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12362898534776652347940881 9272173901082489260955661)
              ·
                refine ⟨3477065212905933472858373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9272173901082489260955661 3477065212905933472858373)
                ·
                  refine ⟨651949727419862526160945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3477065212905933472858373 651949727419862526160945)
                  ·
                    refine ⟨488962295564896894620709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 651949727419862526160945 488962295564896894620709)
                    ·
                      refine ⟨91680430418418167741383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 488962295564896894620709 91680430418418167741383)
                      ·
                        rfl

theorem cell23_178547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_178547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178547 prefixEnd_178547 := by exact prefixLift 178547
  have htrace : WordTrace (prefixWord ++ tailWord_178547) baseStart_178547 baseEnd_178547 := by
    simpa [prefixWord, tailWord_178547, baseEnd_178547] using wordTrace_append hprefix tailTrace_178547
  have hstable : (prefixWord ++ tailWord_178547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178547).length < 2 ^ (prefixWord ++ tailWord_178547).sum := by decide
  have hdescent : baseEnd_178547 < baseStart_178547 := by decide
  rcases family_descends (prefixWord ++ tailWord_178547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178564 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_178564 : Nat := 118140960795 + 178564 * 2 ^ 59
def prefixEnd_178564 : Nat := 4983230072969 + 3 ^ 40 * 178564 * 2
def baseEnd_178564 : Nat := 91689159589544601228805

theorem tailTrace_178564 : CollatzResearch.WordTrace tailWord_178564 prefixEnd_178564 91689159589544601228805 := by
  unfold tailWord_178564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256382062550299574187373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4341842750067066098916497 3256382062550299574187373)
  ·
    refine ⟨1221143273456362340320265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3256382062550299574187373 1221143273456362340320265)
    ·
      refine ⟨915857455092271755240199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221143273456362340320265 915857455092271755240199)
      ·
        refine ⟨1373786182638407632860299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915857455092271755240199 1373786182638407632860299)
        ·
          refine ⟨2060679273957611449290449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373786182638407632860299 2060679273957611449290449)
          ·
            refine ⟨1545509455468208586967837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060679273957611449290449 1545509455468208586967837)
            ·
              refine ⟨579566045800578220112939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1545509455468208586967837 579566045800578220112939)
              ·
                refine ⟨869349068700867330169409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579566045800578220112939 869349068700867330169409)
                ·
                  refine ⟨652011801525650497627057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869349068700867330169409 652011801525650497627057)
                  ·
                    refine ⟨489008851144237873220293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 652011801525650497627057 489008851144237873220293)
                    ·
                      refine ⟨91689159589544601228805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 489008851144237873220293 91689159589544601228805)
                      ·
                        rfl

theorem cell23_178564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_178564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178564 prefixEnd_178564 := by exact prefixLift 178564
  have htrace : WordTrace (prefixWord ++ tailWord_178564) baseStart_178564 baseEnd_178564 := by
    simpa [prefixWord, tailWord_178564, baseEnd_178564] using wordTrace_append hprefix tailTrace_178564
  have hstable : (prefixWord ++ tailWord_178564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178564).length < 2 ^ (prefixWord ++ tailWord_178564).sum := by decide
  have hdescent : baseEnd_178564 < baseStart_178564 := by decide
  rcases family_descends (prefixWord ++ tailWord_178564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178568 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2]
def baseStart_178568 : Nat := 118140960795 + 178568 * 2 ^ 59
def prefixEnd_178568 : Nat := 4983230072969 + 3 ^ 40 * 178568 * 2
def baseEnd_178568 : Nat := 91691213512162585578787

theorem tailTrace_178568 : CollatzResearch.WordTrace tailWord_178568 prefixEnd_178568 91691213512162585578787 := by
  unfold tailWord_178568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3256455008543053915760179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4341940011390738554346905 3256455008543053915760179)
  ·
    refine ⟨4884682512814580873640269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3256455008543053915760179 4884682512814580873640269)
    ·
      refine ⟨1831755942305467827615101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4884682512814580873640269 1831755942305467827615101)
      ·
        refine ⟨686908478364550435355663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1831755942305467827615101 686908478364550435355663)
        ·
          refine ⟨1030362717546825653033495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686908478364550435355663 1030362717546825653033495)
          ·
            refine ⟨1545544076320238479550243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030362717546825653033495 1545544076320238479550243)
            ·
              refine ⟨2318316114480357719325365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1545544076320238479550243 2318316114480357719325365)
              ·
                refine ⟨217342135732533536186753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2318316114480357719325365 217342135732533536186753)
                ·
                  refine ⟨163006601799400152140065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217342135732533536186753 163006601799400152140065)
                  ·
                    refine ⟨122254951349550114105049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163006601799400152140065 122254951349550114105049)
                    ·
                      refine ⟨91691213512162585578787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122254951349550114105049 91691213512162585578787)
                      ·
                        rfl

theorem cell23_178568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_178568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178568 prefixEnd_178568 := by exact prefixLift 178568
  have htrace : WordTrace (prefixWord ++ tailWord_178568) baseStart_178568 baseEnd_178568 := by
    simpa [prefixWord, tailWord_178568, baseEnd_178568] using wordTrace_append hprefix tailTrace_178568
  have hstable : (prefixWord ++ tailWord_178568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178568).length < 2 ^ (prefixWord ++ tailWord_178568).sum := by decide
  have hdescent : baseEnd_178568 < baseStart_178568 := by decide
  rcases family_descends (prefixWord ++ tailWord_178568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178574 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_178574 : Nat := 118140960795 + 178574 * 2 ^ 59
def prefixEnd_178574 : Nat := 4983230072969 + 3 ^ 40 * 178574 * 2
def baseEnd_178574 : Nat := 10188254932898840233751

theorem tailTrace_178574 : CollatzResearch.WordTrace tailWord_178574 prefixEnd_178574 10188254932898840233751 := by
  unfold tailWord_178574
  simp only [CollatzResearch.WordTrace]
  refine ⟨814141106883046357029847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4342085903376247237492517 814141106883046357029847)
  ·
    refine ⟨1221211660324569535544771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 814141106883046357029847 1221211660324569535544771)
    ·
      refine ⟨1831817490486854303317157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1221211660324569535544771 1831817490486854303317157)
      ·
        refine ⟨343465779466285181871967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1831817490486854303317157 343465779466285181871967)
        ·
          refine ⟨515198669199427772807951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343465779466285181871967 515198669199427772807951)
          ·
            refine ⟨772798003799141659211927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515198669199427772807951 772798003799141659211927)
            ·
              refine ⟨1159197005698712488817891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772798003799141659211927 1159197005698712488817891)
              ·
                refine ⟨1738795508548068733226837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159197005698712488817891 1738795508548068733226837)
                ·
                  refine ⟨10188254932898840233751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1738795508548068733226837 10188254932898840233751)
                  ·
                    rfl

theorem cell23_178574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_178574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178574 prefixEnd_178574 := by exact prefixLift 178574
  have htrace : WordTrace (prefixWord ++ tailWord_178574) baseStart_178574 baseEnd_178574 := by
    simpa [prefixWord, tailWord_178574, baseEnd_178574] using wordTrace_append hprefix tailTrace_178574
  have hstable : (prefixWord ++ tailWord_178574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178574).length < 2 ^ (prefixWord ++ tailWord_178574).sum := by decide
  have hdescent : baseEnd_178574 < baseStart_178574 := by decide
  rcases family_descends (prefixWord ++ tailWord_178574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178591 : List Nat := [1, 1, 2, 5, 1, 1, 4, 3, 5]
def baseStart_178591 : Nat := 118140960795 + 178591 * 2 ^ 59
def prefixEnd_178591 : Nat := 4983230072969 + 3 ^ 40 * 178591 * 2
def baseEnd_178591 : Nat := 10189224840801777287909

theorem tailTrace_178591 : CollatzResearch.WordTrace tailWord_178591 prefixEnd_178591 10189224840801777287909 := by
  unfold tailWord_178591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513748896002782759607627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4342499264001855173071751 6513748896002782759607627)
  ·
    refine ⟨9770623344004174139411441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513748896002782759607627 9770623344004174139411441)
    ·
      refine ⟨7327967508003130604558581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9770623344004174139411441 7327967508003130604558581)
      ·
        refine ⟨686996953875293494177367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7327967508003130604558581 686996953875293494177367)
        ·
          refine ⟨1030495430812940241266051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686996953875293494177367 1030495430812940241266051)
          ·
            refine ⟨1545743146219410361899077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1030495430812940241266051 1545743146219410361899077)
            ·
              refine ⟨289826839916139442856077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1545743146219410361899077 289826839916139442856077)
              ·
                refine ⟨108685064968552291071029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289826839916139442856077 108685064968552291071029)
                ·
                  refine ⟨10189224840801777287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108685064968552291071029 10189224840801777287909)
                  ·
                    rfl

theorem cell23_178591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 3, 5].length) (baseStart_178591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178591 prefixEnd_178591 := by exact prefixLift 178591
  have htrace : WordTrace (prefixWord ++ tailWord_178591) baseStart_178591 baseEnd_178591 := by
    simpa [prefixWord, tailWord_178591, baseEnd_178591] using wordTrace_append hprefix tailTrace_178591
  have hstable : (prefixWord ++ tailWord_178591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178591).length < 2 ^ (prefixWord ++ tailWord_178591).sum := by decide
  have hdescent : baseEnd_178591 < baseStart_178591 := by decide
  rcases family_descends (prefixWord ++ tailWord_178591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178642 : List Nat := [3, 2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_178642 : Nat := 118140960795 + 178642 * 2 ^ 59
def prefixEnd_178642 : Nat := 4983230072969 + 3 ^ 40 * 178642 * 2
def baseEnd_178642 : Nat := 10192134564510588450383

theorem tailTrace_178642 : CollatzResearch.WordTrace tailWord_178642 prefixEnd_178642 10192134564510588450383 := by
  unfold tailWord_178642
  simp only [CollatzResearch.WordTrace]
  refine ⟨1628902254704504617428545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4343739345878678979809453 1628902254704504617428545)
  ·
    refine ⟨1221676691028378463071409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1628902254704504617428545 1221676691028378463071409)
    ·
      refine ⟨916257518271283847303557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1221676691028378463071409 916257518271283847303557)
      ·
        refine ⟨171798284675865721369417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 916257518271283847303557 171798284675865721369417)
        ·
          refine ⟨128848713506899291027063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171798284675865721369417 128848713506899291027063)
          ·
            refine ⟨193273070260348936540595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128848713506899291027063 193273070260348936540595)
            ·
              refine ⟨289909605390523404810893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193273070260348936540595 289909605390523404810893)
              ·
                refine ⟨108716102021446276804085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 289909605390523404810893 108716102021446276804085)
                ·
                  refine ⟨10192134564510588450383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108716102021446276804085 10192134564510588450383)
                  ·
                    rfl

theorem cell23_178642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_178642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178642 prefixEnd_178642 := by exact prefixLift 178642
  have htrace : WordTrace (prefixWord ++ tailWord_178642) baseStart_178642 baseEnd_178642 := by
    simpa [prefixWord, tailWord_178642, baseEnd_178642] using wordTrace_append hprefix tailTrace_178642
  have hstable : (prefixWord ++ tailWord_178642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178642).length < 2 ^ (prefixWord ++ tailWord_178642).sum := by decide
  have hdescent : baseEnd_178642 < baseStart_178642 := by decide
  rcases family_descends (prefixWord ++ tailWord_178642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178664 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 8]
def baseStart_178664 : Nat := 118140960795 + 178664 * 2 ^ 59
def prefixEnd_178664 : Nat := 4983230072969 + 3 ^ 40 * 178664 * 2
def baseEnd_178664 : Nat := 10193389739443801108705

theorem tailTrace_178664 : CollatzResearch.WordTrace tailWord_178664 prefixEnd_178664 10193389739443801108705 := by
  unfold tailWord_178664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258205712369158113507523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4344274283158877484676697 3258205712369158113507523)
  ·
    refine ⟨4887308568553737170261285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3258205712369158113507523 4887308568553737170261285)
    ·
      refine ⟨916370356603825719423991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4887308568553737170261285 916370356603825719423991)
      ·
        refine ⟨1374555534905738579135987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916370356603825719423991 1374555534905738579135987)
        ·
          refine ⟨2061833302358607868703981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374555534905738579135987 2061833302358607868703981)
          ·
            refine ⟨773187488384477950763993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2061833302358607868703981 773187488384477950763993)
            ·
              refine ⟨579890616288358463072995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773187488384477950763993 579890616288358463072995)
              ·
                refine ⟨869835924432537694609493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579890616288358463072995 869835924432537694609493)
                ·
                  refine ⟨10193389739443801108705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 869835924432537694609493 10193389739443801108705)
                  ·
                    rfl

theorem cell23_178664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_178664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178664 prefixEnd_178664 := by exact prefixLift 178664
  have htrace : WordTrace (prefixWord ++ tailWord_178664) baseStart_178664 baseEnd_178664 := by
    simpa [prefixWord, tailWord_178664, baseEnd_178664] using wordTrace_append hprefix tailTrace_178664
  have hstable : (prefixWord ++ tailWord_178664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178664).length < 2 ^ (prefixWord ++ tailWord_178664).sum := by decide
  have hdescent : baseEnd_178664 < baseStart_178664 := by decide
  rcases family_descends (prefixWord ++ tailWord_178664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178681 : List Nat := [1, 2, 1, 3, 1, 2, 6, 1, 6]
def baseStart_178681 : Nat := 118140960795 + 178681 * 2 ^ 59
def prefixEnd_178681 : Nat := 4983230072969 + 3 ^ 40 * 178681 * 2
def baseEnd_178681 : Nat := 10194359647346738162863

theorem tailTrace_178681 : CollatzResearch.WordTrace tailWord_178681 prefixEnd_178681 10194359647346738162863 := by
  unfold tailWord_178681
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517031465676728130383897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4344687643784485420255931 6517031465676728130383897)
  ·
    refine ⟨4887773599257546097787923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6517031465676728130383897 4887773599257546097787923)
    ·
      refine ⟨7331660398886319146681885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4887773599257546097787923 7331660398886319146681885)
      ·
        refine ⟨2749372649582369680005707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7331660398886319146681885 2749372649582369680005707)
        ·
          refine ⟨4124058974373554520008561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2749372649582369680005707 4124058974373554520008561)
          ·
            refine ⟨3093044230780165890006421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4124058974373554520008561 3093044230780165890006421)
            ·
              refine ⟨144986448317820276094051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3093044230780165890006421 144986448317820276094051)
              ·
                refine ⟨217479672476730414141077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144986448317820276094051 217479672476730414141077)
                ·
                  refine ⟨10194359647346738162863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 217479672476730414141077 10194359647346738162863)
                  ·
                    rfl

theorem cell23_178681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 1, 6].length) (baseStart_178681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178681 prefixEnd_178681 := by exact prefixLift 178681
  have htrace : WordTrace (prefixWord ++ tailWord_178681) baseStart_178681 baseEnd_178681 := by
    simpa [prefixWord, tailWord_178681, baseEnd_178681] using wordTrace_append hprefix tailTrace_178681
  have hstable : (prefixWord ++ tailWord_178681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178681).length < 2 ^ (prefixWord ++ tailWord_178681).sum := by decide
  have hdescent : baseEnd_178681 < baseStart_178681 := by decide
  rcases family_descends (prefixWord ++ tailWord_178681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178691 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 3]
def baseStart_178691 : Nat := 118140960795 + 178691 * 2 ^ 59
def prefixEnd_178691 : Nat := 4983230072969 + 3 ^ 40 * 178691 * 2
def baseEnd_178691 : Nat := 91754371632665604340721

theorem tailTrace_178691 : CollatzResearch.WordTrace tailWord_178691 prefixEnd_178691 91754371632665604340721 := by
  unfold tailWord_178691
  simp only [CollatzResearch.WordTrace]
  refine ⟨6517396195640499838247927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4344930797093666558831951 6517396195640499838247927)
  ·
    refine ⟨9776094293460749757371891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6517396195640499838247927 9776094293460749757371891)
    ·
      refine ⟨14664141440191124636057837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9776094293460749757371891 14664141440191124636057837)
      ·
        refine ⟨5499053040071671738521689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14664141440191124636057837 5499053040071671738521689)
        ·
          refine ⟨4124289780053753803891267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5499053040071671738521689 4124289780053753803891267)
          ·
            refine ⟨6186434670080630705836901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124289780053753803891267 6186434670080630705836901)
            ·
              refine ⟨1159956500640118257344419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6186434670080630705836901 1159956500640118257344419)
              ·
                refine ⟨1739934750960177386016629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1159956500640118257344419 1739934750960177386016629)
                ·
                  refine ⟨163118882902516629939059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1739934750960177386016629 163118882902516629939059)
                  ·
                    refine ⟨244678324353774944908589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163118882902516629939059 244678324353774944908589)
                    ·
                      refine ⟨91754371632665604340721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244678324353774944908589 91754371632665604340721)
                      ·
                        rfl

theorem cell23_178691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_178691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178691 prefixEnd_178691 := by exact prefixLift 178691
  have htrace : WordTrace (prefixWord ++ tailWord_178691) baseStart_178691 baseEnd_178691 := by
    simpa [prefixWord, tailWord_178691, baseEnd_178691] using wordTrace_append hprefix tailTrace_178691
  have hstable : (prefixWord ++ tailWord_178691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178691).length < 2 ^ (prefixWord ++ tailWord_178691).sum := by decide
  have hdescent : baseEnd_178691 < baseStart_178691 := by decide
  rcases family_descends (prefixWord ++ tailWord_178691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178741 : List Nat := [1, 3, 3, 1, 1, 2, 4, 1, 1, 6]
def baseStart_178741 : Nat := 118140960795 + 178741 * 2 ^ 59
def prefixEnd_178741 : Nat := 4983230072969 + 3 ^ 40 * 178741 * 2
def baseEnd_178741 : Nat := 30593348555130136238497

theorem tailTrace_178741 : CollatzResearch.WordTrace tailWord_178741 prefixEnd_178741 30593348555130136238497 := by
  unfold tailWord_178741
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519219845459358377568077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4346146563639572251712051 6519219845459358377568077)
  ·
    refine ⟨2444707442047259391588029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6519219845459358377568077 2444707442047259391588029)
    ·
      refine ⟨916765290767722271845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2444707442047259391588029 916765290767722271845511)
      ·
        refine ⟨1375147936151583407768267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916765290767722271845511 1375147936151583407768267)
        ·
          refine ⟨2062721904227375111652401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375147936151583407768267 2062721904227375111652401)
          ·
            refine ⟨1547041428170531333739301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062721904227375111652401 1547041428170531333739301)
            ·
              refine ⟨290070267781974625076119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1547041428170531333739301 290070267781974625076119)
              ·
                refine ⟨435105401672961937614179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290070267781974625076119 435105401672961937614179)
                ·
                  refine ⟨652658102509442906421269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435105401672961937614179 652658102509442906421269)
                  ·
                    refine ⟨30593348555130136238497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 652658102509442906421269 30593348555130136238497)
                    ·
                      rfl

theorem cell23_178741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_178741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178741 prefixEnd_178741 := by exact prefixLift 178741
  have htrace : WordTrace (prefixWord ++ tailWord_178741) baseStart_178741 baseEnd_178741 := by
    simpa [prefixWord, tailWord_178741, baseEnd_178741] using wordTrace_append hprefix tailTrace_178741
  have hstable : (prefixWord ++ tailWord_178741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178741).length < 2 ^ (prefixWord ++ tailWord_178741).sum := by decide
  have hdescent : baseEnd_178741 < baseStart_178741 := by decide
  rcases family_descends (prefixWord ++ tailWord_178741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178751 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3]
def baseStart_178751 : Nat := 118140960795 + 178751 * 2 ^ 59
def prefixEnd_178751 : Nat := 4983230072969 + 3 ^ 40 * 178751 * 2
def baseEnd_178751 : Nat := 91785180471935369590445

theorem tailTrace_178751 : CollatzResearch.WordTrace tailWord_178751 prefixEnd_178751 91785180471935369590445 := by
  unfold tailWord_178751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6519584575423130085432107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4346389716948753390288071 6519584575423130085432107)
  ·
    refine ⟨9779376863134695128148161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6519584575423130085432107 9779376863134695128148161)
    ·
      refine ⟨7334532647351021346111121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9779376863134695128148161 7334532647351021346111121)
      ·
        refine ⟨5500899485513266009583341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7334532647351021346111121 5500899485513266009583341)
        ·
          refine ⟨2062837307067474753593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5500899485513266009583341 2062837307067474753593753)
          ·
            refine ⟨1547127980300606065195315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062837307067474753593753 1547127980300606065195315)
            ·
              refine ⟨2320691970450909097792973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547127980300606065195315 2320691970450909097792973)
              ·
                refine ⟨870259488919090911672365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320691970450909097792973 870259488919090911672365)
                ·
                  refine ⟨326347308344659091877137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 870259488919090911672365 326347308344659091877137)
                  ·
                    refine ⟨244760481258494318907853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 326347308344659091877137 244760481258494318907853)
                    ·
                      refine ⟨91785180471935369590445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244760481258494318907853 91785180471935369590445)
                      ·
                        rfl

theorem cell23_178751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_178751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178751 prefixEnd_178751 := by exact prefixLift 178751
  have htrace : WordTrace (prefixWord ++ tailWord_178751) baseStart_178751 baseEnd_178751 := by
    simpa [prefixWord, tailWord_178751, baseEnd_178751] using wordTrace_append hprefix tailTrace_178751
  have hstable : (prefixWord ++ tailWord_178751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178751).length < 2 ^ (prefixWord ++ tailWord_178751).sum := by decide
  have hdescent : baseEnd_178751 < baseStart_178751 := by decide
  rcases family_descends (prefixWord ++ tailWord_178751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178765 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_178765 : Nat := 118140960795 + 178765 * 2 ^ 59
def prefixEnd_178765 : Nat := 4983230072969 + 3 ^ 40 * 178765 * 2
def baseEnd_178765 : Nat := 91792369201098314815381

theorem tailTrace_178765 : CollatzResearch.WordTrace tailWord_178765 prefixEnd_178765 91792369201098314815381 := by
  unfold tailWord_178765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520095197372410476441749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4346730131581606984294499 6520095197372410476441749)
  ·
    refine ⟨305629462376831741083207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6520095197372410476441749 305629462376831741083207)
    ·
      refine ⟨458444193565247611624811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 305629462376831741083207 458444193565247611624811)
      ·
        refine ⟨687666290347871417437217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458444193565247611624811 687666290347871417437217)
        ·
          refine ⟨515749717760903563077913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 687666290347871417437217 515749717760903563077913)
          ·
            refine ⟨386812288320677672308435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 515749717760903563077913 386812288320677672308435)
            ·
              refine ⟨580218432481016508462653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 386812288320677672308435 580218432481016508462653)
              ·
                refine ⟨217581912180381190673495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 580218432481016508462653 217581912180381190673495)
                ·
                  refine ⟨326372868270571786010243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217581912180381190673495 326372868270571786010243)
                  ·
                    refine ⟨489559302405857679015365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326372868270571786010243 489559302405857679015365)
                    ·
                      refine ⟨91792369201098314815381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 489559302405857679015365 91792369201098314815381)
                      ·
                        rfl

theorem cell23_178765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_178765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178765 prefixEnd_178765 := by exact prefixLift 178765
  have htrace : WordTrace (prefixWord ++ tailWord_178765) baseStart_178765 baseEnd_178765 := by
    simpa [prefixWord, tailWord_178765, baseEnd_178765] using wordTrace_append hprefix tailTrace_178765
  have hstable : (prefixWord ++ tailWord_178765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178765).length < 2 ^ (prefixWord ++ tailWord_178765).sum := by decide
  have hdescent : baseEnd_178765 < baseStart_178765 := by decide
  rcases family_descends (prefixWord ++ tailWord_178765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178784 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_178784 : Nat := 118140960795 + 178784 * 2 ^ 59
def prefixEnd_178784 : Nat := 4983230072969 + 3 ^ 40 * 178784 * 2
def baseEnd_178784 : Nat := 30600708444511246825931

theorem tailTrace_178784 : CollatzResearch.WordTrace tailWord_178784 prefixEnd_178784 30600708444511246825931 := by
  unfold tailWord_178784
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260394092151788360691703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4347192122869051147588937 3260394092151788360691703)
  ·
    refine ⟨4890591138227682541037555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3260394092151788360691703 4890591138227682541037555)
    ·
      refine ⟨7335886707341523811556333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4890591138227682541037555 7335886707341523811556333)
      ·
        refine ⟨2750957515253071429333625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7335886707341523811556333 2750957515253071429333625)
        ·
          refine ⟨2063218136439803572000219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750957515253071429333625 2063218136439803572000219)
          ·
            refine ⟨3094827204659705358000329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2063218136439803572000219 3094827204659705358000329)
            ·
              refine ⟨2321120403494779018500247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3094827204659705358000329 2321120403494779018500247)
              ·
                refine ⟨3481680605242168527750371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321120403494779018500247 3481680605242168527750371)
                ·
                  refine ⟨5222520907863252791625557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3481680605242168527750371 5222520907863252791625557)
                  ·
                    refine ⟨30600708444511246825931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5222520907863252791625557 30600708444511246825931)
                    ·
                      rfl

theorem cell23_178784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_178784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178784 prefixEnd_178784 := by exact prefixLift 178784
  have htrace : WordTrace (prefixWord ++ tailWord_178784) baseStart_178784 baseEnd_178784 := by
    simpa [prefixWord, tailWord_178784, baseEnd_178784] using wordTrace_append hprefix tailTrace_178784
  have hstable : (prefixWord ++ tailWord_178784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178784).length < 2 ^ (prefixWord ++ tailWord_178784).sum := by decide
  have hdescent : baseEnd_178784 < baseStart_178784 := by decide
  rcases family_descends (prefixWord ++ tailWord_178784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178792 : List Nat := [2, 1, 4, 3, 2, 1, 3, 1, 2, 4]
def baseStart_178792 : Nat := 118140960795 + 178792 * 2 ^ 59
def prefixEnd_178792 : Nat := 4983230072969 + 3 ^ 40 * 178792 * 2
def baseEnd_178792 : Nat := 30602077726256569725919

theorem tailTrace_178792 : CollatzResearch.WordTrace tailWord_178792 prefixEnd_178792 30602077726256569725919 := by
  unfold tailWord_178792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3260539984137297043837315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4347386645516396058449753 3260539984137297043837315)
  ·
    refine ⟨4890809976205945565755973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3260539984137297043837315 4890809976205945565755973)
    ·
      refine ⟨917026870538614793579245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4890809976205945565755973 917026870538614793579245)
      ·
        refine ⟨343885076451980547592217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 917026870538614793579245 343885076451980547592217)
        ·
          refine ⟨257913807338985410694163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343885076451980547592217 257913807338985410694163)
          ·
            refine ⟨386870711008478116041245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 257913807338985410694163 386870711008478116041245)
            ·
              refine ⟨145076516628179293515467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 386870711008478116041245 145076516628179293515467)
              ·
                refine ⟨217614774942268940273201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145076516628179293515467 217614774942268940273201)
                ·
                  refine ⟨163211081206701705204901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217614774942268940273201 163211081206701705204901)
                  ·
                    refine ⟨30602077726256569725919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163211081206701705204901 30602077726256569725919)
                    ·
                      rfl

theorem cell23_178792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_178792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178792 prefixEnd_178792 := by exact prefixLift 178792
  have htrace : WordTrace (prefixWord ++ tailWord_178792) baseStart_178792 baseEnd_178792 := by
    simpa [prefixWord, tailWord_178792, baseEnd_178792] using wordTrace_append hprefix tailTrace_178792
  have hstable : (prefixWord ++ tailWord_178792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178792).length < 2 ^ (prefixWord ++ tailWord_178792).sum := by decide
  have hdescent : baseEnd_178792 < baseStart_178792 := by decide
  rcases family_descends (prefixWord ++ tailWord_178792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178805 : List Nat := [1, 3, 4, 2, 2, 2, 2, 7]
def baseStart_178805 : Nat := 118140960795 + 178805 * 2 ^ 59
def prefixEnd_178805 : Nat := 4983230072969 + 3 ^ 40 * 178805 * 2
def baseEnd_178805 : Nat := 3400478089899191048711

theorem tailTrace_178805 : CollatzResearch.WordTrace tailWord_178805 prefixEnd_178805 3400478089899191048711 := by
  unfold tailWord_178805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6521554117227497307897869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4347702744818331538598579 6521554117227497307897869)
  ·
    refine ⟨2445582793960311490461701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6521554117227497307897869 2445582793960311490461701)
    ·
      refine ⟨458546773867558404461569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2445582793960311490461701 458546773867558404461569)
      ·
        refine ⟨343910080400668803346177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 458546773867558404461569 343910080400668803346177)
        ·
          refine ⟨257932560300501602509633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 343910080400668803346177 257932560300501602509633)
          ·
            refine ⟨193449420225376201882225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257932560300501602509633 193449420225376201882225)
            ·
              refine ⟨145087065169032151411669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193449420225376201882225 145087065169032151411669)
              ·
                refine ⟨3400478089899191048711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 145087065169032151411669 3400478089899191048711)
                ·
                  rfl

theorem cell23_178805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 7].length) (baseStart_178805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178805 prefixEnd_178805 := by exact prefixLift 178805
  have htrace : WordTrace (prefixWord ++ tailWord_178805) baseStart_178805 baseEnd_178805 := by
    simpa [prefixWord, tailWord_178805, baseEnd_178805] using wordTrace_append hprefix tailTrace_178805
  have hstable : (prefixWord ++ tailWord_178805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178805).length < 2 ^ (prefixWord ++ tailWord_178805).sum := by decide
  have hdescent : baseEnd_178805 < baseStart_178805 := by decide
  rcases family_descends (prefixWord ++ tailWord_178805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178841 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 3]
def baseStart_178841 : Nat := 118140960795 + 178841 * 2 ^ 59
def prefixEnd_178841 : Nat := 4983230072969 + 3 ^ 40 * 178841 * 2
def baseEnd_178841 : Nat := 91831393730840017465031

theorem tailTrace_178841 : CollatzResearch.WordTrace tailWord_178841 prefixEnd_178841 91831393730840017465031 := by
  unfold tailWord_178841
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522867145097075456208377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4348578096731383637472251 6522867145097075456208377)
  ·
    refine ⟨4892150358822806592156283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6522867145097075456208377 4892150358822806592156283)
    ·
      refine ⟨7338225538234209888234425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892150358822806592156283 7338225538234209888234425)
      ·
        refine ⟨5503669153675657416175819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7338225538234209888234425 5503669153675657416175819)
        ·
          refine ⟨8255503730513486124263729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5503669153675657416175819 8255503730513486124263729)
          ·
            refine ⟨6191627797885114593197797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8255503730513486124263729 6191627797885114593197797)
            ·
              refine ⟨1160930212103458986224587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6191627797885114593197797 1160930212103458986224587)
              ·
                refine ⟨1741395318155188479336881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160930212103458986224587 1741395318155188479336881)
                ·
                  refine ⟨1306046488616391359502661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741395318155188479336881 1306046488616391359502661)
                  ·
                    refine ⟨244883716615573379906749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306046488616391359502661 244883716615573379906749)
                    ·
                      refine ⟨91831393730840017465031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244883716615573379906749 91831393730840017465031)
                      ·
                        rfl

theorem cell23_178841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_178841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178841 prefixEnd_178841 := by exact prefixLift 178841
  have htrace : WordTrace (prefixWord ++ tailWord_178841) baseStart_178841 baseEnd_178841 := by
    simpa [prefixWord, tailWord_178841, baseEnd_178841] using wordTrace_append hprefix tailTrace_178841
  have hstable : (prefixWord ++ tailWord_178841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178841).length < 2 ^ (prefixWord ++ tailWord_178841).sum := by decide
  have hdescent : baseEnd_178841 < baseStart_178841 := by decide
  rcases family_descends (prefixWord ++ tailWord_178841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178849 : List Nat := [1, 2, 3, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_178849 : Nat := 118140960795 + 178849 * 2 ^ 59
def prefixEnd_178849 : Nat := 4983230072969 + 3 ^ 40 * 178849 * 2
def baseEnd_178849 : Nat := 91835501576075986164995

theorem tailTrace_178849 : CollatzResearch.WordTrace tailWord_178849 prefixEnd_178849 91835501576075986164995 := by
  unfold tailWord_178849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6523158929068092822499601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4348772619378728548333067 6523158929068092822499601)
  ·
    refine ⟨4892369196801069616874701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6523158929068092822499601 4892369196801069616874701)
    ·
      refine ⟨1834638448800401106328013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4892369196801069616874701 1834638448800401106328013)
      ·
        refine ⟨687989418300150414873005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1834638448800401106328013 687989418300150414873005)
        ·
          refine ⟨257996031862556405577377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 687989418300150414873005 257996031862556405577377)
          ·
            refine ⟨193497023896917304183033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 257996031862556405577377 193497023896917304183033)
            ·
              refine ⟨145122767922687978137275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193497023896917304183033 145122767922687978137275)
              ·
                refine ⟨217684151884031967205913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145122767922687978137275 217684151884031967205913)
                ·
                  refine ⟨163263113913023975404435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 217684151884031967205913 163263113913023975404435)
                  ·
                    refine ⟨244894670869535963106653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163263113913023975404435 244894670869535963106653)
                    ·
                      refine ⟨91835501576075986164995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 244894670869535963106653 91835501576075986164995)
                      ·
                        rfl

theorem cell23_178849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_178849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178849 prefixEnd_178849 := by exact prefixLift 178849
  have htrace : WordTrace (prefixWord ++ tailWord_178849) baseStart_178849 baseEnd_178849 := by
    simpa [prefixWord, tailWord_178849, baseEnd_178849] using wordTrace_append hprefix tailTrace_178849
  have hstable : (prefixWord ++ tailWord_178849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178849).length < 2 ^ (prefixWord ++ tailWord_178849).sum := by decide
  have hdescent : baseEnd_178849 < baseStart_178849 := by decide
  rcases family_descends (prefixWord ++ tailWord_178849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178928 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2]
def baseStart_178928 : Nat := 118140960795 + 178928 * 2 ^ 59
def prefixEnd_178928 : Nat := 4983230072969 + 3 ^ 40 * 178928 * 2
def baseEnd_178928 : Nat := 91876066547781177077131

theorem tailTrace_178928 : CollatzResearch.WordTrace tailWord_178928 prefixEnd_178928 91876066547781177077131 := by
  unfold tailWord_178928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263020147890944657312719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4350693530521259543083625 3263020147890944657312719)
  ·
    refine ⟨4894530221836416985969079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3263020147890944657312719 4894530221836416985969079)
    ·
      refine ⟨7341795332754625478953619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4894530221836416985969079 7341795332754625478953619)
      ·
        refine ⟨11012692999131938218430429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7341795332754625478953619 11012692999131938218430429)
        ·
          refine ⟨4129759874674476831911411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11012692999131938218430429 4129759874674476831911411)
          ·
            refine ⟨6194639812011715247867117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4129759874674476831911411 6194639812011715247867117)
            ·
              refine ⟨2322989929504393217950169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6194639812011715247867117 2322989929504393217950169)
              ·
                refine ⟨1742242447128294913462627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2322989929504393217950169 1742242447128294913462627)
                ·
                  refine ⟨2613363670692442370193941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742242447128294913462627 2613363670692442370193941)
                  ·
                    refine ⟨122501422063708236102841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2613363670692442370193941 122501422063708236102841)
                    ·
                      refine ⟨91876066547781177077131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122501422063708236102841 91876066547781177077131)
                      ·
                        rfl

theorem cell23_178928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 6, 2].length) (baseStart_178928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178928 prefixEnd_178928 := by exact prefixLift 178928
  have htrace : WordTrace (prefixWord ++ tailWord_178928) baseStart_178928 baseEnd_178928 := by
    simpa [prefixWord, tailWord_178928, baseEnd_178928] using wordTrace_append hprefix tailTrace_178928
  have hstable : (prefixWord ++ tailWord_178928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178928).length < 2 ^ (prefixWord ++ tailWord_178928).sum := by decide
  have hdescent : baseEnd_178928 < baseStart_178928 := by decide
  rcases family_descends (prefixWord ++ tailWord_178928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178941 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_178941 : Nat := 118140960795 + 178941 * 2 ^ 59
def prefixEnd_178941 : Nat := 4983230072969 + 3 ^ 40 * 178941 * 2
def baseEnd_178941 : Nat := 91882741796289626214571

theorem tailTrace_178941 : CollatzResearch.WordTrace tailWord_178941 prefixEnd_178941 91882741796289626214571 := by
  unfold tailWord_178941
  simp only [CollatzResearch.WordTrace]
  refine ⟨6526514444734792534848677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4351009629823195023232451 6526514444734792534848677)
  ·
    refine ⟨1223721458387773600284127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6526514444734792534848677 1223721458387773600284127)
    ·
      refine ⟨1835582187581660400426191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1223721458387773600284127 1835582187581660400426191)
      ·
        refine ⟨2753373281372490600639287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1835582187581660400426191 2753373281372490600639287)
        ·
          refine ⟨4130059922058735900958931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753373281372490600639287 4130059922058735900958931)
          ·
            refine ⟨6195089883088103851438397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130059922058735900958931 6195089883088103851438397)
            ·
              refine ⟨2323158706158038944289399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6195089883088103851438397 2323158706158038944289399)
              ·
                refine ⟨3484738059237058416434099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2323158706158038944289399 3484738059237058416434099)
                ·
                  refine ⟨5227107088855587624651149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3484738059237058416434099 5227107088855587624651149)
                  ·
                    refine ⟨1960165158320845359244181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5227107088855587624651149 1960165158320845359244181)
                    ·
                      refine ⟨91882741796289626214571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1960165158320845359244181 91882741796289626214571)
                      ·
                        rfl

theorem cell23_178941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_178941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178941 prefixEnd_178941 := by exact prefixLift 178941
  have htrace : WordTrace (prefixWord ++ tailWord_178941) baseStart_178941 baseEnd_178941 := by
    simpa [prefixWord, tailWord_178941, baseEnd_178941] using wordTrace_append hprefix tailTrace_178941
  have hstable : (prefixWord ++ tailWord_178941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178941).length < 2 ^ (prefixWord ++ tailWord_178941).sum := by decide
  have hdescent : baseEnd_178941 < baseStart_178941 := by decide
  rcases family_descends (prefixWord ++ tailWord_178941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178991 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5]
def baseStart_178991 : Nat := 118140960795 + 178991 * 2 ^ 59
def prefixEnd_178991 : Nat := 4983230072969 + 3 ^ 40 * 178991 * 2
def baseEnd_178991 : Nat := 91908415829014430589341

theorem tailTrace_178991 : CollatzResearch.WordTrace tailWord_178991 prefixEnd_178991 91908415829014430589341 := by
  unfold tailWord_178991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528338094553651074168827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4352225396369100716112551 6528338094553651074168827)
  ·
    refine ⟨9792507141830476611253241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6528338094553651074168827 9792507141830476611253241)
    ·
      refine ⟨7344380356372857458439931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9792507141830476611253241 7344380356372857458439931)
      ·
        refine ⟨11016570534559286187659897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7344380356372857458439931 11016570534559286187659897)
        ·
          refine ⟨8262427900919464640744923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11016570534559286187659897 8262427900919464640744923)
          ·
            refine ⟨12393641851379196961117385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262427900919464640744923 12393641851379196961117385)
            ·
              refine ⟨9295231388534397720838039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12393641851379196961117385 9295231388534397720838039)
              ·
                refine ⟨13942847082801596581257059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9295231388534397720838039 13942847082801596581257059)
                ·
                  refine ⟨20914270624202394871885589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13942847082801596581257059 20914270624202394871885589)
                  ·
                    refine ⟨980356435509487259619637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20914270624202394871885589 980356435509487259619637)
                    ·
                      refine ⟨91908415829014430589341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 980356435509487259619637 91908415829014430589341)
                      ·
                        rfl

theorem cell23_178991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_178991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178991 prefixEnd_178991 := by exact prefixLift 178991
  have htrace : WordTrace (prefixWord ++ tailWord_178991) baseStart_178991 baseEnd_178991 := by
    simpa [prefixWord, tailWord_178991, baseEnd_178991] using wordTrace_append hprefix tailTrace_178991
  have hstable : (prefixWord ++ tailWord_178991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178991).length < 2 ^ (prefixWord ++ tailWord_178991).sum := by decide
  have hdescent : baseEnd_178991 < baseStart_178991 := by decide
  rcases family_descends (prefixWord ++ tailWord_178991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179006 : List Nat := [4, 2, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_179006 : Nat := 118140960795 + 179006 * 2 ^ 59
def prefixEnd_179006 : Nat := 4983230072969 + 3 ^ 40 * 179006 * 2
def baseEnd_179006 : Nat := 30638706012943957300591

theorem tailTrace_179006 : CollatzResearch.WordTrace tailWord_179006 prefixEnd_179006 30638706012943957300591 := by
  unfold tailWord_179006
  simp only [CollatzResearch.WordTrace]
  refine ⟨816110648687413579495609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4352590126332872423976581 816110648687413579495609)
  ·
    refine ⟨612082986515560184621707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 816110648687413579495609 612082986515560184621707)
    ·
      refine ⟨918124479773340276932561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612082986515560184621707 918124479773340276932561)
      ·
        refine ⟨688593359830005207699421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918124479773340276932561 688593359830005207699421)
        ·
          refine ⟨258222509936251952887283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 688593359830005207699421 258222509936251952887283)
          ·
            refine ⟨387333764904377929330925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258222509936251952887283 387333764904377929330925)
            ·
              refine ⟨145250161839141723499097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 387333764904377929330925 145250161839141723499097)
              ·
                refine ⟨108937621379356292624323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145250161839141723499097 108937621379356292624323)
                ·
                  refine ⟨163406432069034438936485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108937621379356292624323 163406432069034438936485)
                  ·
                    refine ⟨30638706012943957300591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 163406432069034438936485 30638706012943957300591)
                    ·
                      rfl

theorem cell23_179006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_179006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179006 prefixEnd_179006 := by exact prefixLift 179006
  have htrace : WordTrace (prefixWord ++ tailWord_179006) baseStart_179006 baseEnd_179006 := by
    simpa [prefixWord, tailWord_179006, baseEnd_179006] using wordTrace_append hprefix tailTrace_179006
  have hstable : (prefixWord ++ tailWord_179006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179006).length < 2 ^ (prefixWord ++ tailWord_179006).sum := by decide
  have hdescent : baseEnd_179006 < baseStart_179006 := by decide
  rcases family_descends (prefixWord ++ tailWord_179006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179052 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_179052 : Nat := 118140960795 + 179052 * 2 ^ 59
def prefixEnd_179052 : Nat := 4983230072969 + 3 ^ 40 * 179052 * 2
def baseEnd_179052 : Nat := 91939738148938691926561

theorem tailTrace_179052 : CollatzResearch.WordTrace tailWord_179052 prefixEnd_179052 91939738148938691926561 := by
  unfold tailWord_179052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265281473666329246069705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4353708631555105661426273 3265281473666329246069705)
  ·
    refine ⟨2448961105249746934552279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3265281473666329246069705 2448961105249746934552279)
    ·
      refine ⟨3673441657874620401828419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2448961105249746934552279 3673441657874620401828419)
      ·
        refine ⟨5510162486811930602742629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3673441657874620401828419 5510162486811930602742629)
        ·
          refine ⟨1033155466277236988014243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5510162486811930602742629 1033155466277236988014243)
          ·
            refine ⟨1549733199415855482021365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033155466277236988014243 1549733199415855482021365)
            ·
              refine ⟨145287487445236451439503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1549733199415855482021365 145287487445236451439503)
              ·
                refine ⟨217931231167854677159255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145287487445236451439503 217931231167854677159255)
                ·
                  refine ⟨326896846751782015738883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217931231167854677159255 326896846751782015738883)
                  ·
                    refine ⟨490345270127673023608325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 326896846751782015738883 490345270127673023608325)
                    ·
                      refine ⟨91939738148938691926561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 490345270127673023608325 91939738148938691926561)
                      ·
                        rfl

theorem cell23_179052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_179052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179052 prefixEnd_179052 := by exact prefixLift 179052
  have htrace : WordTrace (prefixWord ++ tailWord_179052) baseStart_179052 baseEnd_179052 := by
    simpa [prefixWord, tailWord_179052, baseEnd_179052] using wordTrace_append hprefix tailTrace_179052
  have hstable : (prefixWord ++ tailWord_179052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179052).length < 2 ^ (prefixWord ++ tailWord_179052).sum := by decide
  have hdescent : baseEnd_179052 < baseStart_179052 := by decide
  rcases family_descends (prefixWord ++ tailWord_179052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179055 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 3]
def baseStart_179055 : Nat := 118140960795 + 179055 * 2 ^ 59
def prefixEnd_179055 : Nat := 4983230072969 + 3 ^ 40 * 179055 * 2
def baseEnd_179055 : Nat := 91941278590902180189047

theorem tailTrace_179055 : CollatzResearch.WordTrace tailWord_179055 prefixEnd_179055 91941278590902180189047 := by
  unfold tailWord_179055
  simp only [CollatzResearch.WordTrace]
  refine ⟨6530672366321790004498619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4353781577547860002999079 6530672366321790004498619)
  ·
    refine ⟨9796008549482685006747929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6530672366321790004498619 9796008549482685006747929)
    ·
      refine ⟨7347006412112013755060947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9796008549482685006747929 7347006412112013755060947)
      ·
        refine ⟨11020509618168020632591421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347006412112013755060947 11020509618168020632591421)
        ·
          refine ⟨4132691106813007737221783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11020509618168020632591421 4132691106813007737221783)
          ·
            refine ⟨6199036660219511605832675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4132691106813007737221783 6199036660219511605832675)
            ·
              refine ⟨9298554990329267408749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199036660219511605832675 9298554990329267408749013)
              ·
                refine ⟨217934882585842204892555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9298554990329267408749013 217934882585842204892555)
                ·
                  refine ⟨326902323878763307338833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217934882585842204892555 326902323878763307338833)
                  ·
                    refine ⟨245176742909072480504125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 326902323878763307338833 245176742909072480504125)
                    ·
                      refine ⟨91941278590902180189047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245176742909072480504125 91941278590902180189047)
                      ·
                        rfl

theorem cell23_179055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 2, 3].length) (baseStart_179055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179055 prefixEnd_179055 := by exact prefixLift 179055
  have htrace : WordTrace (prefixWord ++ tailWord_179055) baseStart_179055 baseEnd_179055 := by
    simpa [prefixWord, tailWord_179055, baseEnd_179055] using wordTrace_append hprefix tailTrace_179055
  have hstable : (prefixWord ++ tailWord_179055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179055).length < 2 ^ (prefixWord ++ tailWord_179055).sum := by decide
  have hdescent : baseEnd_179055 < baseStart_179055 := by decide
  rcases family_descends (prefixWord ++ tailWord_179055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179082 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_179082 : Nat := 118140960795 + 179082 * 2 ^ 59
def prefixEnd_179082 : Nat := 4983230072969 + 3 ^ 40 * 179082 * 2
def baseEnd_179082 : Nat := 91955142568573574551423

theorem tailTrace_179082 : CollatzResearch.WordTrace tailWord_179082 prefixEnd_179082 91955142568573574551423 := by
  unfold tailWord_179082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1632914284305993403932875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4354438091482649077154333 1632914284305993403932875)
  ·
    refine ⟨2449371426458990105899313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1632914284305993403932875 2449371426458990105899313)
    ·
      refine ⟨1837028569844242579424485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449371426458990105899313 1837028569844242579424485)
      ·
        refine ⟨344442856845795483642091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1837028569844242579424485 344442856845795483642091)
        ·
          refine ⟨516664285268693225463137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344442856845795483642091 516664285268693225463137)
          ·
            refine ⟨387498213951519919097353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516664285268693225463137 387498213951519919097353)
            ·
              refine ⟨290623660463639939323015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387498213951519919097353 290623660463639939323015)
              ·
                refine ⟨435935490695459908984523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290623660463639939323015 435935490695459908984523)
                ·
                  refine ⟨653903236043189863476785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435935490695459908984523 653903236043189863476785)
                  ·
                    refine ⟨490427427032392397607589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 653903236043189863476785 490427427032392397607589)
                    ·
                      refine ⟨91955142568573574551423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 490427427032392397607589 91955142568573574551423)
                      ·
                        rfl

theorem cell23_179082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_179082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179082 prefixEnd_179082 := by exact prefixLift 179082
  have htrace : WordTrace (prefixWord ++ tailWord_179082) baseStart_179082 baseEnd_179082 := by
    simpa [prefixWord, tailWord_179082, baseEnd_179082] using wordTrace_append hprefix tailTrace_179082
  have hstable : (prefixWord ++ tailWord_179082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179082).length < 2 ^ (prefixWord ++ tailWord_179082).sum := by decide
  have hdescent : baseEnd_179082 < baseStart_179082 := by decide
  rcases family_descends (prefixWord ++ tailWord_179082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179106 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_179106 : Nat := 118140960795 + 179106 * 2 ^ 59
def prefixEnd_179106 : Nat := 4983230072969 + 3 ^ 40 * 179106 * 2
def baseEnd_179106 : Nat := 91967466104281480651313

theorem tailTrace_179106 : CollatzResearch.WordTrace tailWord_179106 prefixEnd_179106 91967466104281480651313 := by
  unfold tailWord_179106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633133122284256428651293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4355021659424683809736781 1633133122284256428651293)
  ·
    refine ⟨612424920856596160744235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1633133122284256428651293 612424920856596160744235)
    ·
      refine ⟨918637381284894241116353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612424920856596160744235 918637381284894241116353)
      ·
        refine ⟨688978035963670680837265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 918637381284894241116353 688978035963670680837265)
        ·
          refine ⟨516733526972753010627949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 688978035963670680837265 516733526972753010627949)
          ·
            refine ⟨193775072614782378985481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 516733526972753010627949 193775072614782378985481)
            ·
              refine ⟨145331304461086784239111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193775072614782378985481 145331304461086784239111)
              ·
                refine ⟨217996956691630176358667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145331304461086784239111 217996956691630176358667)
                ·
                  refine ⟨326995435037445264538001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 217996956691630176358667 326995435037445264538001)
                  ·
                    refine ⟨245246576278083948403501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 326995435037445264538001 245246576278083948403501)
                    ·
                      refine ⟨91967466104281480651313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245246576278083948403501 91967466104281480651313)
                      ·
                        rfl

theorem cell23_179106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_179106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179106 prefixEnd_179106 := by exact prefixLift 179106
  have htrace : WordTrace (prefixWord ++ tailWord_179106) baseStart_179106 baseEnd_179106 := by
    simpa [prefixWord, tailWord_179106, baseEnd_179106] using wordTrace_append hprefix tailTrace_179106
  have hstable : (prefixWord ++ tailWord_179106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179106).length < 2 ^ (prefixWord ++ tailWord_179106).sum := by decide
  have hdescent : baseEnd_179106 < baseStart_179106 := by decide
  rcases family_descends (prefixWord ++ tailWord_179106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179168 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_179168 : Nat := 118140960795 + 179168 * 2 ^ 59
def prefixEnd_179168 : Nat := 4983230072969 + 3 ^ 40 * 179168 * 2
def baseEnd_179168 : Nat := 91999301904860238076027

theorem tailTrace_179168 : CollatzResearch.WordTrace tailWord_179168 prefixEnd_179168 91999301904860238076027 := by
  unfold tailWord_179168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267396907456205151681079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4356529209941606868908105 3267396907456205151681079)
  ·
    refine ⟨4901095361184307727521619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267396907456205151681079 4901095361184307727521619)
    ·
      refine ⟨7351643041776461591282429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901095361184307727521619 7351643041776461591282429)
      ·
        refine ⟨2756866140666173096730911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7351643041776461591282429 2756866140666173096730911)
        ·
          refine ⟨4135299210999259645096367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756866140666173096730911 4135299210999259645096367)
          ·
            refine ⟨6202948816498889467644551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135299210999259645096367 6202948816498889467644551)
            ·
              refine ⟨9304423224748334201466827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202948816498889467644551 9304423224748334201466827)
              ·
                refine ⟨13956634837122501302200241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304423224748334201466827 13956634837122501302200241)
                ·
                  refine ⟨10467476127841875976650181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13956634837122501302200241 10467476127841875976650181)
                  ·
                    refine ⟨1962651773970351745621909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10467476127841875976650181 1962651773970351745621909)
                    ·
                      refine ⟨91999301904860238076027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1962651773970351745621909 91999301904860238076027)
                      ·
                        rfl

theorem cell23_179168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_179168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179168 prefixEnd_179168 := by exact prefixLift 179168
  have htrace : WordTrace (prefixWord ++ tailWord_179168) baseStart_179168 baseEnd_179168 := by
    simpa [prefixWord, tailWord_179168, baseEnd_179168] using wordTrace_append hprefix tailTrace_179168
  have hstable : (prefixWord ++ tailWord_179168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179168).length < 2 ^ (prefixWord ++ tailWord_179168).sum := by decide
  have hdescent : baseEnd_179168 < baseStart_179168 := by decide
  rcases family_descends (prefixWord ++ tailWord_179168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179212 : List Nat := [2, 2, 1, 2, 3, 3, 2, 1, 2, 5]
def baseStart_179212 : Nat := 118140960795 + 179212 * 2 ^ 59
def prefixEnd_179212 : Nat := 4983230072969 + 3 ^ 40 * 179212 * 2
def baseEnd_179212 : Nat := 30673965017886021975275

theorem tailTrace_179212 : CollatzResearch.WordTrace tailWord_179212 prefixEnd_179212 30673965017886021975275 := by
  unfold tailWord_179212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268199313376502908981945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4357599084502003878642593 3268199313376502908981945)
  ·
    refine ⟨2451149485032377181736459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268199313376502908981945 2451149485032377181736459)
    ·
      refine ⟨3676724227548565772604689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451149485032377181736459 3676724227548565772604689)
      ·
        refine ⟨2757543170661424329453517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3676724227548565772604689 2757543170661424329453517)
        ·
          refine ⟨1034078688998034123545069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2757543170661424329453517 1034078688998034123545069)
          ·
            refine ⟨387779508374262796329401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1034078688998034123545069 387779508374262796329401)
            ·
              refine ⟨290834631280697097247051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387779508374262796329401 290834631280697097247051)
              ·
                refine ⟨436251946921045645870577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290834631280697097247051 436251946921045645870577)
                ·
                  refine ⟨327188960190784234402933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436251946921045645870577 327188960190784234402933)
                  ·
                    refine ⟨30673965017886021975275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327188960190784234402933 30673965017886021975275)
                    ·
                      rfl

theorem cell23_179212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_179212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179212 prefixEnd_179212 := by exact prefixLift 179212
  have htrace : WordTrace (prefixWord ++ tailWord_179212) baseStart_179212 baseEnd_179212 := by
    simpa [prefixWord, tailWord_179212, baseEnd_179212] using wordTrace_append hprefix tailTrace_179212
  have hstable : (prefixWord ++ tailWord_179212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179212).length < 2 ^ (prefixWord ++ tailWord_179212).sum := by decide
  have hdescent : baseEnd_179212 < baseStart_179212 := by decide
  rcases family_descends (prefixWord ++ tailWord_179212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179309 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_179309 : Nat := 118140960795 + 179309 * 2 ^ 59
def prefixEnd_179309 : Nat := 4983230072969 + 3 ^ 40 * 179309 * 2
def baseEnd_179309 : Nat := 92071702677144186412879

theorem tailTrace_179309 : CollatzResearch.WordTrace tailWord_179309 prefixEnd_179309 92071702677144186412879 := by
  unfold tailWord_179309
  simp only [CollatzResearch.WordTrace]
  refine ⟨6539936507401591384244981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4359957671601060922829987 6539936507401591384244981)
  ·
    refine ⟨613119047568899192272967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6539936507401591384244981 613119047568899192272967)
    ·
      refine ⟨919678571353348788409451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613119047568899192272967 919678571353348788409451)
      ·
        refine ⟨1379517857030023182614177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919678571353348788409451 1379517857030023182614177)
        ·
          refine ⟨1034638392772517386960633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1379517857030023182614177 1034638392772517386960633)
          ·
            refine ⟨775978794579388040220475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034638392772517386960633 775978794579388040220475)
            ·
              refine ⟨1163968191869082060330713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775978794579388040220475 1163968191869082060330713)
              ·
                refine ⟨872976143901811545248035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163968191869082060330713 872976143901811545248035)
                ·
                  refine ⟨1309464215852717317872053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872976143901811545248035 1309464215852717317872053)
                  ·
                    refine ⟨122762270236192248550505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1309464215852717317872053 122762270236192248550505)
                    ·
                      refine ⟨92071702677144186412879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122762270236192248550505 92071702677144186412879)
                      ·
                        rfl

theorem cell23_179309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_179309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179309 prefixEnd_179309 := by exact prefixLift 179309
  have htrace : WordTrace (prefixWord ++ tailWord_179309) baseStart_179309 baseEnd_179309 := by
    simpa [prefixWord, tailWord_179309, baseEnd_179309] using wordTrace_append hprefix tailTrace_179309
  have hstable : (prefixWord ++ tailWord_179309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179309).length < 2 ^ (prefixWord ++ tailWord_179309).sum := by decide
  have hdescent : baseEnd_179309 < baseStart_179309 := by decide
  rcases family_descends (prefixWord ++ tailWord_179309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179339 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 5, 2, 2]
def baseStart_179339 : Nat := 118140960795 + 179339 * 2 ^ 59
def prefixEnd_179339 : Nat := 4983230072969 + 3 ^ 40 * 179339 * 2
def baseEnd_179339 : Nat := 92087107096779069037741

theorem tailTrace_179339 : CollatzResearch.WordTrace tailWord_179339 prefixEnd_179339 92087107096779069037741 := by
  unfold tailWord_179339
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541030697292906507837071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4360687131528604338558047 6541030697292906507837071)
  ·
    refine ⟨9811546045939359761755607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6541030697292906507837071 9811546045939359761755607)
    ·
      refine ⟨14717319068909039642633411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9811546045939359761755607 14717319068909039642633411)
      ·
        refine ⟨22075978603363559463950117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14717319068909039642633411 22075978603363559463950117)
        ·
          refine ⟨4139245988130667399490647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22075978603363559463950117 4139245988130667399490647)
          ·
            refine ⟨6208868982196001099235971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139245988130667399490647 6208868982196001099235971)
            ·
              refine ⟨9313303473294001648853957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208868982196001099235971 9313303473294001648853957)
              ·
                refine ⟨1746244401242625309160117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9313303473294001648853957 1746244401242625309160117)
                ·
                  refine ⟨163710412616496122733761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1746244401242625309160117 163710412616496122733761)
                  ·
                    refine ⟨122782809462372092050321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163710412616496122733761 122782809462372092050321)
                    ·
                      refine ⟨92087107096779069037741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122782809462372092050321 92087107096779069037741)
                      ·
                        rfl

theorem cell23_179339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 2, 2].length) (baseStart_179339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179339 prefixEnd_179339 := by exact prefixLift 179339
  have htrace : WordTrace (prefixWord ++ tailWord_179339) baseStart_179339 baseEnd_179339 := by
    simpa [prefixWord, tailWord_179339, baseEnd_179339] using wordTrace_append hprefix tailTrace_179339
  have hstable : (prefixWord ++ tailWord_179339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179339).length < 2 ^ (prefixWord ++ tailWord_179339).sum := by decide
  have hdescent : baseEnd_179339 < baseStart_179339 := by decide
  rcases family_descends (prefixWord ++ tailWord_179339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179352 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_179352 : Nat := 118140960795 + 179352 * 2 ^ 59
def prefixEnd_179352 : Nat := 4983230072969 + 3 ^ 40 * 179352 * 2
def baseEnd_179352 : Nat := 92093782345287518175181

theorem tailTrace_179352 : CollatzResearch.WordTrace tailWord_179352 prefixEnd_179352 92093782345287518175181 := by
  unfold tailWord_179352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270752423122904864030155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4361003230830539818706873 3270752423122904864030155)
  ·
    refine ⟨4906128634684357296045233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3270752423122904864030155 4906128634684357296045233)
    ·
      refine ⟨3679596476013267972033925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4906128634684357296045233 3679596476013267972033925)
      ·
        refine ⟨689924339252487744756361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3679596476013267972033925 689924339252487744756361)
        ·
          refine ⟨517443254439365808567271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689924339252487744756361 517443254439365808567271)
          ·
            refine ⟨776164881659048712850907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517443254439365808567271 776164881659048712850907)
            ·
              refine ⟨1164247322488573069276361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776164881659048712850907 1164247322488573069276361)
              ·
                refine ⟨873185491866429801957271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164247322488573069276361 873185491866429801957271)
                ·
                  refine ⟨1309778237799644702935907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873185491866429801957271 1309778237799644702935907)
                  ·
                    refine ⟨1964667356699467054403861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1309778237799644702935907 1964667356699467054403861)
                    ·
                      refine ⟨92093782345287518175181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1964667356699467054403861 92093782345287518175181)
                      ·
                        rfl

theorem cell23_179352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_179352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179352 prefixEnd_179352 := by exact prefixLift 179352
  have htrace : WordTrace (prefixWord ++ tailWord_179352) baseStart_179352 baseEnd_179352 := by
    simpa [prefixWord, tailWord_179352, baseEnd_179352] using wordTrace_append hprefix tailTrace_179352
  have hstable : (prefixWord ++ tailWord_179352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179352).length < 2 ^ (prefixWord ++ tailWord_179352).sum := by decide
  have hdescent : baseEnd_179352 < baseStart_179352 := by decide
  rcases family_descends (prefixWord ++ tailWord_179352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179373 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_179373 : Nat := 118140960795 + 179373 * 2 ^ 59
def prefixEnd_179373 : Nat := 4983230072969 + 3 ^ 40 * 179373 * 2
def baseEnd_179373 : Nat := 92104565439031936012585

theorem tailTrace_179373 : CollatzResearch.WordTrace tailWord_179373 prefixEnd_179373 92104565439031936012585 := by
  unfold tailWord_179373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542270779169730314574773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4361513852779820209716515 6542270779169730314574773)
  ·
    refine ⟨613337885547162216991385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6542270779169730314574773 613337885547162216991385)
    ·
      refine ⟨460003414160371662743539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 613337885547162216991385 460003414160371662743539)
      ·
        refine ⟨690005121240557494115309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460003414160371662743539 690005121240557494115309)
        ·
          refine ⟨258751920465209060293241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 690005121240557494115309 258751920465209060293241)
          ·
            refine ⟨194063940348906795219931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258751920465209060293241 194063940348906795219931)
            ·
              refine ⟨291095910523360192829897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194063940348906795219931 291095910523360192829897)
              ·
                refine ⟨218321932892520144622423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291095910523360192829897 218321932892520144622423)
                ·
                  refine ⟨327482899338780216933635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218321932892520144622423 327482899338780216933635)
                  ·
                    refine ⟨491224349008170325400453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327482899338780216933635 491224349008170325400453)
                    ·
                      refine ⟨92104565439031936012585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 491224349008170325400453 92104565439031936012585)
                      ·
                        rfl

theorem cell23_179373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_179373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179373 prefixEnd_179373 := by exact prefixLift 179373
  have htrace : WordTrace (prefixWord ++ tailWord_179373) baseStart_179373 baseEnd_179373 := by
    simpa [prefixWord, tailWord_179373, baseEnd_179373] using wordTrace_append hprefix tailTrace_179373
  have hstable : (prefixWord ++ tailWord_179373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179373).length < 2 ^ (prefixWord ++ tailWord_179373).sum := by decide
  have hdescent : baseEnd_179373 < baseStart_179373 := by decide
  rcases family_descends (prefixWord ++ tailWord_179373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179389 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_179389 : Nat := 118140960795 + 179389 * 2 ^ 59
def prefixEnd_179389 : Nat := 4983230072969 + 3 ^ 40 * 179389 * 2
def baseEnd_179389 : Nat := 92112781129503873412511

theorem tailTrace_179389 : CollatzResearch.WordTrace tailWord_179389 prefixEnd_179389 92112781129503873412511 := by
  unfold tailWord_179389
  simp only [CollatzResearch.WordTrace]
  refine ⟨6542854347111765047157221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4361902898074510031438147 6542854347111765047157221)
  ·
    refine ⟨1226785190083455946341979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6542854347111765047157221 1226785190083455946341979)
    ·
      refine ⟨1840177785125183919512969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226785190083455946341979 1840177785125183919512969)
      ·
        refine ⟨1380133338843887939634727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1840177785125183919512969 1380133338843887939634727)
        ·
          refine ⟨2070200008265831909452091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380133338843887939634727 2070200008265831909452091)
          ·
            refine ⟨3105300012398747864178137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070200008265831909452091 3105300012398747864178137)
            ·
              refine ⟨2328975009299060898133603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3105300012398747864178137 2328975009299060898133603)
              ·
                refine ⟨3493462513948591347200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2328975009299060898133603 3493462513948591347200405)
                ·
                  refine ⟨163756055341340219400019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3493462513948591347200405 163756055341340219400019)
                  ·
                    refine ⟨245634083012010329100029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163756055341340219400019 245634083012010329100029)
                    ·
                      refine ⟨92112781129503873412511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245634083012010329100029 92112781129503873412511)
                      ·
                        rfl

theorem cell23_179389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_179389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179389 prefixEnd_179389 := by exact prefixLift 179389
  have htrace : WordTrace (prefixWord ++ tailWord_179389) baseStart_179389 baseEnd_179389 := by
    simpa [prefixWord, tailWord_179389, baseEnd_179389] using wordTrace_append hprefix tailTrace_179389
  have hstable : (prefixWord ++ tailWord_179389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179389).length < 2 ^ (prefixWord ++ tailWord_179389).sum := by decide
  have hdescent : baseEnd_179389 < baseStart_179389 := by decide
  rcases family_descends (prefixWord ++ tailWord_179389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179444 : List Nat := [2, 6, 1, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_179444 : Nat := 118140960795 + 179444 * 2 ^ 59
def prefixEnd_179444 : Nat := 4983230072969 + 3 ^ 40 * 179444 * 2
def baseEnd_179444 : Nat := 92141022565501158224759

theorem tailTrace_179444 : CollatzResearch.WordTrace tailWord_179444 prefixEnd_179444 92141022565501158224759 := by
  unfold tailWord_179444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272430180956254720204693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4363240241275006293606257 3272430180956254720204693)
  ·
    refine ⟨153395164732324440009595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3272430180956254720204693 153395164732324440009595)
    ·
      refine ⟨230092747098486660014393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153395164732324440009595 230092747098486660014393)
      ·
        refine ⟨172569560323864995010795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230092747098486660014393 172569560323864995010795)
        ·
          refine ⟨258854340485797492516193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172569560323864995010795 258854340485797492516193)
          ·
            refine ⟨194140755364348119387145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258854340485797492516193 194140755364348119387145)
            ·
              refine ⟨145605566523261089540359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194140755364348119387145 145605566523261089540359)
              ·
                refine ⟨218408349784891634310539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145605566523261089540359 218408349784891634310539)
                ·
                  refine ⟨327612524677337451465809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218408349784891634310539 327612524677337451465809)
                  ·
                    refine ⟨245709393508003088599357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327612524677337451465809 245709393508003088599357)
                    ·
                      refine ⟨92141022565501158224759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245709393508003088599357 92141022565501158224759)
                      ·
                        rfl

theorem cell23_179444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_179444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179444 prefixEnd_179444 := by exact prefixLift 179444
  have htrace : WordTrace (prefixWord ++ tailWord_179444) baseStart_179444 baseEnd_179444 := by
    simpa [prefixWord, tailWord_179444, baseEnd_179444] using wordTrace_append hprefix tailTrace_179444
  have hstable : (prefixWord ++ tailWord_179444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179444).length < 2 ^ (prefixWord ++ tailWord_179444).sum := by decide
  have hdescent : baseEnd_179444 < baseStart_179444 := by decide
  rcases family_descends (prefixWord ++ tailWord_179444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179479 : List Nat := [1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3]
def baseStart_179479 : Nat := 118140960795 + 179479 * 2 ^ 59
def prefixEnd_179479 : Nat := 4983230072969 + 3 ^ 40 * 179479 * 2
def baseEnd_179479 : Nat := 92158994388408521287097

theorem tailTrace_179479 : CollatzResearch.WordTrace tailWord_179479 prefixEnd_179479 92158994388408521287097 := by
  unfold tailWord_179479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6546136916785710417933491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4364091277857140278622327 6546136916785710417933491)
  ·
    refine ⟨9819205375178565626900237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6546136916785710417933491 9819205375178565626900237)
    ·
      refine ⟨3682202015691962110087589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9819205375178565626900237 3682202015691962110087589)
      ·
        refine ⟨690412877942242895641423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3682202015691962110087589 690412877942242895641423)
        ·
          refine ⟨1035619316913364343462135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690412877942242895641423 1035619316913364343462135)
          ·
            refine ⟨1553428975370046515193203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035619316913364343462135 1553428975370046515193203)
            ·
              refine ⟨2330143463055069772789805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553428975370046515193203 2330143463055069772789805)
              ·
                refine ⟨873803798645651164796177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2330143463055069772789805 873803798645651164796177)
                ·
                  refine ⟨655352848984238373597133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873803798645651164796177 655352848984238373597133)
                  ·
                    refine ⟨245757318369089390098925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655352848984238373597133 245757318369089390098925)
                    ·
                      refine ⟨92158994388408521287097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245757318369089390098925 92158994388408521287097)
                      ·
                        rfl

theorem cell23_179479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_179479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179479 prefixEnd_179479 := by exact prefixLift 179479
  have htrace : WordTrace (prefixWord ++ tailWord_179479) baseStart_179479 baseEnd_179479 := by
    simpa [prefixWord, tailWord_179479, baseEnd_179479] using wordTrace_append hprefix tailTrace_179479
  have hstable : (prefixWord ++ tailWord_179479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179479).length < 2 ^ (prefixWord ++ tailWord_179479).sum := by decide
  have hdescent : baseEnd_179479 < baseStart_179479 := by decide
  rcases family_descends (prefixWord ++ tailWord_179479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179480 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2]
def baseStart_179480 : Nat := 118140960795 + 179480 * 2 ^ 59
def prefixEnd_179480 : Nat := 4983230072969 + 3 ^ 40 * 179480 * 2
def baseEnd_179480 : Nat := 92159507869063017374593

theorem tailTrace_179480 : CollatzResearch.WordTrace tailWord_179480 prefixEnd_179480 92159507869063017374593 := by
  unfold tailWord_179480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273086694891043794359947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4364115593188058392479929 3273086694891043794359947)
  ·
    refine ⟨4909630042336565691539921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273086694891043794359947 4909630042336565691539921)
    ·
      refine ⟨3682222531752424268654941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4909630042336565691539921 3682222531752424268654941)
      ·
        refine ⟨1380833449407159100745603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3682222531752424268654941 1380833449407159100745603)
        ·
          refine ⟨2071250174110738651118405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380833449407159100745603 2071250174110738651118405)
          ·
            refine ⟨388359407645763497084701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2071250174110738651118405 388359407645763497084701)
            ·
              refine ⟨145634777867161311406763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388359407645763497084701 145634777867161311406763)
              ·
                refine ⟨218452166800741967110145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145634777867161311406763 218452166800741967110145)
                ·
                  refine ⟨163839125100556475332609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 218452166800741967110145 163839125100556475332609)
                  ·
                    refine ⟨122879343825417356499457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 163839125100556475332609 122879343825417356499457)
                    ·
                      refine ⟨92159507869063017374593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122879343825417356499457 92159507869063017374593)
                      ·
                        rfl

theorem cell23_179480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_179480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179480 prefixEnd_179480 := by exact prefixLift 179480
  have htrace : WordTrace (prefixWord ++ tailWord_179480) baseStart_179480 baseEnd_179480 := by
    simpa [prefixWord, tailWord_179480, baseEnd_179480] using wordTrace_append hprefix tailTrace_179480
  have hstable : (prefixWord ++ tailWord_179480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179480).length < 2 ^ (prefixWord ++ tailWord_179480).sum := by decide
  have hdescent : baseEnd_179480 < baseStart_179480 := by decide
  rcases family_descends (prefixWord ++ tailWord_179480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179519 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4]
def baseStart_179519 : Nat := 118140960795 + 179519 * 2 ^ 59
def prefixEnd_179519 : Nat := 4983230072969 + 3 ^ 40 * 179519 * 2
def baseEnd_179519 : Nat := 92179533614588364786913

theorem tailTrace_179519 : CollatzResearch.WordTrace tailWord_179519 prefixEnd_179519 92179533614588364786913 := by
  unfold tailWord_179519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547595836640797249389611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4365063891093864832926407 6547595836640797249389611)
  ·
    refine ⟨9821393754961195874084417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6547595836640797249389611 9821393754961195874084417)
    ·
      refine ⟨7366045316220896905563313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9821393754961195874084417 7366045316220896905563313)
      ·
        refine ⟨5524533987165672679172485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366045316220896905563313 5524533987165672679172485)
        ·
          refine ⟨1035850122593563627344841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5524533987165672679172485 1035850122593563627344841)
          ·
            refine ⟨776887591945172720508631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035850122593563627344841 776887591945172720508631)
            ·
              refine ⟨1165331387917759080762947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776887591945172720508631 1165331387917759080762947)
              ·
                refine ⟨1747997081876638621144421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165331387917759080762947 1747997081876638621144421)
                ·
                  refine ⟨327749452851869741464579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1747997081876638621144421 327749452851869741464579)
                  ·
                    refine ⟨491624179277804612196869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 327749452851869741464579 491624179277804612196869)
                    ·
                      refine ⟨92179533614588364786913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 491624179277804612196869 92179533614588364786913)
                      ·
                        rfl

theorem cell23_179519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_179519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179519 prefixEnd_179519 := by exact prefixLift 179519
  have htrace : WordTrace (prefixWord ++ tailWord_179519) baseStart_179519 baseEnd_179519 := by
    simpa [prefixWord, tailWord_179519, baseEnd_179519] using wordTrace_append hprefix tailTrace_179519
  have hstable : (prefixWord ++ tailWord_179519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179519).length < 2 ^ (prefixWord ++ tailWord_179519).sum := by decide
  have hdescent : baseEnd_179519 < baseStart_179519 := by decide
  rcases family_descends (prefixWord ++ tailWord_179519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179539 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3]
def baseStart_179539 : Nat := 118140960795 + 179539 * 2 ^ 59
def prefixEnd_179539 : Nat := 4983230072969 + 3 ^ 40 * 179539 * 2
def baseEnd_179539 : Nat := 92189803227678286536821

theorem tailTrace_179539 : CollatzResearch.WordTrace tailWord_179539 prefixEnd_179539 92189803227678286536821 := by
  unfold tailWord_179539
  simp only [CollatzResearch.WordTrace]
  refine ⟨6548325296568340665117671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4365550197712227110078447 6548325296568340665117671)
  ·
    refine ⟨9822487944852510997676507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6548325296568340665117671 9822487944852510997676507)
    ·
      refine ⟨14733731917278766496514761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9822487944852510997676507 14733731917278766496514761)
      ·
        refine ⟨11050298937959074872386071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14733731917278766496514761 11050298937959074872386071)
        ·
          refine ⟨16575448406938612308579107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11050298937959074872386071 16575448406938612308579107)
          ·
            refine ⟨24863172610407918462868661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16575448406938612308579107 24863172610407918462868661)
            ·
              refine ⟨2330922432225742355893937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24863172610407918462868661 2330922432225742355893937)
              ·
                refine ⟨1748191824169306766920453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2330922432225742355893937 1748191824169306766920453)
                ·
                  refine ⟨327785967031745018797585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1748191824169306766920453 327785967031745018797585)
                  ·
                    refine ⟨245839475273808764098189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327785967031745018797585 245839475273808764098189)
                    ·
                      refine ⟨92189803227678286536821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245839475273808764098189 92189803227678286536821)
                      ·
                        rfl

theorem cell23_179539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_179539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179539 prefixEnd_179539 := by exact prefixLift 179539
  have htrace : WordTrace (prefixWord ++ tailWord_179539) baseStart_179539 baseEnd_179539 := by
    simpa [prefixWord, tailWord_179539, baseEnd_179539] using wordTrace_append hprefix tailTrace_179539
  have hstable : (prefixWord ++ tailWord_179539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179539).length < 2 ^ (prefixWord ++ tailWord_179539).sum := by decide
  have hdescent : baseEnd_179539 < baseStart_179539 := by decide
  rcases family_descends (prefixWord ++ tailWord_179539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179556 : List Nat := [2, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_179556 : Nat := 118140960795 + 179556 * 2 ^ 59
def prefixEnd_179556 : Nat := 4983230072969 + 3 ^ 40 * 179556 * 2
def baseEnd_179556 : Nat := 92198532398804720024243

theorem tailTrace_179556 : CollatzResearch.WordTrace tailWord_179556 prefixEnd_179556 92198532398804720024243 := by
  unfold tailWord_179556
  simp only [CollatzResearch.WordTrace]
  refine ⟨3274472668753376284243261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4365963558337835045657681 3274472668753376284243261)
  ·
    refine ⟨1227927250782516106591223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3274472668753376284243261 1227927250782516106591223)
    ·
      refine ⟨1841890876173774159886835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1227927250782516106591223 1841890876173774159886835)
      ·
        refine ⟨2762836314260661239830253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841890876173774159886835 2762836314260661239830253)
        ·
          refine ⟨1036063617847747964936345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762836314260661239830253 1036063617847747964936345)
          ·
            refine ⟨777047713385810973702259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036063617847747964936345 777047713385810973702259)
            ·
              refine ⟨1165571570078716460553389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777047713385810973702259 1165571570078716460553389)
              ·
                refine ⟨437089338779518672707521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165571570078716460553389 437089338779518672707521)
                ·
                  refine ⟨327817004084639004530641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437089338779518672707521 327817004084639004530641)
                  ·
                    refine ⟨245862753063479253397981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 327817004084639004530641 245862753063479253397981)
                    ·
                      refine ⟨92198532398804720024243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 245862753063479253397981 92198532398804720024243)
                      ·
                        rfl

theorem cell23_179556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_179556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179556 prefixEnd_179556 := by exact prefixLift 179556
  have htrace : WordTrace (prefixWord ++ tailWord_179556) baseStart_179556 baseEnd_179556 := by
    simpa [prefixWord, tailWord_179556, baseEnd_179556] using wordTrace_append hprefix tailTrace_179556
  have hstable : (prefixWord ++ tailWord_179556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179556).length < 2 ^ (prefixWord ++ tailWord_179556).sum := by decide
  have hdescent : baseEnd_179556 < baseStart_179556 := by decide
  rcases family_descends (prefixWord ++ tailWord_179556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179589 : List Nat := [1, 3, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_179589 : Nat := 118140960795 + 179589 * 2 ^ 59
def prefixEnd_179589 : Nat := 4983230072969 + 3 ^ 40 * 179589 * 2
def baseEnd_179589 : Nat := 30738492420134363637197

theorem tailTrace_179589 : CollatzResearch.WordTrace tailWord_179589 prefixEnd_179589 30738492420134363637197 := by
  unfold tailWord_179589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550148946387199204437821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4366765964258132802958547 6550148946387199204437821)
  ·
    refine ⟨2456305854895199701664183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6550148946387199204437821 2456305854895199701664183)
    ·
      refine ⟨3684458782342799552496275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456305854895199701664183 3684458782342799552496275)
      ·
        refine ⟨5526688173514199328744413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3684458782342799552496275 5526688173514199328744413)
        ·
          refine ⟨2072508065067824748279155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5526688173514199328744413 2072508065067824748279155)
          ·
            refine ⟨3108762097601737122418733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072508065067824748279155 3108762097601737122418733)
            ·
              refine ⟨1165785786600651420907025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108762097601737122418733 1165785786600651420907025)
              ·
                refine ⟨874339339950488565680269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165785786600651420907025 874339339950488565680269)
                ·
                  refine ⟨327877252481433212130101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874339339950488565680269 327877252481433212130101)
                  ·
                    refine ⟨30738492420134363637197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 327877252481433212130101 30738492420134363637197)
                    ·
                      rfl

theorem cell23_179589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_179589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179589 prefixEnd_179589 := by exact prefixLift 179589
  have htrace : WordTrace (prefixWord ++ tailWord_179589) baseStart_179589 baseEnd_179589 := by
    simpa [prefixWord, tailWord_179589, baseEnd_179589] using wordTrace_append hprefix tailTrace_179589
  have hstable : (prefixWord ++ tailWord_179589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179589).length < 2 ^ (prefixWord ++ tailWord_179589).sum := by decide
  have hdescent : baseEnd_179589 < baseStart_179589 := by decide
  rcases family_descends (prefixWord ++ tailWord_179589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179596 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_179596 : Nat := 118140960795 + 179596 * 2 ^ 59
def prefixEnd_179596 : Nat := 4983230072969 + 3 ^ 40 * 179596 * 2
def baseEnd_179596 : Nat := 92219071624984563524059

theorem tailTrace_179596 : CollatzResearch.WordTrace tailWord_179596 prefixEnd_179596 92219071624984563524059 := by
  unfold tailWord_179596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3275202128680919699971321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4366936171574559599961761 3275202128680919699971321)
  ·
    refine ⟨2456401596510689774978491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3275202128680919699971321 2456401596510689774978491)
    ·
      refine ⟨3684602394766034662467737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456401596510689774978491 3684602394766034662467737)
      ·
        refine ⟨2763451796074525996850803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684602394766034662467737 2763451796074525996850803)
        ·
          refine ⟨4145177694111788995276205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763451796074525996850803 4145177694111788995276205)
          ·
            refine ⟨1554441635291920873228577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145177694111788995276205 1554441635291920873228577)
            ·
              refine ⟨1165831226468940654921433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554441635291920873228577 1165831226468940654921433)
              ·
                refine ⟨874373419851705491191075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165831226468940654921433 874373419851705491191075)
                ·
                  refine ⟨1311560129777558236786613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874373419851705491191075 1311560129777558236786613)
                  ·
                    refine ⟨122958762166646084698745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1311560129777558236786613 122958762166646084698745)
                    ·
                      refine ⟨92219071624984563524059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122958762166646084698745 92219071624984563524059)
                      ·
                        rfl

theorem cell23_179596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_179596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179596 prefixEnd_179596 := by exact prefixLift 179596
  have htrace : WordTrace (prefixWord ++ tailWord_179596) baseStart_179596 baseEnd_179596 := by
    simpa [prefixWord, tailWord_179596, baseEnd_179596] using wordTrace_append hprefix tailTrace_179596
  have hstable : (prefixWord ++ tailWord_179596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179596).length < 2 ^ (prefixWord ++ tailWord_179596).sum := by decide
  have hdescent : baseEnd_179596 < baseStart_179596 := by decide
  rcases family_descends (prefixWord ++ tailWord_179596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179613 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_179613 : Nat := 118140960795 + 179613 * 2 ^ 59
def prefixEnd_179613 : Nat := 4983230072969 + 3 ^ 40 * 179613 * 2
def baseEnd_179613 : Nat := 92227800796110997011481

theorem tailTrace_179613 : CollatzResearch.WordTrace tailWord_179613 prefixEnd_179613 92227800796110997011481 := by
  unfold tailWord_179613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551024298300251303311493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367349532200167535540995 6551024298300251303311493)
  ·
    refine ⟨1228317055931297119370905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6551024298300251303311493 1228317055931297119370905)
    ·
      refine ⟨921237791948472839528179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228317055931297119370905 921237791948472839528179)
      ·
        refine ⟨1381856687922709259292269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921237791948472839528179 1381856687922709259292269)
        ·
          refine ⟨518196257971015972234601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381856687922709259292269 518196257971015972234601)
          ·
            refine ⟨388647193478261979175951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518196257971015972234601 388647193478261979175951)
            ·
              refine ⟨582970790217392968763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388647193478261979175951 582970790217392968763927)
              ·
                refine ⟨874456185326089453145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582970790217392968763927 874456185326089453145891)
                ·
                  refine ⟨1311684277989134179718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874456185326089453145891 1311684277989134179718837)
                  ·
                    refine ⟨122970401061481329348641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1311684277989134179718837 122970401061481329348641)
                    ·
                      refine ⟨92227800796110997011481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 122970401061481329348641 92227800796110997011481)
                      ·
                        rfl

theorem cell23_179613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_179613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179613 prefixEnd_179613 := by exact prefixLift 179613
  have htrace : WordTrace (prefixWord ++ tailWord_179613) baseStart_179613 baseEnd_179613 := by
    simpa [prefixWord, tailWord_179613, baseEnd_179613] using wordTrace_append hprefix tailTrace_179613
  have hstable : (prefixWord ++ tailWord_179613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179613).length < 2 ^ (prefixWord ++ tailWord_179613).sum := by decide
  have hdescent : baseEnd_179613 < baseStart_179613 := by decide
  rcases family_descends (prefixWord ++ tailWord_179613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179619 : List Nat := [1, 1, 1, 4, 1, 3, 1, 4, 1, 6]
def baseStart_179619 : Nat := 118140960795 + 179619 * 2 ^ 59
def prefixEnd_179619 : Nat := 4983230072969 + 3 ^ 40 * 179619 * 2
def baseEnd_179619 : Nat := 30743627226679324512151

theorem tailTrace_179619 : CollatzResearch.WordTrace tailWord_179619 prefixEnd_179619 30743627226679324512151 := by
  unfold tailWord_179619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551243136278514328029911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367495424185676218686607 6551243136278514328029911)
  ·
    refine ⟨9826864704417771492044867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551243136278514328029911 9826864704417771492044867)
    ·
      refine ⟨14740297056626657238067301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9826864704417771492044867 14740297056626657238067301)
      ·
        refine ⟨2763805698117498232137619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14740297056626657238067301 2763805698117498232137619)
        ·
          refine ⟨4145708547176247348206429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763805698117498232137619 4145708547176247348206429)
          ·
            refine ⟨1554640705191092755577411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145708547176247348206429 1554640705191092755577411)
            ·
              refine ⟨2331961057786639133366117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554640705191092755577411 2331961057786639133366117)
              ·
                refine ⟨437242698334994837506147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2331961057786639133366117 437242698334994837506147)
                ·
                  refine ⟨655864047502492256259221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437242698334994837506147 655864047502492256259221)
                  ·
                    refine ⟨30743627226679324512151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 655864047502492256259221 30743627226679324512151)
                    ·
                      rfl

theorem cell23_179619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 6].length) (baseStart_179619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179619 prefixEnd_179619 := by exact prefixLift 179619
  have htrace : WordTrace (prefixWord ++ tailWord_179619) baseStart_179619 baseEnd_179619 := by
    simpa [prefixWord, tailWord_179619, baseEnd_179619] using wordTrace_append hprefix tailTrace_179619
  have hstable : (prefixWord ++ tailWord_179619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179619).length < 2 ^ (prefixWord ++ tailWord_179619).sum := by decide
  have hdescent : baseEnd_179619 < baseStart_179619 := by decide
  rcases family_descends (prefixWord ++ tailWord_179619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179639 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_179639 : Nat := 118140960795 + 179639 * 2 ^ 59
def prefixEnd_179639 : Nat := 4983230072969 + 3 ^ 40 * 179639 * 2
def baseEnd_179639 : Nat := 92241151293127895286361

theorem tailTrace_179639 : CollatzResearch.WordTrace tailWord_179639 prefixEnd_179639 92241151293127895286361 := by
  unfold tailWord_179639
  simp only [CollatzResearch.WordTrace]
  refine ⟨6551972596206057743757971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4367981730804038495838647 6551972596206057743757971)
  ·
    refine ⟨9827958894309086615636957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6551972596206057743757971 9827958894309086615636957)
    ·
      refine ⟨3685484585365907480863859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9827958894309086615636957 3685484585365907480863859)
      ·
        refine ⟨5528226878048861221295789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3685484585365907480863859 5528226878048861221295789)
        ·
          refine ⟨2073085079268322957985921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5528226878048861221295789 2073085079268322957985921)
          ·
            refine ⟨1554813809451242218489441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2073085079268322957985921 1554813809451242218489441)
            ·
              refine ⟨1166110357088431663867081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1554813809451242218489441 1166110357088431663867081)
              ·
                refine ⟨874582767816323747900311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166110357088431663867081 874582767816323747900311)
                ·
                  refine ⟨1311874151724485621850467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874582767816323747900311 1311874151724485621850467)
                  ·
                    refine ⟨1967811227586728432775701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1311874151724485621850467 1967811227586728432775701)
                    ·
                      refine ⟨92241151293127895286361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1967811227586728432775701 92241151293127895286361)
                      ·
                        rfl

theorem cell23_179639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_179639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179639 prefixEnd_179639 := by exact prefixLift 179639
  have htrace : WordTrace (prefixWord ++ tailWord_179639) baseStart_179639 baseEnd_179639 := by
    simpa [prefixWord, tailWord_179639, baseEnd_179639] using wordTrace_append hprefix tailTrace_179639
  have hstable : (prefixWord ++ tailWord_179639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179639).length < 2 ^ (prefixWord ++ tailWord_179639).sum := by decide
  have hdescent : baseEnd_179639 < baseStart_179639 := by decide
  rcases family_descends (prefixWord ++ tailWord_179639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179660 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_179660 : Nat := 118140960795 + 179660 * 2 ^ 59
def prefixEnd_179660 : Nat := 4983230072969 + 3 ^ 40 * 179660 * 2
def baseEnd_179660 : Nat := 92251934386872313123765

theorem tailTrace_179660 : CollatzResearch.WordTrace tailWord_179660 prefixEnd_179660 92251934386872313123765 := by
  unfold tailWord_179660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276369264564989165136217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4368492352753318886848289 3276369264564989165136217)
  ·
    refine ⟨2457276948423741873852163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3276369264564989165136217 2457276948423741873852163)
    ·
      refine ⟨3685915422635612810778245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457276948423741873852163 3685915422635612810778245)
      ·
        refine ⟨691109141744177402020921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3685915422635612810778245 691109141744177402020921)
        ·
          refine ⟨518331856308133051515691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691109141744177402020921 518331856308133051515691)
          ·
            refine ⟨777497784462199577273537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518331856308133051515691 777497784462199577273537)
            ·
              refine ⟨583123338346649682955153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777497784462199577273537 583123338346649682955153)
              ·
                refine ⟨437342503759987262216365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583123338346649682955153 437342503759987262216365)
                ·
                  refine ⟨164003438909995223331137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437342503759987262216365 164003438909995223331137)
                  ·
                    refine ⟨123002579182496417498353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164003438909995223331137 123002579182496417498353)
                    ·
                      refine ⟨92251934386872313123765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123002579182496417498353 92251934386872313123765)
                      ·
                        rfl

theorem cell23_179660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_179660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179660 prefixEnd_179660 := by exact prefixLift 179660
  have htrace : WordTrace (prefixWord ++ tailWord_179660) baseStart_179660 baseEnd_179660 := by
    simpa [prefixWord, tailWord_179660, baseEnd_179660] using wordTrace_append hprefix tailTrace_179660
  have hstable : (prefixWord ++ tailWord_179660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179660).length < 2 ^ (prefixWord ++ tailWord_179660).sum := by decide
  have hdescent : baseEnd_179660 < baseStart_179660 := by decide
  rcases family_descends (prefixWord ++ tailWord_179660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179694 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_179694 : Nat := 118140960795 + 179694 * 2 ^ 59
def prefixEnd_179694 : Nat := 4983230072969 + 3 ^ 40 * 179694 * 2
def baseEnd_179694 : Nat := 92269392729125180098609

theorem tailTrace_179694 : CollatzResearch.WordTrace tailWord_179694 prefixEnd_179694 92269392729125180098609 := by
  unfold tailWord_179694
  simp only [CollatzResearch.WordTrace]
  refine ⟨819247326375850267126267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4369319074004534758006757 819247326375850267126267)
  ·
    refine ⟨1228870989563775400689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 819247326375850267126267 1228870989563775400689401)
    ·
      refine ⟨921653242172831550517051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1228870989563775400689401 921653242172831550517051)
      ·
        refine ⟨1382479863259247325775577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 921653242172831550517051 1382479863259247325775577)
        ·
          refine ⟨1036859897444435494331683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1382479863259247325775577 1036859897444435494331683)
          ·
            refine ⟨1555289846166653241497525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036859897444435494331683 1555289846166653241497525)
            ·
              refine ⟨145808423078123741390393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1555289846166653241497525 145808423078123741390393)
              ·
                refine ⟨109356317308592806042795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145808423078123741390393 109356317308592806042795)
                ·
                  refine ⟨164034475962889209064193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109356317308592806042795 164034475962889209064193)
                  ·
                    refine ⟨123025856972166906798145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164034475962889209064193 123025856972166906798145)
                    ·
                      refine ⟨92269392729125180098609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123025856972166906798145 92269392729125180098609)
                      ·
                        rfl

theorem cell23_179694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_179694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179694 prefixEnd_179694 := by exact prefixLift 179694
  have htrace : WordTrace (prefixWord ++ tailWord_179694) baseStart_179694 baseEnd_179694 := by
    simpa [prefixWord, tailWord_179694, baseEnd_179694] using wordTrace_append hprefix tailTrace_179694
  have hstable : (prefixWord ++ tailWord_179694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179694).length < 2 ^ (prefixWord ++ tailWord_179694).sum := by decide
  have hdescent : baseEnd_179694 < baseStart_179694 := by decide
  rcases family_descends (prefixWord ++ tailWord_179694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179720 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2]
def baseStart_179720 : Nat := 118140960795 + 179720 * 2 ^ 59
def prefixEnd_179720 : Nat := 4983230072969 + 3 ^ 40 * 179720 * 2
def baseEnd_179720 : Nat := 92282743226142078373489

theorem tailTrace_179720 : CollatzResearch.WordTrace tailWord_179720 prefixEnd_179720 92282743226142078373489 := by
  unfold tailWord_179720
  simp only [CollatzResearch.WordTrace]
  refine ⟨3277463454456304288728307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4369951272608405718304409 3277463454456304288728307)
  ·
    refine ⟨4916195181684456433092461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3277463454456304288728307 4916195181684456433092461)
    ·
      refine ⟨1843573193131671162409673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4916195181684456433092461 1843573193131671162409673)
      ·
        refine ⟨1382679894848753371807255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1843573193131671162409673 1382679894848753371807255)
        ·
          refine ⟨2074019842273130057710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1382679894848753371807255 2074019842273130057710883)
          ·
            refine ⟨3111029763409695086566325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074019842273130057710883 3111029763409695086566325)
            ·
              refine ⟨291659040319658914365593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3111029763409695086566325 291659040319658914365593)
              ·
                refine ⟨218744280239744185774195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291659040319658914365593 218744280239744185774195)
                ·
                  refine ⟨328116420359616278661293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218744280239744185774195 328116420359616278661293)
                  ·
                    refine ⟨123043657634856104497985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328116420359616278661293 123043657634856104497985)
                    ·
                      refine ⟨92282743226142078373489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123043657634856104497985 92282743226142078373489)
                      ·
                        rfl

theorem cell23_179720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_179720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179720 prefixEnd_179720 := by exact prefixLift 179720
  have htrace : WordTrace (prefixWord ++ tailWord_179720) baseStart_179720 baseEnd_179720 := by
    simpa [prefixWord, tailWord_179720, baseEnd_179720] using wordTrace_append hprefix tailTrace_179720
  have hstable : (prefixWord ++ tailWord_179720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179720).length < 2 ^ (prefixWord ++ tailWord_179720).sum := by decide
  have hdescent : baseEnd_179720 < baseStart_179720 := by decide
  rcases family_descends (prefixWord ++ tailWord_179720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179733 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_179733 : Nat := 118140960795 + 179733 * 2 ^ 59
def prefixEnd_179733 : Nat := 4983230072969 + 3 ^ 40 * 179733 * 2
def baseEnd_179733 : Nat := 92289418474650527510929

theorem tailTrace_179733 : CollatzResearch.WordTrace tailWord_179733 prefixEnd_179733 92289418474650527510929 := by
  unfold tailWord_179733
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555401057865511797679853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4370267371910341198453235 6555401057865511797679853)
  ·
    refine ⟨2458275396699566924129945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6555401057865511797679853 2458275396699566924129945)
    ·
      refine ⟨1843706547524675193097459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2458275396699566924129945 1843706547524675193097459)
      ·
        refine ⟨2765559821287012789646189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843706547524675193097459 2765559821287012789646189)
        ·
          refine ⟨1037084932982629796117321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2765559821287012789646189 1037084932982629796117321)
          ·
            refine ⟨777813699736972347087991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037084932982629796117321 777813699736972347087991)
            ·
              refine ⟨1166720549605458520631987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777813699736972347087991 1166720549605458520631987)
              ·
                refine ⟨1750080824408187780947981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166720549605458520631987 1750080824408187780947981)
                ·
                  refine ⟨656280309153070417855493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1750080824408187780947981 656280309153070417855493)
                  ·
                    refine ⟨123052557966200703347905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 656280309153070417855493 123052557966200703347905)
                    ·
                      refine ⟨92289418474650527510929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123052557966200703347905 92289418474650527510929)
                      ·
                        rfl

theorem cell23_179733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_179733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179733 prefixEnd_179733 := by exact prefixLift 179733
  have htrace : WordTrace (prefixWord ++ tailWord_179733) baseStart_179733 baseEnd_179733 := by
    simpa [prefixWord, tailWord_179733, baseEnd_179733] using wordTrace_append hprefix tailTrace_179733
  have hstable : (prefixWord ++ tailWord_179733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179733).length < 2 ^ (prefixWord ++ tailWord_179733).sum := by decide
  have hdescent : baseEnd_179733 < baseStart_179733 := by decide
  rcases family_descends (prefixWord ++ tailWord_179733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179773 : List Nat := [1, 4, 1, 3, 3, 1, 1, 2, 7]
def baseStart_179773 : Nat := 118140960795 + 179773 * 2 ^ 59
def prefixEnd_179773 : Nat := 4983230072969 + 3 ^ 40 * 179773 * 2
def baseEnd_179773 : Nat := 10256661966758930112305

theorem tailTrace_179773 : CollatzResearch.WordTrace tailWord_179773 prefixEnd_179773 10256661966758930112305 := by
  unfold tailWord_179773
  simp only [CollatzResearch.WordTrace]
  refine ⟨6556859977720598629135973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4371239985147065752757315 6556859977720598629135973)
  ·
    refine ⟨1229411245822612242962995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6556859977720598629135973 1229411245822612242962995)
    ·
      refine ⟨1844116868733918364444493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229411245822612242962995 1844116868733918364444493)
      ·
        refine ⟨691543825775219386666685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1844116868733918364444493 691543825775219386666685)
        ·
          refine ⟨259328934665707270000007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691543825775219386666685 259328934665707270000007)
          ·
            refine ⟨388993401998560905000011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259328934665707270000007 388993401998560905000011)
            ·
              refine ⟨583490102997841357500017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388993401998560905000011 583490102997841357500017)
              ·
                refine ⟨437617577248381018125013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583490102997841357500017 437617577248381018125013)
                ·
                  refine ⟨10256661966758930112305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 437617577248381018125013 10256661966758930112305)
                  ·
                    rfl

theorem cell23_179773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_179773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179773 prefixEnd_179773 := by exact prefixLift 179773
  have htrace : WordTrace (prefixWord ++ tailWord_179773) baseStart_179773 baseEnd_179773 := by
    simpa [prefixWord, tailWord_179773, baseEnd_179773] using wordTrace_append hprefix tailTrace_179773
  have hstable : (prefixWord ++ tailWord_179773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179773).length < 2 ^ (prefixWord ++ tailWord_179773).sum := by decide
  have hdescent : baseEnd_179773 < baseStart_179773 := by decide
  rcases family_descends (prefixWord ++ tailWord_179773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179786 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_179786 : Nat := 118140960795 + 179786 * 2 ^ 59
def prefixEnd_179786 : Nat := 4983230072969 + 3 ^ 40 * 179786 * 2
def baseEnd_179786 : Nat := 30772210983112940049395

theorem tailTrace_179786 : CollatzResearch.WordTrace tailWord_179786 prefixEnd_179786 30772210983112940049395 := by
  unfold tailWord_179786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639333531668375462339803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4371556084449001232906141 1639333531668375462339803)
  ·
    refine ⟨2459000297502563193509705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1639333531668375462339803 2459000297502563193509705)
    ·
      refine ⟨1844250223126922395132279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459000297502563193509705 1844250223126922395132279)
      ·
        refine ⟨2766375334690383592698419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844250223126922395132279 2766375334690383592698419)
        ·
          refine ⟨4149563002035575389047629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766375334690383592698419 4149563002035575389047629)
          ·
            refine ⟨1556086125763340770892861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4149563002035575389047629 1556086125763340770892861)
            ·
              refine ⟨583532297161252789084823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1556086125763340770892861 583532297161252789084823)
              ·
                refine ⟨875298445741879183627235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583532297161252789084823 875298445741879183627235)
                ·
                  refine ⟨1312947668612818775440853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875298445741879183627235 1312947668612818775440853)
                  ·
                    refine ⟨30772210983112940049395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1312947668612818775440853 30772210983112940049395)
                    ·
                      rfl

theorem cell23_179786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_179786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179786 prefixEnd_179786 := by exact prefixLift 179786
  have htrace : WordTrace (prefixWord ++ tailWord_179786) baseStart_179786 baseEnd_179786 := by
    simpa [prefixWord, tailWord_179786, baseEnd_179786] using wordTrace_append hprefix tailTrace_179786
  have hstable : (prefixWord ++ tailWord_179786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179786).length < 2 ^ (prefixWord ++ tailWord_179786).sum := by decide
  have hdescent : baseEnd_179786 < baseStart_179786 := by decide
  rcases family_descends (prefixWord ++ tailWord_179786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179833 : List Nat := [1, 2, 1, 3, 3, 1, 1, 4, 3, 4]
def baseStart_179833 : Nat := 118140960795 + 179833 * 2 ^ 59
def prefixEnd_179833 : Nat := 4983230072969 + 3 ^ 40 * 179833 * 2
def baseEnd_179833 : Nat := 30780255513366712086823

theorem tailTrace_179833 : CollatzResearch.WordTrace tailWord_179833 prefixEnd_179833 30780255513366712086823 := by
  unfold tailWord_179833
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559048357503228876320153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372698905002152584213435 6559048357503228876320153)
  ·
    refine ⟨4919286268127421657240115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6559048357503228876320153 4919286268127421657240115)
    ·
      refine ⟨7378929402191132485860173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4919286268127421657240115 7378929402191132485860173)
      ·
        refine ⟨2767098525821674682197565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7378929402191132485860173 2767098525821674682197565)
        ·
          refine ⟨1037661947183128005824087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767098525821674682197565 1037661947183128005824087)
          ·
            refine ⟨1556492920774692008736131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037661947183128005824087 1556492920774692008736131)
            ·
              refine ⟨2334739381162038013104197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556492920774692008736131 2334739381162038013104197)
              ·
                refine ⟨437763633967882127457037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2334739381162038013104197 437763633967882127457037)
                ·
                  refine ⟨164161362737955797796389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437763633967882127457037 164161362737955797796389)
                  ·
                    refine ⟨30780255513366712086823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164161362737955797796389 30780255513366712086823)
                    ·
                      rfl

theorem cell23_179833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 4].length) (baseStart_179833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179833 prefixEnd_179833 := by exact prefixLift 179833
  have htrace : WordTrace (prefixWord ++ tailWord_179833) baseStart_179833 baseEnd_179833 := by
    simpa [prefixWord, tailWord_179833, baseEnd_179833] using wordTrace_append hprefix tailTrace_179833
  have hstable : (prefixWord ++ tailWord_179833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179833).length < 2 ^ (prefixWord ++ tailWord_179833).sum := by decide
  have hdescent : baseEnd_179833 < baseStart_179833 := by decide
  rcases family_descends (prefixWord ++ tailWord_179833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179836 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_179836 : Nat := 118140960795 + 179836 * 2 ^ 59
def prefixEnd_179836 : Nat := 4983230072969 + 3 ^ 40 * 179836 * 2
def baseEnd_179836 : Nat := 92342306982063624522955

theorem tailTrace_179836 : CollatzResearch.WordTrace tailWord_179836 prefixEnd_179836 92342306982063624522955 := by
  unfold tailWord_179836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3279578888246180194339681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4372771850994906925786241 3279578888246180194339681)
  ·
    refine ⟨2459684166184635145754761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3279578888246180194339681 2459684166184635145754761)
    ·
      refine ⟨1844763124638476359316071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459684166184635145754761 1844763124638476359316071)
      ·
        refine ⟨2767144686957714538974107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1844763124638476359316071 2767144686957714538974107)
        ·
          refine ⟨4150717030436571808461161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767144686957714538974107 4150717030436571808461161)
          ·
            refine ⟨3113037772827428856345871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4150717030436571808461161 3113037772827428856345871)
            ·
              refine ⟨4669556659241143284518807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113037772827428856345871 4669556659241143284518807)
              ·
                refine ⟨7004334988861714926778211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4669556659241143284518807 7004334988861714926778211)
                ·
                  refine ⟨10506502483292572390167317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7004334988861714926778211 10506502483292572390167317)
                  ·
                    refine ⟨492492303904339330789093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10506502483292572390167317 492492303904339330789093)
                    ·
                      refine ⟨92342306982063624522955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 492492303904339330789093 92342306982063624522955)
                      ·
                        rfl

theorem cell23_179836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_179836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179836 prefixEnd_179836 := by exact prefixLift 179836
  have htrace : WordTrace (prefixWord ++ tailWord_179836) baseStart_179836 baseEnd_179836 := by
    simpa [prefixWord, tailWord_179836, baseEnd_179836] using wordTrace_append hprefix tailTrace_179836
  have hstable : (prefixWord ++ tailWord_179836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179836).length < 2 ^ (prefixWord ++ tailWord_179836).sum := by decide
  have hdescent : baseEnd_179836 < baseStart_179836 := by decide
  rcases family_descends (prefixWord ++ tailWord_179836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179843 : List Nat := [1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3]
def baseStart_179843 : Nat := 118140960795 + 179843 * 2 ^ 59
def prefixEnd_179843 : Nat := 4983230072969 + 3 ^ 40 * 179843 * 2
def baseEnd_179843 : Nat := 92345901346645097135423

theorem tailTrace_179843 : CollatzResearch.WordTrace tailWord_179843 prefixEnd_179843 92345901346645097135423 := by
  unfold tailWord_179843
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559413087467000584184183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4372942058311333722789455 6559413087467000584184183)
  ·
    refine ⟨9839119631200500876276275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6559413087467000584184183 9839119631200500876276275)
    ·
      refine ⟨14758679446800751314414413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9839119631200500876276275 14758679446800751314414413)
      ·
        refine ⟨5534504792550281742905405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14758679446800751314414413 5534504792550281742905405)
        ·
          refine ⟨2075439297206355653589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5534504792550281742905405 2075439297206355653589527)
          ·
            refine ⟨3113158945809533480384291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075439297206355653589527 3113158945809533480384291)
            ·
              refine ⟨4669738418714300220576437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3113158945809533480384291 4669738418714300220576437)
              ·
                refine ⟨437787976754465645679041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4669738418714300220576437 437787976754465645679041)
                ·
                  refine ⟨328340982565849234259281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437787976754465645679041 328340982565849234259281)
                  ·
                    refine ⟨246255736924386925694461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328340982565849234259281 246255736924386925694461)
                    ·
                      refine ⟨92345901346645097135423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246255736924386925694461 92345901346645097135423)
                      ·
                        rfl

theorem cell23_179843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_179843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179843 prefixEnd_179843 := by exact prefixLift 179843
  have htrace : WordTrace (prefixWord ++ tailWord_179843) baseStart_179843 baseEnd_179843 := by
    simpa [prefixWord, tailWord_179843, baseEnd_179843] using wordTrace_append hprefix tailTrace_179843
  have hstable : (prefixWord ++ tailWord_179843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179843).length < 2 ^ (prefixWord ++ tailWord_179843).sum := by decide
  have hdescent : baseEnd_179843 < baseStart_179843 := by decide
  rcases family_descends (prefixWord ++ tailWord_179843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179890 : List Nat := [3, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_179890 : Nat := 118140960795 + 179890 * 2 ^ 59
def prefixEnd_179890 : Nat := 4983230072969 + 3 ^ 40 * 179890 * 2
def baseEnd_179890 : Nat := 92370034937406413247707

theorem tailTrace_179890 : CollatzResearch.WordTrace tailWord_179890 prefixEnd_179890 92370034937406413247707 := by
  unfold tailWord_179890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1640281829574181902786281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4374084878864485074096749 1640281829574181902786281)
  ·
    refine ⟨1230211372180636427089711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1640281829574181902786281 1230211372180636427089711)
    ·
      refine ⟨1845317058270954640634567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230211372180636427089711 1845317058270954640634567)
      ·
        refine ⟨2767975587406431960951851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845317058270954640634567 2767975587406431960951851)
        ·
          refine ⟨4151963381109647941427777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2767975587406431960951851 4151963381109647941427777)
          ·
            refine ⟨3113972535832235956070833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4151963381109647941427777 3113972535832235956070833)
            ·
              refine ⟨2335479401874176967053125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3113972535832235956070833 2335479401874176967053125)
              ·
                refine ⟨437902387851408181322461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2335479401874176967053125 437902387851408181322461)
                ·
                  refine ⟨164213395444278067995923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437902387851408181322461 164213395444278067995923)
                  ·
                    refine ⟨246320093166417101993885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164213395444278067995923 246320093166417101993885)
                    ·
                      refine ⟨92370034937406413247707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246320093166417101993885 92370034937406413247707)
                      ·
                        rfl

theorem cell23_179890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_179890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179890 prefixEnd_179890 := by exact prefixLift 179890
  have htrace : WordTrace (prefixWord ++ tailWord_179890) baseStart_179890 baseEnd_179890 := by
    simpa [prefixWord, tailWord_179890, baseEnd_179890] using wordTrace_append hprefix tailTrace_179890
  have hstable : (prefixWord ++ tailWord_179890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179890).length < 2 ^ (prefixWord ++ tailWord_179890).sum := by decide
  have hdescent : baseEnd_179890 < baseStart_179890 := by decide
  rcases family_descends (prefixWord ++ tailWord_179890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179894 : List Nat := [5, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_179894 : Nat := 118140960795 + 179894 * 2 ^ 59
def prefixEnd_179894 : Nat := 4983230072969 + 3 ^ 40 * 179894 * 2
def baseEnd_179894 : Nat := 92372088860024397597689

theorem tailTrace_179894 : CollatzResearch.WordTrace tailWord_179894 prefixEnd_179894 92372088860024397597689 := by
  unfold tailWord_179894
  simp only [CollatzResearch.WordTrace]
  refine ⟨410079575642639768393171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4374182140188157529527157 410079575642639768393171)
  ·
    refine ⟨615119363463959652589757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410079575642639768393171 615119363463959652589757)
    ·
      refine ⟨230669761298984869721159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 615119363463959652589757 230669761298984869721159)
      ·
        refine ⟨346004641948477304581739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230669761298984869721159 346004641948477304581739)
        ·
          refine ⟨519006962922715956872609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346004641948477304581739 519006962922715956872609)
          ·
            refine ⟨389255222192036967654457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519006962922715956872609 389255222192036967654457)
            ·
              refine ⟨291941416644027725740843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389255222192036967654457 291941416644027725740843)
              ·
                refine ⟨437912124966041588611265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291941416644027725740843 437912124966041588611265)
                ·
                  refine ⟨328434093724531191458449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 437912124966041588611265 328434093724531191458449)
                  ·
                    refine ⟨246325570293398393593837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328434093724531191458449 246325570293398393593837)
                    ·
                      refine ⟨92372088860024397597689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246325570293398393593837 92372088860024397597689)
                      ·
                        rfl

theorem cell23_179894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_179894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179894 prefixEnd_179894 := by exact prefixLift 179894
  have htrace : WordTrace (prefixWord ++ tailWord_179894) baseStart_179894 baseEnd_179894 := by
    simpa [prefixWord, tailWord_179894, baseEnd_179894] using wordTrace_append hprefix tailTrace_179894
  have hstable : (prefixWord ++ tailWord_179894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179894).length < 2 ^ (prefixWord ++ tailWord_179894).sum := by decide
  have hdescent : baseEnd_179894 < baseStart_179894 := by decide
  rcases family_descends (prefixWord ++ tailWord_179894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179940 : List Nat := [2, 3, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_179940 : Nat := 118140960795 + 179940 * 2 ^ 59
def prefixEnd_179940 : Nat := 4983230072969 + 3 ^ 40 * 179940 * 2
def baseEnd_179940 : Nat := 30798569656710405874159

theorem tailTrace_179940 : CollatzResearch.WordTrace tailWord_179940 prefixEnd_179940 30798569656710405874159 := by
  unfold tailWord_179940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3281475484057793075232637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4375300645410390766976849 3281475484057793075232637)
  ·
    refine ⟨1230553306521672403212239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3281475484057793075232637 1230553306521672403212239)
    ·
      refine ⟨1845829959782508604818359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230553306521672403212239 1845829959782508604818359)
      ·
        refine ⟨2768744939673762907227539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845829959782508604818359 2768744939673762907227539)
        ·
          refine ⟨4153117409510644360841309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768744939673762907227539 4153117409510644360841309)
          ·
            refine ⟨1557419028566491635315491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4153117409510644360841309 1557419028566491635315491)
            ·
              refine ⟨2336128542849737452973237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557419028566491635315491 2336128542849737452973237)
              ·
                refine ⟨219012050892162886216241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2336128542849737452973237 219012050892162886216241)
                ·
                  refine ⟨164259038169122164662181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219012050892162886216241 164259038169122164662181)
                  ·
                    refine ⟨30798569656710405874159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164259038169122164662181 30798569656710405874159)
                    ·
                      rfl

theorem cell23_179940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_179940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179940 prefixEnd_179940 := by exact prefixLift 179940
  have htrace : WordTrace (prefixWord ++ tailWord_179940) baseStart_179940 baseEnd_179940 := by
    simpa [prefixWord, tailWord_179940, baseEnd_179940] using wordTrace_append hprefix tailTrace_179940
  have hstable : (prefixWord ++ tailWord_179940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179940).length < 2 ^ (prefixWord ++ tailWord_179940).sum := by decide
  have hdescent : baseEnd_179940 < baseStart_179940 := by decide
  rcases family_descends (prefixWord ++ tailWord_179940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179950 : List Nat := [4, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_179950 : Nat := 118140960795 + 179950 * 2 ^ 59
def prefixEnd_179950 : Nat := 4983230072969 + 3 ^ 40 * 179950 * 2
def baseEnd_179950 : Nat := 92400843776676178497431

theorem tailTrace_179950 : CollatzResearch.WordTrace tailWord_179950 prefixEnd_179950 92400843776676178497431 := by
  unfold tailWord_179950
  simp only [CollatzResearch.WordTrace]
  refine ⟨820414462259919732291163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4375543798719571905552869 820414462259919732291163)
  ·
    refine ⟨1230621693389879598436745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820414462259919732291163 1230621693389879598436745)
    ·
      refine ⟨922966270042409698827559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230621693389879598436745 922966270042409698827559)
      ·
        refine ⟨1384449405063614548241339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922966270042409698827559 1384449405063614548241339)
        ·
          refine ⟨2076674107595421822362009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384449405063614548241339 2076674107595421822362009)
          ·
            refine ⟨1557505580696566366771507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076674107595421822362009 1557505580696566366771507)
            ·
              refine ⟨2336258371044849550157261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1557505580696566366771507 2336258371044849550157261)
              ·
                refine ⟨876096889141818581308973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2336258371044849550157261 876096889141818581308973)
                ·
                  refine ⟨328536333428181967990865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 876096889141818581308973 328536333428181967990865)
                  ·
                    refine ⟨246402250071136475993149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328536333428181967990865 246402250071136475993149)
                    ·
                      refine ⟨92400843776676178497431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246402250071136475993149 92400843776676178497431)
                      ·
                        rfl

theorem cell23_179950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_179950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179950 prefixEnd_179950 := by exact prefixLift 179950
  have htrace : WordTrace (prefixWord ++ tailWord_179950) baseStart_179950 baseEnd_179950 := by
    simpa [prefixWord, tailWord_179950, baseEnd_179950] using wordTrace_append hprefix tailTrace_179950
  have hstable : (prefixWord ++ tailWord_179950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179950).length < 2 ^ (prefixWord ++ tailWord_179950).sum := by decide
  have hdescent : baseEnd_179950 < baseStart_179950 := by decide
  rcases family_descends (prefixWord ++ tailWord_179950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179963 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3]
def baseStart_179963 : Nat := 118140960795 + 179963 * 2 ^ 59
def prefixEnd_179963 : Nat := 4983230072969 + 3 ^ 40 * 179963 * 2
def baseEnd_179963 : Nat := 92407519025184627634871

theorem tailTrace_179963 : CollatzResearch.WordTrace tailWord_179963 prefixEnd_179963 92407519025184627634871 := by
  unfold tailWord_179963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563789847032261078552543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4375859898021507385701695 6563789847032261078552543)
  ·
    refine ⟨9845684770548391617828815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563789847032261078552543 9845684770548391617828815)
    ·
      refine ⟨14768527155822587426743223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9845684770548391617828815 14768527155822587426743223)
      ·
        refine ⟨22152790733733881140114835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14768527155822587426743223 22152790733733881140114835)
        ·
          refine ⟨33229186100600821710172253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22152790733733881140114835 33229186100600821710172253)
          ·
            refine ⟨12460944787725308141314595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33229186100600821710172253 12460944787725308141314595)
            ·
              refine ⟨18691417181587962211971893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12460944787725308141314595 18691417181587962211971893)
              ·
                refine ⟨1752320360773871457372365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18691417181587962211971893 1752320360773871457372365)
                ·
                  refine ⟨657120135290201796514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1752320360773871457372365 657120135290201796514637)
                  ·
                    refine ⟨246420050733825673692989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 657120135290201796514637 246420050733825673692989)
                    ·
                      refine ⟨92407519025184627634871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246420050733825673692989 92407519025184627634871)
                      ·
                        rfl

theorem cell23_179963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 3, 3].length) (baseStart_179963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179963 prefixEnd_179963 := by exact prefixLift 179963
  have htrace : WordTrace (prefixWord ++ tailWord_179963) baseStart_179963 baseEnd_179963 := by
    simpa [prefixWord, tailWord_179963, baseEnd_179963] using wordTrace_append hprefix tailTrace_179963
  have hstable : (prefixWord ++ tailWord_179963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179963).length < 2 ^ (prefixWord ++ tailWord_179963).sum := by decide
  have hdescent : baseEnd_179963 < baseStart_179963 := by decide
  rcases family_descends (prefixWord ++ tailWord_179963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_179967 : List Nat := [1, 1, 2, 2, 1, 3, 6, 1, 1, 2, 3]
def baseStart_179967 : Nat := 118140960795 + 179967 * 2 ^ 59
def prefixEnd_179967 : Nat := 4983230072969 + 3 ^ 40 * 179967 * 2
def baseEnd_179967 : Nat := 92409572947802611984853

theorem tailTrace_179967 : CollatzResearch.WordTrace tailWord_179967 prefixEnd_179967 92409572947802611984853 := by
  unfold tailWord_179967
  simp only [CollatzResearch.WordTrace]
  refine ⟨6563935739017769761698155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4375957159345179841132103 6563935739017769761698155)
  ·
    refine ⟨9845903608526654642547233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6563935739017769761698155 9845903608526654642547233)
    ·
      refine ⟨7384427706394990981910425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9845903608526654642547233 7384427706394990981910425)
      ·
        refine ⟨5538320779796243236432819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7384427706394990981910425 5538320779796243236432819)
        ·
          refine ⟨8307481169694364854649229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5538320779796243236432819 8307481169694364854649229)
          ·
            refine ⟨3115305438635386820493461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8307481169694364854649229 3115305438635386820493461)
            ·
              refine ⟨146029942436033757210631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3115305438635386820493461 146029942436033757210631)
              ·
                refine ⟨219044913654050635815947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146029942436033757210631 219044913654050635815947)
                ·
                  refine ⟨328567370481075953723921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219044913654050635815947 328567370481075953723921)
                  ·
                    refine ⟨246425527860806965292941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 328567370481075953723921 246425527860806965292941)
                    ·
                      refine ⟨92409572947802611984853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246425527860806965292941 92409572947802611984853)
                      ·
                        rfl

theorem cell23_179967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 2, 3].length) (baseStart_179967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_179967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_179967 prefixEnd_179967 := by exact prefixLift 179967
  have htrace : WordTrace (prefixWord ++ tailWord_179967) baseStart_179967 baseEnd_179967 := by
    simpa [prefixWord, tailWord_179967, baseEnd_179967] using wordTrace_append hprefix tailTrace_179967
  have hstable : (prefixWord ++ tailWord_179967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_179967).length < 2 ^ (prefixWord ++ tailWord_179967).sum := by decide
  have hdescent : baseEnd_179967 < baseStart_179967 := by decide
  rcases family_descends (prefixWord ++ tailWord_179967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180003 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4]
def baseStart_180003 : Nat := 118140960795 + 180003 * 2 ^ 59
def prefixEnd_180003 : Nat := 4983230072969 + 3 ^ 40 * 180003 * 2
def baseEnd_180003 : Nat := 92428058251364471134687

theorem tailTrace_180003 : CollatzResearch.WordTrace tailWord_180003 prefixEnd_180003 92428058251364471134687 := by
  unfold tailWord_180003
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565248766887347910008663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4376832511258231940005775 6565248766887347910008663)
  ·
    refine ⟨9847873150331021865012995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6565248766887347910008663 9847873150331021865012995)
    ·
      refine ⟨14771809725496532797519493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9847873150331021865012995 14771809725496532797519493)
      ·
        refine ⟨2769714323530599899534905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14771809725496532797519493 2769714323530599899534905)
        ·
          refine ⟨2077285742647949924651179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2769714323530599899534905 2077285742647949924651179)
          ·
            refine ⟨3115928613971924886976769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2077285742647949924651179 3115928613971924886976769)
            ·
              refine ⟨2336946460478943665232577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3115928613971924886976769 2336946460478943665232577)
              ·
                refine ⟨1752709845359207748924433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2336946460478943665232577 1752709845359207748924433)
                ·
                  refine ⟨1314532384019405811693325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1752709845359207748924433 1314532384019405811693325)
                  ·
                    refine ⟨492949644007277179384997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1314532384019405811693325 492949644007277179384997)
                    ·
                      refine ⟨92428058251364471134687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 492949644007277179384997 92428058251364471134687)
                      ·
                        rfl

theorem cell23_180003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_180003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180003 prefixEnd_180003 := by exact prefixLift 180003
  have htrace : WordTrace (prefixWord ++ tailWord_180003) baseStart_180003 baseEnd_180003 := by
    simpa [prefixWord, tailWord_180003, baseEnd_180003] using wordTrace_append hprefix tailTrace_180003
  have hstable : (prefixWord ++ tailWord_180003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180003).length < 2 ^ (prefixWord ++ tailWord_180003).sum := by decide
  have hdescent : baseEnd_180003 < baseStart_180003 := by decide
  rcases family_descends (prefixWord ++ tailWord_180003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180037 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 4, 2, 2]
def baseStart_180037 : Nat := 118140960795 + 180037 * 2 ^ 59
def prefixEnd_180037 : Nat := 4983230072969 + 3 ^ 40 * 180037 * 2
def baseEnd_180037 : Nat := 92445516593617338109531

theorem tailTrace_180037 : CollatzResearch.WordTrace tailWord_180037 prefixEnd_180037 92445516593617338109531 := by
  unfold tailWord_180037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6566488848764171716746365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4377659232509447811164243 6566488848764171716746365)
  ·
    refine ⟨2462433318286564393779887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6566488848764171716746365 2462433318286564393779887)
    ·
      refine ⟨3693649977429846590669831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2462433318286564393779887 3693649977429846590669831)
      ·
        refine ⟨5540474966144769886004747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693649977429846590669831 5540474966144769886004747)
        ·
          refine ⟨8310712449217154829007121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5540474966144769886004747 8310712449217154829007121)
          ·
            refine ⟨6233034336912866121755341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8310712449217154829007121 6233034336912866121755341)
            ·
              refine ⟨2337387876342324795658253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6233034336912866121755341 2337387876342324795658253)
              ·
                refine ⟨876520453628371798371845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2337387876342324795658253 876520453628371798371845)
                ·
                  refine ⟨164347585055319712194721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 876520453628371798371845 164347585055319712194721)
                  ·
                    refine ⟨123260688791489784146041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164347585055319712194721 123260688791489784146041)
                    ·
                      refine ⟨92445516593617338109531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123260688791489784146041 92445516593617338109531)
                      ·
                        rfl

theorem cell23_180037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_180037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180037 prefixEnd_180037 := by exact prefixLift 180037
  have htrace : WordTrace (prefixWord ++ tailWord_180037) baseStart_180037 baseEnd_180037 := by
    simpa [prefixWord, tailWord_180037, baseEnd_180037] using wordTrace_append hprefix tailTrace_180037
  have hstable : (prefixWord ++ tailWord_180037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180037).length < 2 ^ (prefixWord ++ tailWord_180037).sum := by decide
  have hdescent : baseEnd_180037 < baseStart_180037 := by decide
  rcases family_descends (prefixWord ++ tailWord_180037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180073 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 1, 7]
def baseStart_180073 : Nat := 118140960795 + 180073 * 2 ^ 59
def prefixEnd_180073 : Nat := 4983230072969 + 3 ^ 40 * 180073 * 2
def baseEnd_180073 : Nat := 30821333965726399086455

theorem tailTrace_180073 : CollatzResearch.WordTrace tailWord_180073 prefixEnd_180073 30821333965726399086455 := by
  unfold tailWord_180073
  simp only [CollatzResearch.WordTrace]
  refine ⟨6567801876633749865056873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4378534584422499910037915 6567801876633749865056873)
  ·
    refine ⟨4925851407475312398792655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6567801876633749865056873 4925851407475312398792655)
    ·
      refine ⟨7388777111212968598188983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4925851407475312398792655 7388777111212968598188983)
      ·
        refine ⟨11083165666819452897283475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7388777111212968598188983 11083165666819452897283475)
        ·
          refine ⟨16624748500229179345925213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11083165666819452897283475 16624748500229179345925213)
          ·
            refine ⟨6234280687585942254721955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16624748500229179345925213 6234280687585942254721955)
            ·
              refine ⟨9351421031378913382082933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6234280687585942254721955 9351421031378913382082933)
              ·
                refine ⟨876695721691773129570275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9351421031378913382082933 876695721691773129570275)
                ·
                  refine ⟨1315043582537659694355413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876695721691773129570275 1315043582537659694355413)
                  ·
                    refine ⟨30821333965726399086455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1315043582537659694355413 30821333965726399086455)
                    ·
                      rfl

theorem cell23_180073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_180073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180073 prefixEnd_180073 := by exact prefixLift 180073
  have htrace : WordTrace (prefixWord ++ tailWord_180073) baseStart_180073 baseEnd_180073 := by
    simpa [prefixWord, tailWord_180073, baseEnd_180073] using wordTrace_append hprefix tailTrace_180073
  have hstable : (prefixWord ++ tailWord_180073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180073).length < 2 ^ (prefixWord ++ tailWord_180073).sum := by decide
  have hdescent : baseEnd_180073 < baseStart_180073 := by decide
  rcases family_descends (prefixWord ++ tailWord_180073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180090 : List Nat := [3, 1, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_180090 : Nat := 118140960795 + 180090 * 2 ^ 59
def prefixEnd_180090 : Nat := 4983230072969 + 3 ^ 40 * 180090 * 2
def baseEnd_180090 : Nat := 30824243689435210248929

theorem tailTrace_180090 : CollatzResearch.WordTrace tailWord_180090 prefixEnd_180090 30824243689435210248929 := by
  unfold tailWord_180090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1642105479393040442106431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4378947945048107845617149 1642105479393040442106431)
  ·
    refine ⟨2463158219089560663159647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1642105479393040442106431 2463158219089560663159647)
    ·
      refine ⟨3694737328634340994739471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2463158219089560663159647 3694737328634340994739471)
      ·
        refine ⟨5542105992951511492109207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3694737328634340994739471 5542105992951511492109207)
        ·
          refine ⟨8313158989427267238163811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5542105992951511492109207 8313158989427267238163811)
          ·
            refine ⟨12469738484140900857245717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8313158989427267238163811 12469738484140900857245717)
            ·
              refine ⟨584518991444104727683393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12469738484140900857245717 584518991444104727683393)
              ·
                refine ⟨438389243583078545762545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584518991444104727683393 438389243583078545762545)
                ·
                  refine ⟨328791932687308909321909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438389243583078545762545 328791932687308909321909)
                  ·
                    refine ⟨30824243689435210248929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 328791932687308909321909 30824243689435210248929)
                    ·
                      rfl

theorem cell23_180090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_180090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180090 prefixEnd_180090 := by exact prefixLift 180090
  have htrace : WordTrace (prefixWord ++ tailWord_180090) baseStart_180090 baseEnd_180090 := by
    simpa [prefixWord, tailWord_180090, baseEnd_180090] using wordTrace_append hprefix tailTrace_180090
  have hstable : (prefixWord ++ tailWord_180090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180090).length < 2 ^ (prefixWord ++ tailWord_180090).sum := by decide
  have hdescent : baseEnd_180090 < baseStart_180090 := by decide
  rcases family_descends (prefixWord ++ tailWord_180090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180100 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_180100 : Nat := 118140960795 + 180100 * 2 ^ 59
def prefixEnd_180100 : Nat := 4983230072969 + 3 ^ 40 * 180100 * 2
def baseEnd_180100 : Nat := 92477865874850591621741

theorem tailTrace_180100 : CollatzResearch.WordTrace tailWord_180100 prefixEnd_180100 92477865874850591621741 := by
  unfold tailWord_180100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284393323767966738144877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4379191098357288984193169 3284393323767966738144877)
  ·
    refine ⟨1231647496412987526804329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3284393323767966738144877 1231647496412987526804329)
    ·
      refine ⟨923735622309740645103247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1231647496412987526804329 923735622309740645103247)
      ·
        refine ⟨1385603433464610967654871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 923735622309740645103247 1385603433464610967654871)
        ·
          refine ⟨2078405150196916451482307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1385603433464610967654871 2078405150196916451482307)
          ·
            refine ⟨3117607725295374677223461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078405150196916451482307 3117607725295374677223461)
            ·
              refine ⟨584551448492882751979399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3117607725295374677223461 584551448492882751979399)
              ·
                refine ⟨876827172739324127969099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584551448492882751979399 876827172739324127969099)
                ·
                  refine ⟨1315240759108986191953649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876827172739324127969099 1315240759108986191953649)
                  ·
                    refine ⟨986430569331739643965237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1315240759108986191953649 986430569331739643965237)
                    ·
                      refine ⟨92477865874850591621741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 986430569331739643965237 92477865874850591621741)
                      ·
                        rfl

theorem cell23_180100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_180100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180100 prefixEnd_180100 := by exact prefixLift 180100
  have htrace : WordTrace (prefixWord ++ tailWord_180100) baseStart_180100 baseEnd_180100 := by
    simpa [prefixWord, tailWord_180100, baseEnd_180100] using wordTrace_append hprefix tailTrace_180100
  have hstable : (prefixWord ++ tailWord_180100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180100).length < 2 ^ (prefixWord ++ tailWord_180100).sum := by decide
  have hdescent : baseEnd_180100 < baseStart_180100 := by decide
  rcases family_descends (prefixWord ++ tailWord_180100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180124 : List Nat := [2, 2, 3, 3, 1, 3, 1, 1, 2, 5]
def baseStart_180124 : Nat := 118140960795 + 180124 * 2 ^ 59
def prefixEnd_180124 : Nat := 4983230072969 + 3 ^ 40 * 180124 * 2
def baseEnd_180124 : Nat := 30830063136852832573877

theorem tailTrace_180124 : CollatzResearch.WordTrace tailWord_180124 prefixEnd_180124 30830063136852832573877 := by
  unfold tailWord_180124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284830999724492787581713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4379774666299323716775617 3284830999724492787581713)
  ·
    refine ⟨2463623249793369590686285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3284830999724492787581713 2463623249793369590686285)
    ·
      refine ⟨923858718672513596507357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2463623249793369590686285 923858718672513596507357)
      ·
        refine ⟨346447019502192598690259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 923858718672513596507357 346447019502192598690259)
        ·
          refine ⟨519670529253288898035389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346447019502192598690259 519670529253288898035389)
          ·
            refine ⟨194876448469983336763271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519670529253288898035389 194876448469983336763271)
            ·
              refine ⟨292314672704975005144907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194876448469983336763271 292314672704975005144907)
              ·
                refine ⟨438472009057462507717361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292314672704975005144907 438472009057462507717361)
                ·
                  refine ⟨328854006793096880788021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438472009057462507717361 328854006793096880788021)
                  ·
                    refine ⟨30830063136852832573877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 328854006793096880788021 30830063136852832573877)
                    ·
                      rfl

theorem cell23_180124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_180124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180124 prefixEnd_180124 := by exact prefixLift 180124
  have htrace : WordTrace (prefixWord ++ tailWord_180124) baseStart_180124 baseEnd_180124 := by
    simpa [prefixWord, tailWord_180124, baseEnd_180124] using wordTrace_append hprefix tailTrace_180124
  have hstable : (prefixWord ++ tailWord_180124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180124).length < 2 ^ (prefixWord ++ tailWord_180124).sum := by decide
  have hdescent : baseEnd_180124 < baseStart_180124 := by decide
  rcases family_descends (prefixWord ++ tailWord_180124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180127 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4]
def baseStart_180127 : Nat := 118140960795 + 180127 * 2 ^ 59
def prefixEnd_180127 : Nat := 4983230072969 + 3 ^ 40 * 180127 * 2
def baseEnd_180127 : Nat := 92491729852521985984117

theorem tailTrace_180127 : CollatzResearch.WordTrace tailWord_180127 prefixEnd_180127 92491729852521985984117 := by
  unfold tailWord_180127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6569771418438117087522635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4379847612292078058348423 6569771418438117087522635)
  ·
    refine ⟨9854657127657175631283953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6569771418438117087522635 9854657127657175631283953)
    ·
      refine ⟨7390992845742881723462965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9854657127657175631283953 7390992845742881723462965)
      ·
        refine ⟨692905579288395161574653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7390992845742881723462965 692905579288395161574653)
        ·
          refine ⟨259839592233148185590495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 692905579288395161574653 259839592233148185590495)
          ·
            refine ⟨389759388349722278385743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259839592233148185590495 389759388349722278385743)
            ·
              refine ⟨584639082524583417578615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389759388349722278385743 584639082524583417578615)
              ·
                refine ⟨876958623786875126367923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584639082524583417578615 876958623786875126367923)
                ·
                  refine ⟨1315437935680312689551885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876958623786875126367923 1315437935680312689551885)
                  ·
                    refine ⟨493289225880117258581957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1315437935680312689551885 493289225880117258581957)
                    ·
                      refine ⟨92491729852521985984117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 493289225880117258581957 92491729852521985984117)
                      ·
                        rfl

theorem cell23_180127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_180127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180127 prefixEnd_180127 := by exact prefixLift 180127
  have htrace : WordTrace (prefixWord ++ tailWord_180127) baseStart_180127 baseEnd_180127 := by
    simpa [prefixWord, tailWord_180127, baseEnd_180127] using wordTrace_append hprefix tailTrace_180127
  have hstable : (prefixWord ++ tailWord_180127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180127).length < 2 ^ (prefixWord ++ tailWord_180127).sum := by decide
  have hdescent : baseEnd_180127 < baseStart_180127 := by decide
  rcases family_descends (prefixWord ++ tailWord_180127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180177 : List Nat := [1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_180177 : Nat := 118140960795 + 180177 * 2 ^ 59
def prefixEnd_180177 : Nat := 4983230072969 + 3 ^ 40 * 180177 * 2
def baseEnd_180177 : Nat := 92517403885246790358887

theorem tailTrace_180177 : CollatzResearch.WordTrace tailWord_180177 prefixEnd_180177 92517403885246790358887 := by
  unfold tailWord_180177
  simp only [CollatzResearch.WordTrace]
  refine ⟨6571595068256975626842785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381063378837983751228523 6571595068256975626842785)
  ·
    refine ⟨4928696301192731720132089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6571595068256975626842785 4928696301192731720132089)
    ·
      refine ⟨3696522225894548790099067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4928696301192731720132089 3696522225894548790099067)
      ·
        refine ⟨5544783338841823185148601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696522225894548790099067 5544783338841823185148601)
        ·
          refine ⟨4158587504131367388861451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5544783338841823185148601 4158587504131367388861451)
          ·
            refine ⟨6237881256197051083292177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4158587504131367388861451 6237881256197051083292177)
            ·
              refine ⟨4678410942147788312469133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6237881256197051083292177 4678410942147788312469133)
              ·
                refine ⟨1754404103305420617175925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4678410942147788312469133 1754404103305420617175925)
                ·
                  refine ⟨164475384684883182860243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1754404103305420617175925 164475384684883182860243)
                  ·
                    refine ⟨246713077027324774290365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164475384684883182860243 246713077027324774290365)
                    ·
                      refine ⟨92517403885246790358887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246713077027324774290365 92517403885246790358887)
                      ·
                        rfl

theorem cell23_180177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_180177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180177 prefixEnd_180177 := by exact prefixLift 180177
  have htrace : WordTrace (prefixWord ++ tailWord_180177) baseStart_180177 baseEnd_180177 := by
    simpa [prefixWord, tailWord_180177, baseEnd_180177] using wordTrace_append hprefix tailTrace_180177
  have hstable : (prefixWord ++ tailWord_180177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180177).length < 2 ^ (prefixWord ++ tailWord_180177).sum := by decide
  have hdescent : baseEnd_180177 < baseStart_180177 := by decide
  rcases family_descends (prefixWord ++ tailWord_180177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180205 : List Nat := [1, 5, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_180205 : Nat := 118140960795 + 180205 * 2 ^ 59
def prefixEnd_180205 : Nat := 4983230072969 + 3 ^ 40 * 180205 * 2
def baseEnd_180205 : Nat := 30843927114524226936253

theorem tailTrace_180205 : CollatzResearch.WordTrace tailWord_180205 prefixEnd_180205 30843927114524226936253 := by
  unfold tailWord_180205
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572616312155536408862069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4381744208103690939241379 6572616312155536408862069)
  ·
    refine ⟨616182779264581538330819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6572616312155536408862069 616182779264581538330819)
    ·
      refine ⟨924274168896872307496229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 616182779264581538330819 924274168896872307496229)
      ·
        refine ⟨173301406668163557655543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 924274168896872307496229 173301406668163557655543)
        ·
          refine ⟨259952110002245336483315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173301406668163557655543 259952110002245336483315)
          ·
            refine ⟨389928165003368004724973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259952110002245336483315 389928165003368004724973)
            ·
              refine ⟨146223061876263001771865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389928165003368004724973 146223061876263001771865)
              ·
                refine ⟨109667296407197251328899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146223061876263001771865 109667296407197251328899)
                ·
                  refine ⟨164500944610795876993349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109667296407197251328899 164500944610795876993349)
                  ·
                    refine ⟨30843927114524226936253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164500944610795876993349 30843927114524226936253)
                    ·
                      rfl

theorem cell23_180205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_180205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180205 prefixEnd_180205 := by exact prefixLift 180205
  have htrace : WordTrace (prefixWord ++ tailWord_180205) baseStart_180205 baseEnd_180205 := by
    simpa [prefixWord, tailWord_180205, baseEnd_180205] using wordTrace_append hprefix tailTrace_180205
  have hstable : (prefixWord ++ tailWord_180205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180205).length < 2 ^ (prefixWord ++ tailWord_180205).sum := by decide
  have hdescent : baseEnd_180205 < baseStart_180205 := by decide
  rcases family_descends (prefixWord ++ tailWord_180205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180234 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_180234 : Nat := 118140960795 + 180234 * 2 ^ 59
def prefixEnd_180234 : Nat := 4983230072969 + 3 ^ 40 * 180234 * 2
def baseEnd_180234 : Nat := 92546672282553067346125

theorem tailTrace_180234 : CollatzResearch.WordTrace tailWord_180234 prefixEnd_180234 92546672282553067346125 := by
  unfold tailWord_180234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643418507262618590416939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4382449352700316241111837 1643418507262618590416939)
  ·
    refine ⟨2465127760893927885625409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643418507262618590416939 2465127760893927885625409)
    ·
      refine ⟨1848845820670445914219057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465127760893927885625409 1848845820670445914219057)
      ·
        refine ⟨1386634365502834435664293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1848845820670445914219057 1386634365502834435664293)
        ·
          refine ⟨259993943531781456687055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1386634365502834435664293 259993943531781456687055)
          ·
            refine ⟨389990915297672185030583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259993943531781456687055 389990915297672185030583)
            ·
              refine ⟨584986372946508277545875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389990915297672185030583 584986372946508277545875)
              ·
                refine ⟨877479559419762416318813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584986372946508277545875 877479559419762416318813)
                ·
                  refine ⟨329054834782410906119555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 877479559419762416318813 329054834782410906119555)
                  ·
                    refine ⟨493582252173616359179333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329054834782410906119555 493582252173616359179333)
                    ·
                      refine ⟨92546672282553067346125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 493582252173616359179333 92546672282553067346125)
                      ·
                        rfl

theorem cell23_180234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_180234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180234 prefixEnd_180234 := by exact prefixLift 180234
  have htrace : WordTrace (prefixWord ++ tailWord_180234) baseStart_180234 baseEnd_180234 := by
    simpa [prefixWord, tailWord_180234, baseEnd_180234] using wordTrace_append hprefix tailTrace_180234
  have hstable : (prefixWord ++ tailWord_180234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180234).length < 2 ^ (prefixWord ++ tailWord_180234).sum := by decide
  have hdescent : baseEnd_180234 < baseStart_180234 := by decide
  rcases family_descends (prefixWord ++ tailWord_180234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180257 : List Nat := [1, 2, 3, 2, 5, 10]
def baseStart_180257 : Nat := 118140960795 + 180257 * 2 ^ 59
def prefixEnd_180257 : Nat := 4983230072969 + 3 ^ 40 * 180257 * 2
def baseEnd_180257 : Nat := 380899104269985503533

theorem tailTrace_180257 : CollatzResearch.WordTrace tailWord_180257 prefixEnd_180257 380899104269985503533 := by
  unfold tailWord_180257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574512907967149289755025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4383008605311432859836683 6574512907967149289755025)
  ·
    refine ⟨4930884680975361967316269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6574512907967149289755025 4930884680975361967316269)
    ·
      refine ⟨1849081755365760737743601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4930884680975361967316269 1849081755365760737743601)
      ·
        refine ⟨1386811316524320553307701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1849081755365760737743601 1386811316524320553307701)
        ·
          refine ⟨130013560924155051872597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1386811316524320553307701 130013560924155051872597)
          ·
            refine ⟨380899104269985503533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 130013560924155051872597 380899104269985503533)
            ·
              rfl

theorem cell23_180257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 10].length) (baseStart_180257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180257 prefixEnd_180257 := by exact prefixLift 180257
  have htrace : WordTrace (prefixWord ++ tailWord_180257) baseStart_180257 baseEnd_180257 := by
    simpa [prefixWord, tailWord_180257, baseEnd_180257] using wordTrace_append hprefix tailTrace_180257
  have hstable : (prefixWord ++ tailWord_180257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180257).length < 2 ^ (prefixWord ++ tailWord_180257).sum := by decide
  have hdescent : baseEnd_180257 < baseStart_180257 := by decide
  rcases family_descends (prefixWord ++ tailWord_180257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180284 : List Nat := [2, 2, 2, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_180284 : Nat := 118140960795 + 180284 * 2 ^ 59
def prefixEnd_180284 : Nat := 4983230072969 + 3 ^ 40 * 180284 * 2
def baseEnd_180284 : Nat := 92572346315277871720895

theorem tailTrace_180284 : CollatzResearch.WordTrace tailWord_180284 prefixEnd_180284 92572346315277871720895 := by
  unfold tailWord_180284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3287748839434666450493953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4383665119246221933991937 3287748839434666450493953)
  ·
    refine ⟨2465811629575999837870465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3287748839434666450493953 2465811629575999837870465)
    ·
      refine ⟨1849358722181999878402849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465811629575999837870465 1849358722181999878402849)
      ·
        refine ⟨1387019041636499908802137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1849358722181999878402849 1387019041636499908802137)
        ·
          refine ⟨1040264281227374931601603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1387019041636499908802137 1040264281227374931601603)
          ·
            refine ⟨1560396421841062397402405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040264281227374931601603 1560396421841062397402405)
            ·
              refine ⟨292574329095199199512951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1560396421841062397402405 292574329095199199512951)
              ·
                refine ⟨438861493642798799269427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292574329095199199512951 438861493642798799269427)
                ·
                  refine ⟨658292240464198198904141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438861493642798799269427 658292240464198198904141)
                  ·
                    refine ⟨246859590174074324589053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 658292240464198198904141 246859590174074324589053)
                    ·
                      refine ⟨92572346315277871720895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246859590174074324589053 92572346315277871720895)
                      ·
                        rfl

theorem cell23_180284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_180284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180284 prefixEnd_180284 := by exact prefixLift 180284
  have htrace : WordTrace (prefixWord ++ tailWord_180284) baseStart_180284 baseEnd_180284 := by
    simpa [prefixWord, tailWord_180284, baseEnd_180284] using wordTrace_append hprefix tailTrace_180284
  have hstable : (prefixWord ++ tailWord_180284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180284).length < 2 ^ (prefixWord ++ tailWord_180284).sum := by decide
  have hdescent : baseEnd_180284 < baseStart_180284 := by decide
  rcases family_descends (prefixWord ++ tailWord_180284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180301 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_180301 : Nat := 118140960795 + 180301 * 2 ^ 59
def prefixEnd_180301 : Nat := 4983230072969 + 3 ^ 40 * 180301 * 2
def baseEnd_180301 : Nat := 92581075486404305208317

theorem tailTrace_180301 : CollatzResearch.WordTrace tailWord_180301 prefixEnd_180301 92581075486404305208317 := by
  unfold tailWord_180301
  simp only [CollatzResearch.WordTrace]
  refine ⟨6576117719807744804356757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4384078479871829869571171 6576117719807744804356757)
  ·
    refine ⟨308255518115988037704223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6576117719807744804356757 308255518115988037704223)
    ·
      refine ⟨462383277173982056556335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308255518115988037704223 462383277173982056556335)
      ·
        refine ⟨693574915760973084834503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462383277173982056556335 693574915760973084834503)
        ·
          refine ⟨1040362373641459627251755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693574915760973084834503 1040362373641459627251755)
          ·
            refine ⟨1560543560462189440877633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040362373641459627251755 1560543560462189440877633)
            ·
              refine ⟨1170407670346642080658225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560543560462189440877633 1170407670346642080658225)
              ·
                refine ⟨877805752759981560493669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170407670346642080658225 877805752759981560493669)
                ·
                  refine ⟨164588578642496542592563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 877805752759981560493669 164588578642496542592563)
                  ·
                    refine ⟨246882867963744813888845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164588578642496542592563 246882867963744813888845)
                    ·
                      refine ⟨92581075486404305208317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 246882867963744813888845 92581075486404305208317)
                      ·
                        rfl

theorem cell23_180301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_180301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180301 prefixEnd_180301 := by exact prefixLift 180301
  have htrace : WordTrace (prefixWord ++ tailWord_180301) baseStart_180301 baseEnd_180301 := by
    simpa [prefixWord, tailWord_180301, baseEnd_180301] using wordTrace_append hprefix tailTrace_180301
  have hstable : (prefixWord ++ tailWord_180301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180301).length < 2 ^ (prefixWord ++ tailWord_180301).sum := by decide
  have hdescent : baseEnd_180301 < baseStart_180301 := by decide
  rcases family_descends (prefixWord ++ tailWord_180301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180324 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_180324 : Nat := 118140960795 + 180324 * 2 ^ 59
def prefixEnd_180324 : Nat := 4983230072969 + 3 ^ 40 * 180324 * 2
def baseEnd_180324 : Nat := 92592885541457715220711

theorem tailTrace_180324 : CollatzResearch.WordTrace tailWord_180324 prefixEnd_180324 92592885541457715220711 := by
  unfold tailWord_180324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288478299362209866222013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4384637732482946488296017 3288478299362209866222013)
  ·
    refine ⟨1233179362260828699833255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3288478299362209866222013 1233179362260828699833255)
    ·
      refine ⟨1849769043391243049749883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1233179362260828699833255 1849769043391243049749883)
      ·
        refine ⟨2774653565086864574624825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849769043391243049749883 2774653565086864574624825)
        ·
          refine ⟨2080990173815148430968619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2774653565086864574624825 2080990173815148430968619)
          ·
            refine ⟨3121485260722722646452929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080990173815148430968619 3121485260722722646452929)
            ·
              refine ⟨2341113945542041984839697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121485260722722646452929 2341113945542041984839697)
              ·
                refine ⟨1755835459156531488629773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2341113945542041984839697 1755835459156531488629773)
                ·
                  refine ⟨658438297183699308236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1755835459156531488629773 658438297183699308236165)
                  ·
                    refine ⟨123457180721943620294281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658438297183699308236165 123457180721943620294281)
                    ·
                      refine ⟨92592885541457715220711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123457180721943620294281 92592885541457715220711)
                      ·
                        rfl

theorem cell23_180324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_180324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180324 prefixEnd_180324 := by exact prefixLift 180324
  have htrace : WordTrace (prefixWord ++ tailWord_180324) baseStart_180324 baseEnd_180324 := by
    simpa [prefixWord, tailWord_180324, baseEnd_180324] using wordTrace_append hprefix tailTrace_180324
  have hstable : (prefixWord ++ tailWord_180324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180324).length < 2 ^ (prefixWord ++ tailWord_180324).sum := by decide
  have hdescent : baseEnd_180324 < baseStart_180324 := by decide
  rcases family_descends (prefixWord ++ tailWord_180324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180337 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_180337 : Nat := 118140960795 + 180337 * 2 ^ 59
def prefixEnd_180337 : Nat := 4983230072969 + 3 ^ 40 * 180337 * 2
def baseEnd_180337 : Nat := 92599560789966164358151

theorem tailTrace_180337 : CollatzResearch.WordTrace tailWord_180337 prefixEnd_180337 92599560789966164358151 := by
  unfold tailWord_180337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6577430747677322952667265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4384953831784881968444843 6577430747677322952667265)
  ·
    refine ⟨4933073060757992214500449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6577430747677322952667265 4933073060757992214500449)
    ·
      refine ⟨3699804795568494160875337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4933073060757992214500449 3699804795568494160875337)
      ·
        refine ⟨2774853596676370620656503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699804795568494160875337 2774853596676370620656503)
        ·
          refine ⟨4162280395014555930984755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774853596676370620656503 4162280395014555930984755)
          ·
            refine ⟨6243420592521833896477133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162280395014555930984755 6243420592521833896477133)
            ·
              refine ⟨2341282722195687711178925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6243420592521833896477133 2341282722195687711178925)
              ·
                refine ⟨877981020823382891692097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341282722195687711178925 877981020823382891692097)
                ·
                  refine ⟨658485765617537168769073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 877981020823382891692097 658485765617537168769073)
                  ·
                    refine ⟨493864324213152876576805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 658485765617537168769073 493864324213152876576805)
                    ·
                      refine ⟨92599560789966164358151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 493864324213152876576805 92599560789966164358151)
                      ·
                        rfl

theorem cell23_180337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_180337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180337 prefixEnd_180337 := by exact prefixLift 180337
  have htrace : WordTrace (prefixWord ++ tailWord_180337) baseStart_180337 baseEnd_180337 := by
    simpa [prefixWord, tailWord_180337, baseEnd_180337] using wordTrace_append hprefix tailTrace_180337
  have hstable : (prefixWord ++ tailWord_180337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180337).length < 2 ^ (prefixWord ++ tailWord_180337).sum := by decide
  have hdescent : baseEnd_180337 < baseStart_180337 := by decide
  rcases family_descends (prefixWord ++ tailWord_180337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180427 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6]
def baseStart_180427 : Nat := 118140960795 + 180427 * 2 ^ 59
def prefixEnd_180427 : Nat := 4983230072969 + 3 ^ 40 * 180427 * 2
def baseEnd_180427 : Nat := 92645774048870812232737

theorem tailTrace_180427 : CollatzResearch.WordTrace tailWord_180427 prefixEnd_180427 92645774048870812232737 := by
  unfold tailWord_180427
  simp only [CollatzResearch.WordTrace]
  refine ⟨6580713317351268323443535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387142211567512215629023 6580713317351268323443535)
  ·
    refine ⟨9871069976026902485165303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6580713317351268323443535 9871069976026902485165303)
    ·
      refine ⟨14806604964040353727747955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871069976026902485165303 14806604964040353727747955)
      ·
        refine ⟨22209907446060530591621933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14806604964040353727747955 22209907446060530591621933)
        ·
          refine ⟨8328715292272698971858225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22209907446060530591621933 8328715292272698971858225)
          ·
            refine ⟨6246536469204524228893669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328715292272698971858225 6246536469204524228893669)
            ·
              refine ⟨1171225587975848292917563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6246536469204524228893669 1171225587975848292917563)
              ·
                refine ⟨1756838381963772439376345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171225587975848292917563 1756838381963772439376345)
                ·
                  refine ⟨1317628786472829329532259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1756838381963772439376345 1317628786472829329532259)
                  ·
                    refine ⟨1976443179709243994298389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1317628786472829329532259 1976443179709243994298389)
                    ·
                      refine ⟨92645774048870812232737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1976443179709243994298389 92645774048870812232737)
                      ·
                        rfl

theorem cell23_180427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_180427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180427 prefixEnd_180427 := by exact prefixLift 180427
  have htrace : WordTrace (prefixWord ++ tailWord_180427) baseStart_180427 baseEnd_180427 := by
    simpa [prefixWord, tailWord_180427, baseEnd_180427] using wordTrace_append hprefix tailTrace_180427
  have hstable : (prefixWord ++ tailWord_180427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180427).length < 2 ^ (prefixWord ++ tailWord_180427).sum := by decide
  have hdescent : baseEnd_180427 < baseStart_180427 := by decide
  rcases family_descends (prefixWord ++ tailWord_180427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180457 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_180457 : Nat := 118140960795 + 180457 * 2 ^ 59
def prefixEnd_180457 : Nat := 4983230072969 + 3 ^ 40 * 180457 * 2
def baseEnd_180457 : Nat := 92661178468505694857599

theorem tailTrace_180457 : CollatzResearch.WordTrace tailWord_180457 prefixEnd_180457 92661178468505694857599 := by
  unfold tailWord_180457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6581807507242583447035625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4387871671495055631357083 6581807507242583447035625)
  ·
    refine ⟨4936355630431937585276719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6581807507242583447035625 4936355630431937585276719)
    ·
      refine ⟨7404533445647906377915079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4936355630431937585276719 7404533445647906377915079)
      ·
        refine ⟨11106800168471859566872619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7404533445647906377915079 11106800168471859566872619)
        ·
          refine ⟨16660200252707789350308929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106800168471859566872619 16660200252707789350308929)
          ·
            refine ⟨12495150189530842012731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16660200252707789350308929 12495150189530842012731697)
            ·
              refine ⟨9371362642148131509548773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12495150189530842012731697 9371362642148131509548773)
              ·
                refine ⟨1757130495402774658040395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9371362642148131509548773 1757130495402774658040395)
                ·
                  refine ⟨2635695743104161987060593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757130495402774658040395 2635695743104161987060593)
                  ·
                    refine ⟨1976771807328121490295445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2635695743104161987060593 1976771807328121490295445)
                    ·
                      refine ⟨92661178468505694857599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1976771807328121490295445 92661178468505694857599)
                      ·
                        rfl

theorem cell23_180457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_180457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180457 prefixEnd_180457 := by exact prefixLift 180457
  have htrace : WordTrace (prefixWord ++ tailWord_180457) baseStart_180457 baseEnd_180457 := by
    simpa [prefixWord, tailWord_180457, baseEnd_180457] using wordTrace_append hprefix tailTrace_180457
  have hstable : (prefixWord ++ tailWord_180457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180457).length < 2 ^ (prefixWord ++ tailWord_180457).sum := by decide
  have hdescent : baseEnd_180457 < baseStart_180457 := by decide
  rcases family_descends (prefixWord ++ tailWord_180457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180481 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_180481 : Nat := 118140960795 + 180481 * 2 ^ 59
def prefixEnd_180481 : Nat := 4983230072969 + 3 ^ 40 * 180481 * 2
def baseEnd_180481 : Nat := 92673502004213600957489

theorem tailTrace_180481 : CollatzResearch.WordTrace tailWord_180481 prefixEnd_180481 92673502004213600957489 := by
  unfold tailWord_180481
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582682859155635545909297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4388455239437090363939531 6582682859155635545909297)
  ·
    refine ⟨4937012144366726659431973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6582682859155635545909297 4937012144366726659431973)
    ·
      refine ⟨925689777068761248643495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4937012144366726659431973 925689777068761248643495)
      ·
        refine ⟨1388534665603141872965243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 925689777068761248643495 1388534665603141872965243)
        ·
          refine ⟨2082801998404712809447865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388534665603141872965243 2082801998404712809447865)
          ·
            refine ⟨1562101498803534607085899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082801998404712809447865 1562101498803534607085899)
            ·
              refine ⟨2343152248205301910628849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1562101498803534607085899 2343152248205301910628849)
              ·
                refine ⟨1757364186153976432971637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343152248205301910628849 1757364186153976432971637)
                ·
                  refine ⟨164752892451935290591091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1757364186153976432971637 164752892451935290591091)
                  ·
                    refine ⟨247129338677902935886637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164752892451935290591091 247129338677902935886637)
                    ·
                      refine ⟨92673502004213600957489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247129338677902935886637 92673502004213600957489)
                      ·
                        rfl

theorem cell23_180481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_180481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180481 prefixEnd_180481 := by exact prefixLift 180481
  have htrace : WordTrace (prefixWord ++ tailWord_180481) baseStart_180481 baseEnd_180481 := by
    simpa [prefixWord, tailWord_180481, baseEnd_180481] using wordTrace_append hprefix tailTrace_180481
  have hstable : (prefixWord ++ tailWord_180481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180481).length < 2 ^ (prefixWord ++ tailWord_180481).sum := by decide
  have hdescent : baseEnd_180481 < baseStart_180481 := by decide
  rcases family_descends (prefixWord ++ tailWord_180481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180491 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 4, 3, 2]
def baseStart_180491 : Nat := 118140960795 + 180491 * 2 ^ 59
def prefixEnd_180491 : Nat := 4983230072969 + 3 ^ 40 * 180491 * 2
def baseEnd_180491 : Nat := 92678636810758561832443

theorem tailTrace_180491 : CollatzResearch.WordTrace tailWord_180491 prefixEnd_180491 92678636810758561832443 := by
  unfold tailWord_180491
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583047589119407253773327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4388698392746271502515551 6583047589119407253773327)
  ·
    refine ⟨9874571383679110880659991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6583047589119407253773327 9874571383679110880659991)
    ·
      refine ⟨14811857075518666320989987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874571383679110880659991 14811857075518666320989987)
      ·
        refine ⟨22217785613277999481484981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811857075518666320989987 22217785613277999481484981)
        ·
          refine ⟨2082917401244812451389217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22217785613277999481484981 2082917401244812451389217)
          ·
            refine ⟨1562188050933609338541913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082917401244812451389217 1562188050933609338541913)
            ·
              refine ⟨1171641038200207003906435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562188050933609338541913 1171641038200207003906435)
              ·
                refine ⟨1757461557300310505859653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1171641038200207003906435 1757461557300310505859653)
                ·
                  refine ⟨329524041993808219848685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757461557300310505859653 329524041993808219848685)
                  ·
                    refine ⟨123571515747678082443257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329524041993808219848685 123571515747678082443257)
                    ·
                      refine ⟨92678636810758561832443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123571515747678082443257 92678636810758561832443)
                      ·
                        rfl

theorem cell23_180491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 3, 2].length) (baseStart_180491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180491 prefixEnd_180491 := by exact prefixLift 180491
  have htrace : WordTrace (prefixWord ++ tailWord_180491) baseStart_180491 baseEnd_180491 := by
    simpa [prefixWord, tailWord_180491, baseEnd_180491] using wordTrace_append hprefix tailTrace_180491
  have hstable : (prefixWord ++ tailWord_180491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180491).length < 2 ^ (prefixWord ++ tailWord_180491).sum := by decide
  have hdescent : baseEnd_180491 < baseStart_180491 := by decide
  rcases family_descends (prefixWord ++ tailWord_180491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180532 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_180532 : Nat := 118140960795 + 180532 * 2 ^ 59
def prefixEnd_180532 : Nat := 4983230072969 + 3 ^ 40 * 180532 * 2
def baseEnd_180532 : Nat := 92699689517592901419755

theorem tailTrace_180532 : CollatzResearch.WordTrace tailWord_180532 prefixEnd_180532 92699689517592901419755 := by
  unfold tailWord_180532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3292271490985435628007925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4389695321313914170677233 3292271490985435628007925)
  ·
    refine ⟨308650452279884590125743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3292271490985435628007925 308650452279884590125743)
    ·
      refine ⟨462975678419826885188615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308650452279884590125743 462975678419826885188615)
      ·
        refine ⟨694463517629740327782923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462975678419826885188615 694463517629740327782923)
        ·
          refine ⟨1041695276444610491674385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694463517629740327782923 1041695276444610491674385)
          ·
            refine ⟨781271457333457868755789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1041695276444610491674385 781271457333457868755789)
            ·
              refine ⟨292976796500046700783421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781271457333457868755789 292976796500046700783421)
              ·
                refine ⟨109866298687517512793783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292976796500046700783421 109866298687517512793783)
                ·
                  refine ⟨164799448031276269190675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109866298687517512793783 164799448031276269190675)
                  ·
                    refine ⟨247199172046914403786013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164799448031276269190675 247199172046914403786013)
                    ·
                      refine ⟨92699689517592901419755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247199172046914403786013 92699689517592901419755)
                      ·
                        rfl

theorem cell23_180532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_180532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180532 prefixEnd_180532 := by exact prefixLift 180532
  have htrace : WordTrace (prefixWord ++ tailWord_180532) baseStart_180532 baseEnd_180532 := by
    simpa [prefixWord, tailWord_180532, baseEnd_180532] using wordTrace_append hprefix tailTrace_180532
  have hstable : (prefixWord ++ tailWord_180532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180532).length < 2 ^ (prefixWord ++ tailWord_180532).sum := by decide
  have hdescent : baseEnd_180532 < baseStart_180532 := by decide
  rcases family_descends (prefixWord ++ tailWord_180532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180572 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_180572 : Nat := 118140960795 + 180572 * 2 ^ 59
def prefixEnd_180572 : Nat := 4983230072969 + 3 ^ 40 * 180572 * 2
def baseEnd_180572 : Nat := 92720228743772744919571

theorem tailTrace_180572 : CollatzResearch.WordTrace tailWord_180572 prefixEnd_180572 92720228743772744919571 := by
  unfold tailWord_180572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293000950912979043735985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4390667934550638724981313 3293000950912979043735985)
  ·
    refine ⟨2469750713184734282801989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293000950912979043735985 2469750713184734282801989)
    ·
      refine ⟨463078258722137678025373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2469750713184734282801989 463078258722137678025373)
      ·
        refine ⟨173654347020801629259515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463078258722137678025373 173654347020801629259515)
        ·
          refine ⟨260481520531202443889273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173654347020801629259515 260481520531202443889273)
          ·
            refine ⟨195361140398401832916955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 260481520531202443889273 195361140398401832916955)
            ·
              refine ⟨293041710597602749375433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195361140398401832916955 293041710597602749375433)
              ·
                refine ⟨219781282948202062031575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293041710597602749375433 219781282948202062031575)
                ·
                  refine ⟨329671924422303093047363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219781282948202062031575 329671924422303093047363)
                  ·
                    refine ⟨494507886633454639571045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329671924422303093047363 494507886633454639571045)
                    ·
                      refine ⟨92720228743772744919571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 494507886633454639571045 92720228743772744919571)
                      ·
                        rfl

theorem cell23_180572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_180572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180572 prefixEnd_180572 := by exact prefixLift 180572
  have htrace : WordTrace (prefixWord ++ tailWord_180572) baseStart_180572 baseEnd_180572 := by
    simpa [prefixWord, tailWord_180572, baseEnd_180572] using wordTrace_append hprefix tailTrace_180572
  have hstable : (prefixWord ++ tailWord_180572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180572).length < 2 ^ (prefixWord ++ tailWord_180572).sum := by decide
  have hdescent : baseEnd_180572 < baseStart_180572 := by decide
  rcases family_descends (prefixWord ++ tailWord_180572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180588 : List Nat := [2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_180588 : Nat := 118140960795 + 180588 * 2 ^ 59
def prefixEnd_180588 : Nat := 4983230072969 + 3 ^ 40 * 180588 * 2
def baseEnd_180588 : Nat := 92728444434244682319497

theorem tailTrace_180588 : CollatzResearch.WordTrace tailWord_180588 prefixEnd_180588 92728444434244682319497 := by
  unfold tailWord_180588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293292734883996410027209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4391056979845328546702945 3293292734883996410027209)
  ·
    refine ⟨2469969551162997307520407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293292734883996410027209 2469969551162997307520407)
    ·
      refine ⟨3704954326744495961280611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469969551162997307520407 3704954326744495961280611)
      ·
        refine ⟨5557431490116743941920917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704954326744495961280611 5557431490116743941920917)
        ·
          refine ⟨260504601099222372277543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5557431490116743941920917 260504601099222372277543)
          ·
            refine ⟨390756901648833558416315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260504601099222372277543 390756901648833558416315)
            ·
              refine ⟨586135352473250337624473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390756901648833558416315 586135352473250337624473)
              ·
                refine ⟨439601514354937753218355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586135352473250337624473 439601514354937753218355)
                ·
                  refine ⟨659402271532406629827533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439601514354937753218355 659402271532406629827533)
                  ·
                    refine ⟨247275851824652486185325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 659402271532406629827533 247275851824652486185325)
                    ·
                      refine ⟨92728444434244682319497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247275851824652486185325 92728444434244682319497)
                      ·
                        rfl

theorem cell23_180588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_180588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180588 prefixEnd_180588 := by exact prefixLift 180588
  have htrace : WordTrace (prefixWord ++ tailWord_180588) baseStart_180588 baseEnd_180588 := by
    simpa [prefixWord, tailWord_180588, baseEnd_180588] using wordTrace_append hprefix tailTrace_180588
  have hstable : (prefixWord ++ tailWord_180588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180588).length < 2 ^ (prefixWord ++ tailWord_180588).sum := by decide
  have hdescent : baseEnd_180588 < baseStart_180588 := by decide
  rcases family_descends (prefixWord ++ tailWord_180588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180605 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_180605 : Nat := 118140960795 + 180605 * 2 ^ 59
def prefixEnd_180605 : Nat := 4983230072969 + 3 ^ 40 * 180605 * 2
def baseEnd_180605 : Nat := 92737173605371115806919

theorem tailTrace_180605 : CollatzResearch.WordTrace tailWord_180605 prefixEnd_180605 92737173605371115806919 := by
  unfold tailWord_180605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587205510706404723423269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4391470340470936482282179 6587205510706404723423269)
  ·
    refine ⟨1235101033257450885641863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6587205510706404723423269 1235101033257450885641863)
    ·
      refine ⟨1852651549886176328462795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235101033257450885641863 1852651549886176328462795)
      ·
        refine ⟨2778977324829264492694193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852651549886176328462795 2778977324829264492694193)
        ·
          refine ⟨2084232993621948369520645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778977324829264492694193 2084232993621948369520645)
          ·
            refine ⟨390793686304115319285121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2084232993621948369520645 390793686304115319285121)
            ·
              refine ⟨293095264728086489463841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390793686304115319285121 293095264728086489463841)
              ·
                refine ⟨219821448546064867097881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293095264728086489463841 219821448546064867097881)
                ·
                  refine ⟨164866086409548650323411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219821448546064867097881 164866086409548650323411)
                  ·
                    refine ⟨247299129614322975485117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 164866086409548650323411 247299129614322975485117)
                    ·
                      refine ⟨92737173605371115806919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247299129614322975485117 92737173605371115806919)
                      ·
                        rfl

theorem cell23_180605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_180605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180605 prefixEnd_180605 := by exact prefixLift 180605
  have htrace : WordTrace (prefixWord ++ tailWord_180605) baseStart_180605 baseEnd_180605 := by
    simpa [prefixWord, tailWord_180605, baseEnd_180605] using wordTrace_append hprefix tailTrace_180605
  have hstable : (prefixWord ++ tailWord_180605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180605).length < 2 ^ (prefixWord ++ tailWord_180605).sum := by decide
  have hdescent : baseEnd_180605 < baseStart_180605 := by decide
  rcases family_descends (prefixWord ++ tailWord_180605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180668 : List Nat := [2, 2, 2, 4, 1, 2, 2, 1, 7]
def baseStart_180668 : Nat := 118140960795 + 180668 * 2 ^ 59
def prefixEnd_180668 : Nat := 4983230072969 + 3 ^ 40 * 180668 * 2
def baseEnd_180668 : Nat := 10307724765178263257681

theorem tailTrace_180668 : CollatzResearch.WordTrace tailWord_180668 prefixEnd_180668 10307724765178263257681 := by
  unfold tailWord_180668
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294751654739083241483329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4393002206318777655311105 3294751654739083241483329)
  ·
    refine ⟨2471063741054312431112497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3294751654739083241483329 2471063741054312431112497)
    ·
      refine ⟨1853297805790734323334373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471063741054312431112497 1853297805790734323334373)
      ·
        refine ⟨347493338585762685625195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1853297805790734323334373 347493338585762685625195)
        ·
          refine ⟨521240007878644028437793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347493338585762685625195 521240007878644028437793)
          ·
            refine ⟨390930005908983021328345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521240007878644028437793 390930005908983021328345)
            ·
              refine ⟨293197504431737265996259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 390930005908983021328345 293197504431737265996259)
              ·
                refine ⟨439796256647605898994389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293197504431737265996259 439796256647605898994389)
                ·
                  refine ⟨10307724765178263257681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 439796256647605898994389 10307724765178263257681)
                  ·
                    rfl

theorem cell23_180668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_180668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180668 prefixEnd_180668 := by exact prefixLift 180668
  have htrace : WordTrace (prefixWord ++ tailWord_180668) baseStart_180668 baseEnd_180668 := by
    simpa [prefixWord, tailWord_180668, baseEnd_180668] using wordTrace_append hprefix tailTrace_180668
  have hstable : (prefixWord ++ tailWord_180668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180668).length < 2 ^ (prefixWord ++ tailWord_180668).sum := by decide
  have hdescent : baseEnd_180668 < baseStart_180668 := by decide
  rcases family_descends (prefixWord ++ tailWord_180668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180718 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_180718 : Nat := 118140960795 + 180718 * 2 ^ 59
def prefixEnd_180718 : Nat := 4983230072969 + 3 ^ 40 * 180718 * 2
def baseEnd_180718 : Nat := 92795196919329173693899

theorem tailTrace_180718 : CollatzResearch.WordTrace tailWord_180718 prefixEnd_180718 92795196919329173693899 := by
  unfold tailWord_180718
  simp only [CollatzResearch.WordTrace]
  refine ⟨823915869912128127785851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4394217972864683348191205 823915869912128127785851)
  ·
    refine ⟨1235873804868192191678777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 823915869912128127785851 1235873804868192191678777)
    ·
      refine ⟨926905353651144143759083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1235873804868192191678777 926905353651144143759083)
      ·
        refine ⟨1390358030476716215638625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 926905353651144143759083 1390358030476716215638625)
        ·
          refine ⟨1042768522857537161728969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1390358030476716215638625 1042768522857537161728969)
          ·
            refine ⟨782076392143152871296727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042768522857537161728969 782076392143152871296727)
            ·
              refine ⟨1173114588214729306945091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782076392143152871296727 1173114588214729306945091)
              ·
                refine ⟨1759671882322093960417637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1173114588214729306945091 1759671882322093960417637)
                ·
                  refine ⟨329938477935392617578307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759671882322093960417637 329938477935392617578307)
                  ·
                    refine ⟨494907716903088926367461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 329938477935392617578307 494907716903088926367461)
                    ·
                      refine ⟨92795196919329173693899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 494907716903088926367461 92795196919329173693899)
                      ·
                        rfl

theorem cell23_180718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_180718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180718 prefixEnd_180718 := by exact prefixLift 180718
  have htrace : WordTrace (prefixWord ++ tailWord_180718) baseStart_180718 baseEnd_180718 := by
    simpa [prefixWord, tailWord_180718, baseEnd_180718] using wordTrace_append hprefix tailTrace_180718
  have hstable : (prefixWord ++ tailWord_180718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180718).length < 2 ^ (prefixWord ++ tailWord_180718).sum := by decide
  have hdescent : baseEnd_180718 < baseStart_180718 := by decide
  rcases family_descends (prefixWord ++ tailWord_180718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180725 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_180725 : Nat := 118140960795 + 180725 * 2 ^ 59
def prefixEnd_180725 : Nat := 4983230072969 + 3 ^ 40 * 180725 * 2
def baseEnd_180725 : Nat := 92798791283910646306367

theorem tailTrace_180725 : CollatzResearch.WordTrace tailWord_180725 prefixEnd_180725 92798791283910646306367 := by
  unfold tailWord_180725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6591582270271665217791629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4394388180181110145194419 6591582270271665217791629)
  ·
    refine ⟨2471843351351874456671861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6591582270271665217791629 2471843351351874456671861)
    ·
      refine ⟨231735314189238230312987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2471843351351874456671861 231735314189238230312987)
      ·
        refine ⟨347602971283857345469481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231735314189238230312987 347602971283857345469481)
        ·
          refine ⟨260702228462893009102111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347602971283857345469481 260702228462893009102111)
          ·
            refine ⟨391053342694339513653167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260702228462893009102111 391053342694339513653167)
            ·
              refine ⟨586580014041509270479751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391053342694339513653167 586580014041509270479751)
              ·
                refine ⟨879870021062263905719627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586580014041509270479751 879870021062263905719627)
                ·
                  refine ⟨1319805031593395858579441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 879870021062263905719627 1319805031593395858579441)
                  ·
                    refine ⟨989853773695046893934581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1319805031593395858579441 989853773695046893934581)
                    ·
                      refine ⟨92798791283910646306367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 989853773695046893934581 92798791283910646306367)
                      ·
                        rfl

theorem cell23_180725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_180725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180725 prefixEnd_180725 := by exact prefixLift 180725
  have htrace : WordTrace (prefixWord ++ tailWord_180725) baseStart_180725 baseEnd_180725 := by
    simpa [prefixWord, tailWord_180725, baseEnd_180725] using wordTrace_append hprefix tailTrace_180725
  have hstable : (prefixWord ++ tailWord_180725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180725).length < 2 ^ (prefixWord ++ tailWord_180725).sum := by decide
  have hdescent : baseEnd_180725 < baseStart_180725 := by decide
  rcases family_descends (prefixWord ++ tailWord_180725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180751 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3]
def baseStart_180751 : Nat := 118140960795 + 180751 * 2 ^ 59
def prefixEnd_180751 : Nat := 4983230072969 + 3 ^ 40 * 180751 * 2
def baseEnd_180751 : Nat := 92812141780927544581247

theorem tailTrace_180751 : CollatzResearch.WordTrace tailWord_180751 prefixEnd_180751 92812141780927544581247 := by
  unfold tailWord_180751
  simp only [CollatzResearch.WordTrace]
  refine ⟨6592530568177471658238107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4395020378784981105492071 6592530568177471658238107)
  ·
    refine ⟨9888795852266207487357161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6592530568177471658238107 9888795852266207487357161)
    ·
      refine ⟨7416596889199655615517871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9888795852266207487357161 7416596889199655615517871)
      ·
        refine ⟨11124895333799483423276807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7416596889199655615517871 11124895333799483423276807)
        ·
          refine ⟨16687343000699225134915211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11124895333799483423276807 16687343000699225134915211)
          ·
            refine ⟨25031014501048837702372817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16687343000699225134915211 25031014501048837702372817)
            ·
              refine ⟨18773260875786628276779613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25031014501048837702372817 18773260875786628276779613)
              ·
                refine ⟨7039972828419985603792355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18773260875786628276779613 7039972828419985603792355)
                ·
                  refine ⟨10559959242629978405688533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039972828419985603792355 10559959242629978405688533)
                  ·
                    refine ⟨247499044749140118883325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10559959242629978405688533 247499044749140118883325)
                    ·
                      refine ⟨92812141780927544581247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247499044749140118883325 92812141780927544581247)
                      ·
                        rfl

theorem cell23_180751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7, 3].length) (baseStart_180751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180751 prefixEnd_180751 := by exact prefixLift 180751
  have htrace : WordTrace (prefixWord ++ tailWord_180751) baseStart_180751 baseEnd_180751 := by
    simpa [prefixWord, tailWord_180751, baseEnd_180751] using wordTrace_append hprefix tailTrace_180751
  have hstable : (prefixWord ++ tailWord_180751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180751).length < 2 ^ (prefixWord ++ tailWord_180751).sum := by decide
  have hdescent : baseEnd_180751 < baseStart_180751 := by decide
  rcases family_descends (prefixWord ++ tailWord_180751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180818 : List Nat := [3, 2, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_180818 : Nat := 118140960795 + 180818 * 2 ^ 59
def prefixEnd_180818 : Nat := 4983230072969 + 3 ^ 40 * 180818 * 2
def baseEnd_180818 : Nat := 30948848328259594147813

theorem tailTrace_180818 : CollatzResearch.WordTrace tailWord_180818 prefixEnd_180818 30948848328259594147813 := by
  unfold tailWord_180818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648743564733685525231777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4396649505956494733951405 1648743564733685525231777)
  ·
    refine ⟨1236557673550264143923833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1648743564733685525231777 1236557673550264143923833)
    ·
      refine ⟨927418255162698107942875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1236557673550264143923833 927418255162698107942875)
      ·
        refine ⟨1391127382744047161914313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927418255162698107942875 1391127382744047161914313)
        ·
          refine ⟨1043345537058035371435735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1391127382744047161914313 1043345537058035371435735)
          ·
            refine ⟨1565018305587053057153603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043345537058035371435735 1565018305587053057153603)
            ·
              refine ⟨2347527458380579585730405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565018305587053057153603 2347527458380579585730405)
              ·
                refine ⟨440161398446358672324451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2347527458380579585730405 440161398446358672324451)
                ·
                  refine ⟨660242097669538008486677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440161398446358672324451 660242097669538008486677)
                  ·
                    refine ⟨30948848328259594147813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 660242097669538008486677 30948848328259594147813)
                    ·
                      rfl

theorem cell23_180818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_180818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180818 prefixEnd_180818 := by exact prefixLift 180818
  have htrace : WordTrace (prefixWord ++ tailWord_180818) baseStart_180818 baseEnd_180818 := by
    simpa [prefixWord, tailWord_180818, baseEnd_180818] using wordTrace_append hprefix tailTrace_180818
  have hstable : (prefixWord ++ tailWord_180818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180818).length < 2 ^ (prefixWord ++ tailWord_180818).sum := by decide
  have hdescent : baseEnd_180818 < baseStart_180818 := by decide
  rcases family_descends (prefixWord ++ tailWord_180818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180841 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7]
def baseStart_180841 : Nat := 118140960795 + 180841 * 2 ^ 59
def prefixEnd_180841 : Nat := 4983230072969 + 3 ^ 40 * 180841 * 2
def baseEnd_180841 : Nat := 92858355039832192455833

theorem tailTrace_180841 : CollatzResearch.WordTrace tailWord_180841 prefixEnd_180841 92858355039832192455833 := by
  unfold tailWord_180841
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595813137851417029014377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397208758567611352676251 6595813137851417029014377)
  ·
    refine ⟨4946859853388562771760783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6595813137851417029014377 4946859853388562771760783)
    ·
      refine ⟨7420289780082844157641175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4946859853388562771760783 7420289780082844157641175)
      ·
        refine ⟨11130434670124266236461763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7420289780082844157641175 11130434670124266236461763)
        ·
          refine ⟨16695652005186399354692645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11130434670124266236461763 16695652005186399354692645)
          ·
            refine ⟨3130434750972449879004871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16695652005186399354692645 3130434750972449879004871)
            ·
              refine ⟨4695652126458674818507307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3130434750972449879004871 4695652126458674818507307)
              ·
                refine ⟨7043478189688012227760961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4695652126458674818507307 7043478189688012227760961)
                ·
                  refine ⟨5282608642266009170820721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7043478189688012227760961 5282608642266009170820721)
                  ·
                    refine ⟨3961956481699506878115541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5282608642266009170820721 3961956481699506878115541)
                    ·
                      refine ⟨92858355039832192455833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3961956481699506878115541 92858355039832192455833)
                      ·
                        rfl

theorem cell23_180841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_180841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180841 prefixEnd_180841 := by exact prefixLift 180841
  have htrace : WordTrace (prefixWord ++ tailWord_180841) baseStart_180841 baseEnd_180841 := by
    simpa [prefixWord, tailWord_180841, baseEnd_180841] using wordTrace_append hprefix tailTrace_180841
  have hstable : (prefixWord ++ tailWord_180841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180841).length < 2 ^ (prefixWord ++ tailWord_180841).sum := by decide
  have hdescent : baseEnd_180841 < baseStart_180841 := by decide
  rcases family_descends (prefixWord ++ tailWord_180841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180845 : List Nat := [1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_180845 : Nat := 118140960795 + 180845 * 2 ^ 59
def prefixEnd_180845 : Nat := 4983230072969 + 3 ^ 40 * 180845 * 2
def baseEnd_180845 : Nat := 92860408962450176805815

theorem tailTrace_180845 : CollatzResearch.WordTrace tailWord_180845 prefixEnd_180845 92860408962450176805815 := by
  unfold tailWord_180845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6595959029836925712159989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397306019891283808106659 6595959029836925712159989)
  ·
    refine ⟨618371159047211785514999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6595959029836925712159989 618371159047211785514999)
    ·
      refine ⟨927556738570817678272499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618371159047211785514999 927556738570817678272499)
      ·
        refine ⟨1391335107856226517408749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 927556738570817678272499 1391335107856226517408749)
        ·
          refine ⟨521750665446084944028281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1391335107856226517408749 521750665446084944028281)
          ·
            refine ⟨391312999084563708021211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521750665446084944028281 391312999084563708021211)
            ·
              refine ⟨586969498626845562031817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391312999084563708021211 586969498626845562031817)
              ·
                refine ⟨440227123970134171523863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586969498626845562031817 440227123970134171523863)
                ·
                  refine ⟨660340685955201257285795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440227123970134171523863 660340685955201257285795)
                  ·
                    refine ⟨990511028932801885928693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 660340685955201257285795 990511028932801885928693)
                    ·
                      refine ⟨92860408962450176805815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 990511028932801885928693 92860408962450176805815)
                      ·
                        rfl

theorem cell23_180845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_180845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180845 prefixEnd_180845 := by exact prefixLift 180845
  have htrace : WordTrace (prefixWord ++ tailWord_180845) baseStart_180845 baseEnd_180845 := by
    simpa [prefixWord, tailWord_180845, baseEnd_180845] using wordTrace_append hprefix tailTrace_180845
  have hstable : (prefixWord ++ tailWord_180845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180845).length < 2 ^ (prefixWord ++ tailWord_180845).sum := by decide
  have hdescent : baseEnd_180845 < baseStart_180845 := by decide
  rcases family_descends (prefixWord ++ tailWord_180845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180851 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6]
def baseStart_180851 : Nat := 118140960795 + 180851 * 2 ^ 59
def prefixEnd_180851 : Nat := 4983230072969 + 3 ^ 40 * 180851 * 2
def baseEnd_180851 : Nat := 92863489846377153330787

theorem tailTrace_180851 : CollatzResearch.WordTrace tailWord_180851 prefixEnd_180851 92863489846377153330787 := by
  unfold tailWord_180851
  simp only [CollatzResearch.WordTrace]
  refine ⟨6596177867815188736878407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4397451911876792491252271 6596177867815188736878407)
  ·
    refine ⟨9894266801722783105317611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6596177867815188736878407 9894266801722783105317611)
    ·
      refine ⟨14841400202584174657976417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9894266801722783105317611 14841400202584174657976417)
      ·
        refine ⟨11131050151938130993482313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14841400202584174657976417 11131050151938130993482313)
        ·
          refine ⟨8348287613953598245111735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11131050151938130993482313 8348287613953598245111735)
          ·
            refine ⟨12522431420930397367667603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8348287613953598245111735 12522431420930397367667603)
            ·
              refine ⟨18783647131395596051501405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12522431420930397367667603 18783647131395596051501405)
              ·
                refine ⟨7043867674273348519313027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18783647131395596051501405 7043867674273348519313027)
                ·
                  refine ⟨10565801511410022778969541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7043867674273348519313027 10565801511410022778969541)
                  ·
                    refine ⟨1981087783389379271056789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10565801511410022778969541 1981087783389379271056789)
                    ·
                      refine ⟨92863489846377153330787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1981087783389379271056789 92863489846377153330787)
                      ·
                        rfl

theorem cell23_180851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_180851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180851 prefixEnd_180851 := by exact prefixLift 180851
  have htrace : WordTrace (prefixWord ++ tailWord_180851) baseStart_180851 baseEnd_180851 := by
    simpa [prefixWord, tailWord_180851, baseEnd_180851] using wordTrace_append hprefix tailTrace_180851
  have hstable : (prefixWord ++ tailWord_180851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180851).length < 2 ^ (prefixWord ++ tailWord_180851).sum := by decide
  have hdescent : baseEnd_180851 < baseStart_180851 := by decide
  rcases family_descends (prefixWord ++ tailWord_180851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180885 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_180885 : Nat := 118140960795 + 180885 * 2 ^ 59
def prefixEnd_180885 : Nat := 4983230072969 + 3 ^ 40 * 180885 * 2
def baseEnd_180885 : Nat := 92880948188630020305631

theorem tailTrace_180885 : CollatzResearch.WordTrace tailWord_180885 prefixEnd_180885 92880948188630020305631 := by
  unfold tailWord_180885
  simp only [CollatzResearch.WordTrace]
  refine ⟨6597417949692012543616109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4398278633128008362410739 6597417949692012543616109)
  ·
    refine ⟨2474031731134504703856041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6597417949692012543616109 2474031731134504703856041)
    ·
      refine ⟨1855523798350878527892031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2474031731134504703856041 1855523798350878527892031)
      ·
        refine ⟨2783285697526317791838047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1855523798350878527892031 2783285697526317791838047)
        ·
          refine ⟨4174928546289476687757071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2783285697526317791838047 4174928546289476687757071)
          ·
            refine ⟨6262392819434215031635607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4174928546289476687757071 6262392819434215031635607)
            ·
              refine ⟨9393589229151322547453411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6262392819434215031635607 9393589229151322547453411)
              ·
                refine ⟨14090383843726983821180117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9393589229151322547453411 14090383843726983821180117)
                ·
                  refine ⟨330243371337351183308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14090383843726983821180117 330243371337351183308909)
                  ·
                    refine ⟨123841264251506693740841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330243371337351183308909 123841264251506693740841)
                    ·
                      refine ⟨92880948188630020305631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123841264251506693740841 92880948188630020305631)
                      ·
                        rfl

theorem cell23_180885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_180885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180885 prefixEnd_180885 := by exact prefixLift 180885
  have htrace : WordTrace (prefixWord ++ tailWord_180885) baseStart_180885 baseEnd_180885 := by
    simpa [prefixWord, tailWord_180885, baseEnd_180885] using wordTrace_append hprefix tailTrace_180885
  have hstable : (prefixWord ++ tailWord_180885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180885).length < 2 ^ (prefixWord ++ tailWord_180885).sum := by decide
  have hdescent : baseEnd_180885 < baseStart_180885 := by decide
  rcases family_descends (prefixWord ++ tailWord_180885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180888 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_180888 : Nat := 118140960795 + 180888 * 2 ^ 59
def prefixEnd_180888 : Nat := 4983230072969 + 3 ^ 40 * 180888 * 2
def baseEnd_180888 : Nat := 92882488630593508568117

theorem tailTrace_180888 : CollatzResearch.WordTrace tailWord_180888 prefixEnd_180888 92882488630593508568117 := by
  unfold tailWord_180888
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298763684340572027987659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4398351579120762703983545 3298763684340572027987659)
  ·
    refine ⟨4948145526510858041981489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3298763684340572027987659 4948145526510858041981489)
    ·
      refine ⟨3711109144883143531486117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4948145526510858041981489 3711109144883143531486117)
      ·
        refine ⟨695832964665589412153647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3711109144883143531486117 695832964665589412153647)
        ·
          refine ⟨1043749446998384118230471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695832964665589412153647 1043749446998384118230471)
          ·
            refine ⟨1565624170497576177345707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1043749446998384118230471 1565624170497576177345707)
            ·
              refine ⟨2348436255746364266018561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565624170497576177345707 2348436255746364266018561)
              ·
                refine ⟨1761327191809773199513921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348436255746364266018561 1761327191809773199513921)
                ·
                  refine ⟨1320995393857329899635441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761327191809773199513921 1320995393857329899635441)
                  ·
                    refine ⟨990746545392997424726581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1320995393857329899635441 990746545392997424726581)
                    ·
                      refine ⟨92882488630593508568117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 990746545392997424726581 92882488630593508568117)
                      ·
                        rfl

theorem cell23_180888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_180888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180888 prefixEnd_180888 := by exact prefixLift 180888
  have htrace : WordTrace (prefixWord ++ tailWord_180888) baseStart_180888 baseEnd_180888 := by
    simpa [prefixWord, tailWord_180888, baseEnd_180888] using wordTrace_append hprefix tailTrace_180888
  have hstable : (prefixWord ++ tailWord_180888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180888).length < 2 ^ (prefixWord ++ tailWord_180888).sum := by decide
  have hdescent : baseEnd_180888 < baseStart_180888 := by decide
  rcases family_descends (prefixWord ++ tailWord_180888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180892 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_180892 : Nat := 118140960795 + 180892 * 2 ^ 59
def prefixEnd_180892 : Nat := 4983230072969 + 3 ^ 40 * 180892 * 2
def baseEnd_180892 : Nat := 92884542553211492918099

theorem tailTrace_180892 : CollatzResearch.WordTrace tailWord_180892 prefixEnd_180892 92884542553211492918099 := by
  unfold tailWord_180892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3298836630333326369560465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4398448840444435159413953 3298836630333326369560465)
  ·
    refine ⟨2474127472749994777170349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3298836630333326369560465 2474127472749994777170349)
    ·
      refine ⟨927797802281248041438881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2474127472749994777170349 927797802281248041438881)
      ·
        refine ⟨695848351710936031079161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 927797802281248041438881 695848351710936031079161)
        ·
          refine ⟨521886263783202023309371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 695848351710936031079161 521886263783202023309371)
          ·
            refine ⟨782829395674803034964057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521886263783202023309371 782829395674803034964057)
            ·
              refine ⟨587122046756102276223043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 782829395674803034964057 587122046756102276223043)
              ·
                refine ⟨880683070134153414334565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587122046756102276223043 880683070134153414334565)
                ·
                  refine ⟨165128075650153765187731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 880683070134153414334565 165128075650153765187731)
                  ·
                    refine ⟨247692113475230647781597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165128075650153765187731 247692113475230647781597)
                    ·
                      refine ⟨92884542553211492918099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247692113475230647781597 92884542553211492918099)
                      ·
                        rfl

theorem cell23_180892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_180892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180892 prefixEnd_180892 := by exact prefixLift 180892
  have htrace : WordTrace (prefixWord ++ tailWord_180892) baseStart_180892 baseEnd_180892 := by
    simpa [prefixWord, tailWord_180892, baseEnd_180892] using wordTrace_append hprefix tailTrace_180892
  have hstable : (prefixWord ++ tailWord_180892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180892).length < 2 ^ (prefixWord ++ tailWord_180892).sum := by decide
  have hdescent : baseEnd_180892 < baseStart_180892 := by decide
  rcases family_descends (prefixWord ++ tailWord_180892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180903 : List Nat := [1, 1, 6, 3, 2, 1, 2, 1, 2, 4]
def baseStart_180903 : Nat := 118140960795 + 180903 * 2 ^ 59
def prefixEnd_180903 : Nat := 4983230072969 + 3 ^ 40 * 180903 * 2
def baseEnd_180903 : Nat := 30963396946803649960183

theorem tailTrace_180903 : CollatzResearch.WordTrace tailWord_180903 prefixEnd_180903 30963396946803649960183 := by
  unfold tailWord_180903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598074463626801617771363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4398716309084534411847575 6598074463626801617771363)
  ·
    refine ⟨9897111695440202426657045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6598074463626801617771363 9897111695440202426657045)
    ·
      refine ⟨463927110723759488749549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9897111695440202426657045 463927110723759488749549)
      ·
        refine ⟨173972666521409808281081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 463927110723759488749549 173972666521409808281081)
        ·
          refine ⟨130479499891057356210811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173972666521409808281081 130479499891057356210811)
          ·
            refine ⟨195719249836586034316217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130479499891057356210811 195719249836586034316217)
            ·
              refine ⟨146789437377439525737163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195719249836586034316217 146789437377439525737163)
              ·
                refine ⟨220184156066159288605745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146789437377439525737163 220184156066159288605745)
                ·
                  refine ⟨165138117049619466454309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220184156066159288605745 165138117049619466454309)
                  ·
                    refine ⟨30963396946803649960183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165138117049619466454309 30963396946803649960183)
                    ·
                      rfl

theorem cell23_180903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_180903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180903 prefixEnd_180903 := by exact prefixLift 180903
  have htrace : WordTrace (prefixWord ++ tailWord_180903) baseStart_180903 baseEnd_180903 := by
    simpa [prefixWord, tailWord_180903, baseEnd_180903] using wordTrace_append hprefix tailTrace_180903
  have hstable : (prefixWord ++ tailWord_180903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180903).length < 2 ^ (prefixWord ++ tailWord_180903).sum := by decide
  have hdescent : baseEnd_180903 < baseStart_180903 := by decide
  rcases family_descends (prefixWord ++ tailWord_180903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180909 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_180909 : Nat := 118140960795 + 180909 * 2 ^ 59
def prefixEnd_180909 : Nat := 4983230072969 + 3 ^ 40 * 180909 * 2
def baseEnd_180909 : Nat := 92893271724337926405521

theorem tailTrace_180909 : CollatzResearch.WordTrace tailWord_180909 prefixEnd_180909 92893271724337926405521 := by
  unfold tailWord_180909
  simp only [CollatzResearch.WordTrace]
  refine ⟨6598293301605064642489781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4398862201070043094993187 6598293301605064642489781)
  ·
    refine ⟨618589997025474810233417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6598293301605064642489781 618589997025474810233417)
    ·
      refine ⟨463942497769106107675063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 618589997025474810233417 463942497769106107675063)
      ·
        refine ⟨695913746653659161512595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463942497769106107675063 695913746653659161512595)
        ·
          refine ⟨1043870619980488742268893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695913746653659161512595 1043870619980488742268893)
          ·
            refine ⟨391451482492683278350835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1043870619980488742268893 391451482492683278350835)
            ·
              refine ⟨587177223739024917526253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391451482492683278350835 587177223739024917526253)
              ·
                refine ⟨220191458902134344072345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 587177223739024917526253 220191458902134344072345)
                ·
                  refine ⟨165143594176600758054259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220191458902134344072345 165143594176600758054259)
                  ·
                    refine ⟨247715391264901137081389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165143594176600758054259 247715391264901137081389)
                    ·
                      refine ⟨92893271724337926405521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247715391264901137081389 92893271724337926405521)
                      ·
                        rfl

theorem cell23_180909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_180909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180909 prefixEnd_180909 := by exact prefixLift 180909
  have htrace : WordTrace (prefixWord ++ tailWord_180909) baseStart_180909 baseEnd_180909 := by
    simpa [prefixWord, tailWord_180909, baseEnd_180909] using wordTrace_append hprefix tailTrace_180909
  have hstable : (prefixWord ++ tailWord_180909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180909).length < 2 ^ (prefixWord ++ tailWord_180909).sum := by decide
  have hdescent : baseEnd_180909 < baseStart_180909 := by decide
  rcases family_descends (prefixWord ++ tailWord_180909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180932 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_180932 : Nat := 118140960795 + 180932 * 2 ^ 59
def prefixEnd_180932 : Nat := 4983230072969 + 3 ^ 40 * 180932 * 2
def baseEnd_180932 : Nat := 92905081779391336417915

theorem tailTrace_180932 : CollatzResearch.WordTrace tailWord_180932 prefixEnd_180932 92905081779391336417915 := by
  unfold tailWord_180932
  simp only [CollatzResearch.WordTrace]
  refine ⟨3299566090260869785288525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4399421453681159713718033 3299566090260869785288525)
  ·
    refine ⟨1237337283847826169483197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3299566090260869785288525 1237337283847826169483197)
    ·
      refine ⟨464001481442934813556199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1237337283847826169483197 464001481442934813556199)
      ·
        refine ⟨696002222164402220334299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464001481442934813556199 696002222164402220334299)
        ·
          refine ⟨1044003333246603330501449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696002222164402220334299 1044003333246603330501449)
          ·
            refine ⟨783002499934952497876087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044003333246603330501449 783002499934952497876087)
            ·
              refine ⟨1174503749902428746814131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783002499934952497876087 1174503749902428746814131)
              ·
                refine ⟨1761755624853643120221197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174503749902428746814131 1761755624853643120221197)
                ·
                  refine ⟨660658359320116170082949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1761755624853643120221197 660658359320116170082949)
                  ·
                    refine ⟨123873442372521781890553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660658359320116170082949 123873442372521781890553)
                    ·
                      refine ⟨92905081779391336417915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 123873442372521781890553 92905081779391336417915)
                      ·
                        rfl

theorem cell23_180932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_180932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180932 prefixEnd_180932 := by exact prefixLift 180932
  have htrace : WordTrace (prefixWord ++ tailWord_180932) baseStart_180932 baseEnd_180932 := by
    simpa [prefixWord, tailWord_180932, baseEnd_180932] using wordTrace_append hprefix tailTrace_180932
  have hstable : (prefixWord ++ tailWord_180932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180932).length < 2 ^ (prefixWord ++ tailWord_180932).sum := by decide
  have hdescent : baseEnd_180932 < baseStart_180932 := by decide
  rcases family_descends (prefixWord ++ tailWord_180932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_180965 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_180965 : Nat := 118140960795 + 180965 * 2 ^ 59
def prefixEnd_180965 : Nat := 4983230072969 + 3 ^ 40 * 180965 * 2
def baseEnd_180965 : Nat := 92922026640989707305263

theorem tailTrace_180965 : CollatzResearch.WordTrace tailWord_180965 prefixEnd_180965 92922026640989707305263 := by
  unfold tailWord_180965
  simp only [CollatzResearch.WordTrace]
  refine ⟨6600335789402186206528349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4400223859601457471018899 6600335789402186206528349)
  ·
    refine ⟨2475125921025819827448131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6600335789402186206528349 2475125921025819827448131)
    ·
      refine ⟨3712688881538729741172197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475125921025819827448131 3712688881538729741172197)
      ·
        refine ⟨696129165288511826469787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3712688881538729741172197 696129165288511826469787)
        ·
          refine ⟨1044193747932767739704681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696129165288511826469787 1044193747932767739704681)
          ·
            refine ⟨783145310949575804778511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1044193747932767739704681 783145310949575804778511)
            ·
              refine ⟨1174717966424363707167767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783145310949575804778511 1174717966424363707167767)
              ·
                refine ⟨1762076949636545560751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174717966424363707167767 1762076949636545560751651)
                ·
                  refine ⟨2643115424454818341127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1762076949636545560751651 2643115424454818341127477)
                  ·
                    refine ⟨247792071042639219480701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2643115424454818341127477 247792071042639219480701)
                    ·
                      refine ⟨92922026640989707305263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247792071042639219480701 92922026640989707305263)
                      ·
                        rfl

theorem cell23_180965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_180965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_180965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_180965 prefixEnd_180965 := by exact prefixLift 180965
  have htrace : WordTrace (prefixWord ++ tailWord_180965) baseStart_180965 baseEnd_180965 := by
    simpa [prefixWord, tailWord_180965, baseEnd_180965] using wordTrace_append hprefix tailTrace_180965
  have hstable : (prefixWord ++ tailWord_180965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_180965).length < 2 ^ (prefixWord ++ tailWord_180965).sum := by decide
  have hdescent : baseEnd_180965 < baseStart_180965 := by decide
  rcases family_descends (prefixWord ++ tailWord_180965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181025 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_181025 : Nat := 118140960795 + 181025 * 2 ^ 59
def prefixEnd_181025 : Nat := 4983230072969 + 3 ^ 40 * 181025 * 2
def baseEnd_181025 : Nat := 92952835480259472554987

theorem tailTrace_181025 : CollatzResearch.WordTrace tailWord_181025 prefixEnd_181025 92952835480259472554987 := by
  unfold tailWord_181025
  simp only [CollatzResearch.WordTrace]
  refine ⟨6602524169184816453712529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4401682779456544302475019 6602524169184816453712529)
  ·
    refine ⟨4951893126888612340284397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6602524169184816453712529 4951893126888612340284397)
    ·
      refine ⟨1856959922583229627606649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4951893126888612340284397 1856959922583229627606649)
      ·
        refine ⟨1392719941937422220704987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1856959922583229627606649 1392719941937422220704987)
        ·
          refine ⟨2089079912906133331057481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392719941937422220704987 2089079912906133331057481)
          ·
            refine ⟨1566809934679599998293111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089079912906133331057481 1566809934679599998293111)
            ·
              refine ⟨2350214902019399997439667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566809934679599998293111 2350214902019399997439667)
              ·
                refine ⟨3525322353029099996159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2350214902019399997439667 3525322353029099996159501)
                ·
                  refine ⟨1321995882385912498559813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3525322353029099996159501 1321995882385912498559813)
                  ·
                    refine ⟨247874227947358593479965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1321995882385912498559813 247874227947358593479965)
                    ·
                      refine ⟨92952835480259472554987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247874227947358593479965 92952835480259472554987)
                      ·
                        rfl

theorem cell23_181025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_181025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181025 prefixEnd_181025 := by exact prefixLift 181025
  have htrace : WordTrace (prefixWord ++ tailWord_181025) baseStart_181025 baseEnd_181025 := by
    simpa [prefixWord, tailWord_181025, baseEnd_181025] using wordTrace_append hprefix tailTrace_181025
  have hstable : (prefixWord ++ tailWord_181025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181025).length < 2 ^ (prefixWord ++ tailWord_181025).sum := by decide
  have hdescent : baseEnd_181025 < baseStart_181025 := by decide
  rcases family_descends (prefixWord ++ tailWord_181025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181032 : List Nat := [2, 1, 5, 1, 1, 1, 1, 4, 3, 4]
def baseStart_181032 : Nat := 118140960795 + 181032 * 2 ^ 59
def prefixEnd_181032 : Nat := 4983230072969 + 3 ^ 40 * 181032 * 2
def baseEnd_181032 : Nat := 30985476614946981722485

theorem tailTrace_181032 : CollatzResearch.WordTrace tailWord_181032 prefixEnd_181032 30985476614946981722485 := by
  unfold tailWord_181032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3301389740079728324608675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4401852986772971099478233 3301389740079728324608675)
  ·
    refine ⟨4952084610119592486913013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3301389740079728324608675 4952084610119592486913013)
    ·
      refine ⟨464257932198711795648095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4952084610119592486913013 464257932198711795648095)
      ·
        refine ⟨696386898298067693472143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464257932198711795648095 696386898298067693472143)
        ·
          refine ⟨1044580347447101540208215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 696386898298067693472143 1044580347447101540208215)
          ·
            refine ⟨1566870521170652310312323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044580347447101540208215 1566870521170652310312323)
            ·
              refine ⟨2350305781755978465468485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566870521170652310312323 2350305781755978465468485)
              ·
                refine ⟨440682334079245962275341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2350305781755978465468485 440682334079245962275341)
                ·
                  refine ⟨165255875279717235853253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 440682334079245962275341 165255875279717235853253)
                  ·
                    refine ⟨30985476614946981722485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165255875279717235853253 30985476614946981722485)
                    ·
                      rfl

theorem cell23_181032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_181032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181032 prefixEnd_181032 := by exact prefixLift 181032
  have htrace : WordTrace (prefixWord ++ tailWord_181032) baseStart_181032 baseEnd_181032 := by
    simpa [prefixWord, tailWord_181032, baseEnd_181032] using wordTrace_append hprefix tailTrace_181032
  have hstable : (prefixWord ++ tailWord_181032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181032).length < 2 ^ (prefixWord ++ tailWord_181032).sum := by decide
  have hdescent : baseEnd_181032 < baseStart_181032 := by decide
  rcases family_descends (prefixWord ++ tailWord_181032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181042 : List Nat := [3, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_181042 : Nat := 118140960795 + 181042 * 2 ^ 59
def prefixEnd_181042 : Nat := 4983230072969 + 3 ^ 40 * 181042 * 2
def baseEnd_181042 : Nat := 92961564651385906042409

theorem tailTrace_181042 : CollatzResearch.WordTrace tailWord_181042 prefixEnd_181042 92961564651385906042409 := by
  unfold tailWord_181042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1650786052530807089270345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4402096140082152238054253 1650786052530807089270345)
  ·
    refine ⟨1238089539398105316952759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1650786052530807089270345 1238089539398105316952759)
    ·
      refine ⟨1857134309097157975429139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238089539398105316952759 1857134309097157975429139)
      ·
        refine ⟨2785701463645736963143709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857134309097157975429139 2785701463645736963143709)
        ·
          refine ⟨1044638048867151361178891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2785701463645736963143709 1044638048867151361178891)
          ·
            refine ⟨1566957073300727041768337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044638048867151361178891 1566957073300727041768337)
            ·
              refine ⟨1175217804975545281326253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1566957073300727041768337 1175217804975545281326253)
              ·
                refine ⟨440706676865829480497345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1175217804975545281326253 440706676865829480497345)
                ·
                  refine ⟨330530007649372110373009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440706676865829480497345 330530007649372110373009)
                  ·
                    refine ⟨247897505737029082779757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330530007649372110373009 247897505737029082779757)
                    ·
                      refine ⟨92961564651385906042409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 247897505737029082779757 92961564651385906042409)
                      ·
                        rfl

theorem cell23_181042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_181042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181042 prefixEnd_181042 := by exact prefixLift 181042
  have htrace : WordTrace (prefixWord ++ tailWord_181042) baseStart_181042 baseEnd_181042 := by
    simpa [prefixWord, tailWord_181042, baseEnd_181042] using wordTrace_append hprefix tailTrace_181042
  have hstable : (prefixWord ++ tailWord_181042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181042).length < 2 ^ (prefixWord ++ tailWord_181042).sum := by decide
  have hdescent : baseEnd_181042 < baseStart_181042 := by decide
  rcases family_descends (prefixWord ++ tailWord_181042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181045 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 8]
def baseStart_181045 : Nat := 118140960795 + 181045 * 2 ^ 59
def prefixEnd_181045 : Nat := 4983230072969 + 3 ^ 40 * 181045 * 2
def baseEnd_181045 : Nat := 10329233899261043811655

theorem tailTrace_181045 : CollatzResearch.WordTrace tailWord_181045 prefixEnd_181045 10329233899261043811655 := by
  unfold tailWord_181045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6603253629112359869440589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4402169086074906579627059 6603253629112359869440589)
  ·
    refine ⟨2476220110917134951040221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6603253629112359869440589 2476220110917134951040221)
    ·
      refine ⟨928582541593925606640083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2476220110917134951040221 928582541593925606640083)
      ·
        refine ⟨1392873812390888409960125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928582541593925606640083 1392873812390888409960125)
        ·
          refine ⟨522327679646583153735047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1392873812390888409960125 522327679646583153735047)
          ·
            refine ⟨783491519469874730602571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522327679646583153735047 783491519469874730602571)
            ·
              refine ⟨1175237279204812095903857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783491519469874730602571 1175237279204812095903857)
              ·
                refine ⟨881427959403609071927893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175237279204812095903857 881427959403609071927893)
                ·
                  refine ⟨10329233899261043811655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 881427959403609071927893 10329233899261043811655)
                  ·
                    rfl

theorem cell23_181045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_181045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181045 prefixEnd_181045 := by exact prefixLift 181045
  have htrace : WordTrace (prefixWord ++ tailWord_181045) baseStart_181045 baseEnd_181045 := by
    simpa [prefixWord, tailWord_181045, baseEnd_181045] using wordTrace_append hprefix tailTrace_181045
  have hstable : (prefixWord ++ tailWord_181045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181045).length < 2 ^ (prefixWord ++ tailWord_181045).sum := by decide
  have hdescent : baseEnd_181045 < baseStart_181045 := by decide
  rcases family_descends (prefixWord ++ tailWord_181045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181079 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 6]
def baseStart_181079 : Nat := 118140960795 + 181079 * 2 ^ 59
def prefixEnd_181079 : Nat := 4983230072969 + 3 ^ 40 * 181079 * 2
def baseEnd_181079 : Nat := 10331173715066917919971

theorem tailTrace_181079 : CollatzResearch.WordTrace tailWord_181079 prefixEnd_181079 10331173715066917919971 := by
  unfold tailWord_181079
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604493710989183676178291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4402995807326122450785527 6604493710989183676178291)
  ·
    refine ⟨9906740566483775514267437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6604493710989183676178291 9906740566483775514267437)
    ·
      refine ⟨3715027712431415817850289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9906740566483775514267437 3715027712431415817850289)
      ·
        refine ⟨2786270784323561863387717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3715027712431415817850289 2786270784323561863387717)
        ·
          refine ⟨522425772060667849385197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2786270784323561863387717 522425772060667849385197)
          ·
            refine ⟨195909664522750443519449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 522425772060667849385197 195909664522750443519449)
            ·
              refine ⟨146932248392062832639587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 195909664522750443519449 146932248392062832639587)
              ·
                refine ⟨220398372588094248959381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146932248392062832639587 220398372588094248959381)
                ·
                  refine ⟨10331173715066917919971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 220398372588094248959381 10331173715066917919971)
                  ·
                    rfl

theorem cell23_181079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 6].length) (baseStart_181079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181079 prefixEnd_181079 := by exact prefixLift 181079
  have htrace : WordTrace (prefixWord ++ tailWord_181079) baseStart_181079 baseEnd_181079 := by
    simpa [prefixWord, tailWord_181079, baseEnd_181079] using wordTrace_append hprefix tailTrace_181079
  have hstable : (prefixWord ++ tailWord_181079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181079).length < 2 ^ (prefixWord ++ tailWord_181079).sum := by decide
  have hdescent : baseEnd_181079 < baseStart_181079 := by decide
  rcases family_descends (prefixWord ++ tailWord_181079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181092 : List Nat := [2, 3, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_181092 : Nat := 118140960795 + 181092 * 2 ^ 59
def prefixEnd_181092 : Nat := 4983230072969 + 3 ^ 40 * 181092 * 2
def baseEnd_181092 : Nat := 30995746228036903472393

theorem tailTrace_181092 : CollatzResearch.WordTrace tailWord_181092 prefixEnd_181092 30995746228036903472393 := by
  unfold tailWord_181092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302483929971043448200765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4403311906628057930934353 3302483929971043448200765)
  ·
    refine ⟨1238431473739141293075287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3302483929971043448200765 1238431473739141293075287)
    ·
      refine ⟨1857647210608711939612931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1238431473739141293075287 1857647210608711939612931)
      ·
        refine ⟨2786470815913067909419397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857647210608711939612931 2786470815913067909419397)
        ·
          refine ⟨522463277983700233016137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2786470815913067909419397 522463277983700233016137)
          ·
            refine ⟨391847458487775174762103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522463277983700233016137 391847458487775174762103)
            ·
              refine ⟨587771187731662762143155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391847458487775174762103 587771187731662762143155)
              ·
                refine ⟨881656781597494143214733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587771187731662762143155 881656781597494143214733)
                ·
                  refine ⟨330621293099060303705525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881656781597494143214733 330621293099060303705525)
                  ·
                    refine ⟨30995746228036903472393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 330621293099060303705525 30995746228036903472393)
                    ·
                      rfl

theorem cell23_181092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_181092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181092 prefixEnd_181092 := by exact prefixLift 181092
  have htrace : WordTrace (prefixWord ++ tailWord_181092) baseStart_181092 baseEnd_181092 := by
    simpa [prefixWord, tailWord_181092, baseEnd_181092] using wordTrace_append hprefix tailTrace_181092
  have hstable : (prefixWord ++ tailWord_181092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181092).length < 2 ^ (prefixWord ++ tailWord_181092).sum := by decide
  have hdescent : baseEnd_181092 < baseStart_181092 := by decide
  rcases family_descends (prefixWord ++ tailWord_181092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181105 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_181105 : Nat := 118140960795 + 181105 * 2 ^ 59
def prefixEnd_181105 : Nat := 4983230072969 + 3 ^ 40 * 181105 * 2
def baseEnd_181105 : Nat := 30997971310873053184873

theorem tailTrace_181105 : CollatzResearch.WordTrace tailWord_181105 prefixEnd_181105 30997971310873053184873 := by
  unfold tailWord_181105
  simp only [CollatzResearch.WordTrace]
  refine ⟨6605442008894990116624769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4403628005929993411083179 6605442008894990116624769)
  ·
    refine ⟨4954081506671242587468577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6605442008894990116624769 4954081506671242587468577)
    ·
      refine ⟨3715561130003431940601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4954081506671242587468577 3715561130003431940601433)
      ·
        refine ⟨2786670847502573955451075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3715561130003431940601433 2786670847502573955451075)
        ·
          refine ⟨4180006271253860933176613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786670847502573955451075 4180006271253860933176613)
          ·
            refine ⟨783751175860098924970615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4180006271253860933176613 783751175860098924970615)
            ·
              refine ⟨1175626763790148387455923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783751175860098924970615 1175626763790148387455923)
              ·
                refine ⟨1763440145685222581183885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175626763790148387455923 1763440145685222581183885)
                ·
                  refine ⟨661290054631958467943957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1763440145685222581183885 661290054631958467943957)
                  ·
                    refine ⟨30997971310873053184873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 661290054631958467943957 30997971310873053184873)
                    ·
                      rfl

theorem cell23_181105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_181105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181105 prefixEnd_181105 := by exact prefixLift 181105
  have htrace : WordTrace (prefixWord ++ tailWord_181105) baseStart_181105 baseEnd_181105 := by
    simpa [prefixWord, tailWord_181105, baseEnd_181105] using wordTrace_append hprefix tailTrace_181105
  have hstable : (prefixWord ++ tailWord_181105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181105).length < 2 ^ (prefixWord ++ tailWord_181105).sum := by decide
  have hdescent : baseEnd_181105 < baseStart_181105 := by decide
  rcases family_descends (prefixWord ++ tailWord_181105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181132 : List Nat := [2, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3]
def baseStart_181132 : Nat := 118140960795 + 181132 * 2 ^ 59
def prefixEnd_181132 : Nat := 4983230072969 + 3 ^ 40 * 181132 * 2
def baseEnd_181132 : Nat := 93007777910290553916995

theorem tailTrace_181132 : CollatzResearch.WordTrace tailWord_181132 prefixEnd_181132 93007777910290553916995 := by
  unfold tailWord_181132
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303213389898586863928825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4404284519864782485238433 3303213389898586863928825)
  ·
    refine ⟨2477410042423940147946619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3303213389898586863928825 2477410042423940147946619)
    ·
      refine ⟨3716115063635910221919929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477410042423940147946619 3716115063635910221919929)
      ·
        refine ⟨2787086297726932666439947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3716115063635910221919929 2787086297726932666439947)
        ·
          refine ⟨4180629446590398999659921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2787086297726932666439947 4180629446590398999659921)
          ·
            refine ⟨3135472084942799249744941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180629446590398999659921 3135472084942799249744941)
            ·
              refine ⟨1175802031853549718654353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3135472084942799249744941 1175802031853549718654353)
              ·
                refine ⟨881851523890162288990765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175802031853549718654353 881851523890162288990765)
                ·
                  refine ⟨330694321458810858371537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881851523890162288990765 330694321458810858371537)
                  ·
                    refine ⟨248020741094108143778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330694321458810858371537 248020741094108143778653)
                    ·
                      refine ⟨93007777910290553916995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248020741094108143778653 93007777910290553916995)
                      ·
                        rfl

theorem cell23_181132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_181132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181132 prefixEnd_181132 := by exact prefixLift 181132
  have htrace : WordTrace (prefixWord ++ tailWord_181132) baseStart_181132 baseEnd_181132 := by
    simpa [prefixWord, tailWord_181132, baseEnd_181132] using wordTrace_append hprefix tailTrace_181132
  have hstable : (prefixWord ++ tailWord_181132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181132).length < 2 ^ (prefixWord ++ tailWord_181132).sum := by decide
  have hdescent : baseEnd_181132 < baseStart_181132 := by decide
  rcases family_descends (prefixWord ++ tailWord_181132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181149 : List Nat := [1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_181149 : Nat := 118140960795 + 181149 * 2 ^ 59
def prefixEnd_181149 : Nat := 4983230072969 + 3 ^ 40 * 181149 * 2
def baseEnd_181149 : Nat := 93016507081416987404417

theorem tailTrace_181149 : CollatzResearch.WordTrace tailWord_181149 prefixEnd_181149 93016507081416987404417 := by
  unfold tailWord_181149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607046820735585631226501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4404697880490390420817667 6607046820735585631226501)
  ·
    refine ⟨1238821278887922305854969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6607046820735585631226501 1238821278887922305854969)
    ·
      refine ⟨929115959165941729391227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1238821278887922305854969 929115959165941729391227)
      ·
        refine ⟨1393673938748912594086841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929115959165941729391227 1393673938748912594086841)
        ·
          refine ⟨1045255454061684445565131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393673938748912594086841 1045255454061684445565131)
          ·
            refine ⟨1567883181092526668347697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045255454061684445565131 1567883181092526668347697)
            ·
              refine ⟨1175912385819395001260773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1567883181092526668347697 1175912385819395001260773)
              ·
                refine ⟨220483572341136562736395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1175912385819395001260773 220483572341136562736395)
                ·
                  refine ⟨330725358511704844104593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220483572341136562736395 330725358511704844104593)
                  ·
                    refine ⟨248044018883778633078445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 330725358511704844104593 248044018883778633078445)
                    ·
                      refine ⟨93016507081416987404417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248044018883778633078445 93016507081416987404417)
                      ·
                        rfl

theorem cell23_181149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_181149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181149 prefixEnd_181149 := by exact prefixLift 181149
  have htrace : WordTrace (prefixWord ++ tailWord_181149) baseStart_181149 baseEnd_181149 := by
    simpa [prefixWord, tailWord_181149, baseEnd_181149] using wordTrace_append hprefix tailTrace_181149
  have hstable : (prefixWord ++ tailWord_181149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181149).length < 2 ^ (prefixWord ++ tailWord_181149).sum := by decide
  have hdescent : baseEnd_181149 < baseStart_181149 := by decide
  rcases family_descends (prefixWord ++ tailWord_181149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181219 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 3, 4, 2]
def baseStart_181219 : Nat := 118140960795 + 181219 * 2 ^ 59
def prefixEnd_181219 : Nat := 4983230072969 + 3 ^ 40 * 181219 * 2
def baseEnd_181219 : Nat := 93052450727231713529095

theorem tailTrace_181219 : CollatzResearch.WordTrace tailWord_181219 prefixEnd_181219 93052450727231713529095 := by
  unfold tailWord_181219
  simp only [CollatzResearch.WordTrace]
  refine ⟨6609599930481987586274711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4406399953654658390849807 6609599930481987586274711)
  ·
    refine ⟨9914399895722981379412067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6609599930481987586274711 9914399895722981379412067)
    ·
      refine ⟨14871599843584472069118101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914399895722981379412067 14871599843584472069118101)
      ·
        refine ⟨697106242668022128239911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14871599843584472069118101 697106242668022128239911)
        ·
          refine ⟨1045659364002033192359867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697106242668022128239911 1045659364002033192359867)
          ·
            refine ⟨1568489046003049788539801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045659364002033192359867 1568489046003049788539801)
            ·
              refine ⟨1176366784502287341404851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568489046003049788539801 1176366784502287341404851)
              ·
                refine ⟨1764550176753431012107277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176366784502287341404851 1764550176753431012107277)
                ·
                  refine ⟨661706316282536629540229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1764550176753431012107277 661706316282536629540229)
                  ·
                    refine ⟨124069934302975618038793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661706316282536629540229 124069934302975618038793)
                    ·
                      refine ⟨93052450727231713529095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124069934302975618038793 93052450727231713529095)
                      ·
                        rfl

theorem cell23_181219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_181219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181219 prefixEnd_181219 := by exact prefixLift 181219
  have htrace : WordTrace (prefixWord ++ tailWord_181219) baseStart_181219 baseEnd_181219 := by
    simpa [prefixWord, tailWord_181219, baseEnd_181219] using wordTrace_append hprefix tailTrace_181219
  have hstable : (prefixWord ++ tailWord_181219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181219).length < 2 ^ (prefixWord ++ tailWord_181219).sum := by decide
  have hdescent : baseEnd_181219 < baseStart_181219 := by decide
  rcases family_descends (prefixWord ++ tailWord_181219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181319 : List Nat := [1, 1, 4, 1, 3, 2, 1, 1, 5, 4]
def baseStart_181319 : Nat := 118140960795 + 181319 * 2 ^ 59
def prefixEnd_181319 : Nat := 4983230072969 + 3 ^ 40 * 181319 * 2
def baseEnd_181319 : Nat := 31034599597560440759545

theorem tailTrace_181319 : CollatzResearch.WordTrace tailWord_181319 prefixEnd_181319 31034599597560440759545 := by
  unfold tailWord_181319
  simp only [CollatzResearch.WordTrace]
  refine ⟨6613247230119704664915011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4408831486746469776610007 6613247230119704664915011)
  ·
    refine ⟨9919870845179556997372517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6613247230119704664915011 9919870845179556997372517)
    ·
      refine ⟨1859975783471166937007347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9919870845179556997372517 1859975783471166937007347)
      ·
        refine ⟨2789963675206750405511021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859975783471166937007347 2789963675206750405511021)
        ·
          refine ⟨1046236378202531402066633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2789963675206750405511021 1046236378202531402066633)
          ·
            refine ⟨784677283651898551549975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046236378202531402066633 784677283651898551549975)
            ·
              refine ⟨1177015925477847827324963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784677283651898551549975 1177015925477847827324963)
              ·
                refine ⟨1765523888216771740987445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177015925477847827324963 1765523888216771740987445)
                ·
                  refine ⟨165517864520322350717573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1765523888216771740987445 165517864520322350717573)
                  ·
                    refine ⟨31034599597560440759545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 165517864520322350717573 31034599597560440759545)
                    ·
                      rfl

theorem cell23_181319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_181319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181319 prefixEnd_181319 := by exact prefixLift 181319
  have htrace : WordTrace (prefixWord ++ tailWord_181319) baseStart_181319 baseEnd_181319 := by
    simpa [prefixWord, tailWord_181319, baseEnd_181319] using wordTrace_append hprefix tailTrace_181319
  have hstable : (prefixWord ++ tailWord_181319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181319).length < 2 ^ (prefixWord ++ tailWord_181319).sum := by decide
  have hdescent : baseEnd_181319 < baseStart_181319 := by decide
  rcases family_descends (prefixWord ++ tailWord_181319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181376 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3]
def baseStart_181376 : Nat := 118140960795 + 181376 * 2 ^ 59
def prefixEnd_181376 : Nat := 4983230072969 + 3 ^ 40 * 181376 * 2
def baseEnd_181376 : Nat := 93133067189987599265873

theorem tailTrace_181376 : CollatzResearch.WordTrace tailWord_181376 prefixEnd_181376 93133067189987599265873 := by
  unfold tailWord_181376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307663095456601699869991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4410217460608802266493321 3307663095456601699869991)
  ·
    refine ⟨4961494643184902549804987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307663095456601699869991 4961494643184902549804987)
    ·
      refine ⟨7442241964777353824707481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961494643184902549804987 7442241964777353824707481)
      ·
        refine ⟨5581681473583015368530611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7442241964777353824707481 5581681473583015368530611)
        ·
          refine ⟨8372522210374523052795917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5581681473583015368530611 8372522210374523052795917)
          ·
            refine ⟨3139695828890446144798469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8372522210374523052795917 3139695828890446144798469)
            ·
              refine ⟨588692967916958652149713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3139695828890446144798469 588692967916958652149713)
              ·
                refine ⟨441519725937718989112285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588692967916958652149713 441519725937718989112285)
                ·
                  refine ⟨165569897226644620917107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 441519725937718989112285 165569897226644620917107)
                  ·
                    refine ⟨248354845839966931375661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165569897226644620917107 248354845839966931375661)
                    ·
                      refine ⟨93133067189987599265873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248354845839966931375661 93133067189987599265873)
                      ·
                        rfl

theorem cell23_181376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_181376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181376 prefixEnd_181376 := by exact prefixLift 181376
  have htrace : WordTrace (prefixWord ++ tailWord_181376) baseStart_181376 baseEnd_181376 := by
    simpa [prefixWord, tailWord_181376, baseEnd_181376] using wordTrace_append hprefix tailTrace_181376
  have hstable : (prefixWord ++ tailWord_181376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181376).length < 2 ^ (prefixWord ++ tailWord_181376).sum := by decide
  have hdescent : baseEnd_181376 < baseStart_181376 := by decide
  rcases family_descends (prefixWord ++ tailWord_181376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181386 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_181386 : Nat := 118140960795 + 181386 * 2 ^ 59
def prefixEnd_181386 : Nat := 4983230072969 + 3 ^ 40 * 181386 * 2
def baseEnd_181386 : Nat := 93138201996532560140827

theorem tailTrace_181386 : CollatzResearch.WordTrace tailWord_181386 prefixEnd_181386 93138201996532560140827 := by
  unfold tailWord_181386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1653922730219243776901003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4410460613917983405069341 1653922730219243776901003)
  ·
    refine ⟨2480884095328865665351505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1653922730219243776901003 2480884095328865665351505)
    ·
      refine ⟨1860663071496649249013629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480884095328865665351505 1860663071496649249013629)
      ·
        refine ⟨697748651811243468380111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860663071496649249013629 697748651811243468380111)
        ·
          refine ⟨1046622977716865202570167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697748651811243468380111 1046622977716865202570167)
          ·
            refine ⟨1569934466575297803855251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046622977716865202570167 1569934466575297803855251)
            ·
              refine ⟨2354901699862946705782877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569934466575297803855251 2354901699862946705782877)
              ·
                refine ⟨883088137448605014668579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354901699862946705782877 883088137448605014668579)
                ·
                  refine ⟨1324632206172907522002869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883088137448605014668579 1324632206172907522002869)
                  ·
                    refine ⟨124184269328710080187769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1324632206172907522002869 124184269328710080187769)
                    ·
                      refine ⟨93138201996532560140827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124184269328710080187769 93138201996532560140827)
                      ·
                        rfl

theorem cell23_181386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_181386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181386 prefixEnd_181386 := by exact prefixLift 181386
  have htrace : WordTrace (prefixWord ++ tailWord_181386) baseStart_181386 baseEnd_181386 := by
    simpa [prefixWord, tailWord_181386, baseEnd_181386] using wordTrace_append hprefix tailTrace_181386
  have hstable : (prefixWord ++ tailWord_181386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181386).length < 2 ^ (prefixWord ++ tailWord_181386).sum := by decide
  have hdescent : baseEnd_181386 < baseStart_181386 := by decide
  rcases family_descends (prefixWord ++ tailWord_181386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181430 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_181430 : Nat := 118140960795 + 181430 * 2 ^ 59
def prefixEnd_181430 : Nat := 4983230072969 + 3 ^ 40 * 181430 * 2
def baseEnd_181430 : Nat := 31053598381776795996875

theorem tailTrace_181430 : CollatzResearch.WordTrace tailWord_181430 prefixEnd_181430 31053598381776795996875 := by
  unfold tailWord_181430
  simp only [CollatzResearch.WordTrace]
  refine ⟨413580983294848163887859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4411530488478380414803829 413580983294848163887859)
  ·
    refine ⟨620371474942272245831789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413580983294848163887859 620371474942272245831789)
    ·
      refine ⟨232639303103352092186921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 620371474942272245831789 232639303103352092186921)
      ·
        refine ⟨174479477327514069140191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232639303103352092186921 174479477327514069140191)
        ·
          refine ⟨261719215991271103710287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174479477327514069140191 261719215991271103710287)
          ·
            refine ⟨392578823986906655565431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261719215991271103710287 392578823986906655565431)
            ·
              refine ⟨588868235980359983348147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392578823986906655565431 588868235980359983348147)
              ·
                refine ⟨883302353970539975022221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588868235980359983348147 883302353970539975022221)
                ·
                  refine ⟨331238382738952490633333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883302353970539975022221 331238382738952490633333)
                  ·
                    refine ⟨31053598381776795996875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 331238382738952490633333 31053598381776795996875)
                    ·
                      rfl

theorem cell23_181430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_181430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181430 prefixEnd_181430 := by exact prefixLift 181430
  have htrace : WordTrace (prefixWord ++ tailWord_181430) baseStart_181430 baseEnd_181430 := by
    simpa [prefixWord, tailWord_181430, baseEnd_181430] using wordTrace_append hprefix tailTrace_181430
  have hstable : (prefixWord ++ tailWord_181430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181430).length < 2 ^ (prefixWord ++ tailWord_181430).sum := by decide
  have hdescent : baseEnd_181430 < baseStart_181430 := by decide
  rcases family_descends (prefixWord ++ tailWord_181430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181433 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 4]
def baseStart_181433 : Nat := 118140960795 + 181433 * 2 ^ 59
def prefixEnd_181433 : Nat := 4983230072969 + 3 ^ 40 * 181433 * 2
def baseEnd_181433 : Nat := 93162335587293876253111

theorem tailTrace_181433 : CollatzResearch.WordTrace tailWord_181433 prefixEnd_181433 93162335587293876253111 := by
  unfold tailWord_181433
  simp only [CollatzResearch.WordTrace]
  refine ⟨6617405151706702134564953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4411603434471134756376635 6617405151706702134564953)
  ·
    refine ⟨4963053863780026600923715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6617405151706702134564953 4963053863780026600923715)
    ·
      refine ⟨7444580795670039901385573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4963053863780026600923715 7444580795670039901385573)
      ·
        refine ⟨1395858899188132481509795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7444580795670039901385573 1395858899188132481509795)
        ·
          refine ⟨2093788348782198722264693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395858899188132481509795 2093788348782198722264693)
          ·
            refine ⟨196292657698331130212315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2093788348782198722264693 196292657698331130212315)
            ·
              refine ⟨294438986547496695318473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196292657698331130212315 294438986547496695318473)
              ·
                refine ⟨220829239910622521488855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294438986547496695318473 220829239910622521488855)
                ·
                  refine ⟨331243859865933782233283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220829239910622521488855 331243859865933782233283)
                  ·
                    refine ⟨496865789798900673349925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 331243859865933782233283 496865789798900673349925)
                    ·
                      refine ⟨93162335587293876253111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 496865789798900673349925 93162335587293876253111)
                      ·
                        rfl

theorem cell23_181433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_181433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181433 prefixEnd_181433 := by exact prefixLift 181433
  have htrace : WordTrace (prefixWord ++ tailWord_181433) baseStart_181433 baseEnd_181433 := by
    simpa [prefixWord, tailWord_181433, baseEnd_181433] using wordTrace_append hprefix tailTrace_181433
  have hstable : (prefixWord ++ tailWord_181433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181433).length < 2 ^ (prefixWord ++ tailWord_181433).sum := by decide
  have hdescent : baseEnd_181433 < baseStart_181433 := by decide
  rcases family_descends (prefixWord ++ tailWord_181433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181483 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 3]
def baseStart_181483 : Nat := 118140960795 + 181483 * 2 ^ 59
def prefixEnd_181483 : Nat := 4983230072969 + 3 ^ 40 * 181483 * 2
def baseEnd_181483 : Nat := 93188009620018680627881

theorem tailTrace_181483 : CollatzResearch.WordTrace tailWord_181483 prefixEnd_181483 93188009620018680627881 := by
  unfold tailWord_181483
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619228801525560673885103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4412819201017040449256735 6619228801525560673885103)
  ·
    refine ⟨9928843202288341010827655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6619228801525560673885103 9928843202288341010827655)
    ·
      refine ⟨14893264803432511516241483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928843202288341010827655 14893264803432511516241483)
      ·
        refine ⟨22339897205148767274362225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14893264803432511516241483 22339897205148767274362225)
        ·
          refine ⟨16754922903861575455771669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22339897205148767274362225 16754922903861575455771669)
          ·
            refine ⟨785387011118511349489297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16754922903861575455771669 785387011118511349489297)
            ·
              refine ⟨589040258338883512116973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785387011118511349489297 589040258338883512116973)
              ·
                refine ⟨220890096877081317043865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589040258338883512116973 220890096877081317043865)
                ·
                  refine ⟨165667572657810987782899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220890096877081317043865 165667572657810987782899)
                  ·
                    refine ⟨248501358986716481674349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 165667572657810987782899 248501358986716481674349)
                    ·
                      refine ⟨93188009620018680627881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248501358986716481674349 93188009620018680627881)
                      ·
                        rfl

theorem cell23_181483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 3].length) (baseStart_181483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181483 prefixEnd_181483 := by exact prefixLift 181483
  have htrace : WordTrace (prefixWord ++ tailWord_181483) baseStart_181483 baseEnd_181483 := by
    simpa [prefixWord, tailWord_181483, baseEnd_181483] using wordTrace_append hprefix tailTrace_181483
  have hstable : (prefixWord ++ tailWord_181483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181483).length < 2 ^ (prefixWord ++ tailWord_181483).sum := by decide
  have hdescent : baseEnd_181483 < baseStart_181483 := by decide
  rcases family_descends (prefixWord ++ tailWord_181483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181489 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_181489 : Nat := 118140960795 + 181489 * 2 ^ 59
def prefixEnd_181489 : Nat := 4983230072969 + 3 ^ 40 * 181489 * 2
def baseEnd_181489 : Nat := 93191090503945657152853

theorem tailTrace_181489 : CollatzResearch.WordTrace tailWord_181489 prefixEnd_181489 93191090503945657152853 := by
  unfold tailWord_181489
  simp only [CollatzResearch.WordTrace]
  refine ⟨6619447639503823698603521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4412965093002549132402347 6619447639503823698603521)
  ·
    refine ⟨4964585729627867773952641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6619447639503823698603521 4964585729627867773952641)
    ·
      refine ⟨3723439297220900830464481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4964585729627867773952641 3723439297220900830464481)
      ·
        refine ⟨2792579472915675622848361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3723439297220900830464481 2792579472915675622848361)
        ·
          refine ⟨2094434604686756717136271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2792579472915675622848361 2094434604686756717136271)
          ·
            refine ⟨3141651907030135075704407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094434604686756717136271 3141651907030135075704407)
            ·
              refine ⟨4712477860545202613556611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141651907030135075704407 4712477860545202613556611)
              ·
                refine ⟨7068716790817803920334917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4712477860545202613556611 7068716790817803920334917)
                ·
                  refine ⟨1325384398278338235062797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7068716790817803920334917 1325384398278338235062797)
                  ·
                    refine ⟨497019149354376838148549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1325384398278338235062797 497019149354376838148549)
                    ·
                      refine ⟨93191090503945657152853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 497019149354376838148549 93191090503945657152853)
                      ·
                        rfl

theorem cell23_181489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_181489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181489 prefixEnd_181489 := by exact prefixLift 181489
  have htrace : WordTrace (prefixWord ++ tailWord_181489) baseStart_181489 baseEnd_181489 := by
    simpa [prefixWord, tailWord_181489, baseEnd_181489] using wordTrace_append hprefix tailTrace_181489
  have hstable : (prefixWord ++ tailWord_181489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181489).length < 2 ^ (prefixWord ++ tailWord_181489).sum := by decide
  have hdescent : baseEnd_181489 < baseStart_181489 := by decide
  rcases family_descends (prefixWord ++ tailWord_181489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181509 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_181509 : Nat := 118140960795 + 181509 * 2 ^ 59
def prefixEnd_181509 : Nat := 4983230072969 + 3 ^ 40 * 181509 * 2
def baseEnd_181509 : Nat := 93201360117035578902761

theorem tailTrace_181509 : CollatzResearch.WordTrace tailWord_181509 prefixEnd_181509 93201360117035578902761 := by
  unfold tailWord_181509
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620177099431367114331581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4413451399620911409554387 6620177099431367114331581)
  ·
    refine ⟨2482566412286762667874343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6620177099431367114331581 2482566412286762667874343)
    ·
      refine ⟨3723849618430144001811515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2482566412286762667874343 3723849618430144001811515)
      ·
        refine ⟨5585774427645216002717273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3723849618430144001811515 5585774427645216002717273)
        ·
          refine ⟨4189330820733912002037955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5585774427645216002717273 4189330820733912002037955)
          ·
            refine ⟨6283996231100868003056933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189330820733912002037955 6283996231100868003056933)
            ·
              refine ⟨1178249293331412750573175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6283996231100868003056933 1178249293331412750573175)
              ·
                refine ⟨1767373939997119125859763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178249293331412750573175 1767373939997119125859763)
                ·
                  refine ⟨2651060909995678688789645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1767373939997119125859763 2651060909995678688789645)
                  ·
                    refine ⟨994147841248379508296117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2651060909995678688789645 994147841248379508296117)
                    ·
                      refine ⟨93201360117035578902761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 994147841248379508296117 93201360117035578902761)
                      ·
                        rfl

theorem cell23_181509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_181509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181509 prefixEnd_181509 := by exact prefixLift 181509
  have htrace : WordTrace (prefixWord ++ tailWord_181509) baseStart_181509 baseEnd_181509 := by
    simpa [prefixWord, tailWord_181509, baseEnd_181509] using wordTrace_append hprefix tailTrace_181509
  have hstable : (prefixWord ++ tailWord_181509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181509).length < 2 ^ (prefixWord ++ tailWord_181509).sum := by decide
  have hdescent : baseEnd_181509 < baseStart_181509 := by decide
  rcases family_descends (prefixWord ++ tailWord_181509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181534 : List Nat := [4, 3, 2, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_181534 : Nat := 118140960795 + 181534 * 2 ^ 59
def prefixEnd_181534 : Nat := 4983230072969 + 3 ^ 40 * 181534 * 2
def baseEnd_181534 : Nat := 93214197133397981090147

theorem tailTrace_181534 : CollatzResearch.WordTrace tailWord_181534 prefixEnd_181534 93214197133397981090147 := by
  unfold tailWord_181534
  simp only [CollatzResearch.WordTrace]
  refine ⟨827636115542599547998957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4414059282893864255994437 827636115542599547998957)
  ·
    refine ⟨310363543328474830499609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 827636115542599547998957 310363543328474830499609)
    ·
      refine ⟨232772657496356122874707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310363543328474830499609 232772657496356122874707)
      ·
        refine ⟨349158986244534184312061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232772657496356122874707 349158986244534184312061)
        ·
          refine ⟨130934619841700319117023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349158986244534184312061 130934619841700319117023)
          ·
            refine ⟨196401929762550478675535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130934619841700319117023 196401929762550478675535)
            ·
              refine ⟨294602894643825718013303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196401929762550478675535 294602894643825718013303)
              ·
                refine ⟨441904341965738577019955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294602894643825718013303 441904341965738577019955)
                ·
                  refine ⟨662856512948607865529933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441904341965738577019955 662856512948607865529933)
                  ·
                    refine ⟨248571192355727949573725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 662856512948607865529933 248571192355727949573725)
                    ·
                      refine ⟨93214197133397981090147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248571192355727949573725 93214197133397981090147)
                      ·
                        rfl

theorem cell23_181534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_181534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181534 prefixEnd_181534 := by exact prefixLift 181534
  have htrace : WordTrace (prefixWord ++ tailWord_181534) baseStart_181534 baseEnd_181534 := by
    simpa [prefixWord, tailWord_181534, baseEnd_181534] using wordTrace_append hprefix tailTrace_181534
  have hstable : (prefixWord ++ tailWord_181534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181534).length < 2 ^ (prefixWord ++ tailWord_181534).sum := by decide
  have hdescent : baseEnd_181534 < baseStart_181534 := by decide
  rcases family_descends (prefixWord ++ tailWord_181534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181580 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 5]
def baseStart_181580 : Nat := 118140960795 + 181580 * 2 ^ 59
def prefixEnd_181580 : Nat := 4983230072969 + 3 ^ 40 * 181580 * 2
def baseEnd_181580 : Nat := 10359757471500533457215

theorem tailTrace_181580 : CollatzResearch.WordTrace tailWord_181580 prefixEnd_181580 10359757471500533457215 := by
  unfold tailWord_181580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311383341087073120083097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4415177788116097493444129 3311383341087073120083097)
  ·
    refine ⟨2483537505815304840062323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3311383341087073120083097 2483537505815304840062323)
    ·
      refine ⟨3725306258722957260093485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483537505815304840062323 3725306258722957260093485)
      ·
        refine ⟨1396989847021108972535057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3725306258722957260093485 1396989847021108972535057)
        ·
          refine ⟨1047742385265831729401293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396989847021108972535057 1047742385265831729401293)
          ·
            refine ⟨392903394474686898525485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1047742385265831729401293 392903394474686898525485)
            ·
              refine ⟨147338772928007586947057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392903394474686898525485 147338772928007586947057)
              ·
                refine ⟨110504079696005690210293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147338772928007586947057 110504079696005690210293)
                ·
                  refine ⟨10359757471500533457215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110504079696005690210293 10359757471500533457215)
                  ·
                    rfl

theorem cell23_181580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_181580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181580 prefixEnd_181580 := by exact prefixLift 181580
  have htrace : WordTrace (prefixWord ++ tailWord_181580) baseStart_181580 baseEnd_181580 := by
    simpa [prefixWord, tailWord_181580, baseEnd_181580] using wordTrace_append hprefix tailTrace_181580
  have hstable : (prefixWord ++ tailWord_181580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181580).length < 2 ^ (prefixWord ++ tailWord_181580).sum := by decide
  have hdescent : baseEnd_181580 < baseStart_181580 := by decide
  rcases family_descends (prefixWord ++ tailWord_181580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181610 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_181610 : Nat := 118140960795 + 181610 * 2 ^ 59
def prefixEnd_181610 : Nat := 4983230072969 + 3 ^ 40 * 181610 * 2
def baseEnd_181610 : Nat := 31084407221046561246599

theorem tailTrace_181610 : CollatzResearch.WordTrace tailWord_181610 prefixEnd_181610 31084407221046561246599 := by
  unfold tailWord_181610
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655965218016365340939571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4415907248043640909172189 1655965218016365340939571)
  ·
    refine ⟨2483947827024548011409357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1655965218016365340939571 2483947827024548011409357)
    ·
      refine ⟨931480435134205504278509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2483947827024548011409357 931480435134205504278509)
      ·
        refine ⟨349305163175327064104441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 931480435134205504278509 349305163175327064104441)
        ·
          refine ⟨261978872381495298078331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349305163175327064104441 261978872381495298078331)
          ·
            refine ⟨392968308572242947117497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261978872381495298078331 392968308572242947117497)
            ·
              refine ⟨294726231429182210338123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392968308572242947117497 294726231429182210338123)
              ·
                refine ⟨442089347143773315507185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294726231429182210338123 442089347143773315507185)
                ·
                  refine ⟨331567010357829986630389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442089347143773315507185 331567010357829986630389)
                  ·
                    refine ⟨31084407221046561246599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 331567010357829986630389 31084407221046561246599)
                    ·
                      rfl

theorem cell23_181610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_181610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181610 prefixEnd_181610 := by exact prefixLift 181610
  have htrace : WordTrace (prefixWord ++ tailWord_181610) baseStart_181610 baseEnd_181610 := by
    simpa [prefixWord, tailWord_181610, baseEnd_181610] using wordTrace_append hprefix tailTrace_181610
  have hstable : (prefixWord ++ tailWord_181610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181610).length < 2 ^ (prefixWord ++ tailWord_181610).sum := by decide
  have hdescent : baseEnd_181610 < baseStart_181610 := by decide
  rcases family_descends (prefixWord ++ tailWord_181610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181613 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_181613 : Nat := 118140960795 + 181613 * 2 ^ 59
def prefixEnd_181613 : Nat := 4983230072969 + 3 ^ 40 * 181613 * 2
def baseEnd_181613 : Nat := 93254762105103172002283

theorem tailTrace_181613 : CollatzResearch.WordTrace tailWord_181613 prefixEnd_181613 93254762105103172002283 := by
  unfold tailWord_181613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623970291054592876117493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4415980194036395250744995 6623970291054592876117493)
  ·
    refine ⟨620997214786368082136015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6623970291054592876117493 620997214786368082136015)
    ·
      refine ⟨931495822179552123204023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620997214786368082136015 931495822179552123204023)
      ·
        refine ⟨1397243733269328184806035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 931495822179552123204023 1397243733269328184806035)
        ·
          refine ⟨2095865599903992277209053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397243733269328184806035 2095865599903992277209053)
          ·
            refine ⟨785949599963997103953395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2095865599903992277209053 785949599963997103953395)
            ·
              refine ⟨1178924399945995655930093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785949599963997103953395 1178924399945995655930093)
              ·
                refine ⟨442096649979748370973785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1178924399945995655930093 442096649979748370973785)
                ·
                  refine ⟨331572487484811278230339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442096649979748370973785 331572487484811278230339)
                  ·
                    refine ⟨497358731227216917345509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 331572487484811278230339 497358731227216917345509)
                    ·
                      refine ⟨93254762105103172002283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 497358731227216917345509 93254762105103172002283)
                      ·
                        rfl

theorem cell23_181613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_181613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181613 prefixEnd_181613 := by exact prefixLift 181613
  have htrace : WordTrace (prefixWord ++ tailWord_181613) baseStart_181613 baseEnd_181613 := by
    simpa [prefixWord, tailWord_181613, baseEnd_181613] using wordTrace_append hprefix tailTrace_181613
  have hstable : (prefixWord ++ tailWord_181613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181613).length < 2 ^ (prefixWord ++ tailWord_181613).sum := by decide
  have hdescent : baseEnd_181613 < baseStart_181613 := by decide
  rcases family_descends (prefixWord ++ tailWord_181613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181696 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 3, 6]
def baseStart_181696 : Nat := 118140960795 + 181696 * 2 ^ 59
def prefixEnd_181696 : Nat := 4983230072969 + 3 ^ 40 * 181696 * 2
def baseEnd_181696 : Nat := 31099126999808782421467

theorem tailTrace_181696 : CollatzResearch.WordTrace tailWord_181696 prefixEnd_181696 31099126999808782421467 := by
  unfold tailWord_181696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3313498774876949025694471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4417998366502598700925961 3313498774876949025694471)
  ·
    refine ⟨4970248162315423538541707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3313498774876949025694471 4970248162315423538541707)
    ·
      refine ⟨7455372243473135307812561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970248162315423538541707 7455372243473135307812561)
      ·
        refine ⟨5591529182604851480859421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455372243473135307812561 5591529182604851480859421)
        ·
          refine ⟨2096823443476819305322283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5591529182604851480859421 2096823443476819305322283)
          ·
            refine ⟨3145235165215228957983425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096823443476819305322283 3145235165215228957983425)
            ·
              refine ⟨2358926373911421718487569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3145235165215228957983425 2358926373911421718487569)
              ·
                refine ⟨1769194780433566288865677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2358926373911421718487569 1769194780433566288865677)
                ·
                  refine ⟨663448042662587358324629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1769194780433566288865677 663448042662587358324629)
                  ·
                    refine ⟨31099126999808782421467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 663448042662587358324629 31099126999808782421467)
                    ·
                      rfl

theorem cell23_181696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_181696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181696 prefixEnd_181696 := by exact prefixLift 181696
  have htrace : WordTrace (prefixWord ++ tailWord_181696) baseStart_181696 baseEnd_181696 := by
    simpa [prefixWord, tailWord_181696, baseEnd_181696] using wordTrace_append hprefix tailTrace_181696
  have hstable : (prefixWord ++ tailWord_181696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181696).length < 2 ^ (prefixWord ++ tailWord_181696).sum := by decide
  have hdescent : baseEnd_181696 < baseStart_181696 := by decide
  rcases family_descends (prefixWord ++ tailWord_181696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181774 : List Nat := [4, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_181774 : Nat := 118140960795 + 181774 * 2 ^ 59
def prefixEnd_181774 : Nat := 4983230072969 + 3 ^ 40 * 181774 * 2
def baseEnd_181774 : Nat := 93337432490477042089043

theorem tailTrace_181774 : CollatzResearch.WordTrace tailWord_181774 prefixEnd_181774 93337432490477042089043 := by
  unfold tailWord_181774
  simp only [CollatzResearch.WordTrace]
  refine ⟨828730305433914671591047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4419894962314211581818917 828730305433914671591047)
  ·
    refine ⟨1243095458150872007386571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828730305433914671591047 1243095458150872007386571)
    ·
      refine ⟨1864643187226308011079857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243095458150872007386571 1864643187226308011079857)
      ·
        refine ⟨1398482390419731008309893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1864643187226308011079857 1398482390419731008309893)
        ·
          refine ⟨262215448203699564058105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1398482390419731008309893 262215448203699564058105)
          ·
            refine ⟨196661586152774673043579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262215448203699564058105 196661586152774673043579)
            ·
              refine ⟨294992379229162009565369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196661586152774673043579 294992379229162009565369)
              ·
                refine ⟨221244284421871507174027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294992379229162009565369 221244284421871507174027)
                ·
                  refine ⟨331866426632807260761041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221244284421871507174027 331866426632807260761041)
                  ·
                    refine ⟨248899819974605445570781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 331866426632807260761041 248899819974605445570781)
                    ·
                      refine ⟨93337432490477042089043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 248899819974605445570781 93337432490477042089043)
                      ·
                        rfl

theorem cell23_181774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_181774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181774 prefixEnd_181774 := by exact prefixLift 181774
  have htrace : WordTrace (prefixWord ++ tailWord_181774) baseStart_181774 baseEnd_181774 := by
    simpa [prefixWord, tailWord_181774, baseEnd_181774] using wordTrace_append hprefix tailTrace_181774
  have hstable : (prefixWord ++ tailWord_181774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181774).length < 2 ^ (prefixWord ++ tailWord_181774).sum := by decide
  have hdescent : baseEnd_181774 < baseStart_181774 := by decide
  rcases family_descends (prefixWord ++ tailWord_181774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181810 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2]
def baseStart_181810 : Nat := 118140960795 + 181810 * 2 ^ 59
def prefixEnd_181810 : Nat := 4983230072969 + 3 ^ 40 * 181810 * 2
def baseEnd_181810 : Nat := 93355917794038901238877

theorem tailTrace_181810 : CollatzResearch.WordTrace tailWord_181810 prefixEnd_181810 93355917794038901238877 := by
  unfold tailWord_181810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657788867835223880259721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4420770314227263680692589 1657788867835223880259721)
  ·
    refine ⟨1243341650876417910194791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1657788867835223880259721 1243341650876417910194791)
    ·
      refine ⟨1865012476314626865292187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243341650876417910194791 1865012476314626865292187)
      ·
        refine ⟨2797518714471940297938281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865012476314626865292187 2797518714471940297938281)
        ·
          refine ⟨2098139035853955223453711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797518714471940297938281 2098139035853955223453711)
          ·
            refine ⟨3147208553780932835180567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098139035853955223453711 3147208553780932835180567)
            ·
              refine ⟨4720812830671399252770851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147208553780932835180567 4720812830671399252770851)
              ·
                refine ⟨7081219246007098879156277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720812830671399252770851 7081219246007098879156277)
                ·
                  refine ⟨663864304313165519920901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7081219246007098879156277 663864304313165519920901)
                  ·
                    refine ⟨124474557058718534985169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663864304313165519920901 124474557058718534985169)
                    ·
                      refine ⟨93355917794038901238877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124474557058718534985169 93355917794038901238877)
                      ·
                        rfl

theorem cell23_181810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_181810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181810 prefixEnd_181810 := by exact prefixLift 181810
  have htrace : WordTrace (prefixWord ++ tailWord_181810) baseStart_181810 baseEnd_181810 := by
    simpa [prefixWord, tailWord_181810, baseEnd_181810] using wordTrace_append hprefix tailTrace_181810
  have hstable : (prefixWord ++ tailWord_181810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181810).length < 2 ^ (prefixWord ++ tailWord_181810).sum := by decide
  have hdescent : baseEnd_181810 < baseStart_181810 := by decide
  rcases family_descends (prefixWord ++ tailWord_181810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181820 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_181820 : Nat := 118140960795 + 181820 * 2 ^ 59
def prefixEnd_181820 : Nat := 4983230072969 + 3 ^ 40 * 181820 * 2
def baseEnd_181820 : Nat := 31120350866861287371277

theorem tailTrace_181820 : CollatzResearch.WordTrace tailWord_181820 prefixEnd_181820 31120350866861287371277 := by
  unfold tailWord_181820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315760100652333614451457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4421013467536444819268609 3315760100652333614451457)
  ·
    refine ⟨2486820075489250210838593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3315760100652333614451457 2486820075489250210838593)
    ·
      refine ⟨1865115056616937658128945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2486820075489250210838593 1865115056616937658128945)
      ·
        refine ⟨1398836292462703243596709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865115056616937658128945 1398836292462703243596709)
        ·
          refine ⟨262281804836756858174383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1398836292462703243596709 262281804836756858174383)
          ·
            refine ⟨393422707255135287261575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262281804836756858174383 393422707255135287261575)
            ·
              refine ⟨590134060882702930892363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393422707255135287261575 590134060882702930892363)
              ·
                refine ⟨885201091324054396338545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590134060882702930892363 885201091324054396338545)
                ·
                  refine ⟨663900818493040797253909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885201091324054396338545 663900818493040797253909)
                  ·
                    refine ⟨31120350866861287371277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 663900818493040797253909 31120350866861287371277)
                    ·
                      rfl

theorem cell23_181820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_181820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181820 prefixEnd_181820 := by exact prefixLift 181820
  have htrace : WordTrace (prefixWord ++ tailWord_181820) baseStart_181820 baseEnd_181820 := by
    simpa [prefixWord, tailWord_181820, baseEnd_181820] using wordTrace_append hprefix tailTrace_181820
  have hstable : (prefixWord ++ tailWord_181820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181820).length < 2 ^ (prefixWord ++ tailWord_181820).sum := by decide
  have hdescent : baseEnd_181820 < baseStart_181820 := by decide
  rcases family_descends (prefixWord ++ tailWord_181820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181823 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_181823 : Nat := 118140960795 + 181823 * 2 ^ 59
def prefixEnd_181823 : Nat := 4983230072969 + 3 ^ 40 * 181823 * 2
def baseEnd_181823 : Nat := 93362593042547350376317

theorem tailTrace_181823 : CollatzResearch.WordTrace tailWord_181823 prefixEnd_181823 93362593042547350376317 := by
  unfold tailWord_181823
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631629620293798741262123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4421086413529199160841415 6631629620293798741262123)
  ·
    refine ⟨9947444430440698111893185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6631629620293798741262123 9947444430440698111893185)
    ·
      refine ⟨7460583322830523583919889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9947444430440698111893185 7460583322830523583919889)
      ·
        refine ⟨5595437492122892687939917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7460583322830523583919889 5595437492122892687939917)
        ·
          refine ⟨2098289059546084757977469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5595437492122892687939917 2098289059546084757977469)
          ·
            refine ⟨786858397329781784241551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098289059546084757977469 786858397329781784241551)
            ·
              refine ⟨1180287595994672676362327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 786858397329781784241551 1180287595994672676362327)
              ·
                refine ⟨1770431393992009014543491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180287595994672676362327 1770431393992009014543491)
                ·
                  refine ⟨2655647090988013521815237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770431393992009014543491 2655647090988013521815237)
                  ·
                    refine ⟨497933829560252535340357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2655647090988013521815237 497933829560252535340357)
                    ·
                      refine ⟨93362593042547350376317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 497933829560252535340357 93362593042547350376317)
                      ·
                        rfl

theorem cell23_181823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_181823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181823 prefixEnd_181823 := by exact prefixLift 181823
  have htrace : WordTrace (prefixWord ++ tailWord_181823) baseStart_181823 baseEnd_181823 := by
    simpa [prefixWord, tailWord_181823, baseEnd_181823] using wordTrace_append hprefix tailTrace_181823
  have hstable : (prefixWord ++ tailWord_181823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181823).length < 2 ^ (prefixWord ++ tailWord_181823).sum := by decide
  have hdescent : baseEnd_181823 < baseStart_181823 := by decide
  rcases family_descends (prefixWord ++ tailWord_181823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181860 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_181860 : Nat := 118140960795 + 181860 * 2 ^ 59
def prefixEnd_181860 : Nat := 4983230072969 + 3 ^ 40 * 181860 * 2
def baseEnd_181860 : Nat := 93381591826763705613647

theorem tailTrace_181860 : CollatzResearch.WordTrace tailWord_181860 prefixEnd_181860 93381591826763705613647 := by
  unfold tailWord_181860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3316489560579877030179517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4421986080773169373572689 3316489560579877030179517)
  ·
    refine ⟨1243683585217453886317319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3316489560579877030179517 1243683585217453886317319)
    ·
      refine ⟨1865525377826180829475979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243683585217453886317319 1865525377826180829475979)
      ·
        refine ⟨2798288066739271244213969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865525377826180829475979 2798288066739271244213969)
        ·
          refine ⟨2098716050054453433160477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2798288066739271244213969 2098716050054453433160477)
          ·
            refine ⟨787018518770420037435179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2098716050054453433160477 787018518770420037435179)
            ·
              refine ⟨1180527778155630056152769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787018518770420037435179 1180527778155630056152769)
              ·
                refine ⟨885395833616722542114577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180527778155630056152769 885395833616722542114577)
                ·
                  refine ⟨664046875212541906585933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885395833616722542114577 664046875212541906585933)
                  ·
                    refine ⟨249017578204703214969725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664046875212541906585933 249017578204703214969725)
                    ·
                      refine ⟨93381591826763705613647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249017578204703214969725 93381591826763705613647)
                      ·
                        rfl

theorem cell23_181860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_181860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181860 prefixEnd_181860 := by exact prefixLift 181860
  have htrace : WordTrace (prefixWord ++ tailWord_181860) baseStart_181860 baseEnd_181860 := by
    simpa [prefixWord, tailWord_181860, baseEnd_181860] using wordTrace_append hprefix tailTrace_181860
  have hstable : (prefixWord ++ tailWord_181860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181860).length < 2 ^ (prefixWord ++ tailWord_181860).sum := by decide
  have hdescent : baseEnd_181860 < baseStart_181860 := by decide
  rcases family_descends (prefixWord ++ tailWord_181860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181861 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 2, 2, 2]
def baseStart_181861 : Nat := 118140960795 + 181861 * 2 ^ 59
def prefixEnd_181861 : Nat := 4983230072969 + 3 ^ 40 * 181861 * 2
def baseEnd_181861 : Nat := 93382105307418201701143

theorem tailTrace_181861 : CollatzResearch.WordTrace tailWord_181861 prefixEnd_181861 93382105307418201701143 := by
  unfold tailWord_181861
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633015594156131231145437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422010396104087487430291 6633015594156131231145437)
  ·
    refine ⟨2487380847808549211679539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6633015594156131231145437 2487380847808549211679539)
    ·
      refine ⟨3731071271712823817519309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487380847808549211679539 3731071271712823817519309)
      ·
        refine ⟨1399151726892308931569741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3731071271712823817519309 1399151726892308931569741)
        ·
          refine ⟨524681897584615849338653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1399151726892308931569741 524681897584615849338653)
          ·
            refine ⟨196755711594230943501995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 524681897584615849338653 196755711594230943501995)
            ·
              refine ⟨295133567391346415252993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196755711594230943501995 295133567391346415252993)
              ·
                refine ⟨221350175543509811439745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295133567391346415252993 221350175543509811439745)
                ·
                  refine ⟨166012631657632358579809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221350175543509811439745 166012631657632358579809)
                  ·
                    refine ⟨124509473743224268934857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166012631657632358579809 124509473743224268934857)
                    ·
                      refine ⟨93382105307418201701143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124509473743224268934857 93382105307418201701143)
                      ·
                        rfl

theorem cell23_181861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_181861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181861 prefixEnd_181861 := by exact prefixLift 181861
  have htrace : WordTrace (prefixWord ++ tailWord_181861) baseStart_181861 baseEnd_181861 := by
    simpa [prefixWord, tailWord_181861, baseEnd_181861] using wordTrace_append hprefix tailTrace_181861
  have hstable : (prefixWord ++ tailWord_181861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181861).length < 2 ^ (prefixWord ++ tailWord_181861).sum := by decide
  have hdescent : baseEnd_181861 < baseStart_181861 := by decide
  rcases family_descends (prefixWord ++ tailWord_181861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181873 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_181873 : Nat := 118140960795 + 181873 * 2 ^ 59
def prefixEnd_181873 : Nat := 4983230072969 + 3 ^ 40 * 181873 * 2
def baseEnd_181873 : Nat := 93388267075272154751087

theorem tailTrace_181873 : CollatzResearch.WordTrace tailWord_181873 prefixEnd_181873 93388267075272154751087 := by
  unfold tailWord_181873
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633453270112657280582273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422302180075104853721515 6633453270112657280582273)
  ·
    refine ⟨4975089952584492960436705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6633453270112657280582273 4975089952584492960436705)
    ·
      refine ⟨3731317464438369720327529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4975089952584492960436705 3731317464438369720327529)
      ·
        refine ⟨2798488098328777290245647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3731317464438369720327529 2798488098328777290245647)
        ·
          refine ⟨4197732147493165935368471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798488098328777290245647 4197732147493165935368471)
          ·
            refine ⟨6296598221239748903052707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197732147493165935368471 6296598221239748903052707)
            ·
              refine ⟨9444897331859623354579061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296598221239748903052707 9444897331859623354579061)
              ·
                refine ⟨885459124861839689491787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9444897331859623354579061 885459124861839689491787)
                ·
                  refine ⟨1328188687292759534237681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885459124861839689491787 1328188687292759534237681)
                  ·
                    refine ⟨996141515469569650678261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1328188687292759534237681 996141515469569650678261)
                    ·
                      refine ⟨93388267075272154751087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 996141515469569650678261 93388267075272154751087)
                      ·
                        rfl

theorem cell23_181873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_181873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181873 prefixEnd_181873 := by exact prefixLift 181873
  have htrace : WordTrace (prefixWord ++ tailWord_181873) baseStart_181873 baseEnd_181873 := by
    simpa [prefixWord, tailWord_181873, baseEnd_181873] using wordTrace_append hprefix tailTrace_181873
  have hstable : (prefixWord ++ tailWord_181873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181873).length < 2 ^ (prefixWord ++ tailWord_181873).sum := by decide
  have hdescent : baseEnd_181873 < baseStart_181873 := by decide
  rcases family_descends (prefixWord ++ tailWord_181873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181877 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_181877 : Nat := 118140960795 + 181877 * 2 ^ 59
def prefixEnd_181877 : Nat := 4983230072969 + 3 ^ 40 * 181877 * 2
def baseEnd_181877 : Nat := 93390320997890139101069

theorem tailTrace_181877 : CollatzResearch.WordTrace tailWord_181877 prefixEnd_181877 93390320997890139101069 := by
  unfold tailWord_181877
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633599162098165963727885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422399441398777309151923 6633599162098165963727885)
  ·
    refine ⟨2487599685786812236397957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6633599162098165963727885 2487599685786812236397957)
    ·
      refine ⟨466424941085027294324617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2487599685786812236397957 466424941085027294324617)
      ·
        refine ⟨349818705813770470743463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466424941085027294324617 349818705813770470743463)
        ·
          refine ⟨524728058720655706115195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349818705813770470743463 524728058720655706115195)
          ·
            refine ⟨787092088080983559172793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524728058720655706115195 787092088080983559172793)
            ·
              refine ⟨590319066060737669379595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787092088080983559172793 590319066060737669379595)
              ·
                refine ⟨885478599091106504069393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590319066060737669379595 885478599091106504069393)
                ·
                  refine ⟨664108949318329878052045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 885478599091106504069393 664108949318329878052045)
                  ·
                    refine ⟨249040855994373704269517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 664108949318329878052045 249040855994373704269517)
                    ·
                      refine ⟨93390320997890139101069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249040855994373704269517 93390320997890139101069)
                      ·
                        rfl

theorem cell23_181877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_181877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181877 prefixEnd_181877 := by exact prefixLift 181877
  have htrace : WordTrace (prefixWord ++ tailWord_181877) baseStart_181877 baseEnd_181877 := by
    simpa [prefixWord, tailWord_181877, baseEnd_181877] using wordTrace_append hprefix tailTrace_181877
  have hstable : (prefixWord ++ tailWord_181877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181877).length < 2 ^ (prefixWord ++ tailWord_181877).sum := by decide
  have hdescent : baseEnd_181877 < baseStart_181877 := by decide
  rcases family_descends (prefixWord ++ tailWord_181877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181878 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_181878 : Nat := 118140960795 + 181878 * 2 ^ 59
def prefixEnd_181878 : Nat := 4983230072969 + 3 ^ 40 * 181878 * 2
def baseEnd_181878 : Nat := 93390834478544635188565

theorem tailTrace_181878 : CollatzResearch.WordTrace tailWord_181878 prefixEnd_181878 93390834478544635188565 := by
  unfold tailWord_181878
  simp only [CollatzResearch.WordTrace]
  refine ⟨414602227193408945907143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4422423756729695423009525 414602227193408945907143)
  ·
    refine ⟨621903340790113418860715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414602227193408945907143 621903340790113418860715)
    ·
      refine ⟨932855011185170128291073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 621903340790113418860715 932855011185170128291073)
      ·
        refine ⟨699641258388877596218305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 932855011185170128291073 699641258388877596218305)
        ·
          refine ⟨524730943791658197163729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699641258388877596218305 524730943791658197163729)
          ·
            refine ⟨393548207843743647872797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524730943791658197163729 393548207843743647872797)
            ·
              refine ⟨147580577941403867952299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393548207843743647872797 147580577941403867952299)
              ·
                refine ⟨221370866912105801928449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147580577941403867952299 221370866912105801928449)
                ·
                  refine ⟨166028150184079351446337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221370866912105801928449 166028150184079351446337)
                  ·
                    refine ⟨124521112638059513584753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166028150184079351446337 124521112638059513584753)
                    ·
                      refine ⟨93390834478544635188565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124521112638059513584753 93390834478544635188565)
                      ·
                        rfl

theorem cell23_181878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_181878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181878 prefixEnd_181878 := by exact prefixLift 181878
  have htrace : WordTrace (prefixWord ++ tailWord_181878) baseStart_181878 baseEnd_181878 := by
    simpa [prefixWord, tailWord_181878, baseEnd_181878] using wordTrace_append hprefix tailTrace_181878
  have hstable : (prefixWord ++ tailWord_181878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181878).length < 2 ^ (prefixWord ++ tailWord_181878).sum := by decide
  have hdescent : baseEnd_181878 < baseStart_181878 := by decide
  rcases family_descends (prefixWord ++ tailWord_181878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181883 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_181883 : Nat := 118140960795 + 181883 * 2 ^ 59
def prefixEnd_181883 : Nat := 4983230072969 + 3 ^ 40 * 181883 * 2
def baseEnd_181883 : Nat := 93393401881817115626041

theorem tailTrace_181883 : CollatzResearch.WordTrace tailWord_181883 prefixEnd_181883 93393401881817115626041 := by
  unfold tailWord_181883
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633818000076428988446303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422545333384285992297535 6633818000076428988446303)
  ·
    refine ⟨9950727000114643482669455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633818000076428988446303 9950727000114643482669455)
    ·
      refine ⟨14926090500171965224004183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950727000114643482669455 14926090500171965224004183)
      ·
        refine ⟨22389135750257947836006275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926090500171965224004183 22389135750257947836006275)
        ·
          refine ⟨33583703625386921754009413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22389135750257947836006275 33583703625386921754009413)
          ·
            refine ⟨6296944429760047828876765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33583703625386921754009413 6296944429760047828876765)
            ·
              refine ⟨2361354161160017935828787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6296944429760047828876765 2361354161160017935828787)
              ·
                refine ⟨3542031241740026903743181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361354161160017935828787 3542031241740026903743181)
                ·
                  refine ⟨1328261715652510088903693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3542031241740026903743181 1328261715652510088903693)
                  ·
                    refine ⟨498098143369691283338885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1328261715652510088903693 498098143369691283338885)
                    ·
                      refine ⟨93393401881817115626041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 498098143369691283338885 93393401881817115626041)
                      ·
                        rfl

theorem cell23_181883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_181883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181883 prefixEnd_181883 := by exact prefixLift 181883
  have htrace : WordTrace (prefixWord ++ tailWord_181883) baseStart_181883 baseEnd_181883 := by
    simpa [prefixWord, tailWord_181883, baseEnd_181883] using wordTrace_append hprefix tailTrace_181883
  have hstable : (prefixWord ++ tailWord_181883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181883).length < 2 ^ (prefixWord ++ tailWord_181883).sum := by decide
  have hdescent : baseEnd_181883 < baseStart_181883 := by decide
  rcases family_descends (prefixWord ++ tailWord_181883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181893 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_181893 : Nat := 118140960795 + 181893 * 2 ^ 59
def prefixEnd_181893 : Nat := 4983230072969 + 3 ^ 40 * 181893 * 2
def baseEnd_181893 : Nat := 31132845562787358833665

theorem tailTrace_181893 : CollatzResearch.WordTrace tailWord_181893 prefixEnd_181893 31132845562787358833665 := by
  unfold tailWord_181893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634182730040200696310333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4422788486693467130873555 6634182730040200696310333)
  ·
    refine ⟨2487818523765075261116375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6634182730040200696310333 2487818523765075261116375)
    ·
      refine ⟨3731727785647612891674563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487818523765075261116375 3731727785647612891674563)
      ·
        refine ⟨5597591678471419337511845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3731727785647612891674563 5597591678471419337511845)
        ·
          refine ⟨1049548439713391125783471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5597591678471419337511845 1049548439713391125783471)
          ·
            refine ⟨1574322659570086688675207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049548439713391125783471 1574322659570086688675207)
            ·
              refine ⟨2361483989355130033012811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574322659570086688675207 2361483989355130033012811)
              ·
                refine ⟨3542225984032695049519217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361483989355130033012811 3542225984032695049519217)
                ·
                  refine ⟨2656669488024521287139413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542225984032695049519217 2656669488024521287139413)
                  ·
                    refine ⟨31132845562787358833665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2656669488024521287139413 31132845562787358833665)
                    ·
                      rfl

theorem cell23_181893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_181893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181893 prefixEnd_181893 := by exact prefixLift 181893
  have htrace : WordTrace (prefixWord ++ tailWord_181893) baseStart_181893 baseEnd_181893 := by
    simpa [prefixWord, tailWord_181893, baseEnd_181893] using wordTrace_append hprefix tailTrace_181893
  have hstable : (prefixWord ++ tailWord_181893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181893).length < 2 ^ (prefixWord ++ tailWord_181893).sum := by decide
  have hdescent : baseEnd_181893 < baseStart_181893 := by decide
  rcases family_descends (prefixWord ++ tailWord_181893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181900 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 2, 1, 4]
def baseStart_181900 : Nat := 118140960795 + 181900 * 2 ^ 59
def prefixEnd_181900 : Nat := 4983230072969 + 3 ^ 40 * 181900 * 2
def baseEnd_181900 : Nat := 93402131052943549113463

theorem tailTrace_181900 : CollatzResearch.WordTrace tailWord_181900 prefixEnd_181900 93402131052943549113463 := by
  unfold tailWord_181900
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317219020507420445907577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4422958694009893927876769 3317219020507420445907577)
  ·
    refine ⟨2487914265380565334430683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317219020507420445907577 2487914265380565334430683)
    ·
      refine ⟨3731871398070848001646025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487914265380565334430683 3731871398070848001646025)
      ·
        refine ⟨2798903548553136001234519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3731871398070848001646025 2798903548553136001234519)
        ·
          refine ⟨4198355322829704001851779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798903548553136001234519 4198355322829704001851779)
          ·
            refine ⟨6297532984244556002777669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198355322829704001851779 6297532984244556002777669)
            ·
              refine ⟨1180787434545854250520813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6297532984244556002777669 1180787434545854250520813)
              ·
                refine ⟨442795287954695343945305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1180787434545854250520813 442795287954695343945305)
                ·
                  refine ⟨332096465966021507958979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442795287954695343945305 332096465966021507958979)
                  ·
                    refine ⟨498144698949032261938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 332096465966021507958979 498144698949032261938469)
                    ·
                      refine ⟨93402131052943549113463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 498144698949032261938469 93402131052943549113463)
                      ·
                        rfl

theorem cell23_181900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_181900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181900 prefixEnd_181900 := by exact prefixLift 181900
  have htrace : WordTrace (prefixWord ++ tailWord_181900) baseStart_181900 baseEnd_181900 := by
    simpa [prefixWord, tailWord_181900, baseEnd_181900] using wordTrace_append hprefix tailTrace_181900
  have hstable : (prefixWord ++ tailWord_181900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181900).length < 2 ^ (prefixWord ++ tailWord_181900).sum := by decide
  have hdescent : baseEnd_181900 < baseStart_181900 := by decide
  rcases family_descends (prefixWord ++ tailWord_181900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181913 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_181913 : Nat := 118140960795 + 181913 * 2 ^ 59
def prefixEnd_181913 : Nat := 4983230072969 + 3 ^ 40 * 181913 * 2
def baseEnd_181913 : Nat := 93408806301451998250903

theorem tailTrace_181913 : CollatzResearch.WordTrace tailWord_181913 prefixEnd_181913 93408806301451998250903 := by
  unfold tailWord_181913
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634912189967744112038393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423274793311829408025595 6634912189967744112038393)
  ·
    refine ⟨4976184142475808084028795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6634912189967744112038393 4976184142475808084028795)
    ·
      refine ⟨7464276213713712126043193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4976184142475808084028795 7464276213713712126043193)
      ·
        refine ⟨5598207160285284094532395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7464276213713712126043193 5598207160285284094532395)
        ·
          refine ⟨8397310740427926141798593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598207160285284094532395 8397310740427926141798593)
          ·
            refine ⟨6297983055320944606348945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8397310740427926141798593 6297983055320944606348945)
            ·
              refine ⟨4723487291490708454761709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6297983055320944606348945 4723487291490708454761709)
              ·
                refine ⟨1771307734309015670535641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4723487291490708454761709 1771307734309015670535641)
                ·
                  refine ⟨1328480800731761752901731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771307734309015670535641 1328480800731761752901731)
                  ·
                    refine ⟨1992721201097642629352597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328480800731761752901731 1992721201097642629352597)
                    ·
                      refine ⟨93408806301451998250903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1992721201097642629352597 93408806301451998250903)
                      ·
                        rfl

theorem cell23_181913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_181913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181913 prefixEnd_181913 := by exact prefixLift 181913
  have htrace : WordTrace (prefixWord ++ tailWord_181913) baseStart_181913 baseEnd_181913 := by
    simpa [prefixWord, tailWord_181913, baseEnd_181913] using wordTrace_append hprefix tailTrace_181913
  have hstable : (prefixWord ++ tailWord_181913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181913).length < 2 ^ (prefixWord ++ tailWord_181913).sum := by decide
  have hdescent : baseEnd_181913 < baseStart_181913 := by decide
  rcases family_descends (prefixWord ++ tailWord_181913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181923 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 8]
def baseStart_181923 : Nat := 118140960795 + 181923 * 2 ^ 59
def prefixEnd_181923 : Nat := 4983230072969 + 3 ^ 40 * 181923 * 2
def baseEnd_181923 : Nat := 10379326789777439902873

theorem tailTrace_181923 : CollatzResearch.WordTrace tailWord_181923 prefixEnd_181923 10379326789777439902873 := by
  unfold tailWord_181923
  simp only [CollatzResearch.WordTrace]
  refine ⟨6635276919931515819902423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4423517946621010546601615 6635276919931515819902423)
  ·
    refine ⟨9952915379897273729853635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6635276919931515819902423 9952915379897273729853635)
    ·
      refine ⟨14929373069845910594780453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9952915379897273729853635 14929373069845910594780453)
      ·
        refine ⟨2799257450596108236521335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14929373069845910594780453 2799257450596108236521335)
        ·
          refine ⟨4198886175894162354782003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799257450596108236521335 4198886175894162354782003)
          ·
            refine ⟨6298329263841243532173005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198886175894162354782003 6298329263841243532173005)
            ·
              refine ⟨2361873473940466324564877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6298329263841243532173005 2361873473940466324564877)
              ·
                refine ⟨885702552727674871711829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2361873473940466324564877 885702552727674871711829)
                ·
                  refine ⟨10379326789777439902873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 885702552727674871711829 10379326789777439902873)
                  ·
                    rfl

theorem cell23_181923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 8].length) (baseStart_181923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181923 prefixEnd_181923 := by exact prefixLift 181923
  have htrace : WordTrace (prefixWord ++ tailWord_181923) baseStart_181923 baseEnd_181923 := by
    simpa [prefixWord, tailWord_181923, baseEnd_181923] using wordTrace_append hprefix tailTrace_181923
  have hstable : (prefixWord ++ tailWord_181923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181923).length < 2 ^ (prefixWord ++ tailWord_181923).sum := by decide
  have hdescent : baseEnd_181923 < baseStart_181923 := by decide
  rcases family_descends (prefixWord ++ tailWord_181923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_181963 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_181963 : Nat := 118140960795 + 181963 * 2 ^ 59
def prefixEnd_181963 : Nat := 4983230072969 + 3 ^ 40 * 181963 * 2
def baseEnd_181963 : Nat := 93434480334176802625673

theorem tailTrace_181963 : CollatzResearch.WordTrace tailWord_181963 prefixEnd_181963 93434480334176802625673 := by
  unfold tailWord_181963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6636735839786602651358543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4424490559857735100905695 6636735839786602651358543)
  ·
    refine ⟨9955103759679903977037815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6636735839786602651358543 9955103759679903977037815)
    ·
      refine ⟨14932655639519855965556723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9955103759679903977037815 14932655639519855965556723)
      ·
        refine ⟨22398983459279783948335085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14932655639519855965556723 22398983459279783948335085)
        ·
          refine ⟨8399618797229918980625657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22398983459279783948335085 8399618797229918980625657)
          ·
            refine ⟨6299714097922439235469243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399618797229918980625657 6299714097922439235469243)
            ·
              refine ⟨9449571146883658853203865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299714097922439235469243 9449571146883658853203865)
              ·
                refine ⟨7087178360162744139902899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9449571146883658853203865 7087178360162744139902899)
                ·
                  refine ⟨10630767540244116209854349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7087178360162744139902899 10630767540244116209854349)
                  ·
                    refine ⟨3986537827591543578695381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10630767540244116209854349 3986537827591543578695381)
                    ·
                      refine ⟨93434480334176802625673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3986537827591543578695381 93434480334176802625673)
                      ·
                        rfl

theorem cell23_181963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_181963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_181963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_181963 prefixEnd_181963 := by exact prefixLift 181963
  have htrace : WordTrace (prefixWord ++ tailWord_181963) baseStart_181963 baseEnd_181963 := by
    simpa [prefixWord, tailWord_181963, baseEnd_181963] using wordTrace_append hprefix tailTrace_181963
  have hstable : (prefixWord ++ tailWord_181963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_181963).length < 2 ^ (prefixWord ++ tailWord_181963).sum := by decide
  have hdescent : baseEnd_181963 < baseStart_181963 := by decide
  rcases family_descends (prefixWord ++ tailWord_181963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182018 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_182018 : Nat := 118140960795 + 182018 * 2 ^ 59
def prefixEnd_182018 : Nat := 4983230072969 + 3 ^ 40 * 182018 * 2
def baseEnd_182018 : Nat := 93462721770174087437921

theorem tailTrace_182018 : CollatzResearch.WordTrace tailWord_182018 prefixEnd_182018 93462721770174087437921 := by
  unfold tailWord_182018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659685463646836761152677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4425827903058231363073805 1659685463646836761152677)
  ·
    refine ⟨311191024433781892716127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1659685463646836761152677 311191024433781892716127)
    ·
      refine ⟨466786536650672839074191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311191024433781892716127 466786536650672839074191)
      ·
        refine ⟨700179804976009258611287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466786536650672839074191 700179804976009258611287)
        ·
          refine ⟨1050269707464013887916931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700179804976009258611287 1050269707464013887916931)
          ·
            refine ⟨1575404561196020831875397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050269707464013887916931 1575404561196020831875397)
            ·
              refine ⟨295388355224253905976637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1575404561196020831875397 295388355224253905976637)
              ·
                refine ⟨110770633209095214741239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295388355224253905976637 110770633209095214741239)
                ·
                  refine ⟨166155949813642822111859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110770633209095214741239 166155949813642822111859)
                  ·
                    refine ⟨249233924720464233167789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166155949813642822111859 249233924720464233167789)
                    ·
                      refine ⟨93462721770174087437921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249233924720464233167789 93462721770174087437921)
                      ·
                        rfl

theorem cell23_182018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_182018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182018 prefixEnd_182018 := by exact prefixLift 182018
  have htrace : WordTrace (prefixWord ++ tailWord_182018) baseStart_182018 baseEnd_182018 := by
    simpa [prefixWord, tailWord_182018, baseEnd_182018] using wordTrace_append hprefix tailTrace_182018
  have hstable : (prefixWord ++ tailWord_182018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182018).length < 2 ^ (prefixWord ++ tailWord_182018).sum := by decide
  have hdescent : baseEnd_182018 < baseStart_182018 := by decide
  rcases family_descends (prefixWord ++ tailWord_182018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182024 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2]
def baseStart_182024 : Nat := 118140960795 + 182024 * 2 ^ 59
def prefixEnd_182024 : Nat := 4983230072969 + 3 ^ 40 * 182024 * 2
def baseEnd_182024 : Nat := 93465802654101063962893

theorem tailTrace_182024 : CollatzResearch.WordTrace tailWord_182024 prefixEnd_182024 93465802654101063962893 := by
  unfold tailWord_182024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3319480346282805034664563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4425973795043740046219417 3319480346282805034664563)
  ·
    refine ⟨4979220519424207551996845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3319480346282805034664563 4979220519424207551996845)
    ·
      refine ⟨1867207694784077831998817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4979220519424207551996845 1867207694784077831998817)
      ·
        refine ⟨1400405771088058373999113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867207694784077831998817 1400405771088058373999113)
        ·
          refine ⟨1050304328316043780499335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400405771088058373999113 1050304328316043780499335)
          ·
            refine ⟨1575456492474065670749003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050304328316043780499335 1575456492474065670749003)
            ·
              refine ⟨2363184738711098506123505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575456492474065670749003 2363184738711098506123505)
              ·
                refine ⟨1772388554033323879592629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363184738711098506123505 1772388554033323879592629)
                ·
                  refine ⟨166161426940624113711809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1772388554033323879592629 166161426940624113711809)
                  ·
                    refine ⟨124621070205468085283857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166161426940624113711809 124621070205468085283857)
                    ·
                      refine ⟨93465802654101063962893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124621070205468085283857 93465802654101063962893)
                      ·
                        rfl

theorem cell23_182024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_182024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182024 prefixEnd_182024 := by exact prefixLift 182024
  have htrace : WordTrace (prefixWord ++ tailWord_182024) baseStart_182024 baseEnd_182024 := by
    simpa [prefixWord, tailWord_182024, baseEnd_182024] using wordTrace_append hprefix tailTrace_182024
  have hstable : (prefixWord ++ tailWord_182024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182024).length < 2 ^ (prefixWord ++ tailWord_182024).sum := by decide
  have hdescent : baseEnd_182024 < baseStart_182024 := by decide
  rcases family_descends (prefixWord ++ tailWord_182024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182057 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 3]
def baseStart_182057 : Nat := 118140960795 + 182057 * 2 ^ 59
def prefixEnd_182057 : Nat := 4983230072969 + 3 ^ 40 * 182057 * 2
def baseEnd_182057 : Nat := 93482747515699434850241

theorem tailTrace_182057 : CollatzResearch.WordTrace tailWord_182057 prefixEnd_182057 93482747515699434850241 := by
  unfold tailWord_182057
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640164301446056705280425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4426776200964037803520283 6640164301446056705280425)
  ·
    refine ⟨4980123226084542528960319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640164301446056705280425 4980123226084542528960319)
    ·
      refine ⟨7470184839126813793440479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980123226084542528960319 7470184839126813793440479)
      ·
        refine ⟨11205277258690220690160719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7470184839126813793440479 11205277258690220690160719)
        ·
          refine ⟨16807915888035331035241079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11205277258690220690160719 16807915888035331035241079)
          ·
            refine ⟨25211873832052996552861619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807915888035331035241079 25211873832052996552861619)
            ·
              refine ⟨37817810748079494829292429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25211873832052996552861619 37817810748079494829292429)
              ·
                refine ⟨14181679030529810560984661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37817810748079494829292429 14181679030529810560984661)
                ·
                  refine ⟨166191551139021217511539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14181679030529810560984661 166191551139021217511539)
                  ·
                    refine ⟨249287326708531826267309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166191551139021217511539 249287326708531826267309)
                    ·
                      refine ⟨93482747515699434850241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249287326708531826267309 93482747515699434850241)
                      ·
                        rfl

theorem cell23_182057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_182057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182057 prefixEnd_182057 := by exact prefixLift 182057
  have htrace : WordTrace (prefixWord ++ tailWord_182057) baseStart_182057 baseEnd_182057 := by
    simpa [prefixWord, tailWord_182057, baseEnd_182057] using wordTrace_append hprefix tailTrace_182057
  have hstable : (prefixWord ++ tailWord_182057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182057).length < 2 ^ (prefixWord ++ tailWord_182057).sum := by decide
  have hdescent : baseEnd_182057 < baseStart_182057 := by decide
  rcases family_descends (prefixWord ++ tailWord_182057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182074 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_182074 : Nat := 118140960795 + 182074 * 2 ^ 59
def prefixEnd_182074 : Nat := 4983230072969 + 3 ^ 40 * 182074 * 2
def baseEnd_182074 : Nat := 93491476686825868337663

theorem tailTrace_182074 : CollatzResearch.WordTrace tailWord_182074 prefixEnd_182074 93491476686825868337663 := by
  unfold tailWord_182074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660196085596117152162319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4427189561589645739099517 1660196085596117152162319)
  ·
    refine ⟨2490294128394175728243479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660196085596117152162319 2490294128394175728243479)
    ·
      refine ⟨3735441192591263592365219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490294128394175728243479 3735441192591263592365219)
      ·
        refine ⟨5603161788886895388547829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735441192591263592365219 5603161788886895388547829)
        ·
          refine ⟨525296417708146442676359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5603161788886895388547829 525296417708146442676359)
          ·
            refine ⟨787944626562219664014539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525296417708146442676359 787944626562219664014539)
            ·
              refine ⟨1181916939843329496021809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787944626562219664014539 1181916939843329496021809)
              ·
                refine ⟨886437704882497122016357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181916939843329496021809 886437704882497122016357)
                ·
                  refine ⟨166207069665468210378067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886437704882497122016357 166207069665468210378067)
                  ·
                    refine ⟨249310604498202315567101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166207069665468210378067 249310604498202315567101)
                    ·
                      refine ⟨93491476686825868337663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249310604498202315567101 93491476686825868337663)
                      ·
                        rfl

theorem cell23_182074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_182074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182074 prefixEnd_182074 := by exact prefixLift 182074
  have htrace : WordTrace (prefixWord ++ tailWord_182074) baseStart_182074 baseEnd_182074 := by
    simpa [prefixWord, tailWord_182074, baseEnd_182074] using wordTrace_append hprefix tailTrace_182074
  have hstable : (prefixWord ++ tailWord_182074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182074).length < 2 ^ (prefixWord ++ tailWord_182074).sum := by decide
  have hdescent : baseEnd_182074 < baseStart_182074 := by decide
  rcases family_descends (prefixWord ++ tailWord_182074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182080 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_182080 : Nat := 118140960795 + 182080 * 2 ^ 59
def prefixEnd_182080 : Nat := 4983230072969 + 3 ^ 40 * 182080 * 2
def baseEnd_182080 : Nat := 93494557570752844862635

theorem tailTrace_182080 : CollatzResearch.WordTrace tailWord_182080 prefixEnd_182080 93494557570752844862635 := by
  unfold tailWord_182080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320501590181365816683847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4427335453575154422245129 3320501590181365816683847)
  ·
    refine ⟨4980752385272048725025771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3320501590181365816683847 4980752385272048725025771)
    ·
      refine ⟨7471128577908073087538657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980752385272048725025771 7471128577908073087538657)
      ·
        refine ⟨5603346433431054815653993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7471128577908073087538657 5603346433431054815653993)
        ·
          refine ⟨4202509825073291111740495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5603346433431054815653993 4202509825073291111740495)
          ·
            refine ⟨6303764737609936667610743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202509825073291111740495 6303764737609936667610743)
            ·
              refine ⟨9455647106414905001416115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303764737609936667610743 9455647106414905001416115)
              ·
                refine ⟨14183470659622357502124173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9455647106414905001416115 14183470659622357502124173)
                ·
                  refine ⟨5318801497358384063296565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14183470659622357502124173 5318801497358384063296565)
                  ·
                    refine ⟨498637640377348505934053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5318801497358384063296565 498637640377348505934053)
                    ·
                      refine ⟨93494557570752844862635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 498637640377348505934053 93494557570752844862635)
                      ·
                        rfl

theorem cell23_182080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_182080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182080 prefixEnd_182080 := by exact prefixLift 182080
  have htrace : WordTrace (prefixWord ++ tailWord_182080) baseStart_182080 baseEnd_182080 := by
    simpa [prefixWord, tailWord_182080, baseEnd_182080] using wordTrace_append hprefix tailTrace_182080
  have hstable : (prefixWord ++ tailWord_182080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182080).length < 2 ^ (prefixWord ++ tailWord_182080).sum := by decide
  have hdescent : baseEnd_182080 < baseStart_182080 := by decide
  rcases family_descends (prefixWord ++ tailWord_182080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182108 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_182108 : Nat := 118140960795 + 182108 * 2 ^ 59
def prefixEnd_182108 : Nat := 4983230072969 + 3 ^ 40 * 182108 * 2
def baseEnd_182108 : Nat := 93508935029078735312507

theorem tailTrace_182108 : CollatzResearch.WordTrace tailWord_182108 prefixEnd_182108 93508935029078735312507 := by
  unfold tailWord_182108
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321012212130646207693489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4428016282840861610257985 3321012212130646207693489)
  ·
    refine ⟨2490759159097984655770117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3321012212130646207693489 2490759159097984655770117)
    ·
      refine ⟨467017342330872122956897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2490759159097984655770117 467017342330872122956897)
      ·
        refine ⟨350263006748154092217673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467017342330872122956897 350263006748154092217673)
        ·
          refine ⟨262697255061115569163255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350263006748154092217673 262697255061115569163255)
          ·
            refine ⟨394045882591673353744883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262697255061115569163255 394045882591673353744883)
            ·
              refine ⟨591068823887510030617325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394045882591673353744883 591068823887510030617325)
              ·
                refine ⟨221650808957816261481497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591068823887510030617325 221650808957816261481497)
                ·
                  refine ⟨166238106718362196111123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221650808957816261481497 166238106718362196111123)
                  ·
                    refine ⟨249357160077543294166685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166238106718362196111123 249357160077543294166685)
                    ·
                      refine ⟨93508935029078735312507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249357160077543294166685 93508935029078735312507)
                      ·
                        rfl

theorem cell23_182108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_182108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182108 prefixEnd_182108 := by exact prefixLift 182108
  have htrace : WordTrace (prefixWord ++ tailWord_182108) baseStart_182108 baseEnd_182108 := by
    simpa [prefixWord, tailWord_182108, baseEnd_182108] using wordTrace_append hprefix tailTrace_182108
  have hstable : (prefixWord ++ tailWord_182108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182108).length < 2 ^ (prefixWord ++ tailWord_182108).sum := by decide
  have hdescent : baseEnd_182108 < baseStart_182108 := by decide
  rcases family_descends (prefixWord ++ tailWord_182108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182164 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_182164 : Nat := 118140960795 + 182164 * 2 ^ 59
def prefixEnd_182164 : Nat := 4983230072969 + 3 ^ 40 * 182164 * 2
def baseEnd_182164 : Nat := 93537689945730516212249

theorem tailTrace_182164 : CollatzResearch.WordTrace tailWord_182164 prefixEnd_182164 93537689945730516212249 := by
  unfold tailWord_182164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322033456029206989712773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4429377941372275986283697 3322033456029206989712773)
  ·
    refine ⟨622881273005476310571145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3322033456029206989712773 622881273005476310571145)
    ·
      refine ⟨467160954754107232928359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 622881273005476310571145 467160954754107232928359)
      ·
        refine ⟨700741432131160849392539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467160954754107232928359 700741432131160849392539)
        ·
          refine ⟨1051112148196741274088809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700741432131160849392539 1051112148196741274088809)
          ·
            refine ⟨788334111147555955566607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051112148196741274088809 788334111147555955566607)
            ·
              refine ⟨1182501166721333933349911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788334111147555955566607 1182501166721333933349911)
              ·
                refine ⟨1773751750082000900024867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182501166721333933349911 1773751750082000900024867)
                ·
                  refine ⟨2660627625123001350037301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773751750082000900024867 2660627625123001350037301)
                  ·
                    refine ⟨249433839855281376565997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2660627625123001350037301 249433839855281376565997)
                    ·
                      refine ⟨93537689945730516212249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249433839855281376565997 93537689945730516212249)
                      ·
                        rfl

theorem cell23_182164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_182164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182164 prefixEnd_182164 := by exact prefixLift 182164
  have htrace : WordTrace (prefixWord ++ tailWord_182164) baseStart_182164 baseEnd_182164 := by
    simpa [prefixWord, tailWord_182164, baseEnd_182164] using wordTrace_append hprefix tailTrace_182164
  have hstable : (prefixWord ++ tailWord_182164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182164).length < 2 ^ (prefixWord ++ tailWord_182164).sum := by decide
  have hdescent : baseEnd_182164 < baseStart_182164 := by decide
  rcases family_descends (prefixWord ++ tailWord_182164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182298 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_182298 : Nat := 118140960795 + 182298 * 2 ^ 59
def prefixEnd_182298 : Nat := 4983230072969 + 3 ^ 40 * 182298 * 2
def baseEnd_182298 : Nat := 93606496353432991936633

theorem tailTrace_182298 : CollatzResearch.WordTrace tailWord_182298 prefixEnd_182298 93606496353432991936633 := by
  unfold tailWord_182298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662238573393238716200887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4432636195715303243202365 1662238573393238716200887)
  ·
    refine ⟨2493357860089858074301331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1662238573393238716200887 2493357860089858074301331)
    ·
      refine ⟨3740036790134787111451997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493357860089858074301331 3740036790134787111451997)
      ·
        refine ⟨1402513796300545166794499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3740036790134787111451997 1402513796300545166794499)
        ·
          refine ⟨2103770694450817750191749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402513796300545166794499 2103770694450817750191749)
          ·
            refine ⟨394457005209528328160953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2103770694450817750191749 394457005209528328160953)
            ·
              refine ⟨295842753907146246120715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394457005209528328160953 295842753907146246120715)
              ·
                refine ⟨443764130860719369181073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295842753907146246120715 443764130860719369181073)
                ·
                  refine ⟨332823098145539526885805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443764130860719369181073 332823098145539526885805)
                  ·
                    refine ⟨124808661804577322582177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332823098145539526885805 124808661804577322582177)
                    ·
                      refine ⟨93606496353432991936633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124808661804577322582177 93606496353432991936633)
                      ·
                        rfl

theorem cell23_182298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_182298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182298 prefixEnd_182298 := by exact prefixLift 182298
  have htrace : WordTrace (prefixWord ++ tailWord_182298) baseStart_182298 baseEnd_182298 := by
    simpa [prefixWord, tailWord_182298, baseEnd_182298] using wordTrace_append hprefix tailTrace_182298
  have hstable : (prefixWord ++ tailWord_182298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182298).length < 2 ^ (prefixWord ++ tailWord_182298).sum := by decide
  have hdescent : baseEnd_182298 < baseStart_182298 := by decide
  rcases family_descends (prefixWord ++ tailWord_182298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182317 : List Nat := [1, 5, 17]
def baseStart_182317 : Nat := 118140960795 + 182317 * 2 ^ 59
def prefixEnd_182317 : Nat := 4983230072969 + 3 ^ 40 * 182317 * 2
def baseEnd_182317 : Nat := 14268595105299255845

theorem tailTrace_182317 : CollatzResearch.WordTrace tailWord_182317 prefixEnd_182317 14268595105299255845 := by
  unfold tailWord_182317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649647280504121109745205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4433098187002747406496803 6649647280504121109745205)
  ·
    refine ⟨623404432547261354038613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6649647280504121109745205 623404432547261354038613)
    ·
      refine ⟨14268595105299255845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 623404432547261354038613 14268595105299255845)
      ·
        rfl

theorem cell23_182317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 17].length) (baseStart_182317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182317 prefixEnd_182317 := by exact prefixLift 182317
  have htrace : WordTrace (prefixWord ++ tailWord_182317) baseStart_182317 baseEnd_182317 := by
    simpa [prefixWord, tailWord_182317, baseEnd_182317] using wordTrace_append hprefix tailTrace_182317
  have hstable : (prefixWord ++ tailWord_182317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182317).length < 2 ^ (prefixWord ++ tailWord_182317).sum := by decide
  have hdescent : baseEnd_182317 < baseStart_182317 := by decide
  rcases family_descends (prefixWord ++ tailWord_182317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182321 : List Nat := [1, 2, 2, 3, 1, 3, 1, 4, 2, 4]
def baseStart_182321 : Nat := 118140960795 + 182321 * 2 ^ 59
def prefixEnd_182321 : Nat := 4983230072969 + 3 ^ 40 * 182321 * 2
def baseEnd_182321 : Nat := 31206102136162133983009

theorem tailTrace_182321 : CollatzResearch.WordTrace tailWord_182321 prefixEnd_182321 31206102136162133983009 := by
  unfold tailWord_182321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649793172489629792890817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4433195448326419861927211 6649793172489629792890817)
  ·
    refine ⟨4987344879367222344668113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6649793172489629792890817 4987344879367222344668113)
    ·
      refine ⟨3740508659525416758501085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4987344879367222344668113 3740508659525416758501085)
      ·
        refine ⟨1402690747322031284437907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3740508659525416758501085 1402690747322031284437907)
        ·
          refine ⟨2104036120983046926656861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402690747322031284437907 2104036120983046926656861)
          ·
            refine ⟨789013545368642597496323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2104036120983046926656861 789013545368642597496323)
            ·
              refine ⟨1183520318052963896244485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789013545368642597496323 1183520318052963896244485)
              ·
                refine ⟨221910059634930730545841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1183520318052963896244485 221910059634930730545841)
                ·
                  refine ⟨166432544726198047909381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221910059634930730545841 166432544726198047909381)
                  ·
                    refine ⟨31206102136162133983009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166432544726198047909381 31206102136162133983009)
                    ·
                      rfl

theorem cell23_182321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_182321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182321 prefixEnd_182321 := by exact prefixLift 182321
  have htrace : WordTrace (prefixWord ++ tailWord_182321) baseStart_182321 baseEnd_182321 := by
    simpa [prefixWord, tailWord_182321, baseEnd_182321] using wordTrace_append hprefix tailTrace_182321
  have hstable : (prefixWord ++ tailWord_182321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182321).length < 2 ^ (prefixWord ++ tailWord_182321).sum := by decide
  have hdescent : baseEnd_182321 < baseStart_182321 := by decide
  rcases family_descends (prefixWord ++ tailWord_182321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182322 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3]
def baseStart_182322 : Nat := 118140960795 + 182322 * 2 ^ 59
def prefixEnd_182322 : Nat := 4983230072969 + 3 ^ 40 * 182322 * 2
def baseEnd_182322 : Nat := 93618819889140898036523

theorem tailTrace_182322 : CollatzResearch.WordTrace tailWord_182322 prefixEnd_182322 93618819889140898036523 := by
  unfold tailWord_182322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662457411371501740919305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4433219763657337975784813 1662457411371501740919305)
  ·
    refine ⟨1246843058528626305689479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1662457411371501740919305 1246843058528626305689479)
    ·
      refine ⟨1870264587792939458534219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246843058528626305689479 1870264587792939458534219)
      ·
        refine ⟨2805396881689409187801329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870264587792939458534219 2805396881689409187801329)
        ·
          refine ⟨2104047661267056890850997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2805396881689409187801329 2104047661267056890850997)
          ·
            refine ⟨197254468243786583517281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2104047661267056890850997 197254468243786583517281)
            ·
              refine ⟨147940851182839937637961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197254468243786583517281 147940851182839937637961)
              ·
                refine ⟨110955638387129953228471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147940851182839937637961 110955638387129953228471)
                ·
                  refine ⟨166433457580694929842707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110955638387129953228471 166433457580694929842707)
                  ·
                    refine ⟨249650186371042394764061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166433457580694929842707 249650186371042394764061)
                    ·
                      refine ⟨93618819889140898036523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249650186371042394764061 93618819889140898036523)
                      ·
                        rfl

theorem cell23_182322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_182322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182322 prefixEnd_182322 := by exact prefixLift 182322
  have htrace : WordTrace (prefixWord ++ tailWord_182322) baseStart_182322 baseEnd_182322 := by
    simpa [prefixWord, tailWord_182322, baseEnd_182322] using wordTrace_append hprefix tailTrace_182322
  have hstable : (prefixWord ++ tailWord_182322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182322).length < 2 ^ (prefixWord ++ tailWord_182322).sum := by decide
  have hdescent : baseEnd_182322 < baseStart_182322 := by decide
  rcases family_descends (prefixWord ++ tailWord_182322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182361 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 3]
def baseStart_182361 : Nat := 118140960795 + 182361 * 2 ^ 59
def prefixEnd_182361 : Nat := 4983230072969 + 3 ^ 40 * 182361 * 2
def baseEnd_182361 : Nat := 93638845634666245448843

theorem tailTrace_182361 : CollatzResearch.WordTrace tailWord_182361 prefixEnd_182361 93638845634666245448843 := by
  unfold tailWord_182361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651252092344716624346937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4434168061563144416231291 6651252092344716624346937)
  ·
    refine ⟨4988439069258537468260203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6651252092344716624346937 4988439069258537468260203)
    ·
      refine ⟨7482658603887806202390305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988439069258537468260203 7482658603887806202390305)
      ·
        refine ⟨5611993952915854651792729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7482658603887806202390305 5611993952915854651792729)
        ·
          refine ⟨4208995464686890988844547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611993952915854651792729 4208995464686890988844547)
          ·
            refine ⟨6313493197030336483266821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208995464686890988844547 6313493197030336483266821)
            ·
              refine ⟨1183779974443188090612529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6313493197030336483266821 1183779974443188090612529)
              ·
                refine ⟨887834980832391067959397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183779974443188090612529 887834980832391067959397)
                ·
                  refine ⟨166469058906073325242387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 887834980832391067959397 166469058906073325242387)
                  ·
                    refine ⟨249703588359109987863581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166469058906073325242387 249703588359109987863581)
                    ·
                      refine ⟨93638845634666245448843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249703588359109987863581 93638845634666245448843)
                      ·
                        rfl

theorem cell23_182361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_182361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182361 prefixEnd_182361 := by exact prefixLift 182361
  have htrace : WordTrace (prefixWord ++ tailWord_182361) baseStart_182361 baseEnd_182361 := by
    simpa [prefixWord, tailWord_182361, baseEnd_182361] using wordTrace_append hprefix tailTrace_182361
  have hstable : (prefixWord ++ tailWord_182361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182361).length < 2 ^ (prefixWord ++ tailWord_182361).sum := by decide
  have hdescent : baseEnd_182361 < baseStart_182361 := by decide
  rcases family_descends (prefixWord ++ tailWord_182361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182365 : List Nat := [1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_182365 : Nat := 118140960795 + 182365 * 2 ^ 59
def prefixEnd_182365 : Nat := 4983230072969 + 3 ^ 40 * 182365 * 2
def baseEnd_182365 : Nat := 93640899557284229798825

theorem tailTrace_182365 : CollatzResearch.WordTrace tailWord_182365 prefixEnd_182365 93640899557284229798825 := by
  unfold tailWord_182365
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651397984330225307492549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4434265322886816871661699 6651397984330225307492549)
  ·
    refine ⟨1247137122061917245154853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6651397984330225307492549 1247137122061917245154853)
    ·
      refine ⟨233838210386609483466535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1247137122061917245154853 233838210386609483466535)
      ·
        refine ⟨350757315579914225199803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233838210386609483466535 350757315579914225199803)
        ·
          refine ⟨526135973369871337799705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350757315579914225199803 526135973369871337799705)
          ·
            refine ⟨394601980027403503349779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526135973369871337799705 394601980027403503349779)
            ·
              refine ⟨591902970041105255024669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394601980027403503349779 591902970041105255024669)
              ·
                refine ⟨221963613765414470634251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591902970041105255024669 221963613765414470634251)
                ·
                  refine ⟨332945420648121705951377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221963613765414470634251 332945420648121705951377)
                  ·
                    refine ⟨249709065486091279463533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 332945420648121705951377 249709065486091279463533)
                    ·
                      refine ⟨93640899557284229798825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249709065486091279463533 93640899557284229798825)
                      ·
                        rfl

theorem cell23_182365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_182365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182365 prefixEnd_182365 := by exact prefixLift 182365
  have htrace : WordTrace (prefixWord ++ tailWord_182365) baseStart_182365 baseEnd_182365 := by
    simpa [prefixWord, tailWord_182365, baseEnd_182365] using wordTrace_append hprefix tailTrace_182365
  have hstable : (prefixWord ++ tailWord_182365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182365).length < 2 ^ (prefixWord ++ tailWord_182365).sum := by decide
  have hdescent : baseEnd_182365 < baseStart_182365 := by decide
  rcases family_descends (prefixWord ++ tailWord_182365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182405 : List Nat := [1, 3, 1, 1, 5, 2, 2, 2, 1, 3, 2]
def baseStart_182405 : Nat := 118140960795 + 182405 * 2 ^ 59
def prefixEnd_182405 : Nat := 4983230072969 + 3 ^ 40 * 182405 * 2
def baseEnd_182405 : Nat := 93661438783464073298641

theorem tailTrace_182405 : CollatzResearch.WordTrace tailWord_182405 prefixEnd_182405 93661438783464073298641 := by
  unfold tailWord_182405
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652856904185312138948669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4435237936123541425965779 6652856904185312138948669)
  ·
    refine ⟨2494821339069492052105751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6652856904185312138948669 2494821339069492052105751)
    ·
      refine ⟨3742232008604238078158627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494821339069492052105751 3742232008604238078158627)
      ·
        refine ⟨5613348012906357117237941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742232008604238078158627 5613348012906357117237941)
        ·
          refine ⟨526251376209970979741057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5613348012906357117237941 526251376209970979741057)
          ·
            refine ⟨394688532157478234805793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526251376209970979741057 394688532157478234805793)
            ·
              refine ⟨296016399118108676104345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394688532157478234805793 296016399118108676104345)
              ·
                refine ⟨222012299338581507078259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296016399118108676104345 222012299338581507078259)
                ·
                  refine ⟨333018449007872260617389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222012299338581507078259 333018449007872260617389)
                  ·
                    refine ⟨124881918377952097731521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333018449007872260617389 124881918377952097731521)
                    ·
                      refine ⟨93661438783464073298641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124881918377952097731521 93661438783464073298641)
                      ·
                        rfl

theorem cell23_182405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_182405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182405 prefixEnd_182405 := by exact prefixLift 182405
  have htrace : WordTrace (prefixWord ++ tailWord_182405) baseStart_182405 baseEnd_182405 := by
    simpa [prefixWord, tailWord_182405, baseEnd_182405] using wordTrace_append hprefix tailTrace_182405
  have hstable : (prefixWord ++ tailWord_182405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182405).length < 2 ^ (prefixWord ++ tailWord_182405).sum := by decide
  have hdescent : baseEnd_182405 < baseStart_182405 := by decide
  rcases family_descends (prefixWord ++ tailWord_182405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182418 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_182418 : Nat := 118140960795 + 182418 * 2 ^ 59
def prefixEnd_182418 : Nat := 4983230072969 + 3 ^ 40 * 182418 * 2
def baseEnd_182418 : Nat := 93668114031972522436081

theorem tailTrace_182418 : CollatzResearch.WordTrace tailWord_182418 prefixEnd_182418 93668114031972522436081 := by
  unfold tailWord_182418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1663332763284553839792977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4435554035425476906114605 1663332763284553839792977)
  ·
    refine ⟨1247499572463415379844733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1663332763284553839792977 1247499572463415379844733)
    ·
      refine ⟨467812339673780767441775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1247499572463415379844733 467812339673780767441775)
      ·
        refine ⟨701718509510671151162663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467812339673780767441775 701718509510671151162663)
        ·
          refine ⟨1052577764266006726743995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701718509510671151162663 1052577764266006726743995)
          ·
            refine ⟨1578866646399010090115993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052577764266006726743995 1578866646399010090115993)
            ·
              refine ⟨1184149984799257567586995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578866646399010090115993 1184149984799257567586995)
              ·
                refine ⟨1776224977198886351380493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184149984799257567586995 1776224977198886351380493)
                ·
                  refine ⟨666084366449582381767685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1776224977198886351380493 666084366449582381767685)
                  ·
                    refine ⟨124890818709296696581441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666084366449582381767685 124890818709296696581441)
                    ·
                      refine ⟨93668114031972522436081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124890818709296696581441 93668114031972522436081)
                      ·
                        rfl

theorem cell23_182418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_182418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182418 prefixEnd_182418 := by exact prefixLift 182418
  have htrace : WordTrace (prefixWord ++ tailWord_182418) baseStart_182418 baseEnd_182418 := by
    simpa [prefixWord, tailWord_182418, baseEnd_182418] using wordTrace_append hprefix tailTrace_182418
  have hstable : (prefixWord ++ tailWord_182418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182418).length < 2 ^ (prefixWord ++ tailWord_182418).sum := by decide
  have hdescent : baseEnd_182418 < baseStart_182418 := by decide
  rcases family_descends (prefixWord ++ tailWord_182418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182446 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_182446 : Nat := 118140960795 + 182446 * 2 ^ 59
def prefixEnd_182446 : Nat := 4983230072969 + 3 ^ 40 * 182446 * 2
def baseEnd_182446 : Nat := 93682491490298412885953

theorem tailTrace_182446 : CollatzResearch.WordTrace tailWord_182446 prefixEnd_182446 93682491490298412885953 := by
  unfold tailWord_182446
  simp only [CollatzResearch.WordTrace]
  refine ⟨831794037129597017648899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4436234864691184094127461 831794037129597017648899)
  ·
    refine ⟨1247691055694395526473349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 831794037129597017648899 1247691055694395526473349)
    ·
      refine ⟨233942072942699161213753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1247691055694395526473349 233942072942699161213753)
      ·
        refine ⟨175456554707024370910315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233942072942699161213753 175456554707024370910315)
        ·
          refine ⟨263184832060536556365473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175456554707024370910315 263184832060536556365473)
          ·
            refine ⟨197388624045402417274105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263184832060536556365473 197388624045402417274105)
            ·
              refine ⟨148041468034051812955579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197388624045402417274105 148041468034051812955579)
              ·
                refine ⟨222062202051077719433369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148041468034051812955579 222062202051077719433369)
                ·
                  refine ⟨166546651538308289575027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222062202051077719433369 166546651538308289575027)
                  ·
                    refine ⟨249819977307462434362541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166546651538308289575027 249819977307462434362541)
                    ·
                      refine ⟨93682491490298412885953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249819977307462434362541 93682491490298412885953)
                      ·
                        rfl

theorem cell23_182446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_182446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182446 prefixEnd_182446 := by exact prefixLift 182446
  have htrace : WordTrace (prefixWord ++ tailWord_182446) baseStart_182446 baseEnd_182446 := by
    simpa [prefixWord, tailWord_182446, baseEnd_182446] using wordTrace_append hprefix tailTrace_182446
  have hstable : (prefixWord ++ tailWord_182446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182446).length < 2 ^ (prefixWord ++ tailWord_182446).sum := by decide
  have hdescent : baseEnd_182446 < baseStart_182446 := by decide
  rcases family_descends (prefixWord ++ tailWord_182446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182492 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 5]
def baseStart_182492 : Nat := 118140960795 + 182492 * 2 ^ 59
def prefixEnd_182492 : Nat := 4983230072969 + 3 ^ 40 * 182492 * 2
def baseEnd_182492 : Nat := 10411790177822803656749

theorem tailTrace_182492 : CollatzResearch.WordTrace tailWord_182492 prefixEnd_182492 10411790177822803656749 := by
  unfold tailWord_182492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328015027435062998682865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4437353369913417331577153 3328015027435062998682865)
  ·
    refine ⟨2496011270576297249012149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3328015027435062998682865 2496011270576297249012149)
    ·
      refine ⟨234001056616527867094889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2496011270576297249012149 234001056616527867094889)
      ·
        refine ⟨175500792462395900321167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234001056616527867094889 175500792462395900321167)
        ·
          refine ⟨263251188693593850481751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175500792462395900321167 263251188693593850481751)
          ·
            refine ⟨394876783040390775722627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263251188693593850481751 394876783040390775722627)
            ·
              refine ⟨592315174560586163583941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394876783040390775722627 592315174560586163583941)
              ·
                refine ⟨111059095230109905671989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 592315174560586163583941 111059095230109905671989)
                ·
                  refine ⟨10411790177822803656749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111059095230109905671989 10411790177822803656749)
                  ·
                    rfl

theorem cell23_182492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_182492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182492 prefixEnd_182492 := by exact prefixLift 182492
  have htrace : WordTrace (prefixWord ++ tailWord_182492) baseStart_182492 baseEnd_182492 := by
    simpa [prefixWord, tailWord_182492, baseEnd_182492] using wordTrace_append hprefix tailTrace_182492
  have hstable : (prefixWord ++ tailWord_182492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182492).length < 2 ^ (prefixWord ++ tailWord_182492).sum := by decide
  have hdescent : baseEnd_182492 < baseStart_182492 := by decide
  rcases family_descends (prefixWord ++ tailWord_182492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182508 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 2, 4, 2]
def baseStart_182508 : Nat := 118140960795 + 182508 * 2 ^ 59
def prefixEnd_182508 : Nat := 4983230072969 + 3 ^ 40 * 182508 * 2
def baseEnd_182508 : Nat := 93714327290877170310667

theorem tailTrace_182508 : CollatzResearch.WordTrace tailWord_182508 prefixEnd_182508 93714327290877170310667 := by
  unfold tailWord_182508
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328306811406080364974089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4437742415208107153298785 3328306811406080364974089)
  ·
    refine ⟨2496230108554560273730567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3328306811406080364974089 2496230108554560273730567)
    ·
      refine ⟨3744345162831840410595851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2496230108554560273730567 3744345162831840410595851)
      ·
        refine ⟨5616517744247760615893777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3744345162831840410595851 5616517744247760615893777)
        ·
          refine ⟨4212388308185820461920333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5616517744247760615893777 4212388308185820461920333)
          ·
            refine ⟨1579645615569682673220125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4212388308185820461920333 1579645615569682673220125)
            ·
              refine ⟨592367105838631002457547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1579645615569682673220125 592367105838631002457547)
              ·
                refine ⟨888550658757946503686321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592367105838631002457547 888550658757946503686321)
                ·
                  refine ⟨666412994068459877764741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888550658757946503686321 666412994068459877764741)
                  ·
                    refine ⟨124952436387836227080889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666412994068459877764741 124952436387836227080889)
                    ·
                      refine ⟨93714327290877170310667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 124952436387836227080889 93714327290877170310667)
                      ·
                        rfl

theorem cell23_182508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_182508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182508 prefixEnd_182508 := by exact prefixLift 182508
  have htrace : WordTrace (prefixWord ++ tailWord_182508) baseStart_182508 baseEnd_182508 := by
    simpa [prefixWord, tailWord_182508, baseEnd_182508] using wordTrace_append hprefix tailTrace_182508
  have hstable : (prefixWord ++ tailWord_182508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182508).length < 2 ^ (prefixWord ++ tailWord_182508).sum := by decide
  have hdescent : baseEnd_182508 < baseStart_182508 := by decide
  rcases family_descends (prefixWord ++ tailWord_182508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182518 : List Nat := [5, 1, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_182518 : Nat := 118140960795 + 182518 * 2 ^ 59
def prefixEnd_182518 : Nat := 4983230072969 + 3 ^ 40 * 182518 * 2
def baseEnd_182518 : Nat := 31239820699140710395207

theorem tailTrace_182518 : CollatzResearch.WordTrace tailWord_182518 prefixEnd_182518 31239820699140710395207 := by
  unfold tailWord_182518
  simp only [CollatzResearch.WordTrace]
  refine ⟨416061147048495777363263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4437985568517288291874805 416061147048495777363263)
  ·
    refine ⟨624091720572743666044895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 416061147048495777363263 624091720572743666044895)
    ·
      refine ⟨936137580859115499067343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 624091720572743666044895 936137580859115499067343)
      ·
        refine ⟨1404206371288673248601015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936137580859115499067343 1404206371288673248601015)
        ·
          refine ⟨2106309556933009872901523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404206371288673248601015 2106309556933009872901523)
          ·
            refine ⟨3159464335399514809352285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106309556933009872901523 3159464335399514809352285)
            ·
              refine ⟨1184799125774818053507107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3159464335399514809352285 1184799125774818053507107)
              ·
                refine ⟨1777198688662227080260661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184799125774818053507107 1777198688662227080260661)
                ·
                  refine ⟨166612377062083788774437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1777198688662227080260661 166612377062083788774437)
                  ·
                    refine ⟨31239820699140710395207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166612377062083788774437 31239820699140710395207)
                    ·
                      rfl

theorem cell23_182518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_182518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182518 prefixEnd_182518 := by exact prefixLift 182518
  have htrace : WordTrace (prefixWord ++ tailWord_182518) baseStart_182518 baseEnd_182518 := by
    simpa [prefixWord, tailWord_182518, baseEnd_182518] using wordTrace_append hprefix tailTrace_182518
  have hstable : (prefixWord ++ tailWord_182518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182518).length < 2 ^ (prefixWord ++ tailWord_182518).sum := by decide
  have hdescent : baseEnd_182518 < baseStart_182518 := by decide
  rcases family_descends (prefixWord ++ tailWord_182518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182528 : List Nat := [2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_182528 : Nat := 118140960795 + 182528 * 2 ^ 59
def prefixEnd_182528 : Nat := 4983230072969 + 3 ^ 40 * 182528 * 2
def baseEnd_182528 : Nat := 93724596903967092060575

theorem tailTrace_182528 : CollatzResearch.WordTrace tailWord_182528 prefixEnd_182528 93724596903967092060575 := by
  unfold tailWord_182528
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328671541369852072838119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4438228721826469430450825 3328671541369852072838119)
  ·
    refine ⟨4993007312054778109257179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3328671541369852072838119 4993007312054778109257179)
    ·
      refine ⟨7489510968082167163885769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993007312054778109257179 7489510968082167163885769)
      ·
        refine ⟨5617133226061625372914327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489510968082167163885769 5617133226061625372914327)
        ·
          refine ⟨8425699839092438059371491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5617133226061625372914327 8425699839092438059371491)
          ·
            refine ⟨12638549758638657089057237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425699839092438059371491 12638549758638657089057237)
            ·
              refine ⟨296216009968093525524779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12638549758638657089057237 296216009968093525524779)
              ·
                refine ⟨444324014952140288287169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296216009968093525524779 444324014952140288287169)
                ·
                  refine ⟨333243011214105216215377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444324014952140288287169 333243011214105216215377)
                  ·
                    refine ⟨249932258410578912161533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333243011214105216215377 249932258410578912161533)
                    ·
                      refine ⟨93724596903967092060575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 249932258410578912161533 93724596903967092060575)
                      ·
                        rfl

theorem cell23_182528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_182528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182528 prefixEnd_182528 := by exact prefixLift 182528
  have htrace : WordTrace (prefixWord ++ tailWord_182528) baseStart_182528 baseEnd_182528 := by
    simpa [prefixWord, tailWord_182528, baseEnd_182528] using wordTrace_append hprefix tailTrace_182528
  have hstable : (prefixWord ++ tailWord_182528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182528).length < 2 ^ (prefixWord ++ tailWord_182528).sum := by decide
  have hdescent : baseEnd_182528 < baseStart_182528 := by decide
  rcases family_descends (prefixWord ++ tailWord_182528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182551 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_182551 : Nat := 118140960795 + 182551 * 2 ^ 59
def prefixEnd_182551 : Nat := 4983230072969 + 3 ^ 40 * 182551 * 2
def baseEnd_182551 : Nat := 93736406959020502072969

theorem tailTrace_182551 : CollatzResearch.WordTrace tailWord_182551 prefixEnd_182551 93736406959020502072969 := by
  unfold tailWord_182551
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658181961656379073763507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4438787974437586049175671 6658181961656379073763507)
  ·
    refine ⟨9987272942484568610645261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6658181961656379073763507 9987272942484568610645261)
    ·
      refine ⟨3745227353431713228991973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9987272942484568610645261 3745227353431713228991973)
      ·
        refine ⟨702230128768446230435995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3745227353431713228991973 702230128768446230435995)
        ·
          refine ⟨1053345193152669345653993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702230128768446230435995 1053345193152669345653993)
          ·
            refine ⟨790008894864502009240495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1053345193152669345653993 790008894864502009240495)
            ·
              refine ⟨1185013342296753013860743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790008894864502009240495 1185013342296753013860743)
              ·
                refine ⟨1777520013445129520791115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185013342296753013860743 1777520013445129520791115)
                ·
                  refine ⟨2666280020167694281186673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777520013445129520791115 2666280020167694281186673)
                  ·
                    refine ⟨1999710015125770710890005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666280020167694281186673 1999710015125770710890005)
                    ·
                      refine ⟨93736406959020502072969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1999710015125770710890005 93736406959020502072969)
                      ·
                        rfl

theorem cell23_182551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_182551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182551 prefixEnd_182551 := by exact prefixLift 182551
  have htrace : WordTrace (prefixWord ++ tailWord_182551) baseStart_182551 baseEnd_182551 := by
    simpa [prefixWord, tailWord_182551, baseEnd_182551] using wordTrace_append hprefix tailTrace_182551
  have hstable : (prefixWord ++ tailWord_182551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182551).length < 2 ^ (prefixWord ++ tailWord_182551).sum := by decide
  have hdescent : baseEnd_182551 < baseStart_182551 := by decide
  rcases family_descends (prefixWord ++ tailWord_182551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182561 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_182561 : Nat := 118140960795 + 182561 * 2 ^ 59
def prefixEnd_182561 : Nat := 4983230072969 + 3 ^ 40 * 182561 * 2
def baseEnd_182561 : Nat := 31247180588521820982641

theorem tailTrace_182561 : CollatzResearch.WordTrace tailWord_182561 prefixEnd_182561 31247180588521820982641 := by
  unfold tailWord_182561
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658546691620150781627537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439031127746767187751691 6658546691620150781627537)
  ·
    refine ⟨4993910018715113086220653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6658546691620150781627537 4993910018715113086220653)
    ·
      refine ⟨1872716257018167407332745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4993910018715113086220653 1872716257018167407332745)
      ·
        refine ⟨1404537192763625555499559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1872716257018167407332745 1404537192763625555499559)
        ·
          refine ⟨2106805789145438333249339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404537192763625555499559 2106805789145438333249339)
          ·
            refine ⟨3160208683718157499874009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106805789145438333249339 3160208683718157499874009)
            ·
              refine ⟨2370156512788618124905507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3160208683718157499874009 2370156512788618124905507)
              ·
                refine ⟨3555234769182927187358261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370156512788618124905507 3555234769182927187358261)
                ·
                  refine ⟨333303259610899423814837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3555234769182927187358261 333303259610899423814837)
                  ·
                    refine ⟨31247180588521820982641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 333303259610899423814837 31247180588521820982641)
                    ·
                      rfl

theorem cell23_182561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_182561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182561 prefixEnd_182561 := by exact prefixLift 182561
  have htrace : WordTrace (prefixWord ++ tailWord_182561) baseStart_182561 baseEnd_182561 := by
    simpa [prefixWord, tailWord_182561, baseEnd_182561] using wordTrace_append hprefix tailTrace_182561
  have hstable : (prefixWord ++ tailWord_182561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182561).length < 2 ^ (prefixWord ++ tailWord_182561).sum := by decide
  have hdescent : baseEnd_182561 < baseStart_182561 := by decide
  rcases family_descends (prefixWord ++ tailWord_182561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182565 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 6]
def baseStart_182565 : Nat := 118140960795 + 182565 * 2 ^ 59
def prefixEnd_182565 : Nat := 4983230072969 + 3 ^ 40 * 182565 * 2
def baseEnd_182565 : Nat := 10415955076464827477545

theorem tailTrace_182565 : CollatzResearch.WordTrace tailWord_182565 prefixEnd_182565 10415955076464827477545 := by
  unfold tailWord_182565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6658692583605659464773149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439128389070439643182099 6658692583605659464773149)
  ·
    refine ⟨2497009718852122299289931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6658692583605659464773149 2497009718852122299289931)
    ·
      refine ⟨3745514578278183448934897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497009718852122299289931 3745514578278183448934897)
      ·
        refine ⟨2809135933708637586701173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3745514578278183448934897 2809135933708637586701173)
        ·
          refine ⟨263356493785184773753235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2809135933708637586701173 263356493785184773753235)
          ·
            refine ⟨395034740677777160629853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263356493785184773753235 395034740677777160629853)
            ·
              refine ⟨148138027754166435236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395034740677777160629853 148138027754166435236195)
              ·
                refine ⟨222207041631249652854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148138027754166435236195 222207041631249652854293)
                ·
                  refine ⟨10415955076464827477545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222207041631249652854293 10415955076464827477545)
                  ·
                    rfl

theorem cell23_182565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_182565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182565 prefixEnd_182565 := by exact prefixLift 182565
  have htrace : WordTrace (prefixWord ++ tailWord_182565) baseStart_182565 baseEnd_182565 := by
    simpa [prefixWord, tailWord_182565, baseEnd_182565] using wordTrace_append hprefix tailTrace_182565
  have hstable : (prefixWord ++ tailWord_182565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182565).length < 2 ^ (prefixWord ++ tailWord_182565).sum := by decide
  have hdescent : baseEnd_182565 < baseStart_182565 := by decide
  rcases family_descends (prefixWord ++ tailWord_182565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182585 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 1, 5, 2]
def baseStart_182585 : Nat := 118140960795 + 182585 * 2 ^ 59
def prefixEnd_182585 : Nat := 4983230072969 + 3 ^ 40 * 182585 * 2
def baseEnd_182585 : Nat := 93753865301273369047813

theorem tailTrace_182585 : CollatzResearch.WordTrace tailWord_182585 prefixEnd_182585 93753865301273369047813 := by
  unfold tailWord_182585
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659422043533202880501209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439614695688801920334139 6659422043533202880501209)
  ·
    refine ⟨4994566532649902160375907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6659422043533202880501209 4994566532649902160375907)
    ·
      refine ⟨7491849798974853240563861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994566532649902160375907 7491849798974853240563861)
      ·
        refine ⟨351180459326946245651431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7491849798974853240563861 351180459326946245651431)
        ·
          refine ⟨526770688990419368477147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351180459326946245651431 526770688990419368477147)
          ·
            refine ⟨790156033485629052715721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526770688990419368477147 790156033485629052715721)
            ·
              refine ⟨592617025114221789536791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790156033485629052715721 592617025114221789536791)
              ·
                refine ⟨888925537671332684305187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592617025114221789536791 888925537671332684305187)
                ·
                  refine ⟨1333388306506999026457781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888925537671332684305187 1333388306506999026457781)
                  ·
                    refine ⟨125005153735031158730417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1333388306506999026457781 125005153735031158730417)
                    ·
                      refine ⟨93753865301273369047813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125005153735031158730417 93753865301273369047813)
                      ·
                        rfl

theorem cell23_182585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_182585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182585 prefixEnd_182585 := by exact prefixLift 182585
  have htrace : WordTrace (prefixWord ++ tailWord_182585) baseStart_182585 baseEnd_182585 := by
    simpa [prefixWord, tailWord_182585, baseEnd_182585] using wordTrace_append hprefix tailTrace_182585
  have hstable : (prefixWord ++ tailWord_182585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182585).length < 2 ^ (prefixWord ++ tailWord_182585).sum := by decide
  have hdescent : baseEnd_182585 < baseStart_182585 := by decide
  rcases family_descends (prefixWord ++ tailWord_182585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182591 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 3, 6]
def baseStart_182591 : Nat := 118140960795 + 182591 * 2 ^ 59
def prefixEnd_182591 : Nat := 4983230072969 + 3 ^ 40 * 182591 * 2
def baseEnd_182591 : Nat := 31252315395066781857595

theorem tailTrace_182591 : CollatzResearch.WordTrace tailWord_182591 prefixEnd_182591 31252315395066781857595 := by
  unfold tailWord_182591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6659640881511465905219627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4439760587674310603479751 6659640881511465905219627)
  ·
    refine ⟨9989461322267198857829441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6659640881511465905219627 9989461322267198857829441)
    ·
      refine ⟨7492095991700399143372081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9989461322267198857829441 7492095991700399143372081)
      ·
        refine ⟨5619071993775299357529061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7492095991700399143372081 5619071993775299357529061)
        ·
          refine ⟨1053575998832868629536699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5619071993775299357529061 1053575998832868629536699)
          ·
            refine ⟨1580363998249302944305049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053575998832868629536699 1580363998249302944305049)
            ·
              refine ⟨1185272998686977208228787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580363998249302944305049 1185272998686977208228787)
              ·
                refine ⟨1777909498030465812343181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185272998686977208228787 1777909498030465812343181)
                ·
                  refine ⟨666716061761424679628693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1777909498030465812343181 666716061761424679628693)
                  ·
                    refine ⟨31252315395066781857595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 666716061761424679628693 31252315395066781857595)
                    ·
                      rfl

theorem cell23_182591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_182591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182591 prefixEnd_182591 := by exact prefixLift 182591
  have htrace : WordTrace (prefixWord ++ tailWord_182591) baseStart_182591 baseEnd_182591 := by
    simpa [prefixWord, tailWord_182591, baseEnd_182591] using wordTrace_append hprefix tailTrace_182591
  have hstable : (prefixWord ++ tailWord_182591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182591).length < 2 ^ (prefixWord ++ tailWord_182591).sum := by decide
  have hdescent : baseEnd_182591 < baseStart_182591 := by decide
  rcases family_descends (prefixWord ++ tailWord_182591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182608 : List Nat := [2, 1, 1, 1, 1, 6, 2, 1, 4, 4]
def baseStart_182608 : Nat := 118140960795 + 182608 * 2 ^ 59
def prefixEnd_182608 : Nat := 4983230072969 + 3 ^ 40 * 182608 * 2
def baseEnd_182608 : Nat := 31255225118775593020069

theorem tailTrace_182608 : CollatzResearch.WordTrace tailWord_182608 prefixEnd_182608 31255225118775593020069 := by
  unfold tailWord_182608
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330130461224938904294239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440173948299918539058985 3330130461224938904294239)
  ·
    refine ⟨4995195691837408356441359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330130461224938904294239 4995195691837408356441359)
    ·
      refine ⟨7492793537756112534662039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995195691837408356441359 7492793537756112534662039)
      ·
        refine ⟨11239190306634168801993059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7492793537756112534662039 11239190306634168801993059)
        ·
          refine ⟨16858785459951253202989589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239190306634168801993059 16858785459951253202989589)
          ·
            refine ⟨790255568435214993890137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16858785459951253202989589 790255568435214993890137)
            ·
              refine ⟨592691676326411245417603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790255568435214993890137 592691676326411245417603)
              ·
                refine ⟨889037514489616868126405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592691676326411245417603 889037514489616868126405)
                ·
                  refine ⟨166694533966803162773701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 889037514489616868126405 166694533966803162773701)
                  ·
                    refine ⟨31255225118775593020069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166694533966803162773701 31255225118775593020069)
                    ·
                      rfl

theorem cell23_182608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 4, 4].length) (baseStart_182608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182608 prefixEnd_182608 := by exact prefixLift 182608
  have htrace : WordTrace (prefixWord ++ tailWord_182608) baseStart_182608 baseEnd_182608 := by
    simpa [prefixWord, tailWord_182608, baseEnd_182608] using wordTrace_append hprefix tailTrace_182608
  have hstable : (prefixWord ++ tailWord_182608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182608).length < 2 ^ (prefixWord ++ tailWord_182608).sum := by decide
  have hdescent : baseEnd_182608 < baseStart_182608 := by decide
  rcases family_descends (prefixWord ++ tailWord_182608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182609 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_182609 : Nat := 118140960795 + 182609 * 2 ^ 59
def prefixEnd_182609 : Nat := 4983230072969 + 3 ^ 40 * 182609 * 2
def baseEnd_182609 : Nat := 93766188836981275147703

theorem tailTrace_182609 : CollatzResearch.WordTrace tailWord_182609 prefixEnd_182609 93766188836981275147703 := by
  unfold tailWord_182609
  simp only [CollatzResearch.WordTrace]
  refine ⟨6660297395446254979374881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4440198263630836652916587 6660297395446254979374881)
  ·
    refine ⟨4995223046584691234531161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6660297395446254979374881 4995223046584691234531161)
    ·
      refine ⟨3746417284938518425898371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4995223046584691234531161 3746417284938518425898371)
      ·
        refine ⟨5619625927407777638847557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3746417284938518425898371 5619625927407777638847557)
        ·
          refine ⟨1053679861388958307283917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5619625927407777638847557 1053679861388958307283917)
          ·
            refine ⟨395129948020859365231469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1053679861388958307283917 395129948020859365231469)
            ·
              refine ⟨148173730507822261961801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 395129948020859365231469 148173730507822261961801)
              ·
                refine ⟨111130297880866696471351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148173730507822261961801 111130297880866696471351)
                ·
                  refine ⟨166695446821300044707027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111130297880866696471351 166695446821300044707027)
                  ·
                    refine ⟨250043170231950067060541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166695446821300044707027 250043170231950067060541)
                    ·
                      refine ⟨93766188836981275147703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250043170231950067060541 93766188836981275147703)
                      ·
                        rfl

theorem cell23_182609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_182609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182609 prefixEnd_182609 := by exact prefixLift 182609
  have htrace : WordTrace (prefixWord ++ tailWord_182609) baseStart_182609 baseEnd_182609 := by
    simpa [prefixWord, tailWord_182609, baseEnd_182609] using wordTrace_append hprefix tailTrace_182609
  have hstable : (prefixWord ++ tailWord_182609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182609).length < 2 ^ (prefixWord ++ tailWord_182609).sum := by decide
  have hdescent : baseEnd_182609 < baseStart_182609 := by decide
  rcases family_descends (prefixWord ++ tailWord_182609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182611 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_182611 : Nat := 118140960795 + 182611 * 2 ^ 59
def prefixEnd_182611 : Nat := 4983230072969 + 3 ^ 40 * 182611 * 2
def baseEnd_182611 : Nat := 93767215798290267322693

theorem tailTrace_182611 : CollatzResearch.WordTrace tailWord_182611 prefixEnd_182611 93767215798290267322693 := by
  unfold tailWord_182611
  simp only [CollatzResearch.WordTrace]
  refine ⟨6660370341439009320947687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4440246894292672880631791 6660370341439009320947687)
  ·
    refine ⟨9990555512158513981421531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6660370341439009320947687 9990555512158513981421531)
    ·
      refine ⟨14985833268237770972132297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9990555512158513981421531 14985833268237770972132297)
      ·
        refine ⟨11239374951178328229099223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14985833268237770972132297 11239374951178328229099223)
        ·
          refine ⟨16859062426767492343648835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11239374951178328229099223 16859062426767492343648835)
          ·
            refine ⟨25288593640151238515473253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16859062426767492343648835 25288593640151238515473253)
            ·
              refine ⟨4741611307528357221651235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25288593640151238515473253 4741611307528357221651235)
              ·
                refine ⟨7112416961292535832476853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4741611307528357221651235 7112416961292535832476853)
                ·
                  refine ⟨666789090121175234294705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7112416961292535832476853 666789090121175234294705)
                  ·
                    refine ⟨500091817590881425721029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666789090121175234294705 500091817590881425721029)
                    ·
                      refine ⟨93767215798290267322693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500091817590881425721029 93767215798290267322693)
                      ·
                        rfl

theorem cell23_182611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_182611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182611 prefixEnd_182611 := by exact prefixLift 182611
  have htrace : WordTrace (prefixWord ++ tailWord_182611) baseStart_182611 baseEnd_182611 := by
    simpa [prefixWord, tailWord_182611, baseEnd_182611] using wordTrace_append hprefix tailTrace_182611
  have hstable : (prefixWord ++ tailWord_182611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182611).length < 2 ^ (prefixWord ++ tailWord_182611).sum := by decide
  have hdescent : baseEnd_182611 < baseStart_182611 := by decide
  rcases family_descends (prefixWord ++ tailWord_182611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182618 : List Nat := [3, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_182618 : Nat := 118140960795 + 182618 * 2 ^ 59
def prefixEnd_182618 : Nat := 4983230072969 + 3 ^ 40 * 182618 * 2
def baseEnd_182618 : Nat := 93770810162871739935161

theorem tailTrace_182618 : CollatzResearch.WordTrace tailWord_182618 prefixEnd_182618 93770810162871739935161 := by
  unfold tailWord_182618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665156413103412379113127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4440417101609099677635005 1665156413103412379113127)
  ·
    refine ⟨2497734619655118568669691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1665156413103412379113127 2497734619655118568669691)
    ·
      refine ⟨3746601929482677853004537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2497734619655118568669691 3746601929482677853004537)
      ·
        refine ⟨2809951447112008389753403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3746601929482677853004537 2809951447112008389753403)
        ·
          refine ⟨4214927170668012584630105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809951447112008389753403 4214927170668012584630105)
          ·
            refine ⟨3161195378001009438472579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4214927170668012584630105 3161195378001009438472579)
            ·
              refine ⟨4741793067001514157708869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161195378001009438472579 4741793067001514157708869)
              ·
                refine ⟨889086200062783904570413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4741793067001514157708869 889086200062783904570413)
                ·
                  refine ⟨333407325023543964213905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889086200062783904570413 333407325023543964213905)
                  ·
                    refine ⟨250055493767657973160429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 333407325023543964213905 250055493767657973160429)
                    ·
                      refine ⟨93770810162871739935161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250055493767657973160429 93770810162871739935161)
                      ·
                        rfl

theorem cell23_182618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_182618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182618 prefixEnd_182618 := by exact prefixLift 182618
  have htrace : WordTrace (prefixWord ++ tailWord_182618) baseStart_182618 baseEnd_182618 := by
    simpa [prefixWord, tailWord_182618, baseEnd_182618] using wordTrace_append hprefix tailTrace_182618
  have hstable : (prefixWord ++ tailWord_182618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182618).length < 2 ^ (prefixWord ++ tailWord_182618).sum := by decide
  have hdescent : baseEnd_182618 < baseStart_182618 := by decide
  rcases family_descends (prefixWord ++ tailWord_182618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182628 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_182628 : Nat := 118140960795 + 182628 * 2 ^ 59
def prefixEnd_182628 : Nat := 4983230072969 + 3 ^ 40 * 182628 * 2
def baseEnd_182628 : Nat := 93775944969416700810115

theorem tailTrace_182628 : CollatzResearch.WordTrace tailWord_182628 prefixEnd_182628 93775944969416700810115 := by
  unfold tailWord_182628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330495191188710612158269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440660254918280816211025 3330495191188710612158269)
  ·
    refine ⟨1248935696695766479559351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3330495191188710612158269 1248935696695766479559351)
    ·
      refine ⟨1873403545043649719339027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248935696695766479559351 1873403545043649719339027)
      ·
        refine ⟨2810105317565474579008541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1873403545043649719339027 2810105317565474579008541)
        ·
          refine ⟨1053789494087052967128203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2810105317565474579008541 1053789494087052967128203)
          ·
            refine ⟨1580684241130579450692305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053789494087052967128203 1580684241130579450692305)
            ·
              refine ⟨1185513180847934588019229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580684241130579450692305 1185513180847934588019229)
              ·
                refine ⟨444567442817975470507211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1185513180847934588019229 444567442817975470507211)
                ·
                  refine ⟨666851164226963205760817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444567442817975470507211 666851164226963205760817)
                  ·
                    refine ⟨500138373170222404320613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666851164226963205760817 500138373170222404320613)
                    ·
                      refine ⟨93775944969416700810115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500138373170222404320613 93775944969416700810115)
                      ·
                        rfl

theorem cell23_182628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_182628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182628 prefixEnd_182628 := by exact prefixLift 182628
  have htrace : WordTrace (prefixWord ++ tailWord_182628) baseStart_182628 baseEnd_182628 := by
    simpa [prefixWord, tailWord_182628, baseEnd_182628] using wordTrace_append hprefix tailTrace_182628
  have hstable : (prefixWord ++ tailWord_182628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182628).length < 2 ^ (prefixWord ++ tailWord_182628).sum := by decide
  have hdescent : baseEnd_182628 < baseStart_182628 := by decide
  rcases family_descends (prefixWord ++ tailWord_182628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182632 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_182632 : Nat := 118140960795 + 182632 * 2 ^ 59
def prefixEnd_182632 : Nat := 4983230072969 + 3 ^ 40 * 182632 * 2
def baseEnd_182632 : Nat := 93777998892034685160097

theorem tailTrace_182632 : CollatzResearch.WordTrace tailWord_182632 prefixEnd_182632 93777998892034685160097 := by
  unfold tailWord_182632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330568137181464953731075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4440757516241953271641433 3330568137181464953731075)
  ·
    refine ⟨4995852205772197430596613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330568137181464953731075 4995852205772197430596613)
    ·
      refine ⟨936722288582287018236865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4995852205772197430596613 936722288582287018236865)
      ·
        refine ⟨702541716436715263677649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 936722288582287018236865 702541716436715263677649)
        ·
          refine ⟨526906287327536447758237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702541716436715263677649 526906287327536447758237)
          ·
            refine ⟨197589857747826167909339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 526906287327536447758237 197589857747826167909339)
            ·
              refine ⟨296384786621739251864009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197589857747826167909339 296384786621739251864009)
              ·
                refine ⟨222288589966304438898007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296384786621739251864009 222288589966304438898007)
                ·
                  refine ⟨333432884949456658347011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222288589966304438898007 333432884949456658347011)
                  ·
                    refine ⟨500149327424184987520517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333432884949456658347011 500149327424184987520517)
                    ·
                      refine ⟨93777998892034685160097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500149327424184987520517 93777998892034685160097)
                      ·
                        rfl

theorem cell23_182632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_182632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182632 prefixEnd_182632 := by exact prefixLift 182632
  have htrace : WordTrace (prefixWord ++ tailWord_182632) baseStart_182632 baseEnd_182632 := by
    simpa [prefixWord, tailWord_182632, baseEnd_182632] using wordTrace_append hprefix tailTrace_182632
  have hstable : (prefixWord ++ tailWord_182632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182632).length < 2 ^ (prefixWord ++ tailWord_182632).sum := by decide
  have hdescent : baseEnd_182632 < baseStart_182632 := by decide
  rcases family_descends (prefixWord ++ tailWord_182632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182645 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_182645 : Nat := 118140960795 + 182645 * 2 ^ 59
def prefixEnd_182645 : Nat := 4983230072969 + 3 ^ 40 * 182645 * 2
def baseEnd_182645 : Nat := 93784674140543134297537

theorem tailTrace_182645 : CollatzResearch.WordTrace tailWord_182645 prefixEnd_182645 93784674140543134297537 := by
  unfold tailWord_182645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661610423315833127685389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4441073615543888751790259 6661610423315833127685389)
  ·
    refine ⟨2498103908743437422882021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6661610423315833127685389 2498103908743437422882021)
    ·
      refine ⟨468394482889394516790379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2498103908743437422882021 468394482889394516790379)
      ·
        refine ⟨702591724334091775185569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 468394482889394516790379 702591724334091775185569)
        ·
          refine ⟨526943793250568831389177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702591724334091775185569 526943793250568831389177)
          ·
            refine ⟨395207844937926623541883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526943793250568831389177 395207844937926623541883)
            ·
              refine ⟨592811767406889935312825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395207844937926623541883 592811767406889935312825)
              ·
                refine ⟨444608825555167451484619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592811767406889935312825 444608825555167451484619)
                ·
                  refine ⟨666913238332751177226929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444608825555167451484619 666913238332751177226929)
                  ·
                    refine ⟨500184928749563382920197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 666913238332751177226929 500184928749563382920197)
                    ·
                      refine ⟨93784674140543134297537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500184928749563382920197 93784674140543134297537)
                      ·
                        rfl

theorem cell23_182645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_182645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182645 prefixEnd_182645 := by exact prefixLift 182645
  have htrace : WordTrace (prefixWord ++ tailWord_182645) baseStart_182645 baseEnd_182645 := by
    simpa [prefixWord, tailWord_182645, baseEnd_182645] using wordTrace_append hprefix tailTrace_182645
  have hstable : (prefixWord ++ tailWord_182645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182645).length < 2 ^ (prefixWord ++ tailWord_182645).sum := by decide
  have hdescent : baseEnd_182645 < baseStart_182645 := by decide
  rcases family_descends (prefixWord ++ tailWord_182645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182682 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_182682 : Nat := 118140960795 + 182682 * 2 ^ 59
def prefixEnd_182682 : Nat := 4983230072969 + 3 ^ 40 * 182682 * 2
def baseEnd_182682 : Nat := 93803672924759489534867

theorem tailTrace_182682 : CollatzResearch.WordTrace tailWord_182682 prefixEnd_182682 93803672924759489534867 := by
  unfold tailWord_182682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1665739981045447111695575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4441973282787858964521533 1665739981045447111695575)
  ·
    refine ⟨2498609971568170667543363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1665739981045447111695575 2498609971568170667543363)
    ·
      refine ⟨3747914957352256001315045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498609971568170667543363 3747914957352256001315045)
      ·
        refine ⟨702734054503548000246571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3747914957352256001315045 702734054503548000246571)
        ·
          refine ⟨1054101081755322000369857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 702734054503548000246571 1054101081755322000369857)
          ·
            refine ⟨790575811316491500277393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054101081755322000369857 790575811316491500277393)
            ·
              refine ⟨592931858487368625208045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 790575811316491500277393 592931858487368625208045)
              ·
                refine ⟨222349446932763234453017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 592931858487368625208045 222349446932763234453017)
                ·
                  refine ⟨166762085199572425839763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222349446932763234453017 166762085199572425839763)
                  ·
                    refine ⟨250143127799358638759645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166762085199572425839763 250143127799358638759645)
                    ·
                      refine ⟨93803672924759489534867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250143127799358638759645 93803672924759489534867)
                      ·
                        rfl

theorem cell23_182682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_182682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182682 prefixEnd_182682 := by exact prefixLift 182682
  have htrace : WordTrace (prefixWord ++ tailWord_182682) baseStart_182682 baseEnd_182682 := by
    simpa [prefixWord, tailWord_182682, baseEnd_182682] using wordTrace_append hprefix tailTrace_182682
  have hstable : (prefixWord ++ tailWord_182682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182682).length < 2 ^ (prefixWord ++ tailWord_182682).sum := by decide
  have hdescent : baseEnd_182682 < baseStart_182682 := by decide
  rcases family_descends (prefixWord ++ tailWord_182682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182709 : List Nat := [1, 3, 3, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_182709 : Nat := 118140960795 + 182709 * 2 ^ 59
def prefixEnd_182709 : Nat := 4983230072969 + 3 ^ 40 * 182709 * 2
def baseEnd_182709 : Nat := 93817536902430883897243

theorem tailTrace_182709 : CollatzResearch.WordTrace tailWord_182709 prefixEnd_182709 93817536902430883897243 := by
  unfold tailWord_182709
  simp only [CollatzResearch.WordTrace]
  refine ⟨6663944695083972058015181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4442629796722648038676787 6663944695083972058015181)
  ·
    refine ⟨2498979260656489521755693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6663944695083972058015181 2498979260656489521755693)
    ·
      refine ⟨937117222746183570658385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2498979260656489521755693 937117222746183570658385)
      ·
        refine ⟨702837917059637677993789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 937117222746183570658385 702837917059637677993789)
        ·
          refine ⟨263564218897364129247671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 702837917059637677993789 263564218897364129247671)
          ·
            refine ⟨395346328346046193871507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263564218897364129247671 395346328346046193871507)
            ·
              refine ⟨593019492519069290807261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395346328346046193871507 593019492519069290807261)
              ·
                refine ⟨222382309694650984052723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593019492519069290807261 222382309694650984052723)
                ·
                  refine ⟨333573464541976476079085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222382309694650984052723 333573464541976476079085)
                  ·
                    refine ⟨125090049203241178529657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333573464541976476079085 125090049203241178529657)
                    ·
                      refine ⟨93817536902430883897243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125090049203241178529657 93817536902430883897243)
                      ·
                        rfl

theorem cell23_182709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_182709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182709 prefixEnd_182709 := by exact prefixLift 182709
  have htrace : WordTrace (prefixWord ++ tailWord_182709) baseStart_182709 baseEnd_182709 := by
    simpa [prefixWord, tailWord_182709, baseEnd_182709] using wordTrace_append hprefix tailTrace_182709
  have hstable : (prefixWord ++ tailWord_182709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182709).length < 2 ^ (prefixWord ++ tailWord_182709).sum := by decide
  have hdescent : baseEnd_182709 < baseStart_182709 := by decide
  rcases family_descends (prefixWord ++ tailWord_182709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182728 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 7]
def baseStart_182728 : Nat := 118140960795 + 182728 * 2 ^ 59
def prefixEnd_182728 : Nat := 4983230072969 + 3 ^ 40 * 182728 * 2
def baseEnd_182728 : Nat := 10425254781651812173295

theorem tailTrace_182728 : CollatzResearch.WordTrace tailWord_182728 prefixEnd_182728 10425254781651812173295 := by
  unfold tailWord_182728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332318841007569151478419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4443091788010092201971225 3332318841007569151478419)
  ·
    refine ⟨4998478261511353727217629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332318841007569151478419 4998478261511353727217629)
    ·
      refine ⟨1874429348066757647706611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4998478261511353727217629 1874429348066757647706611)
      ·
        refine ⟨2811644022100136471559917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1874429348066757647706611 2811644022100136471559917)
        ·
          refine ⟨1054366508287551176834969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2811644022100136471559917 1054366508287551176834969)
          ·
            refine ⟨790774881215663382626227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054366508287551176834969 790774881215663382626227)
            ·
              refine ⟨1186162321823495073939341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790774881215663382626227 1186162321823495073939341)
              ·
                refine ⟨444810870683810652727253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1186162321823495073939341 444810870683810652727253)
                ·
                  refine ⟨10425254781651812173295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 444810870683810652727253 10425254781651812173295)
                  ·
                    rfl

theorem cell23_182728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 7].length) (baseStart_182728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182728 prefixEnd_182728 := by exact prefixLift 182728
  have htrace : WordTrace (prefixWord ++ tailWord_182728) baseStart_182728 baseEnd_182728 := by
    simpa [prefixWord, tailWord_182728, baseEnd_182728] using wordTrace_append hprefix tailTrace_182728
  have hstable : (prefixWord ++ tailWord_182728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182728).length < 2 ^ (prefixWord ++ tailWord_182728).sum := by decide
  have hdescent : baseEnd_182728 < baseStart_182728 := by decide
  rcases family_descends (prefixWord ++ tailWord_182728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182762 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_182762 : Nat := 118140960795 + 182762 * 2 ^ 59
def prefixEnd_182762 : Nat := 4983230072969 + 3 ^ 40 * 182762 * 2
def baseEnd_182762 : Nat := 10427194597457686281611

theorem tailTrace_182762 : CollatzResearch.WordTrace tailWord_182762 prefixEnd_182762 10427194597457686281611 := by
  unfold tailWord_182762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666469440972990527423635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4443918509261308073129693 1666469440972990527423635)
  ·
    refine ⟨2499704161459485791135453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666469440972990527423635 2499704161459485791135453)
    ·
      refine ⟨937389060547307171675795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2499704161459485791135453 937389060547307171675795)
      ·
        refine ⟨1406083590820960757513693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937389060547307171675795 1406083590820960757513693)
        ·
          refine ⟨527281346557860284067635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1406083590820960757513693 527281346557860284067635)
          ·
            refine ⟨790922019836790426101453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527281346557860284067635 790922019836790426101453)
            ·
              refine ⟨296595757438796409788045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 790922019836790426101453 296595757438796409788045)
              ·
                refine ⟨111223409039548653670517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 296595757438796409788045 111223409039548653670517)
                ·
                  refine ⟨10427194597457686281611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111223409039548653670517 10427194597457686281611)
                  ·
                    rfl

theorem cell23_182762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_182762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182762 prefixEnd_182762 := by exact prefixLift 182762
  have htrace : WordTrace (prefixWord ++ tailWord_182762) baseStart_182762 baseEnd_182762 := by
    simpa [prefixWord, tailWord_182762, baseEnd_182762] using wordTrace_append hprefix tailTrace_182762
  have hstable : (prefixWord ++ tailWord_182762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182762).length < 2 ^ (prefixWord ++ tailWord_182762).sum := by decide
  have hdescent : baseEnd_182762 < baseStart_182762 := by decide
  rcases family_descends (prefixWord ++ tailWord_182762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182768 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_182768 : Nat := 118140960795 + 182768 * 2 ^ 59
def prefixEnd_182768 : Nat := 4983230072969 + 3 ^ 40 * 182768 * 2
def baseEnd_182768 : Nat := 93847832261046153059471

theorem tailTrace_182768 : CollatzResearch.WordTrace tailWord_182768 prefixEnd_182768 93847832261046153059471 := by
  unfold tailWord_182768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333048300935112567206479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4444064401246816756275305 3333048300935112567206479)
  ·
    refine ⟨4999572451402668850809719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333048300935112567206479 4999572451402668850809719)
    ·
      refine ⟨7499358677104003276214579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4999572451402668850809719 7499358677104003276214579)
      ·
        refine ⟨11249038015656004914321869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7499358677104003276214579 11249038015656004914321869)
        ·
          refine ⟨4218389255871001842870701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11249038015656004914321869 4218389255871001842870701)
          ·
            refine ⟨1581895970951625691076513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4218389255871001842870701 1581895970951625691076513)
            ·
              refine ⟨1186421978213719268307385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1581895970951625691076513 1186421978213719268307385)
              ·
                refine ⟨889816483660289451230539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1186421978213719268307385 889816483660289451230539)
                ·
                  refine ⟨1334724725490434176845809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889816483660289451230539 1334724725490434176845809)
                  ·
                    refine ⟨1001043544117825632634357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334724725490434176845809 1001043544117825632634357)
                    ·
                      refine ⟨93847832261046153059471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1001043544117825632634357 93847832261046153059471)
                      ·
                        rfl

theorem cell23_182768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_182768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182768 prefixEnd_182768 := by exact prefixLift 182768
  have htrace : WordTrace (prefixWord ++ tailWord_182768) baseStart_182768 baseEnd_182768 := by
    simpa [prefixWord, tailWord_182768, baseEnd_182768] using wordTrace_append hprefix tailTrace_182768
  have hstable : (prefixWord ++ tailWord_182768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182768).length < 2 ^ (prefixWord ++ tailWord_182768).sum := by decide
  have hdescent : baseEnd_182768 < baseStart_182768 := by decide
  rcases family_descends (prefixWord ++ tailWord_182768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182778 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_182778 : Nat := 118140960795 + 182778 * 2 ^ 59
def prefixEnd_182778 : Nat := 4983230072969 + 3 ^ 40 * 182778 * 2
def baseEnd_182778 : Nat := 93852967067591113934425

theorem tailTrace_182778 : CollatzResearch.WordTrace tailWord_182778 prefixEnd_182778 93852967067591113934425 := by
  unfold tailWord_182778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666615332958499210569247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4444307554555997894851325 1666615332958499210569247)
  ·
    refine ⟨2499922999437748815853871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1666615332958499210569247 2499922999437748815853871)
    ·
      refine ⟨3749884499156623223780807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2499922999437748815853871 3749884499156623223780807)
      ·
        refine ⟨5624826748734934835671211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3749884499156623223780807 5624826748734934835671211)
        ·
          refine ⟨8437240123102402253506817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5624826748734934835671211 8437240123102402253506817)
          ·
            refine ⟨6327930092326801690130113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8437240123102402253506817 6327930092326801690130113)
            ·
              refine ⟨4745947569245101267597585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6327930092326801690130113 4745947569245101267597585)
              ·
                refine ⟨3559460676933825950698189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4745947569245101267597585 3559460676933825950698189)
                ·
                  refine ⟨1334797753850184731511821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3559460676933825950698189 1334797753850184731511821)
                  ·
                    refine ⟨500549157693819274316933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1334797753850184731511821 500549157693819274316933)
                    ·
                      refine ⟨93852967067591113934425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500549157693819274316933 93852967067591113934425)
                      ·
                        rfl

theorem cell23_182778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_182778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182778 prefixEnd_182778 := by exact prefixLift 182778
  have htrace : WordTrace (prefixWord ++ tailWord_182778) baseStart_182778 baseEnd_182778 := by
    simpa [prefixWord, tailWord_182778, baseEnd_182778] using wordTrace_append hprefix tailTrace_182778
  have hstable : (prefixWord ++ tailWord_182778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182778).length < 2 ^ (prefixWord ++ tailWord_182778).sum := by decide
  have hdescent : baseEnd_182778 < baseStart_182778 := by decide
  rcases family_descends (prefixWord ++ tailWord_182778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182785 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_182785 : Nat := 118140960795 + 182785 * 2 ^ 59
def prefixEnd_182785 : Nat := 4983230072969 + 3 ^ 40 * 182785 * 2
def baseEnd_182785 : Nat := 93856561432172586546893

theorem tailTrace_182785 : CollatzResearch.WordTrace tailWord_182785 prefixEnd_182785 93856561432172586546893 := by
  unfold tailWord_182785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6666716642808637037781809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4444477761872424691854539 6666716642808637037781809)
  ·
    refine ⟨5000037482106477778336357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6666716642808637037781809 5000037482106477778336357)
    ·
      refine ⟨937507027894964583438067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5000037482106477778336357 937507027894964583438067)
      ·
        refine ⟨1406260541842446875157101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937507027894964583438067 1406260541842446875157101)
        ·
          refine ⟨527347703190917578183913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1406260541842446875157101 527347703190917578183913)
          ·
            refine ⟨395510777393188183637935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527347703190917578183913 395510777393188183637935)
            ·
              refine ⟨593266166089782275456903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395510777393188183637935 593266166089782275456903)
              ·
                refine ⟨889899249134673413185355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593266166089782275456903 889899249134673413185355)
                ·
                  refine ⟨1334848873702010119778033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889899249134673413185355 1334848873702010119778033)
                  ·
                    refine ⟨1001136655276507589833525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1334848873702010119778033 1001136655276507589833525)
                    ·
                      refine ⟨93856561432172586546893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1001136655276507589833525 93856561432172586546893)
                      ·
                        rfl

theorem cell23_182785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_182785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182785 prefixEnd_182785 := by exact prefixLift 182785
  have htrace : WordTrace (prefixWord ++ tailWord_182785) baseStart_182785 baseEnd_182785 := by
    simpa [prefixWord, tailWord_182785, baseEnd_182785] using wordTrace_append hprefix tailTrace_182785
  have hstable : (prefixWord ++ tailWord_182785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182785).length < 2 ^ (prefixWord ++ tailWord_182785).sum := by decide
  have hdescent : baseEnd_182785 < baseStart_182785 := by decide
  rcases family_descends (prefixWord ++ tailWord_182785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182790 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_182790 : Nat := 118140960795 + 182790 * 2 ^ 59
def prefixEnd_182790 : Nat := 4983230072969 + 3 ^ 40 * 182790 * 2
def baseEnd_182790 : Nat := 93859128835445066984371

theorem tailTrace_182790 : CollatzResearch.WordTrace tailWord_182790 prefixEnd_182790 93859128835445066984371 := by
  unfold tailWord_182790
  simp only [CollatzResearch.WordTrace]
  refine ⟨208340593993453840366057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4444599338527015261142549 208340593993453840366057)
  ·
    refine ⟨156255445495090380274543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208340593993453840366057 156255445495090380274543)
    ·
      refine ⟨234383168242635570411815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156255445495090380274543 234383168242635570411815)
      ·
        refine ⟨351574752363953355617723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234383168242635570411815 351574752363953355617723)
        ·
          refine ⟨527362128545930033426585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351574752363953355617723 527362128545930033426585)
          ·
            refine ⟨395521596409447525069939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527362128545930033426585 395521596409447525069939)
            ·
              refine ⟨593282394614171287604909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395521596409447525069939 593282394614171287604909)
              ·
                refine ⟨222480897980314232851841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 593282394614171287604909 222480897980314232851841)
                ·
                  refine ⟨166860673485235674638881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222480897980314232851841 166860673485235674638881)
                  ·
                    refine ⟨125145505113926755979161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166860673485235674638881 125145505113926755979161)
                    ·
                      refine ⟨93859128835445066984371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125145505113926755979161 93859128835445066984371)
                      ·
                        rfl

theorem cell23_182790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_182790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182790 prefixEnd_182790 := by exact prefixLift 182790
  have htrace : WordTrace (prefixWord ++ tailWord_182790) baseStart_182790 baseEnd_182790 := by
    simpa [prefixWord, tailWord_182790, baseEnd_182790] using wordTrace_append hprefix tailTrace_182790
  have hstable : (prefixWord ++ tailWord_182790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182790).length < 2 ^ (prefixWord ++ tailWord_182790).sum := by decide
  have hdescent : baseEnd_182790 < baseStart_182790 := by decide
  rcases family_descends (prefixWord ++ tailWord_182790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182805 : List Nat := [1, 3, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_182805 : Nat := 118140960795 + 182805 * 2 ^ 59
def prefixEnd_182805 : Nat := 4983230072969 + 3 ^ 40 * 182805 * 2
def baseEnd_182805 : Nat := 31288943681754169432267

theorem tailTrace_182805 : CollatzResearch.WordTrace tailWord_182805 prefixEnd_182805 31288943681754169432267 := by
  unfold tailWord_182805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667446102736180453509869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4444964068490786969006579 6667446102736180453509869)
  ·
    refine ⟨2500292288526067670066201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6667446102736180453509869 2500292288526067670066201)
    ·
      refine ⟨1875219216394550752549651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2500292288526067670066201 1875219216394550752549651)
      ·
        refine ⟨2812828824591826128824477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875219216394550752549651 2812828824591826128824477)
        ·
          refine ⟨1054810809221934798309179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2812828824591826128824477 1054810809221934798309179)
          ·
            refine ⟨1582216213832902197463769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054810809221934798309179 1582216213832902197463769)
            ·
              refine ⟨1186662160374676648097827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582216213832902197463769 1186662160374676648097827)
              ·
                refine ⟨1779993240562014972146741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186662160374676648097827 1779993240562014972146741)
                ·
                  refine ⟨166874366302688903638757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1779993240562014972146741 166874366302688903638757)
                  ·
                    refine ⟨31288943681754169432267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 166874366302688903638757 31288943681754169432267)
                    ·
                      rfl

theorem cell23_182805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_182805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182805 prefixEnd_182805 := by exact prefixLift 182805
  have htrace : WordTrace (prefixWord ++ tailWord_182805) baseStart_182805 baseEnd_182805 := by
    simpa [prefixWord, tailWord_182805, baseEnd_182805] using wordTrace_append hprefix tailTrace_182805
  have hstable : (prefixWord ++ tailWord_182805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182805).length < 2 ^ (prefixWord ++ tailWord_182805).sum := by decide
  have hdescent : baseEnd_182805 < baseStart_182805 := by decide
  rcases family_descends (prefixWord ++ tailWord_182805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182812 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_182812 : Nat := 118140960795 + 182812 * 2 ^ 59
def prefixEnd_182812 : Nat := 4983230072969 + 3 ^ 40 * 182812 * 2
def baseEnd_182812 : Nat := 93870425409843980909269

theorem tailTrace_182812 : CollatzResearch.WordTrace tailWord_182812 prefixEnd_182812 93870425409843980909269 := by
  unfold tailWord_182812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333850706855410324507345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4445134275807213766009793 3333850706855410324507345)
  ·
    refine ⟨2500388030141557743380509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3333850706855410324507345 2500388030141557743380509)
    ·
      refine ⟨937645511303084153767691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2500388030141557743380509 937645511303084153767691)
      ·
        refine ⟨1406468266954626230651537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937645511303084153767691 1406468266954626230651537)
        ·
          refine ⟨1054851200215969672988653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1406468266954626230651537 1054851200215969672988653)
          ·
            refine ⟨395569200080988627370745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1054851200215969672988653 395569200080988627370745)
            ·
              refine ⟨296676900060741470528059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395569200080988627370745 296676900060741470528059)
              ·
                refine ⟨445015350091112205792089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296676900060741470528059 445015350091112205792089)
                ·
                  refine ⟨333761512568334154344067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 445015350091112205792089 333761512568334154344067)
                  ·
                    refine ⟨500642268852501231516101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 333761512568334154344067 500642268852501231516101)
                    ·
                      refine ⟨93870425409843980909269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 500642268852501231516101 93870425409843980909269)
                      ·
                        rfl

theorem cell23_182812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_182812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182812 prefixEnd_182812 := by exact prefixLift 182812
  have htrace : WordTrace (prefixWord ++ tailWord_182812) baseStart_182812 baseEnd_182812 := by
    simpa [prefixWord, tailWord_182812, baseEnd_182812] using wordTrace_append hprefix tailTrace_182812
  have hstable : (prefixWord ++ tailWord_182812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182812).length < 2 ^ (prefixWord ++ tailWord_182812).sum := by decide
  have hdescent : baseEnd_182812 < baseStart_182812 := by decide
  rcases family_descends (prefixWord ++ tailWord_182812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182835 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 6]
def baseStart_182835 : Nat := 118140960795 + 182835 * 2 ^ 59
def prefixEnd_182835 : Nat := 4983230072969 + 3 ^ 40 * 182835 * 2
def baseEnd_182835 : Nat := 10431359496099710102407

theorem tailTrace_182835 : CollatzResearch.WordTrace tailWord_182835 prefixEnd_182835 10431359496099710102407 := by
  unfold tailWord_182835
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668540292627495577101959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4445693528418330384734639 6668540292627495577101959)
  ·
    refine ⟨10002810438941243365652939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6668540292627495577101959 10002810438941243365652939)
    ·
      refine ⟨15004215658411865048479409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10002810438941243365652939 15004215658411865048479409)
      ·
        refine ⟨11253161743808898786359557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15004215658411865048479409 11253161743808898786359557)
        ·
          refine ⟨2109967826964168522442417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11253161743808898786359557 2109967826964168522442417)
          ·
            refine ⟨1582475870223126391831813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2109967826964168522442417 1582475870223126391831813)
            ·
              refine ⟨296714225666836198468465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1582475870223126391831813 296714225666836198468465)
              ·
                refine ⟨222535669250127148851349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296714225666836198468465 222535669250127148851349)
                ·
                  refine ⟨10431359496099710102407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222535669250127148851349 10431359496099710102407)
                  ·
                    rfl

theorem cell23_182835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 6].length) (baseStart_182835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182835 prefixEnd_182835 := by exact prefixLift 182835
  have htrace : WordTrace (prefixWord ++ tailWord_182835) baseStart_182835 baseEnd_182835 := by
    simpa [prefixWord, tailWord_182835, baseEnd_182835] using wordTrace_append hprefix tailTrace_182835
  have hstable : (prefixWord ++ tailWord_182835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182835).length < 2 ^ (prefixWord ++ tailWord_182835).sum := by decide
  have hdescent : baseEnd_182835 < baseStart_182835 := by decide
  rcases family_descends (prefixWord ++ tailWord_182835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182846 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_182846 : Nat := 118140960795 + 182846 * 2 ^ 59
def prefixEnd_182846 : Nat := 4983230072969 + 3 ^ 40 * 182846 * 2
def baseEnd_182846 : Nat := 93887883752096847884113

theorem tailTrace_182846 : CollatzResearch.WordTrace tailWord_182846 prefixEnd_182846 93887883752096847884113 := by
  unfold tailWord_182846
  simp only [CollatzResearch.WordTrace]
  refine ⟨833617686948455556969049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4445960997058429637168261 833617686948455556969049)
  ·
    refine ⟨625213265211341667726787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 833617686948455556969049 625213265211341667726787)
    ·
      refine ⟨937819897817012501590181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625213265211341667726787 937819897817012501590181)
      ·
        refine ⟨175841230840689844048159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 937819897817012501590181 175841230840689844048159)
        ·
          refine ⟨263761846261034766072239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175841230840689844048159 263761846261034766072239)
          ·
            refine ⟨395642769391552149108359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263761846261034766072239 395642769391552149108359)
            ·
              refine ⟨593464154087328223662539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395642769391552149108359 593464154087328223662539)
              ·
                refine ⟨890196231130992335493809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593464154087328223662539 890196231130992335493809)
                ·
                  refine ⟨667647173348244251620357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890196231130992335493809 667647173348244251620357)
                  ·
                    refine ⟨125183845002795797178817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667647173348244251620357 125183845002795797178817)
                    ·
                      refine ⟨93887883752096847884113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125183845002795797178817 93887883752096847884113)
                      ·
                        rfl

theorem cell23_182846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_182846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182846 prefixEnd_182846 := by exact prefixLift 182846
  have htrace : WordTrace (prefixWord ++ tailWord_182846) baseStart_182846 baseEnd_182846 := by
    simpa [prefixWord, tailWord_182846, baseEnd_182846] using wordTrace_append hprefix tailTrace_182846
  have hstable : (prefixWord ++ tailWord_182846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182846).length < 2 ^ (prefixWord ++ tailWord_182846).sum := by decide
  have hdescent : baseEnd_182846 < baseStart_182846 := by decide
  rcases family_descends (prefixWord ++ tailWord_182846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182862 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3]
def baseStart_182862 : Nat := 118140960795 + 182862 * 2 ^ 59
def prefixEnd_182862 : Nat := 4983230072969 + 3 ^ 40 * 182862 * 2
def baseEnd_182862 : Nat := 93896099442568785284039

theorem tailTrace_182862 : CollatzResearch.WordTrace tailWord_182862 prefixEnd_182862 93896099442568785284039 := by
  unfold tailWord_182862
  simp only [CollatzResearch.WordTrace]
  refine ⟨833690632941209898541855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4446350042353119458889893 833690632941209898541855)
  ·
    refine ⟨1250535949411814847812783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 833690632941209898541855 1250535949411814847812783)
    ·
      refine ⟨1875803924117722271719175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250535949411814847812783 1875803924117722271719175)
      ·
        refine ⟨2813705886176583407578763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875803924117722271719175 2813705886176583407578763)
        ·
          refine ⟨4220558829264875111368145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813705886176583407578763 4220558829264875111368145)
          ·
            refine ⟨3165419121948656333526109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4220558829264875111368145 3165419121948656333526109)
            ·
              refine ⟨1187032170730746125072291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3165419121948656333526109 1187032170730746125072291)
              ·
                refine ⟨1780548256096119187608437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187032170730746125072291 1780548256096119187608437)
                ·
                  refine ⟨166926399009011173838291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1780548256096119187608437 166926399009011173838291)
                  ·
                    refine ⟨250389598513516760757437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166926399009011173838291 250389598513516760757437)
                    ·
                      refine ⟨93896099442568785284039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250389598513516760757437 93896099442568785284039)
                      ·
                        rfl

theorem cell23_182862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3].length) (baseStart_182862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182862 prefixEnd_182862 := by exact prefixLift 182862
  have htrace : WordTrace (prefixWord ++ tailWord_182862) baseStart_182862 baseEnd_182862 := by
    simpa [prefixWord, tailWord_182862, baseEnd_182862] using wordTrace_append hprefix tailTrace_182862
  have hstable : (prefixWord ++ tailWord_182862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182862).length < 2 ^ (prefixWord ++ tailWord_182862).sum := by decide
  have hdescent : baseEnd_182862 < baseStart_182862 := by decide
  rcases family_descends (prefixWord ++ tailWord_182862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182865 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_182865 : Nat := 118140960795 + 182865 * 2 ^ 59
def prefixEnd_182865 : Nat := 4983230072969 + 3 ^ 40 * 182865 * 2
def baseEnd_182865 : Nat := 31299213294844091182175

theorem tailTrace_182865 : CollatzResearch.WordTrace tailWord_182865 prefixEnd_182865 31299213294844091182175 := by
  unfold tailWord_182865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6669634482518810700694049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4446422988345873800462699 6669634482518810700694049)
  ·
    refine ⟨5002225861889108025520537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6669634482518810700694049 5002225861889108025520537)
    ·
      refine ⟨3751669396416831019140403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5002225861889108025520537 3751669396416831019140403)
      ·
        refine ⟨5627504094625246528710605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751669396416831019140403 5627504094625246528710605)
        ·
          refine ⟨2110314035484467448266477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5627504094625246528710605 2110314035484467448266477)
          ·
            refine ⟨791367763306675293099929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2110314035484467448266477 791367763306675293099929)
            ·
              refine ⟨593525822480006469824947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 791367763306675293099929 593525822480006469824947)
              ·
                refine ⟨890288733720009704737421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593525822480006469824947 890288733720009704737421)
                ·
                  refine ⟨333858275145003639276533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 890288733720009704737421 333858275145003639276533)
                  ·
                    refine ⟨31299213294844091182175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 333858275145003639276533 31299213294844091182175)
                    ·
                      rfl

theorem cell23_182865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_182865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182865 prefixEnd_182865 := by exact prefixLift 182865
  have htrace : WordTrace (prefixWord ++ tailWord_182865) baseStart_182865 baseEnd_182865 := by
    simpa [prefixWord, tailWord_182865, baseEnd_182865] using wordTrace_append hprefix tailTrace_182865
  have hstable : (prefixWord ++ tailWord_182865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182865).length < 2 ^ (prefixWord ++ tailWord_182865).sum := by decide
  have hdescent : baseEnd_182865 < baseStart_182865 := by decide
  rcases family_descends (prefixWord ++ tailWord_182865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182905 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_182905 : Nat := 118140960795 + 182905 * 2 ^ 59
def prefixEnd_182905 : Nat := 4983230072969 + 3 ^ 40 * 182905 * 2
def baseEnd_182905 : Nat := 93918179110712117046341

theorem tailTrace_182905 : CollatzResearch.WordTrace tailWord_182905 prefixEnd_182905 93918179110712117046341 := by
  unfold tailWord_182905
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671093402373897532150169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4447395601582598354766779 6671093402373897532150169)
  ·
    refine ⟨5003320051780423149112627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6671093402373897532150169 5003320051780423149112627)
    ·
      refine ⟨7504980077670634723668941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003320051780423149112627 7504980077670634723668941)
      ·
        refine ⟨2814367529126488021375853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7504980077670634723668941 2814367529126488021375853)
        ·
          refine ⟨1055387823422433008015945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2814367529126488021375853 1055387823422433008015945)
          ·
            refine ⟨791540867566824756011959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1055387823422433008015945 791540867566824756011959)
            ·
              refine ⟨1187311301350237134017939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791540867566824756011959 1187311301350237134017939)
              ·
                refine ⟨1780966952025355701026909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1187311301350237134017939 1780966952025355701026909)
                ·
                  refine ⟨667862607009508387885091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1780966952025355701026909 667862607009508387885091)
                  ·
                    refine ⟨1001793910514262581827637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 667862607009508387885091 1001793910514262581827637)
                    ·
                      refine ⟨93918179110712117046341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1001793910514262581827637 93918179110712117046341)
                      ·
                        rfl

theorem cell23_182905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_182905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182905 prefixEnd_182905 := by exact prefixLift 182905
  have htrace : WordTrace (prefixWord ++ tailWord_182905) baseStart_182905 baseEnd_182905 := by
    simpa [prefixWord, tailWord_182905, baseEnd_182905] using wordTrace_append hprefix tailTrace_182905
  have hstable : (prefixWord ++ tailWord_182905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182905).length < 2 ^ (prefixWord ++ tailWord_182905).sum := by decide
  have hdescent : baseEnd_182905 < baseStart_182905 := by decide
  rcases family_descends (prefixWord ++ tailWord_182905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182912 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 1, 6]
def baseStart_182912 : Nat := 118140960795 + 182912 * 2 ^ 59
def prefixEnd_182912 : Nat := 4983230072969 + 3 ^ 40 * 182912 * 2
def baseEnd_182912 : Nat := 31307257825097863219603

theorem tailTrace_182912 : CollatzResearch.WordTrace tailWord_182912 prefixEnd_182912 31307257825097863219603 := by
  unfold tailWord_182912
  simp only [CollatzResearch.WordTrace]
  refine ⟨3335674356674268863827495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4447565808899025151769993 3335674356674268863827495)
  ·
    refine ⟨5003511535011403295741243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3335674356674268863827495 5003511535011403295741243)
    ·
      refine ⟨7505267302517104943611865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5003511535011403295741243 7505267302517104943611865)
      ·
        refine ⟨5628950476887828707708899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7505267302517104943611865 5628950476887828707708899)
        ·
          refine ⟨8443425715331743061563349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5628950476887828707708899 8443425715331743061563349)
          ·
            refine ⟨197892790203087728005391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8443425715331743061563349 197892790203087728005391)
            ·
              refine ⟨296839185304631592008087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197892790203087728005391 296839185304631592008087)
              ·
                refine ⟨445258777956947388012131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296839185304631592008087 445258777956947388012131)
                ·
                  refine ⟨667888166935421082018197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445258777956947388012131 667888166935421082018197)
                  ·
                    refine ⟨31307257825097863219603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 667888166935421082018197 31307257825097863219603)
                    ·
                      rfl

theorem cell23_182912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 1, 6].length) (baseStart_182912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182912 prefixEnd_182912 := by exact prefixLift 182912
  have htrace : WordTrace (prefixWord ++ tailWord_182912) baseStart_182912 baseEnd_182912 := by
    simpa [prefixWord, tailWord_182912, baseEnd_182912] using wordTrace_append hprefix tailTrace_182912
  have hstable : (prefixWord ++ tailWord_182912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182912).length < 2 ^ (prefixWord ++ tailWord_182912).sum := by decide
  have hdescent : baseEnd_182912 < baseStart_182912 := by decide
  rcases family_descends (prefixWord ++ tailWord_182912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182919 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_182919 : Nat := 118140960795 + 182919 * 2 ^ 59
def prefixEnd_182919 : Nat := 4983230072969 + 3 ^ 40 * 182919 * 2
def baseEnd_182919 : Nat := 93925367839875062271277

theorem tailTrace_182919 : CollatzResearch.WordTrace tailWord_182919 prefixEnd_182919 93925367839875062271277 := by
  unfold tailWord_182919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6671604024323177923159811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4447736016215451948773207 6671604024323177923159811)
  ·
    refine ⟨10007406036484766884739717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6671604024323177923159811 10007406036484766884739717)
    ·
      refine ⟨1876388631840893790888697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10007406036484766884739717 1876388631840893790888697)
      ·
        refine ⟨1407291473880670343166523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1876388631840893790888697 1407291473880670343166523)
        ·
          refine ⟨2110937210821005514749785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407291473880670343166523 2110937210821005514749785)
          ·
            refine ⟨1583202908115754136062339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2110937210821005514749785 1583202908115754136062339)
            ·
              refine ⟨2374804362173631204093509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583202908115754136062339 2374804362173631204093509)
              ·
                refine ⟨445275817907555850767533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2374804362173631204093509 445275817907555850767533)
                ·
                  refine ⟨166978431715333444037825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 445275817907555850767533 166978431715333444037825)
                  ·
                    refine ⟨125233823786500083028369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166978431715333444037825 125233823786500083028369)
                    ·
                      refine ⟨93925367839875062271277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125233823786500083028369 93925367839875062271277)
                      ·
                        rfl

theorem cell23_182919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_182919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182919 prefixEnd_182919 := by exact prefixLift 182919
  have htrace : WordTrace (prefixWord ++ tailWord_182919) baseStart_182919 baseEnd_182919 := by
    simpa [prefixWord, tailWord_182919, baseEnd_182919] using wordTrace_append hprefix tailTrace_182919
  have hstable : (prefixWord ++ tailWord_182919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182919).length < 2 ^ (prefixWord ++ tailWord_182919).sum := by decide
  have hdescent : baseEnd_182919 < baseStart_182919 := by decide
  rcases family_descends (prefixWord ++ tailWord_182919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_182962 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2]
def baseStart_182962 : Nat := 118140960795 + 182962 * 2 ^ 59
def prefixEnd_182962 : Nat := 4983230072969 + 3 ^ 40 * 182962 * 2
def baseEnd_182962 : Nat := 93947447508018394033579

theorem tailTrace_182962 : CollatzResearch.WordTrace tailWord_182962 prefixEnd_182962 93947447508018394033579 := by
  unfold tailWord_182962
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668293090791849066743785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4448781575444930844650093 1668293090791849066743785)
  ·
    refine ⟨1251219818093886800057839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668293090791849066743785 1251219818093886800057839)
    ·
      refine ⟨1876829727140830200086759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251219818093886800057839 1876829727140830200086759)
      ·
        refine ⟨2815244590711245300130139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876829727140830200086759 2815244590711245300130139)
        ·
          refine ⟨4222866886066867950195209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815244590711245300130139 4222866886066867950195209)
          ·
            refine ⟨3167150164550150962646407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4222866886066867950195209 3167150164550150962646407)
            ·
              refine ⟨4750725246825226443969611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3167150164550150962646407 4750725246825226443969611)
              ·
                refine ⟨7126087870237839665954417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4750725246825226443969611 7126087870237839665954417)
                ·
                  refine ⟨5344565902678379749465813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7126087870237839665954417 5344565902678379749465813)
                  ·
                    refine ⟨125263263344024525378105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5344565902678379749465813 125263263344024525378105)
                    ·
                      refine ⟨93947447508018394033579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125263263344024525378105 93947447508018394033579)
                      ·
                        rfl

theorem cell23_182962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_182962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_182962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_182962 prefixEnd_182962 := by exact prefixLift 182962
  have htrace : WordTrace (prefixWord ++ tailWord_182962) baseStart_182962 baseEnd_182962 := by
    simpa [prefixWord, tailWord_182962, baseEnd_182962] using wordTrace_append hprefix tailTrace_182962
  have hstable : (prefixWord ++ tailWord_182962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_182962).length < 2 ^ (prefixWord ++ tailWord_182962).sum := by decide
  have hdescent : baseEnd_182962 < baseStart_182962 := by decide
  rcases family_descends (prefixWord ++ tailWord_182962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183012 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_183012 : Nat := 118140960795 + 183012 * 2 ^ 59
def prefixEnd_183012 : Nat := 4983230072969 + 3 ^ 40 * 183012 * 2
def baseEnd_183012 : Nat := 93973121540743198408349

theorem tailTrace_183012 : CollatzResearch.WordTrace tailWord_183012 prefixEnd_183012 93973121540743198408349 := by
  unfold tailWord_183012
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337498006493127403147645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4449997341990836537530193 3337498006493127403147645)
  ·
    refine ⟨1251561752434922776180367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3337498006493127403147645 1251561752434922776180367)
    ·
      refine ⟨1877342628652384164270551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251561752434922776180367 1877342628652384164270551)
      ·
        refine ⟨2816013942978576246405827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1877342628652384164270551 2816013942978576246405827)
        ·
          refine ⟨4224020914467864369608741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2816013942978576246405827 4224020914467864369608741)
          ·
            refine ⟨792003921462724569301639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4224020914467864369608741 792003921462724569301639)
            ·
              refine ⟨1188005882194086853952459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792003921462724569301639 1188005882194086853952459)
              ·
                refine ⟨1782008823291130280928689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188005882194086853952459 1782008823291130280928689)
                ·
                  refine ⟨1336506617468347710696517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1782008823291130280928689 1336506617468347710696517)
                  ·
                    refine ⟨250594990775315195755597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1336506617468347710696517 250594990775315195755597)
                    ·
                      refine ⟨93973121540743198408349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250594990775315195755597 93973121540743198408349)
                      ·
                        rfl

theorem cell23_183012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_183012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183012 prefixEnd_183012 := by exact prefixLift 183012
  have htrace : WordTrace (prefixWord ++ tailWord_183012) baseStart_183012 baseEnd_183012 := by
    simpa [prefixWord, tailWord_183012, baseEnd_183012] using wordTrace_append hprefix tailTrace_183012
  have hstable : (prefixWord ++ tailWord_183012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183012).length < 2 ^ (prefixWord ++ tailWord_183012).sum := by decide
  have hdescent : baseEnd_183012 < baseStart_183012 := by decide
  rcases family_descends (prefixWord ++ tailWord_183012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183022 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_183022 : Nat := 118140960795 + 183022 * 2 ^ 59
def prefixEnd_183022 : Nat := 4983230072969 + 3 ^ 40 * 183022 * 2
def baseEnd_183022 : Nat := 93978256347288159283303

theorem tailTrace_183022 : CollatzResearch.WordTrace tailWord_183022 prefixEnd_183022 93978256347288159283303 := by
  unfold tailWord_183022
  simp only [CollatzResearch.WordTrace]
  refine ⟨834420092868753314269915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4450240495300017676106213 834420092868753314269915)
  ·
    refine ⟨1251630139303129971404873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 834420092868753314269915 1251630139303129971404873)
    ·
      refine ⟨938722604477347478553655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1251630139303129971404873 938722604477347478553655)
      ·
        refine ⟨1408083906716021217830483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938722604477347478553655 1408083906716021217830483)
        ·
          refine ⟨2112125860074031826745725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408083906716021217830483 2112125860074031826745725)
          ·
            refine ⟨792047197527761935029647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2112125860074031826745725 792047197527761935029647)
            ·
              refine ⟨1188070796291642902544471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792047197527761935029647 1188070796291642902544471)
              ·
                refine ⟨1782106194437464353816707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1188070796291642902544471 1782106194437464353816707)
                ·
                  refine ⟨2673159291656196530725061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1782106194437464353816707 2673159291656196530725061)
                  ·
                    refine ⟨501217367185536849510949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2673159291656196530725061 501217367185536849510949)
                    ·
                      refine ⟨93978256347288159283303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 501217367185536849510949 93978256347288159283303)
                      ·
                        rfl

theorem cell23_183022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_183022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183022 prefixEnd_183022 := by exact prefixLift 183022
  have htrace : WordTrace (prefixWord ++ tailWord_183022) baseStart_183022 baseEnd_183022 := by
    simpa [prefixWord, tailWord_183022, baseEnd_183022] using wordTrace_append hprefix tailTrace_183022
  have hstable : (prefixWord ++ tailWord_183022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183022).length < 2 ^ (prefixWord ++ tailWord_183022).sum := by decide
  have hdescent : baseEnd_183022 < baseStart_183022 := by decide
  rcases family_descends (prefixWord ++ tailWord_183022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183026 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 1, 4, 2]
def baseStart_183026 : Nat := 118140960795 + 183026 * 2 ^ 59
def prefixEnd_183026 : Nat := 4983230072969 + 3 ^ 40 * 183026 * 2
def baseEnd_183026 : Nat := 93980310269906143633285

theorem tailTrace_183026 : CollatzResearch.WordTrace tailWord_183026 prefixEnd_183026 93980310269906143633285 := by
  unfold tailWord_183026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1668876658733883799326233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4450337756623690131536621 1668876658733883799326233)
  ·
    refine ⟨1251657494050412849494675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1668876658733883799326233 1251657494050412849494675)
    ·
      refine ⟨1877486241075619274242013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1251657494050412849494675 1877486241075619274242013)
      ·
        refine ⟨704057340403357227840755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1877486241075619274242013 704057340403357227840755)
        ·
          refine ⟨1056086010605035841761133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704057340403357227840755 1056086010605035841761133)
          ·
            refine ⟨396032253976888440660425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1056086010605035841761133 396032253976888440660425)
            ·
              refine ⟨297024190482666330495319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396032253976888440660425 297024190482666330495319)
              ·
                refine ⟨445536285723999495742979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297024190482666330495319 445536285723999495742979)
                ·
                  refine ⟨668304428585999243614469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445536285723999495742979 668304428585999243614469)
                  ·
                    refine ⟨125307080359874858177713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 668304428585999243614469 125307080359874858177713)
                    ·
                      refine ⟨93980310269906143633285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125307080359874858177713 93980310269906143633285)
                      ·
                        rfl

theorem cell23_183026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_183026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183026 prefixEnd_183026 := by exact prefixLift 183026
  have htrace : WordTrace (prefixWord ++ tailWord_183026) baseStart_183026 baseEnd_183026 := by
    simpa [prefixWord, tailWord_183026, baseEnd_183026] using wordTrace_append hprefix tailTrace_183026
  have hstable : (prefixWord ++ tailWord_183026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183026).length < 2 ^ (prefixWord ++ tailWord_183026).sum := by decide
  have hdescent : baseEnd_183026 < baseStart_183026 := by decide
  rcases family_descends (prefixWord ++ tailWord_183026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183122 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_183122 : Nat := 118140960795 + 183122 * 2 ^ 59
def prefixEnd_183122 : Nat := 4983230072969 + 3 ^ 40 * 183122 * 2
def baseEnd_183122 : Nat := 10447733823637529781427

theorem tailTrace_183122 : CollatzResearch.WordTrace tailWord_183122 prefixEnd_183122 10447733823637529781427 := by
  unfold tailWord_183122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669752010646935898199905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4452672028391829061866413 1669752010646935898199905)
  ·
    refine ⟨1252314007985201923649929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1669752010646935898199905 1252314007985201923649929)
    ·
      refine ⟨939235505988901442737447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1252314007985201923649929 939235505988901442737447)
      ·
        refine ⟨1408853258983352164106171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 939235505988901442737447 1408853258983352164106171)
        ·
          refine ⟨2113279888475028246159257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1408853258983352164106171 2113279888475028246159257)
          ·
            refine ⟨1584959916356271184619443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2113279888475028246159257 1584959916356271184619443)
            ·
              refine ⟨2377439874534406776929165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584959916356271184619443 2377439874534406776929165)
              ·
                refine ⟨891539952950402541348437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2377439874534406776929165 891539952950402541348437)
                ·
                  refine ⟨10447733823637529781427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 891539952950402541348437 10447733823637529781427)
                  ·
                    rfl

theorem cell23_183122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_183122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183122 prefixEnd_183122 := by exact prefixLift 183122
  have htrace : WordTrace (prefixWord ++ tailWord_183122) baseStart_183122 baseEnd_183122 := by
    simpa [prefixWord, tailWord_183122, baseEnd_183122] using wordTrace_append hprefix tailTrace_183122
  have hstable : (prefixWord ++ tailWord_183122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183122).length < 2 ^ (prefixWord ++ tailWord_183122).sum := by decide
  have hdescent : baseEnd_183122 < baseStart_183122 := by decide
  rcases family_descends (prefixWord ++ tailWord_183122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183139 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 6]
def baseStart_183139 : Nat := 118140960795 + 183139 * 2 ^ 59
def prefixEnd_183139 : Nat := 4983230072969 + 3 ^ 40 * 183139 * 2
def baseEnd_183139 : Nat := 10448703731540466835585

theorem tailTrace_183139 : CollatzResearch.WordTrace tailWord_183139 prefixEnd_183139 10448703731540466835585 := by
  unfold tailWord_183139
  simp only [CollatzResearch.WordTrace]
  refine ⟨6679628083526155496168471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4453085389017436997445647 6679628083526155496168471)
  ·
    refine ⟨10019442125289233244252707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6679628083526155496168471 10019442125289233244252707)
    ·
      refine ⟨15029163187933849866379061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10019442125289233244252707 15029163187933849866379061)
      ·
        refine ⟨1408984048868798424973037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15029163187933849866379061 1408984048868798424973037)
        ·
          refine ⟨528369018325799409364889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408984048868798424973037 528369018325799409364889)
          ·
            refine ⟨396276763744349557023667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528369018325799409364889 396276763744349557023667)
            ·
              refine ⟨594415145616524335535501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396276763744349557023667 594415145616524335535501)
              ·
                refine ⟨222905679606196625825813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594415145616524335535501 222905679606196625825813)
                ·
                  refine ⟨10448703731540466835585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 222905679606196625825813 10448703731540466835585)
                  ·
                    rfl

theorem cell23_183139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 6].length) (baseStart_183139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183139 prefixEnd_183139 := by exact prefixLift 183139
  have htrace : WordTrace (prefixWord ++ tailWord_183139) baseStart_183139 baseEnd_183139 := by
    simpa [prefixWord, tailWord_183139, baseEnd_183139] using wordTrace_append hprefix tailTrace_183139
  have hstable : (prefixWord ++ tailWord_183139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183139).length < 2 ^ (prefixWord ++ tailWord_183139).sum := by decide
  have hdescent : baseEnd_183139 < baseStart_183139 := by decide
  rcases family_descends (prefixWord ++ tailWord_183139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183159 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 1, 5, 2]
def baseStart_183159 : Nat := 118140960795 + 183159 * 2 ^ 59
def prefixEnd_183159 : Nat := 4983230072969 + 3 ^ 40 * 183159 * 2
def baseEnd_183159 : Nat := 94048603196954123270173

theorem tailTrace_183159 : CollatzResearch.WordTrace tailWord_183159 prefixEnd_183159 94048603196954123270173 := by
  unfold tailWord_183159
  simp only [CollatzResearch.WordTrace]
  refine ⟨6680357543453698911896531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4453571695635799274597687 6680357543453698911896531)
  ·
    refine ⟨10020536315180548367844797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6680357543453698911896531 10020536315180548367844797)
    ·
      refine ⟨3757701118192705637941799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10020536315180548367844797 3757701118192705637941799)
      ·
        refine ⟨5636551677289058456912699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3757701118192705637941799 5636551677289058456912699)
        ·
          refine ⟨8454827515933587685369049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636551677289058456912699 8454827515933587685369049)
          ·
            refine ⟨6341120636950190764026787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454827515933587685369049 6341120636950190764026787)
            ·
              refine ⟨9511680955425286146040181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341120636950190764026787 9511680955425286146040181)
              ·
                refine ⟨891720089571120576191267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9511680955425286146040181 891720089571120576191267)
                ·
                  refine ⟨1337580134356680864286901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 891720089571120576191267 1337580134356680864286901)
                  ·
                    refine ⟨125398137595938831026897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1337580134356680864286901 125398137595938831026897)
                    ·
                      refine ⟨94048603196954123270173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125398137595938831026897 94048603196954123270173)
                      ·
                        rfl

theorem cell23_183159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 5, 2].length) (baseStart_183159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183159 prefixEnd_183159 := by exact prefixLift 183159
  have htrace : WordTrace (prefixWord ++ tailWord_183159) baseStart_183159 baseEnd_183159 := by
    simpa [prefixWord, tailWord_183159, baseEnd_183159] using wordTrace_append hprefix tailTrace_183159
  have hstable : (prefixWord ++ tailWord_183159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183159).length < 2 ^ (prefixWord ++ tailWord_183159).sum := by decide
  have hdescent : baseEnd_183159 < baseStart_183159 := by decide
  rcases family_descends (prefixWord ++ tailWord_183159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183189 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_183189 : Nat := 118140960795 + 183189 * 2 ^ 59
def prefixEnd_183189 : Nat := 4983230072969 + 3 ^ 40 * 183189 * 2
def baseEnd_183189 : Nat := 94064007616589005895035

theorem tailTrace_183189 : CollatzResearch.WordTrace tailWord_183189 prefixEnd_183189 94064007616589005895035 := by
  unfold tailWord_183189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681451733345014035488621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454301155563342690325747 6681451733345014035488621)
  ·
    refine ⟨2505544400004380263308233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6681451733345014035488621 2505544400004380263308233)
    ·
      refine ⟨1879158300003285197481175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2505544400004380263308233 1879158300003285197481175)
      ·
        refine ⟨2818737450004927796221763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879158300003285197481175 2818737450004927796221763)
        ·
          refine ⟨4228106175007391694332645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818737450004927796221763 4228106175007391694332645)
          ·
            refine ⟨792769907813885942687371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4228106175007391694332645 792769907813885942687371)
            ·
              refine ⟨1189154861720828914031057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792769907813885942687371 1189154861720828914031057)
              ·
                refine ⟨891866146290621685523293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189154861720828914031057 891866146290621685523293)
                ·
                  refine ⟨334449804858983132071235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891866146290621685523293 334449804858983132071235)
                  ·
                    refine ⟨501674707288474698106853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334449804858983132071235 501674707288474698106853)
                    ·
                      refine ⟨94064007616589005895035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 501674707288474698106853 94064007616589005895035)
                      ·
                        rfl

theorem cell23_183189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_183189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183189 prefixEnd_183189 := by exact prefixLift 183189
  have htrace : WordTrace (prefixWord ++ tailWord_183189) baseStart_183189 baseEnd_183189 := by
    simpa [prefixWord, tailWord_183189, baseEnd_183189] using wordTrace_append hprefix tailTrace_183189
  have hstable : (prefixWord ++ tailWord_183189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183189).length < 2 ^ (prefixWord ++ tailWord_183189).sum := by decide
  have hdescent : baseEnd_183189 < baseStart_183189 := by decide
  rcases family_descends (prefixWord ++ tailWord_183189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183199 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 1, 6]
def baseStart_183199 : Nat := 118140960795 + 183199 * 2 ^ 59
def prefixEnd_183199 : Nat := 4983230072969 + 3 ^ 40 * 183199 * 2
def baseEnd_183199 : Nat := 31356380807711322256663

theorem tailTrace_183199 : CollatzResearch.WordTrace tailWord_183199 prefixEnd_183199 31356380807711322256663 := by
  unfold tailWord_183199
  simp only [CollatzResearch.WordTrace]
  refine ⟨6681816463308785743352651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454544308872523828901767 6681816463308785743352651)
  ·
    refine ⟨10022724694963178615028977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6681816463308785743352651 10022724694963178615028977)
    ·
      refine ⟨7517043521222383961271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10022724694963178615028977 7517043521222383961271733)
      ·
        refine ⟨704722830114598496369225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7517043521222383961271733 704722830114598496369225)
        ·
          refine ⟨528542122585948872276919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704722830114598496369225 528542122585948872276919)
          ·
            refine ⟨792813183878923308415379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528542122585948872276919 792813183878923308415379)
            ·
              refine ⟨1189219775818384962623069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792813183878923308415379 1189219775818384962623069)
              ·
                refine ⟨445957415931894360983651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1189219775818384962623069 445957415931894360983651)
                ·
                  refine ⟨668936123897841541475477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 445957415931894360983651 668936123897841541475477)
                  ·
                    refine ⟨31356380807711322256663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 668936123897841541475477 31356380807711322256663)
                    ·
                      rfl

theorem cell23_183199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 6].length) (baseStart_183199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183199 prefixEnd_183199 := by exact prefixLift 183199
  have htrace : WordTrace (prefixWord ++ tailWord_183199) baseStart_183199 baseEnd_183199 := by
    simpa [prefixWord, tailWord_183199, baseEnd_183199] using wordTrace_append hprefix tailTrace_183199
  have hstable : (prefixWord ++ tailWord_183199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183199).length < 2 ^ (prefixWord ++ tailWord_183199).sum := by decide
  have hdescent : baseEnd_183199 < baseStart_183199 := by decide
  rcases family_descends (prefixWord ++ tailWord_183199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183209 : List Nat := [1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 3]
def baseStart_183209 : Nat := 118140960795 + 183209 * 2 ^ 59
def prefixEnd_183209 : Nat := 4983230072969 + 3 ^ 40 * 183209 * 2
def baseEnd_183209 : Nat := 94074277229678927644943

theorem tailTrace_183209 : CollatzResearch.WordTrace tailWord_183209 prefixEnd_183209 94074277229678927644943 := by
  unfold tailWord_183209
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682181193272557451216681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4454787462181704967477787 6682181193272557451216681)
  ·
    refine ⟨5011635894954418088412511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6682181193272557451216681 5011635894954418088412511)
    ·
      refine ⟨7517453842431627132618767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011635894954418088412511 7517453842431627132618767)
      ·
        refine ⟨11276180763647440698928151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7517453842431627132618767 11276180763647440698928151)
        ·
          refine ⟨16914271145471161048392227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11276180763647440698928151 16914271145471161048392227)
          ·
            refine ⟨25371406718206741572588341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16914271145471161048392227 25371406718206741572588341)
            ·
              refine ⟨2378569379831882022430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25371406718206741572588341 2378569379831882022430157)
              ·
                refine ⟨891963517436955758411309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2378569379831882022430157 891963517436955758411309)
                ·
                  refine ⟨334486319038858409404241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 891963517436955758411309 334486319038858409404241)
                  ·
                    refine ⟨250864739279143807053181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334486319038858409404241 250864739279143807053181)
                    ·
                      refine ⟨94074277229678927644943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250864739279143807053181 94074277229678927644943)
                      ·
                        rfl

theorem cell23_183209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_183209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183209 prefixEnd_183209 := by exact prefixLift 183209
  have htrace : WordTrace (prefixWord ++ tailWord_183209) baseStart_183209 baseEnd_183209 := by
    simpa [prefixWord, tailWord_183209, baseEnd_183209] using wordTrace_append hprefix tailTrace_183209
  have hstable : (prefixWord ++ tailWord_183209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183209).length < 2 ^ (prefixWord ++ tailWord_183209).sum := by decide
  have hdescent : baseEnd_183209 < baseStart_183209 := by decide
  rcases family_descends (prefixWord ++ tailWord_183209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183220 : List Nat := [2, 5, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_183220 : Nat := 118140960795 + 183220 * 2 ^ 59
def prefixEnd_183220 : Nat := 4983230072969 + 3 ^ 40 * 183220 * 2
def baseEnd_183220 : Nat := 31359975172292794869131

theorem tailTrace_183220 : CollatzResearch.WordTrace tailWord_183220 prefixEnd_183220 31359975172292794869131 := by
  unfold tailWord_183220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341291198116353164933557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4455054930821804219911409 3341291198116353164933557)
  ·
    refine ⟨313246049823408109212521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3341291198116353164933557 313246049823408109212521)
    ·
      refine ⟨234934537367556081909391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313246049823408109212521 234934537367556081909391)
      ·
        refine ⟨352401806051334122864087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234934537367556081909391 352401806051334122864087)
        ·
          refine ⟨528602709077001184296131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352401806051334122864087 528602709077001184296131)
          ·
            refine ⟨792904063615501776444197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528602709077001184296131 792904063615501776444197)
            ·
              refine ⟨148669511927906583083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 792904063615501776444197 148669511927906583083287)
              ·
                refine ⟨223004267891859874624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148669511927906583083287 223004267891859874624931)
                ·
                  refine ⟨334506401837789811937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223004267891859874624931 334506401837789811937397)
                  ·
                    refine ⟨31359975172292794869131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 334506401837789811937397 31359975172292794869131)
                    ·
                      rfl

theorem cell23_183220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_183220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183220 prefixEnd_183220 := by exact prefixLift 183220
  have htrace : WordTrace (prefixWord ++ tailWord_183220) baseStart_183220 baseEnd_183220 := by
    simpa [prefixWord, tailWord_183220, baseEnd_183220] using wordTrace_append hprefix tailTrace_183220
  have hstable : (prefixWord ++ tailWord_183220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183220).length < 2 ^ (prefixWord ++ tailWord_183220).sum := by decide
  have hdescent : baseEnd_183220 < baseStart_183220 := by decide
  rcases family_descends (prefixWord ++ tailWord_183220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183226 : List Nat := [3, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_183226 : Nat := 118140960795 + 183226 * 2 ^ 59
def prefixEnd_183226 : Nat := 4983230072969 + 3 ^ 40 * 183226 * 2
def baseEnd_183226 : Nat := 94083006400805361132365

theorem tailTrace_183226 : CollatzResearch.WordTrace tailWord_183226 prefixEnd_183226 94083006400805361132365 := by
  unfold tailWord_183226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670700308552742338646383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4455200822807312903057021 1670700308552742338646383)
  ·
    refine ⟨2506050462829113507969575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670700308552742338646383 2506050462829113507969575)
    ·
      refine ⟨3759075694243670261954363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506050462829113507969575 3759075694243670261954363)
      ·
        refine ⟨5638613541365505392931545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3759075694243670261954363 5638613541365505392931545)
        ·
          refine ⟨4228960156024129044698659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5638613541365505392931545 4228960156024129044698659)
          ·
            refine ⟨6343440234036193567047989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228960156024129044698659 6343440234036193567047989)
            ·
              refine ⟨594697521940893146910749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6343440234036193567047989 594697521940893146910749)
              ·
                refine ⟨223011570727834930091531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594697521940893146910749 223011570727834930091531)
                ·
                  refine ⟨334517356091752395137297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223011570727834930091531 334517356091752395137297)
                  ·
                    refine ⟨250888017068814296352973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 334517356091752395137297 250888017068814296352973)
                    ·
                      refine ⟨94083006400805361132365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250888017068814296352973 94083006400805361132365)
                      ·
                        rfl

theorem cell23_183226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_183226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183226 prefixEnd_183226 := by exact prefixLift 183226
  have htrace : WordTrace (prefixWord ++ tailWord_183226) baseStart_183226 baseEnd_183226 := by
    simpa [prefixWord, tailWord_183226, baseEnd_183226] using wordTrace_append hprefix tailTrace_183226
  have hstable : (prefixWord ++ tailWord_183226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183226).length < 2 ^ (prefixWord ++ tailWord_183226).sum := by decide
  have hdescent : baseEnd_183226 < baseStart_183226 := by decide
  rcases family_descends (prefixWord ++ tailWord_183226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183229 : List Nat := [1, 4, 1, 2, 4, 1, 10]
def baseStart_183229 : Nat := 118140960795 + 183229 * 2 ^ 59
def prefixEnd_183229 : Nat := 4983230072969 + 3 ^ 40 * 183229 * 2
def baseEnd_183229 : Nat := 1161537615342825301171

theorem tailTrace_183229 : CollatzResearch.WordTrace tailWord_183229 prefixEnd_183229 1161537615342825301171 := by
  unfold tailWord_183229
  simp only [CollatzResearch.WordTrace]
  refine ⟨6682910653200100866944741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4455273768800067244629827 6682910653200100866944741)
  ·
    refine ⟨1253045747475018912552139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6682910653200100866944741 1253045747475018912552139)
    ·
      refine ⟨1879568621212528368828209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253045747475018912552139 1879568621212528368828209)
      ·
        refine ⟨1409676465909396276621157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1879568621212528368828209 1409676465909396276621157)
        ·
          refine ⟨264314337358011801866467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1409676465909396276621157 264314337358011801866467)
          ·
            refine ⟨396471506037017702799701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264314337358011801866467 396471506037017702799701)
            ·
              refine ⟨1161537615342825301171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 396471506037017702799701 1161537615342825301171)
              ·
                rfl

theorem cell23_183229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 10].length) (baseStart_183229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183229 prefixEnd_183229 := by exact prefixLift 183229
  have htrace : WordTrace (prefixWord ++ tailWord_183229) baseStart_183229 baseEnd_183229 := by
    simpa [prefixWord, tailWord_183229, baseEnd_183229] using wordTrace_append hprefix tailTrace_183229
  have hstable : (prefixWord ++ tailWord_183229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183229).length < 2 ^ (prefixWord ++ tailWord_183229).sum := by decide
  have hdescent : baseEnd_183229 < baseStart_183229 := by decide
  rcases family_descends (prefixWord ++ tailWord_183229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183239 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_183239 : Nat := 118140960795 + 183239 * 2 ^ 59
def prefixEnd_183239 : Nat := 4983230072969 + 3 ^ 40 * 183239 * 2
def baseEnd_183239 : Nat := 94089681649313810269805

theorem tailTrace_183239 : CollatzResearch.WordTrace tailWord_183239 prefixEnd_183239 94089681649313810269805 := by
  unfold tailWord_183239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683275383163872574808771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4455516922109248383205847 6683275383163872574808771)
  ·
    refine ⟨10024913074745808862213157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6683275383163872574808771 10024913074745808862213157)
    ·
      refine ⟨1879671201514839161664967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10024913074745808862213157 1879671201514839161664967)
      ·
        refine ⟨2819506802272258742497451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879671201514839161664967 2819506802272258742497451)
        ·
          refine ⟨4229260203408388113746177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2819506802272258742497451 4229260203408388113746177)
          ·
            refine ⟨3171945152556291085309633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4229260203408388113746177 3171945152556291085309633)
            ·
              refine ⟨2378958864417218313982225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3171945152556291085309633 2378958864417218313982225)
              ·
                refine ⟨1784219148312913735486669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2378958864417218313982225 1784219148312913735486669)
                ·
                  refine ⟨669082180617342650807501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1784219148312913735486669 669082180617342650807501)
                  ·
                    refine ⟨250905817731503494052813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669082180617342650807501 250905817731503494052813)
                    ·
                      refine ⟨94089681649313810269805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250905817731503494052813 94089681649313810269805)
                      ·
                        rfl

theorem cell23_183239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_183239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183239 prefixEnd_183239 := by exact prefixLift 183239
  have htrace : WordTrace (prefixWord ++ tailWord_183239) baseStart_183239 baseEnd_183239 := by
    simpa [prefixWord, tailWord_183239, baseEnd_183239] using wordTrace_append hprefix tailTrace_183239
  have hstable : (prefixWord ++ tailWord_183239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183239).length < 2 ^ (prefixWord ++ tailWord_183239).sum := by decide
  have hdescent : baseEnd_183239 < baseStart_183239 := by decide
  rcases family_descends (prefixWord ++ tailWord_183239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183240 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2]
def baseStart_183240 : Nat := 118140960795 + 183240 * 2 ^ 59
def prefixEnd_183240 : Nat := 4983230072969 + 3 ^ 40 * 183240 * 2
def baseEnd_183240 : Nat := 94090195129968306357301

theorem tailTrace_183240 : CollatzResearch.WordTrace tailWord_183240 prefixEnd_183240 94090195129968306357301 := by
  unfold tailWord_183240
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341655928080124872797587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4455541237440166497063449 3341655928080124872797587)
  ·
    refine ⟨5012483892120187309196381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341655928080124872797587 5012483892120187309196381)
    ·
      refine ⟨1879681459545070240948643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5012483892120187309196381 1879681459545070240948643)
      ·
        refine ⟨2819522189317605361422965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1879681459545070240948643 2819522189317605361422965)
        ·
          refine ⟨264330205248525502633403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2819522189317605361422965 264330205248525502633403)
          ·
            refine ⟨396495307872788253950105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264330205248525502633403 396495307872788253950105)
            ·
              refine ⟨297371480904591190462579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396495307872788253950105 297371480904591190462579)
              ·
                refine ⟨446057221356886785693869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297371480904591190462579 446057221356886785693869)
                ·
                  refine ⟨167271458008832544635201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 446057221356886785693869 167271458008832544635201)
                  ·
                    refine ⟨125453593506624408476401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167271458008832544635201 125453593506624408476401)
                    ·
                      refine ⟨94090195129968306357301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125453593506624408476401 94090195129968306357301)
                      ·
                        rfl

theorem cell23_183240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_183240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183240 prefixEnd_183240 := by exact prefixLift 183240
  have htrace : WordTrace (prefixWord ++ tailWord_183240) baseStart_183240 baseEnd_183240 := by
    simpa [prefixWord, tailWord_183240, baseEnd_183240] using wordTrace_append hprefix tailTrace_183240
  have hstable : (prefixWord ++ tailWord_183240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183240).length < 2 ^ (prefixWord ++ tailWord_183240).sum := by decide
  have hdescent : baseEnd_183240 < baseStart_183240 := by decide
  rcases family_descends (prefixWord ++ tailWord_183240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183250 : List Nat := [3, 2, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_183250 : Nat := 118140960795 + 183250 * 2 ^ 59
def prefixEnd_183250 : Nat := 4983230072969 + 3 ^ 40 * 183250 * 2
def baseEnd_183250 : Nat := 31365109978837755744085

theorem tailTrace_183250 : CollatzResearch.WordTrace tailWord_183250 prefixEnd_183250 31365109978837755744085 := by
  unfold tailWord_183250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670919146531005363364801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4455784390749347635639469 1670919146531005363364801)
  ·
    refine ⟨1253189359898254022523601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1670919146531005363364801 1253189359898254022523601)
    ·
      refine ⟨939892019923690516892701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1253189359898254022523601 939892019923690516892701)
      ·
        refine ⟨352459507471383943834763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 939892019923690516892701 352459507471383943834763)
        ·
          refine ⟨528689261207075915752145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352459507471383943834763 528689261207075915752145)
          ·
            refine ⟨396516945905306936814109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528689261207075915752145 396516945905306936814109)
            ·
              refine ⟨148693854714490101305291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396516945905306936814109 148693854714490101305291)
              ·
                refine ⟨223040782071735151957937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148693854714490101305291 223040782071735151957937)
                ·
                  refine ⟨167280586553801363968453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223040782071735151957937 167280586553801363968453)
                  ·
                    refine ⟨31365109978837755744085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167280586553801363968453 31365109978837755744085)
                    ·
                      rfl

theorem cell23_183250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_183250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183250 prefixEnd_183250 := by exact prefixLift 183250
  have htrace : WordTrace (prefixWord ++ tailWord_183250) baseStart_183250 baseEnd_183250 := by
    simpa [prefixWord, tailWord_183250, baseEnd_183250] using wordTrace_append hprefix tailTrace_183250
  have hstable : (prefixWord ++ tailWord_183250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183250).length < 2 ^ (prefixWord ++ tailWord_183250).sum := by decide
  have hdescent : baseEnd_183250 < baseStart_183250 := by decide
  rcases family_descends (prefixWord ++ tailWord_183250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183253 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_183253 : Nat := 118140960795 + 183253 * 2 ^ 59
def prefixEnd_183253 : Nat := 4983230072969 + 3 ^ 40 * 183253 * 2
def baseEnd_183253 : Nat := 94096870378476755494741

theorem tailTrace_183253 : CollatzResearch.WordTrace tailWord_183253 prefixEnd_183253 94096870378476755494741 := by
  unfold tailWord_183253
  simp only [CollatzResearch.WordTrace]
  refine ⟨6683786005113152965818413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4455857336742101977212275 6683786005113152965818413)
  ·
    refine ⟨2506419751917432362181905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6683786005113152965818413 2506419751917432362181905)
    ·
      refine ⟨1879814813938074271636429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2506419751917432362181905 1879814813938074271636429)
      ·
        refine ⟨704930555226777851863661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1879814813938074271636429 704930555226777851863661)
        ·
          refine ⟨264348958210041694448873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704930555226777851863661 264348958210041694448873)
          ·
            refine ⟨198261718657531270836655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264348958210041694448873 198261718657531270836655)
            ·
              refine ⟨297392577986296906254983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198261718657531270836655 297392577986296906254983)
              ·
                refine ⟨446088866979445359382475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297392577986296906254983 446088866979445359382475)
                ·
                  refine ⟨669133300469168039073713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446088866979445359382475 669133300469168039073713)
                  ·
                    refine ⟨501849975351876029305285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 669133300469168039073713 501849975351876029305285)
                    ·
                      refine ⟨94096870378476755494741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 501849975351876029305285 94096870378476755494741)
                      ·
                        rfl

theorem cell23_183253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_183253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183253 prefixEnd_183253 := by exact prefixLift 183253
  have htrace : WordTrace (prefixWord ++ tailWord_183253) baseStart_183253 baseEnd_183253 := by
    simpa [prefixWord, tailWord_183253, baseEnd_183253] using wordTrace_append hprefix tailTrace_183253
  have hstable : (prefixWord ++ tailWord_183253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183253).length < 2 ^ (prefixWord ++ tailWord_183253).sum := by decide
  have hdescent : baseEnd_183253 < baseStart_183253 := by decide
  rcases family_descends (prefixWord ++ tailWord_183253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183256 : List Nat := [2, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_183256 : Nat := 118140960795 + 183256 * 2 ^ 59
def prefixEnd_183256 : Nat := 4983230072969 + 3 ^ 40 * 183256 * 2
def baseEnd_183256 : Nat := 94098410820440243757227

theorem tailTrace_183256 : CollatzResearch.WordTrace tailWord_183256 prefixEnd_183256 94098410820440243757227 := by
  unfold tailWord_183256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3341947712051142239088811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4455930282734856318785081 3341947712051142239088811)
  ·
    refine ⟨5012921568076713358633217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3341947712051142239088811 5012921568076713358633217)
    ·
      refine ⟨3759691176057535018974913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5012921568076713358633217 3759691176057535018974913)
      ·
        refine ⟨2819768382043151264231185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3759691176057535018974913 2819768382043151264231185)
        ·
          refine ⟨2114826286532363448173389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2819768382043151264231185 2114826286532363448173389)
          ·
            refine ⟨793059857449636293065021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2114826286532363448173389 793059857449636293065021)
            ·
              refine ⟨297397446543613609899383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 793059857449636293065021 297397446543613609899383)
              ·
                refine ⟨446096169815420414849075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297397446543613609899383 446096169815420414849075)
                ·
                  refine ⟨669144254723130622273613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446096169815420414849075 669144254723130622273613)
                  ·
                    refine ⟨250929095521173983352605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669144254723130622273613 250929095521173983352605)
                    ·
                      refine ⟨94098410820440243757227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 250929095521173983352605 94098410820440243757227)
                      ·
                        rfl

theorem cell23_183256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_183256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183256 prefixEnd_183256 := by exact prefixLift 183256
  have htrace : WordTrace (prefixWord ++ tailWord_183256) baseStart_183256 baseEnd_183256 := by
    simpa [prefixWord, tailWord_183256, baseEnd_183256] using wordTrace_append hprefix tailTrace_183256
  have hstable : (prefixWord ++ tailWord_183256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183256).length < 2 ^ (prefixWord ++ tailWord_183256).sum := by decide
  have hdescent : baseEnd_183256 < baseStart_183256 := by decide
  rcases family_descends (prefixWord ++ tailWord_183256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183263 : List Nat := [1, 1, 2, 3, 6, 1, 2, 7]
def baseStart_183263 : Nat := 118140960795 + 183263 * 2 ^ 59
def prefixEnd_183263 : Nat := 4983230072969 + 3 ^ 40 * 183263 * 2
def baseEnd_183263 : Nat := 3485259451297100606285

theorem tailTrace_183263 : CollatzResearch.WordTrace tailWord_183263 prefixEnd_183263 3485259451297100606285 := by
  unfold tailWord_183263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6684150735076924673682443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4456100490051283115788295 6684150735076924673682443)
  ·
    refine ⟨10026226102615387010523665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6684150735076924673682443 10026226102615387010523665)
    ·
      refine ⟨7519669576961540257892749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10026226102615387010523665 7519669576961540257892749)
      ·
        refine ⟨2819876091360577596709781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7519669576961540257892749 2819876091360577596709781)
        ·
          refine ⟨132181691782527074845771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2819876091360577596709781 132181691782527074845771)
          ·
            refine ⟨198272537673790612268657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132181691782527074845771 198272537673790612268657)
            ·
              refine ⟨148704403255342959201493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198272537673790612268657 148704403255342959201493)
              ·
                refine ⟨3485259451297100606285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148704403255342959201493 3485259451297100606285)
                ·
                  rfl

theorem cell23_183263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 7].length) (baseStart_183263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183263 prefixEnd_183263 := by exact prefixLift 183263
  have htrace : WordTrace (prefixWord ++ tailWord_183263) baseStart_183263 baseEnd_183263 := by
    simpa [prefixWord, tailWord_183263, baseEnd_183263] using wordTrace_append hprefix tailTrace_183263
  have hstable : (prefixWord ++ tailWord_183263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183263).length < 2 ^ (prefixWord ++ tailWord_183263).sum := by decide
  have hdescent : baseEnd_183263 < baseStart_183263 := by decide
  rcases family_descends (prefixWord ++ tailWord_183263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183346 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3]
def baseStart_183346 : Nat := 118140960795 + 183346 * 2 ^ 59
def prefixEnd_183346 : Nat := 4983230072969 + 3 ^ 40 * 183346 * 2
def baseEnd_183346 : Nat := 94144624079344891631813

theorem tailTrace_183346 : CollatzResearch.WordTrace tailWord_183346 prefixEnd_183346 94144624079344891631813 := by
  unfold tailWord_183346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671794498444057462238473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4458118662517486565969261 1671794498444057462238473)
  ·
    refine ⟨1253845873833043096678855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1671794498444057462238473 1253845873833043096678855)
    ·
      refine ⟨1880768810749564645018283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253845873833043096678855 1880768810749564645018283)
      ·
        refine ⟨2821153216124346967527425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1880768810749564645018283 2821153216124346967527425)
        ·
          refine ⟨2115864912093260225645569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821153216124346967527425 2115864912093260225645569)
          ·
            refine ⟨1586898684069945169234177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2115864912093260225645569 1586898684069945169234177)
            ·
              refine ⟨1190174013052458876925633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1586898684069945169234177 1190174013052458876925633)
              ·
                refine ⟨892630509789344157694225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190174013052458876925633 892630509789344157694225)
                ·
                  refine ⟨669472882342008118270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892630509789344157694225 669472882342008118270669)
                  ·
                    refine ⟨251052330878253044351501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 669472882342008118270669 251052330878253044351501)
                    ·
                      refine ⟨94144624079344891631813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 251052330878253044351501 94144624079344891631813)
                      ·
                        rfl

theorem cell23_183346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_183346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183346 prefixEnd_183346 := by exact prefixLift 183346
  have htrace : WordTrace (prefixWord ++ tailWord_183346) baseStart_183346 baseEnd_183346 := by
    simpa [prefixWord, tailWord_183346, baseEnd_183346] using wordTrace_append hprefix tailTrace_183346
  have hstable : (prefixWord ++ tailWord_183346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183346).length < 2 ^ (prefixWord ++ tailWord_183346).sum := by decide
  have hdescent : baseEnd_183346 < baseStart_183346 := by decide
  rcases family_descends (prefixWord ++ tailWord_183346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183349 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_183349 : Nat := 118140960795 + 183349 * 2 ^ 59
def prefixEnd_183349 : Nat := 4983230072969 + 3 ^ 40 * 183349 * 2
def baseEnd_183349 : Nat := 31382054840436126631433

theorem tailTrace_183349 : CollatzResearch.WordTrace tailWord_183349 prefixEnd_183349 31382054840436126631433 := by
  unfold tailWord_183349
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687287412765361361313101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4458191608510240907542067 6687287412765361361313101)
  ·
    refine ⟨2507732779787010510492413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6687287412765361361313101 2507732779787010510492413)
    ·
      refine ⟨940399792420128941434655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2507732779787010510492413 940399792420128941434655)
      ·
        refine ⟨1410599688630193412151983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940399792420128941434655 1410599688630193412151983)
        ·
          refine ⟨2115899532945290118227975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1410599688630193412151983 2115899532945290118227975)
          ·
            refine ⟨3173849299417935177341963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115899532945290118227975 3173849299417935177341963)
            ·
              refine ⟨4760773949126902766012945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3173849299417935177341963 4760773949126902766012945)
              ·
                refine ⟨3570580461845177074509709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4760773949126902766012945 3570580461845177074509709)
                ·
                  refine ⟨1338967673191941402941141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3570580461845177074509709 1338967673191941402941141)
                  ·
                    refine ⟨31382054840436126631433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1338967673191941402941141 31382054840436126631433)
                    ·
                      rfl

theorem cell23_183349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_183349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183349 prefixEnd_183349 := by exact prefixLift 183349
  have htrace : WordTrace (prefixWord ++ tailWord_183349) baseStart_183349 baseEnd_183349 := by
    simpa [prefixWord, tailWord_183349, baseEnd_183349] using wordTrace_append hprefix tailTrace_183349
  have hstable : (prefixWord ++ tailWord_183349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183349).length < 2 ^ (prefixWord ++ tailWord_183349).sum := by decide
  have hdescent : baseEnd_183349 < baseStart_183349 := by decide
  rcases family_descends (prefixWord ++ tailWord_183349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183353 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 5]
def baseStart_183353 : Nat := 118140960795 + 183353 * 2 ^ 59
def prefixEnd_183353 : Nat := 4983230072969 + 3 ^ 40 * 183353 * 2
def baseEnd_183353 : Nat := 10460913160436262693809

theorem tailTrace_183353 : CollatzResearch.WordTrace tailWord_183353 prefixEnd_183353 10460913160436262693809 := by
  unfold tailWord_183353
  simp only [CollatzResearch.WordTrace]
  refine ⟨6687433304750870044458713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4458288869833913362972475 6687433304750870044458713)
  ·
    refine ⟨5015574978563152533344035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6687433304750870044458713 5015574978563152533344035)
    ·
      refine ⟨7523362467844728800016053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5015574978563152533344035 7523362467844728800016053)
      ·
        refine ⟨705315231360443325001505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7523362467844728800016053 705315231360443325001505)
        ·
          refine ⟨528986423520332493751129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705315231360443325001505 528986423520332493751129)
          ·
            refine ⟨396739817640249370313347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528986423520332493751129 396739817640249370313347)
            ·
              refine ⟨595109726460374055470021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396739817640249370313347 595109726460374055470021)
              ·
                refine ⟨111583073711320135400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595109726460374055470021 111583073711320135400629)
                ·
                  refine ⟨10460913160436262693809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111583073711320135400629 10460913160436262693809)
                  ·
                    rfl

theorem cell23_183353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 5].length) (baseStart_183353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183353 prefixEnd_183353 := by exact prefixLift 183353
  have htrace : WordTrace (prefixWord ++ tailWord_183353) baseStart_183353 baseEnd_183353 := by
    simpa [prefixWord, tailWord_183353, baseEnd_183353] using wordTrace_append hprefix tailTrace_183353
  have hstable : (prefixWord ++ tailWord_183353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183353).length < 2 ^ (prefixWord ++ tailWord_183353).sum := by decide
  have hdescent : baseEnd_183353 < baseStart_183353 := by decide
  rcases family_descends (prefixWord ++ tailWord_183353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183386 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_183386 : Nat := 118140960795 + 183386 * 2 ^ 59
def prefixEnd_183386 : Nat := 4983230072969 + 3 ^ 40 * 183386 * 2
def baseEnd_183386 : Nat := 94165163305524735131629

theorem tailTrace_183386 : CollatzResearch.WordTrace tailWord_183386 prefixEnd_183386 94165163305524735131629 := by
  unfold tailWord_183386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1672159228407829170102503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4459091275754211120273341 1672159228407829170102503)
  ·
    refine ⟨2508238842611743755153755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1672159228407829170102503 2508238842611743755153755)
    ·
      refine ⟨3762358263917615632730633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508238842611743755153755 3762358263917615632730633)
      ·
        refine ⟨2821768697938211724547975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762358263917615632730633 2821768697938211724547975)
        ·
          refine ⟨4232653046907317586821963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2821768697938211724547975 4232653046907317586821963)
          ·
            refine ⟨6348979570360976380232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4232653046907317586821963 6348979570360976380232945)
            ·
              refine ⟨4761734677770732285174709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348979570360976380232945 4761734677770732285174709)
              ·
                refine ⟨446412626041006151735129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4761734677770732285174709 446412626041006151735129)
                ·
                  refine ⟨334809469530754613801347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 446412626041006151735129 334809469530754613801347)
                  ·
                    refine ⟨502214204296131920702021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 334809469530754613801347 502214204296131920702021)
                    ·
                      refine ⟨94165163305524735131629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 502214204296131920702021 94165163305524735131629)
                      ·
                        rfl

theorem cell23_183386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_183386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183386 prefixEnd_183386 := by exact prefixLift 183386
  have htrace : WordTrace (prefixWord ++ tailWord_183386) baseStart_183386 baseEnd_183386 := by
    simpa [prefixWord, tailWord_183386, baseEnd_183386] using wordTrace_append hprefix tailTrace_183386
  have hstable : (prefixWord ++ tailWord_183386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183386).length < 2 ^ (prefixWord ++ tailWord_183386).sum := by decide
  have hdescent : baseEnd_183386 < baseStart_183386 := by decide
  rcases family_descends (prefixWord ++ tailWord_183386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183396 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_183396 : Nat := 118140960795 + 183396 * 2 ^ 59
def prefixEnd_183396 : Nat := 4983230072969 + 3 ^ 40 * 183396 * 2
def baseEnd_183396 : Nat := 31390099370689898668861

theorem tailTrace_183396 : CollatzResearch.WordTrace tailWord_183396 prefixEnd_183396 31390099370689898668861 := by
  unfold tailWord_183396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344500821797544194137021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4459334429063392258849361 3344500821797544194137021)
  ·
    refine ⟨1254187808174079072801383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3344500821797544194137021 1254187808174079072801383)
    ·
      refine ⟨1881281712261118609202075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254187808174079072801383 1881281712261118609202075)
      ·
        refine ⟨2821922568391677913803113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881281712261118609202075 2821922568391677913803113)
        ·
          refine ⟨2116441926293758435352335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821922568391677913803113 2116441926293758435352335)
          ·
            refine ⟨3174662889440637653028503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116441926293758435352335 3174662889440637653028503)
            ·
              refine ⟨4761994334160956479542755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174662889440637653028503 4761994334160956479542755)
              ·
                refine ⟨7142991501241434719314133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761994334160956479542755 7142991501241434719314133)
                ·
                  refine ⟨167413863310346126233925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7142991501241434719314133 167413863310346126233925)
                  ·
                    refine ⟨31390099370689898668861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167413863310346126233925 31390099370689898668861)
                    ·
                      rfl

theorem cell23_183396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_183396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183396 prefixEnd_183396 := by exact prefixLift 183396
  have htrace : WordTrace (prefixWord ++ tailWord_183396) baseStart_183396 baseEnd_183396 := by
    simpa [prefixWord, tailWord_183396, baseEnd_183396] using wordTrace_append hprefix tailTrace_183396
  have hstable : (prefixWord ++ tailWord_183396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183396).length < 2 ^ (prefixWord ++ tailWord_183396).sum := by decide
  have hdescent : baseEnd_183396 < baseStart_183396 := by decide
  rcases family_descends (prefixWord ++ tailWord_183396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183447 : List Nat := [1, 1, 3, 3, 3, 3, 1, 3, 1, 4]
def baseStart_183447 : Nat := 118140960795 + 183447 * 2 ^ 59
def prefixEnd_183447 : Nat := 4983230072969 + 3 ^ 40 * 183447 * 2
def baseEnd_183447 : Nat := 31398828541816332156283

theorem tailTrace_183447 : CollatzResearch.WordTrace tailWord_183447 prefixEnd_183447 31398828541816332156283 := by
  unfold tailWord_183447
  simp only [CollatzResearch.WordTrace]
  refine ⟨6690861766410324098380595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4460574510940216065587063 6690861766410324098380595)
  ·
    refine ⟨10036292649615486147570893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6690861766410324098380595 10036292649615486147570893)
    ·
      refine ⟨3763609743605807305339085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10036292649615486147570893 3763609743605807305339085)
      ·
        refine ⟨1411353653852177739502157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3763609743605807305339085 1411353653852177739502157)
        ·
          refine ⟨529257620194566652313309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1411353653852177739502157 529257620194566652313309)
          ·
            refine ⟨198471607572962494617491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 529257620194566652313309 198471607572962494617491)
            ·
              refine ⟨297707411359443741926237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198471607572962494617491 297707411359443741926237)
              ·
                refine ⟨111640279259791403222339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297707411359443741926237 111640279259791403222339)
                ·
                  refine ⟨167460418889687104833509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111640279259791403222339 167460418889687104833509)
                  ·
                    refine ⟨31398828541816332156283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167460418889687104833509 31398828541816332156283)
                    ·
                      rfl

theorem cell23_183447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_183447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183447 prefixEnd_183447 := by exact prefixLift 183447
  have htrace : WordTrace (prefixWord ++ tailWord_183447) baseStart_183447 baseEnd_183447 := by
    simpa [prefixWord, tailWord_183447, baseEnd_183447] using wordTrace_append hprefix tailTrace_183447
  have hstable : (prefixWord ++ tailWord_183447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183447).length < 2 ^ (prefixWord ++ tailWord_183447).sum := by decide
  have hdescent : baseEnd_183447 < baseStart_183447 := by decide
  rcases family_descends (prefixWord ++ tailWord_183447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183496 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_183496 : Nat := 118140960795 + 183496 * 2 ^ 59
def prefixEnd_183496 : Nat := 4983230072969 + 3 ^ 40 * 183496 * 2
def baseEnd_183496 : Nat := 94221646177519304756123

theorem tailTrace_183496 : CollatzResearch.WordTrace tailWord_183496 prefixEnd_183496 94221646177519304756123 := by
  unfold tailWord_183496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346324471616402733457171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4461765962155203644609561 3346324471616402733457171)
  ·
    refine ⟨5019486707424604100185757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346324471616402733457171 5019486707424604100185757)
    ·
      refine ⟨1882307515284226537569659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5019486707424604100185757 1882307515284226537569659)
      ·
        refine ⟨2823461272926339806354489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882307515284226537569659 2823461272926339806354489)
        ·
          refine ⟨2117595954694754854765867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823461272926339806354489 2117595954694754854765867)
          ·
            refine ⟨3176393932042132282148801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117595954694754854765867 3176393932042132282148801)
            ·
              refine ⟨2382295449031599211611601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176393932042132282148801 2382295449031599211611601)
              ·
                refine ⟨1786721586773699408708701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382295449031599211611601 1786721586773699408708701)
                ·
                  refine ⟨670020595040137278265763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1786721586773699408708701 670020595040137278265763)
                  ·
                    refine ⟨1005030892560205917398645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 670020595040137278265763 1005030892560205917398645)
                    ·
                      refine ⟨94221646177519304756123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1005030892560205917398645 94221646177519304756123)
                      ·
                        rfl

theorem cell23_183496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_183496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183496 prefixEnd_183496 := by exact prefixLift 183496
  have htrace : WordTrace (prefixWord ++ tailWord_183496) baseStart_183496 baseEnd_183496 := by
    simpa [prefixWord, tailWord_183496, baseEnd_183496] using wordTrace_append hprefix tailTrace_183496
  have hstable : (prefixWord ++ tailWord_183496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183496).length < 2 ^ (prefixWord ++ tailWord_183496).sum := by decide
  have hdescent : baseEnd_183496 < baseStart_183496 := by decide
  rcases family_descends (prefixWord ++ tailWord_183496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183516 : List Nat := [2, 2, 5, 14]
def baseStart_183516 : Nat := 118140960795 + 183516 * 2 ^ 59
def prefixEnd_183516 : Nat := 4983230072969 + 3 ^ 40 * 183516 * 2
def baseEnd_183516 : Nat := 43087295743305544813

theorem tailTrace_183516 : CollatzResearch.WordTrace tailWord_183516 prefixEnd_183516 43087295743305544813 := by
  unfold tailWord_183516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346689201580174441321201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462252268773565921761601 3346689201580174441321201)
  ·
    refine ⟨2510016901185130830990901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3346689201580174441321201 2510016901185130830990901)
    ·
      refine ⟨235314084486106015405397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2510016901185130830990901 235314084486106015405397)
      ·
        refine ⟨43087295743305544813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 235314084486106015405397 43087295743305544813)
        ·
          rfl

theorem cell23_183516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 14].length) (baseStart_183516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183516 prefixEnd_183516 := by exact prefixLift 183516
  have htrace : WordTrace (prefixWord ++ tailWord_183516) baseStart_183516 baseEnd_183516 := by
    simpa [prefixWord, tailWord_183516, baseEnd_183516] using wordTrace_append hprefix tailTrace_183516
  have hstable : (prefixWord ++ tailWord_183516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183516).length < 2 ^ (prefixWord ++ tailWord_183516).sum := by decide
  have hdescent : baseEnd_183516 < baseStart_183516 := by decide
  rcases family_descends (prefixWord ++ tailWord_183516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183520 : List Nat := [2, 1, 1, 3, 1, 5, 2, 2, 2, 4]
def baseStart_183520 : Nat := 118140960795 + 183520 * 2 ^ 59
def prefixEnd_183520 : Nat := 4983230072969 + 3 ^ 40 * 183520 * 2
def baseEnd_183520 : Nat := 31411323237742403618671

theorem tailTrace_183520 : CollatzResearch.WordTrace tailWord_183520 prefixEnd_183520 31411323237742403618671 := by
  unfold tailWord_183520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3346762147572928782894007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4462349530097238377192009 3346762147572928782894007)
  ·
    refine ⟨5020143221359393174341011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3346762147572928782894007 5020143221359393174341011)
    ·
      refine ⟨7530214832039089761511517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5020143221359393174341011 7530214832039089761511517)
      ·
        refine ⟨2823830562014658660566819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7530214832039089761511517 2823830562014658660566819)
        ·
          refine ⟨4235745843021987990850229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823830562014658660566819 4235745843021987990850229)
          ·
            refine ⟨397101172783311374142209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4235745843021987990850229 397101172783311374142209)
            ·
              refine ⟨297825879587483530606657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397101172783311374142209 297825879587483530606657)
              ·
                refine ⟨223369409690612647954993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297825879587483530606657 223369409690612647954993)
                ·
                  refine ⟨167527057267959485966245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223369409690612647954993 167527057267959485966245)
                  ·
                    refine ⟨31411323237742403618671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167527057267959485966245 31411323237742403618671)
                    ·
                      rfl

theorem cell23_183520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 2, 4].length) (baseStart_183520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183520 prefixEnd_183520 := by exact prefixLift 183520
  have htrace : WordTrace (prefixWord ++ tailWord_183520) baseStart_183520 baseEnd_183520 := by
    simpa [prefixWord, tailWord_183520, baseEnd_183520] using wordTrace_append hprefix tailTrace_183520
  have hstable : (prefixWord ++ tailWord_183520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183520).length < 2 ^ (prefixWord ++ tailWord_183520).sum := by decide
  have hdescent : baseEnd_183520 < baseStart_183520 := by decide
  rcases family_descends (prefixWord ++ tailWord_183520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183533 : List Nat := [1, 5, 1, 2, 2, 1, 3, 8]
def baseStart_183533 : Nat := 118140960795 + 183533 * 2 ^ 59
def prefixEnd_183533 : Nat := 4983230072969 + 3 ^ 40 * 183533 * 2
def baseEnd_183533 : Nat := 3490394257842061481239

theorem tailTrace_183533 : CollatzResearch.WordTrace tailWord_183533 prefixEnd_183533 3490394257842061481239 := by
  unfold tailWord_183533
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693998444098760786011253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4462665629399173857340835 6693998444098760786011253)
  ·
    refine ⟨627562354134258823688555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6693998444098760786011253 627562354134258823688555)
    ·
      refine ⟨941343531201388235532833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627562354134258823688555 941343531201388235532833)
      ·
        refine ⟨706007648401041176649625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 941343531201388235532833 706007648401041176649625)
        ·
          refine ⟨529505736300780882487219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706007648401041176649625 529505736300780882487219)
          ·
            refine ⟨794258604451171323730829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529505736300780882487219 794258604451171323730829)
            ·
              refine ⟨297846976669189246399061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794258604451171323730829 297846976669189246399061)
              ·
                refine ⟨3490394257842061481239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 297846976669189246399061 3490394257842061481239)
                ·
                  rfl

theorem cell23_183533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 8].length) (baseStart_183533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183533 prefixEnd_183533 := by exact prefixLift 183533
  have htrace : WordTrace (prefixWord ++ tailWord_183533) baseStart_183533 baseEnd_183533 := by
    simpa [prefixWord, tailWord_183533, baseEnd_183533] using wordTrace_append hprefix tailTrace_183533
  have hstable : (prefixWord ++ tailWord_183533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183533).length < 2 ^ (prefixWord ++ tailWord_183533).sum := by decide
  have hdescent : baseEnd_183533 < baseStart_183533 := by decide
  rcases family_descends (prefixWord ++ tailWord_183533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183546 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_183546 : Nat := 118140960795 + 183546 * 2 ^ 59
def prefixEnd_183546 : Nat := 4983230072969 + 3 ^ 40 * 183546 * 2
def baseEnd_183546 : Nat := 31415773403414703043631

theorem tailTrace_183546 : CollatzResearch.WordTrace tailWord_183546 prefixEnd_183546 31415773403414703043631 := by
  unfold tailWord_183546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673618148262916001558623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4462981728701109337489661 1673618148262916001558623)
  ·
    refine ⟨2510427222394374002337935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673618148262916001558623 2510427222394374002337935)
    ·
      refine ⟨3765640833591561003506903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510427222394374002337935 3765640833591561003506903)
      ·
        refine ⟨5648461250387341505260355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765640833591561003506903 5648461250387341505260355)
        ·
          refine ⟨8472691875581012257890533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648461250387341505260355 8472691875581012257890533)
          ·
            refine ⟨1588629726671439798354475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8472691875581012257890533 1588629726671439798354475)
            ·
              refine ⟨2382944590007159697531713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588629726671439798354475 2382944590007159697531713)
              ·
                refine ⟨1787208442505369773148785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382944590007159697531713 1787208442505369773148785)
                ·
                  refine ⟨1340406331879027329861589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787208442505369773148785 1340406331879027329861589)
                  ·
                    refine ⟨31415773403414703043631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1340406331879027329861589 31415773403414703043631)
                    ·
                      rfl

theorem cell23_183546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_183546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183546 prefixEnd_183546 := by exact prefixLift 183546
  have htrace : WordTrace (prefixWord ++ tailWord_183546) baseStart_183546 baseEnd_183546 := by
    simpa [prefixWord, tailWord_183546, baseEnd_183546] using wordTrace_append hprefix tailTrace_183546
  have hstable : (prefixWord ++ tailWord_183546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183546).length < 2 ^ (prefixWord ++ tailWord_183546).sum := by decide
  have hdescent : baseEnd_183546 < baseStart_183546 := by decide
  rcases family_descends (prefixWord ++ tailWord_183546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183550 : List Nat := [4, 2, 2, 1, 1, 3, 3, 7]
def baseStart_183550 : Nat := 118140960795 + 183550 * 2 ^ 59
def prefixEnd_183550 : Nat := 4983230072969 + 3 ^ 40 * 183550 * 2
def baseEnd_183550 : Nat := 3490717560476373832625

theorem tailTrace_183550 : CollatzResearch.WordTrace tailWord_183550 prefixEnd_183550 3490717560476373832625 := by
  unfold tailWord_183550
  simp only [CollatzResearch.WordTrace]
  refine ⟨836827310629646586172513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4463078990024781792920069 836827310629646586172513)
  ·
    refine ⟨627620482972234939629385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 836827310629646586172513 627620482972234939629385)
    ·
      refine ⟨470715362229176204722039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627620482972234939629385 470715362229176204722039)
      ·
        refine ⟨706073043343764307083059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470715362229176204722039 706073043343764307083059)
        ·
          refine ⟨1059109565015646460624589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706073043343764307083059 1059109565015646460624589)
          ·
            refine ⟨397166086880867422734221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1059109565015646460624589 397166086880867422734221)
            ·
              refine ⟨148937282580325283525333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397166086880867422734221 148937282580325283525333)
              ·
                refine ⟨3490717560476373832625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 148937282580325283525333 3490717560476373832625)
                ·
                  rfl

theorem cell23_183550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_183550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183550 prefixEnd_183550 := by exact prefixLift 183550
  have htrace : WordTrace (prefixWord ++ tailWord_183550) baseStart_183550 baseEnd_183550 := by
    simpa [prefixWord, tailWord_183550, baseEnd_183550] using wordTrace_append hprefix tailTrace_183550
  have hstable : (prefixWord ++ tailWord_183550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183550).length < 2 ^ (prefixWord ++ tailWord_183550).sum := by decide
  have hdescent : baseEnd_183550 < baseStart_183550 := by decide
  rcases family_descends (prefixWord ++ tailWord_183550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183604 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_183604 : Nat := 118140960795 + 183604 * 2 ^ 59
def prefixEnd_183604 : Nat := 4983230072969 + 3 ^ 40 * 183604 * 2
def baseEnd_183604 : Nat := 94277102088204882205627

theorem tailTrace_183604 : CollatzResearch.WordTrace tailWord_183604 prefixEnd_183604 94277102088204882205627 := by
  unfold tailWord_183604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348294013420769955922933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4464392017894359941230577 3348294013420769955922933)
  ·
    refine ⟨313902563758197183367775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3348294013420769955922933 313902563758197183367775)
    ·
      refine ⟨470853845637295775051663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313902563758197183367775 470853845637295775051663)
      ·
        refine ⟨706280768455943662577495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470853845637295775051663 706280768455943662577495)
        ·
          refine ⟨1059421152683915493866243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706280768455943662577495 1059421152683915493866243)
          ·
            refine ⟨1589131729025873240799365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059421152683915493866243 1589131729025873240799365)
            ·
              refine ⟨297962199192351232649881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1589131729025873240799365 297962199192351232649881)
              ·
                refine ⟨223471649394263424487411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297962199192351232649881 223471649394263424487411)
                ·
                  refine ⟨335207474091395136731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223471649394263424487411 335207474091395136731117)
                  ·
                    refine ⟨125702802784273176274169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335207474091395136731117 125702802784273176274169)
                    ·
                      refine ⟨94277102088204882205627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125702802784273176274169 94277102088204882205627)
                      ·
                        rfl

theorem cell23_183604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_183604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183604 prefixEnd_183604 := by exact prefixLift 183604
  have htrace : WordTrace (prefixWord ++ tailWord_183604) baseStart_183604 baseEnd_183604 := by
    simpa [prefixWord, tailWord_183604, baseEnd_183604] using wordTrace_append hprefix tailTrace_183604
  have hstable : (prefixWord ++ tailWord_183604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183604).length < 2 ^ (prefixWord ++ tailWord_183604).sum := by decide
  have hdescent : baseEnd_183604 < baseStart_183604 := by decide
  rcases family_descends (prefixWord ++ tailWord_183604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183620 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_183620 : Nat := 118140960795 + 183620 * 2 ^ 59
def prefixEnd_183620 : Nat := 4983230072969 + 3 ^ 40 * 183620 * 2
def baseEnd_183620 : Nat := 94285317778676819605553

theorem tailTrace_183620 : CollatzResearch.WordTrace tailWord_183620 prefixEnd_183620 94285317778676819605553 := by
  unfold tailWord_183620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348585797391787322214157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4464781063189049762952209 3348585797391787322214157)
  ·
    refine ⟨1255719674021920245830309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3348585797391787322214157 1255719674021920245830309)
    ·
      refine ⟨235447438879110046093183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1255719674021920245830309 235447438879110046093183)
      ·
        refine ⟨353171158318665069139775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235447438879110046093183 353171158318665069139775)
        ·
          refine ⟨529756737477997603709663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353171158318665069139775 529756737477997603709663)
          ·
            refine ⟨794635106216996405564495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529756737477997603709663 794635106216996405564495)
            ·
              refine ⟨1191952659325494608346743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794635106216996405564495 1191952659325494608346743)
              ·
                refine ⟨1787928988988241912520115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191952659325494608346743 1787928988988241912520115)
                ·
                  refine ⟨2681893483482362868780173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787928988988241912520115 2681893483482362868780173)
                  ·
                    refine ⟨1005710056305886075792565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681893483482362868780173 1005710056305886075792565)
                    ·
                      refine ⟨94285317778676819605553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1005710056305886075792565 94285317778676819605553)
                      ·
                        rfl

theorem cell23_183620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_183620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183620 prefixEnd_183620 := by exact prefixLift 183620
  have htrace : WordTrace (prefixWord ++ tailWord_183620) baseStart_183620 baseEnd_183620 := by
    simpa [prefixWord, tailWord_183620, baseEnd_183620] using wordTrace_append hprefix tailTrace_183620
  have hstable : (prefixWord ++ tailWord_183620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183620).length < 2 ^ (prefixWord ++ tailWord_183620).sum := by decide
  have hdescent : baseEnd_183620 < baseStart_183620 := by decide
  rcases family_descends (prefixWord ++ tailWord_183620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183645 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_183645 : Nat := 118140960795 + 183645 * 2 ^ 59
def prefixEnd_183645 : Nat := 4983230072969 + 3 ^ 40 * 183645 * 2
def baseEnd_183645 : Nat := 94298154795039221792939

theorem tailTrace_183645 : CollatzResearch.WordTrace tailWord_183645 prefixEnd_183645 94298154795039221792939 := by
  unfold tailWord_183645
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698083419693003914088389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4465388946462002609392259 6698083419693003914088389)
  ·
    refine ⟨1255890641192438233891573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6698083419693003914088389 1255890641192438233891573)
    ·
      refine ⟨117739747611791084427335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1255890641192438233891573 117739747611791084427335)
      ·
        refine ⟨176609621417686626641003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117739747611791084427335 176609621417686626641003)
        ·
          refine ⟨264914432126529939961505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176609621417686626641003 264914432126529939961505)
          ·
            refine ⟨198685824094897454971129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264914432126529939961505 198685824094897454971129)
            ·
              refine ⟨149014368071173091228347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198685824094897454971129 149014368071173091228347)
              ·
                refine ⟨223521552106759636842521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149014368071173091228347 223521552106759636842521)
                ·
                  refine ⟨167641164080069727631891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223521552106759636842521 167641164080069727631891)
                  ·
                    refine ⟨251461746120104591447837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167641164080069727631891 251461746120104591447837)
                    ·
                      refine ⟨94298154795039221792939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 251461746120104591447837 94298154795039221792939)
                      ·
                        rfl

theorem cell23_183645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_183645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183645 prefixEnd_183645 := by exact prefixLift 183645
  have htrace : WordTrace (prefixWord ++ tailWord_183645) baseStart_183645 baseEnd_183645 := by
    simpa [prefixWord, tailWord_183645, baseEnd_183645] using wordTrace_append hprefix tailTrace_183645
  have hstable : (prefixWord ++ tailWord_183645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183645).length < 2 ^ (prefixWord ++ tailWord_183645).sum := by decide
  have hdescent : baseEnd_183645 < baseStart_183645 := by decide
  rcases family_descends (prefixWord ++ tailWord_183645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183650 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_183650 : Nat := 118140960795 + 183650 * 2 ^ 59
def prefixEnd_183650 : Nat := 4983230072969 + 3 ^ 40 * 183650 * 2
def baseEnd_183650 : Nat := 94300722198311702230415

theorem tailTrace_183650 : CollatzResearch.WordTrace tailWord_183650 prefixEnd_183650 94300722198311702230415 := by
  unfold tailWord_183650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674566446168722442005101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4465510523116593178680269 1674566446168722442005101)
  ·
    refine ⟨627962417313270915751913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1674566446168722442005101 627962417313270915751913)
    ·
      refine ⟨470971812984953186813935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627962417313270915751913 470971812984953186813935)
      ·
        refine ⟨706457719477429780220903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470971812984953186813935 706457719477429780220903)
        ·
          refine ⟨1059686579216144670331355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706457719477429780220903 1059686579216144670331355)
          ·
            refine ⟨1589529868824217005497033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059686579216144670331355 1589529868824217005497033)
            ·
              refine ⟨1192147401618162754122775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589529868824217005497033 1192147401618162754122775)
              ·
                refine ⟨1788221102427244131184163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192147401618162754122775 1788221102427244131184163)
                ·
                  refine ⟨2682331653640866196776245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788221102427244131184163 2682331653640866196776245)
                  ·
                    refine ⟨251468592528831205947773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2682331653640866196776245 251468592528831205947773)
                    ·
                      refine ⟨94300722198311702230415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 251468592528831205947773 94300722198311702230415)
                      ·
                        rfl

theorem cell23_183650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_183650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183650 prefixEnd_183650 := by exact prefixLift 183650
  have htrace : WordTrace (prefixWord ++ tailWord_183650) baseStart_183650 baseEnd_183650 := by
    simpa [prefixWord, tailWord_183650, baseEnd_183650] using wordTrace_append hprefix tailTrace_183650
  have hstable : (prefixWord ++ tailWord_183650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183650).length < 2 ^ (prefixWord ++ tailWord_183650).sum := by decide
  have hdescent : baseEnd_183650 < baseStart_183650 := by decide
  rcases family_descends (prefixWord ++ tailWord_183650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183651 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 2, 2, 2]
def baseStart_183651 : Nat := 118140960795 + 183651 * 2 ^ 59
def prefixEnd_183651 : Nat := 4983230072969 + 3 ^ 40 * 183651 * 2
def baseEnd_183651 : Nat := 94301235678966198317911

theorem tailTrace_183651 : CollatzResearch.WordTrace tailWord_183651 prefixEnd_183651 94301235678966198317911 := by
  unfold tailWord_183651
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698302257671266938806807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4465534838447511292537871 6698302257671266938806807)
  ·
    refine ⟨10047453386506900408210211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6698302257671266938806807 10047453386506900408210211)
    ·
      refine ⟨15071180079760350612315317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10047453386506900408210211 15071180079760350612315317)
      ·
        refine ⟨1412923132477532869904561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15071180079760350612315317 1412923132477532869904561)
        ·
          refine ⟨1059692349358149652428421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1412923132477532869904561 1059692349358149652428421)
          ·
            refine ⟨198692315504653059830329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1059692349358149652428421 198692315504653059830329)
            ·
              refine ⟨149019236628489794872747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198692315504653059830329 149019236628489794872747)
              ·
                refine ⟨223528854942734692309121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149019236628489794872747 223528854942734692309121)
                ·
                  refine ⟨167646641207051019231841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223528854942734692309121 167646641207051019231841)
                  ·
                    refine ⟨125734980905288264423881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167646641207051019231841 125734980905288264423881)
                    ·
                      refine ⟨94301235678966198317911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125734980905288264423881 94301235678966198317911)
                      ·
                        rfl

theorem cell23_183651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_183651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183651 prefixEnd_183651 := by exact prefixLift 183651
  have htrace : WordTrace (prefixWord ++ tailWord_183651) baseStart_183651 baseEnd_183651 := by
    simpa [prefixWord, tailWord_183651, baseEnd_183651] using wordTrace_append hprefix tailTrace_183651
  have hstable : (prefixWord ++ tailWord_183651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183651).length < 2 ^ (prefixWord ++ tailWord_183651).sum := by decide
  have hdescent : baseEnd_183651 < baseStart_183651 := by decide
  rcases family_descends (prefixWord ++ tailWord_183651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183653 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_183653 : Nat := 118140960795 + 183653 * 2 ^ 59
def prefixEnd_183653 : Nat := 4983230072969 + 3 ^ 40 * 183653 * 2
def baseEnd_183653 : Nat := 31434087546758396830967

theorem tailTrace_183653 : CollatzResearch.WordTrace tailWord_183653 prefixEnd_183653 31434087546758396830967 := by
  unfold tailWord_183653
  simp only [CollatzResearch.WordTrace]
  refine ⟨6698375203664021280379613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4465583469109347520253075 6698375203664021280379613)
  ·
    refine ⟨2511890701374007980142355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6698375203664021280379613 2511890701374007980142355)
    ·
      refine ⟨3767836052061011970213533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511890701374007980142355 3767836052061011970213533)
      ·
        refine ⟨1412938519522879488830075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3767836052061011970213533 1412938519522879488830075)
        ·
          refine ⟨2119407779284319233245113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412938519522879488830075 2119407779284319233245113)
          ·
            refine ⟨1589555834463239424933835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119407779284319233245113 1589555834463239424933835)
            ·
              refine ⟨2384333751694859137400753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589555834463239424933835 2384333751694859137400753)
              ·
                refine ⟨1788250313771144353050565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384333751694859137400753 1788250313771144353050565)
                ·
                  refine ⟨335296933832089566196981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1788250313771144353050565 335296933832089566196981)
                  ·
                    refine ⟨31434087546758396830967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 335296933832089566196981 31434087546758396830967)
                    ·
                      rfl

theorem cell23_183653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_183653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183653 prefixEnd_183653 := by exact prefixLift 183653
  have htrace : WordTrace (prefixWord ++ tailWord_183653) baseStart_183653 baseEnd_183653 := by
    simpa [prefixWord, tailWord_183653, baseEnd_183653] using wordTrace_append hprefix tailTrace_183653
  have hstable : (prefixWord ++ tailWord_183653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183653).length < 2 ^ (prefixWord ++ tailWord_183653).sum := by decide
  have hdescent : baseEnd_183653 < baseStart_183653 := by decide
  rcases family_descends (prefixWord ++ tailWord_183653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183673 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4]
def baseStart_183673 : Nat := 118140960795 + 183673 * 2 ^ 59
def prefixEnd_183673 : Nat := 4983230072969 + 3 ^ 40 * 183673 * 2
def baseEnd_183673 : Nat := 94312532253365112242809

theorem tailTrace_183673 : CollatzResearch.WordTrace tailWord_183673 prefixEnd_183673 94312532253365112242809 := by
  unfold tailWord_183673
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699104663591564696107673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4466069775727709797405115 6699104663591564696107673)
  ·
    refine ⟨5024328497693673522080755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6699104663591564696107673 5024328497693673522080755)
    ·
      refine ⟨7536492746540510283121133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024328497693673522080755 7536492746540510283121133)
      ·
        refine ⟨2826184779952691356170425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7536492746540510283121133 2826184779952691356170425)
        ·
          refine ⟨2119638584964518517127819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826184779952691356170425 2119638584964518517127819)
          ·
            refine ⟨3179457877446777775691729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119638584964518517127819 3179457877446777775691729)
            ·
              refine ⟨2384593408085083331768797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179457877446777775691729 2384593408085083331768797)
              ·
                refine ⟨894222528031906249413299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2384593408085083331768797 894222528031906249413299)
                ·
                  refine ⟨1341333792047859374119949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894222528031906249413299 1341333792047859374119949)
                  ·
                    refine ⟨503000172017947265294981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1341333792047859374119949 503000172017947265294981)
                    ·
                      refine ⟨94312532253365112242809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 503000172017947265294981 94312532253365112242809)
                      ·
                        rfl

theorem cell23_183673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_183673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183673 prefixEnd_183673 := by exact prefixLift 183673
  have htrace : WordTrace (prefixWord ++ tailWord_183673) baseStart_183673 baseEnd_183673 := by
    simpa [prefixWord, tailWord_183673, baseEnd_183673] using wordTrace_append hprefix tailTrace_183673
  have hstable : (prefixWord ++ tailWord_183673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183673).length < 2 ^ (prefixWord ++ tailWord_183673).sum := by decide
  have hdescent : baseEnd_183673 < baseStart_183673 := by decide
  rcases family_descends (prefixWord ++ tailWord_183673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183703 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4]
def baseStart_183703 : Nat := 118140960795 + 183703 * 2 ^ 59
def prefixEnd_183703 : Nat := 4983230072969 + 3 ^ 40 * 183703 * 2
def baseEnd_183703 : Nat := 94327936672999994867671

theorem tailTrace_183703 : CollatzResearch.WordTrace tailWord_183703 prefixEnd_183703 94327936672999994867671 := by
  unfold tailWord_183703
  simp only [CollatzResearch.WordTrace]
  refine ⟨6700198853482879819699763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4466799235655253213133175 6700198853482879819699763)
  ·
    refine ⟨10050298280224319729549645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6700198853482879819699763 10050298280224319729549645)
    ·
      refine ⟨3768861855084119898581117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10050298280224319729549645 3768861855084119898581117)
      ·
        refine ⟨1413323195656544961967919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3768861855084119898581117 1413323195656544961967919)
        ·
          refine ⟨2119984793484817442951879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413323195656544961967919 2119984793484817442951879)
          ·
            refine ⟨3179977190227226164427819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119984793484817442951879 3179977190227226164427819)
            ·
              refine ⟨4769965785340839246641729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179977190227226164427819 4769965785340839246641729)
              ·
                refine ⟨3577474339005629434981297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769965785340839246641729 3577474339005629434981297)
                ·
                  refine ⟨2683105754254222076235973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577474339005629434981297 2683105754254222076235973)
                  ·
                    refine ⟨503082328922666639294245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2683105754254222076235973 503082328922666639294245)
                    ·
                      refine ⟨94327936672999994867671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 503082328922666639294245 94327936672999994867671)
                      ·
                        rfl

theorem cell23_183703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_183703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183703 prefixEnd_183703 := by exact prefixLift 183703
  have htrace : WordTrace (prefixWord ++ tailWord_183703) baseStart_183703 baseEnd_183703 := by
    simpa [prefixWord, tailWord_183703, baseEnd_183703] using wordTrace_append hprefix tailTrace_183703
  have hstable : (prefixWord ++ tailWord_183703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183703).length < 2 ^ (prefixWord ++ tailWord_183703).sum := by decide
  have hdescent : baseEnd_183703 < baseStart_183703 := by decide
  rcases family_descends (prefixWord ++ tailWord_183703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183764 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 6]
def baseStart_183764 : Nat := 118140960795 + 183764 * 2 ^ 59
def prefixEnd_183764 : Nat := 4983230072969 + 3 ^ 40 * 183764 * 2
def baseEnd_183764 : Nat := 10484362110324917356099

theorem tailTrace_183764 : CollatzResearch.WordTrace tailWord_183764 prefixEnd_183764 10484362110324917356099 := by
  unfold tailWord_183764
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351211853130943618835173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4468282470841258158446897 3351211853130943618835173)
  ·
    refine ⟨628352222462051928531595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3351211853130943618835173 628352222462051928531595)
    ·
      refine ⟨942528333693077892797393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628352222462051928531595 942528333693077892797393)
      ·
        refine ⟨706896250269808419598045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942528333693077892797393 706896250269808419598045)
        ·
          refine ⟨265086093851178157349267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706896250269808419598045 265086093851178157349267)
          ·
            refine ⟨397629140776767236023901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265086093851178157349267 397629140776767236023901)
            ·
              refine ⟨149110927791287713508963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 397629140776767236023901 149110927791287713508963)
              ·
                refine ⟨223666391686931570263445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149110927791287713508963 223666391686931570263445)
                ·
                  refine ⟨10484362110324917356099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 223666391686931570263445 10484362110324917356099)
                  ·
                    rfl

theorem cell23_183764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_183764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183764 prefixEnd_183764 := by exact prefixLift 183764
  have htrace : WordTrace (prefixWord ++ tailWord_183764) baseStart_183764 baseEnd_183764 := by
    simpa [prefixWord, tailWord_183764, baseEnd_183764] using wordTrace_append hprefix tailTrace_183764
  have hstable : (prefixWord ++ tailWord_183764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183764).length < 2 ^ (prefixWord ++ tailWord_183764).sum := by decide
  have hdescent : baseEnd_183764 < baseStart_183764 := by decide
  rcases family_descends (prefixWord ++ tailWord_183764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183777 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 1, 5]
def baseStart_183777 : Nat := 118140960795 + 183777 * 2 ^ 59
def prefixEnd_183777 : Nat := 4983230072969 + 3 ^ 40 * 183777 * 2
def baseEnd_183777 : Nat := 31455311413810901780777

theorem tailTrace_183777 : CollatzResearch.WordTrace tailWord_183777 prefixEnd_183777 31455311413810901780777 := by
  unfold tailWord_183777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6702897855214790457893585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4468598570143193638595723 6702897855214790457893585)
  ·
    refine ⟨5027173391411092843420189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6702897855214790457893585 5027173391411092843420189)
    ·
      refine ⟨1885190021779159816282571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5027173391411092843420189 1885190021779159816282571)
      ·
        refine ⟨2827785032668739724423857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885190021779159816282571 2827785032668739724423857)
        ·
          refine ⟨2120838774501554793317893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2827785032668739724423857 2120838774501554793317893)
          ·
            refine ⟨397657270219041523747105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2120838774501554793317893 397657270219041523747105)
            ·
              refine ⟨298242952664281142810329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397657270219041523747105 298242952664281142810329)
              ·
                refine ⟨223682214498210857107747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298242952664281142810329 223682214498210857107747)
                ·
                  refine ⟨335523321747316285661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223682214498210857107747 335523321747316285661621)
                  ·
                    refine ⟨31455311413810901780777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 335523321747316285661621 31455311413810901780777)
                    ·
                      rfl

theorem cell23_183777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_183777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183777 prefixEnd_183777 := by exact prefixLift 183777
  have htrace : WordTrace (prefixWord ++ tailWord_183777) baseStart_183777 baseEnd_183777 := by
    simpa [prefixWord, tailWord_183777, baseEnd_183777] using wordTrace_append hprefix tailTrace_183777
  have hstable : (prefixWord ++ tailWord_183777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183777).length < 2 ^ (prefixWord ++ tailWord_183777).sum := by decide
  have hdescent : baseEnd_183777 < baseStart_183777 := by decide
  rcases family_descends (prefixWord ++ tailWord_183777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183780 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_183780 : Nat := 118140960795 + 183780 * 2 ^ 59
def prefixEnd_183780 : Nat := 4983230072969 + 3 ^ 40 * 183780 * 2
def baseEnd_183780 : Nat := 94367474683396193604817

theorem tailTrace_183780 : CollatzResearch.WordTrace tailWord_183780 prefixEnd_183780 94367474683396193604817 := by
  unfold tailWord_183780
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351503637101960985126397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4468671516135947980168529 3351503637101960985126397)
  ·
    refine ⟨1256813863913235369422399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3351503637101960985126397 1256813863913235369422399)
    ·
      refine ⟨1885220795869853054133599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256813863913235369422399 1885220795869853054133599)
      ·
        refine ⟨2827831193804779581200399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885220795869853054133599 2827831193804779581200399)
        ·
          refine ⟨4241746790707169371800599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2827831193804779581200399 4241746790707169371800599)
          ·
            refine ⟨6362620186060754057700899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4241746790707169371800599 6362620186060754057700899)
            ·
              refine ⟨9543930279091131086551349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6362620186060754057700899 9543930279091131086551349)
              ·
                refine ⟨894743463664793539364189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9543930279091131086551349 894743463664793539364189)
                ·
                  refine ⟨335528798874297577261571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894743463664793539364189 335528798874297577261571)
                  ·
                    refine ⟨503293198311446365892357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 335528798874297577261571 503293198311446365892357)
                    ·
                      refine ⟨94367474683396193604817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 503293198311446365892357 94367474683396193604817)
                      ·
                        rfl

theorem cell23_183780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_183780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183780 prefixEnd_183780 := by exact prefixLift 183780
  have htrace : WordTrace (prefixWord ++ tailWord_183780) baseStart_183780 baseEnd_183780 := by
    simpa [prefixWord, tailWord_183780, baseEnd_183780] using wordTrace_append hprefix tailTrace_183780
  have hstable : (prefixWord ++ tailWord_183780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183780).length < 2 ^ (prefixWord ++ tailWord_183780).sum := by decide
  have hdescent : baseEnd_183780 < baseStart_183780 := by decide
  rcases family_descends (prefixWord ++ tailWord_183780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183790 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_183790 : Nat := 118140960795 + 183790 * 2 ^ 59
def prefixEnd_183790 : Nat := 4983230072969 + 3 ^ 40 * 183790 * 2
def baseEnd_183790 : Nat := 31457536496647051493257

theorem tailTrace_183790 : CollatzResearch.WordTrace tailWord_183790 prefixEnd_183790 31457536496647051493257 := by
  unfold tailWord_183790
  simp only [CollatzResearch.WordTrace]
  refine ⟨837921500520961709764603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4468914669445129118744549 837921500520961709764603)
  ·
    refine ⟨1256882250781442564646905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 837921500520961709764603 1256882250781442564646905)
    ·
      refine ⟨942661688086081923485179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1256882250781442564646905 942661688086081923485179)
      ·
        refine ⟨1413992532129122885227769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942661688086081923485179 1413992532129122885227769)
        ·
          refine ⟨1060494399096842163920827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413992532129122885227769 1060494399096842163920827)
          ·
            refine ⟨1590741598645263245881241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060494399096842163920827 1590741598645263245881241)
            ·
              refine ⟨1193056198983947434410931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590741598645263245881241 1193056198983947434410931)
              ·
                refine ⟨1789584298475921151616397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193056198983947434410931 1789584298475921151616397)
                ·
                  refine ⟨671094111928470431856149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1789584298475921151616397 671094111928470431856149)
                  ·
                    refine ⟨31457536496647051493257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 671094111928470431856149 31457536496647051493257)
                    ·
                      rfl

theorem cell23_183790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_183790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183790 prefixEnd_183790 := by exact prefixLift 183790
  have htrace : WordTrace (prefixWord ++ tailWord_183790) baseStart_183790 baseEnd_183790 := by
    simpa [prefixWord, tailWord_183790, baseEnd_183790] using wordTrace_append hprefix tailTrace_183790
  have hstable : (prefixWord ++ tailWord_183790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183790).length < 2 ^ (prefixWord ++ tailWord_183790).sum := by decide
  have hdescent : baseEnd_183790 < baseStart_183790 := by decide
  rcases family_descends (prefixWord ++ tailWord_183790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183800 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_183800 : Nat := 118140960795 + 183800 * 2 ^ 59
def prefixEnd_183800 : Nat := 4983230072969 + 3 ^ 40 * 183800 * 2
def baseEnd_183800 : Nat := 94377744296486115354725

theorem tailTrace_183800 : CollatzResearch.WordTrace tailWord_183800 prefixEnd_183800 94377744296486115354725 := by
  unfold tailWord_183800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351868367065732692990427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4469157822754310257320569 3351868367065732692990427)
  ·
    refine ⟨5027802550598599039485641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3351868367065732692990427 5027802550598599039485641)
    ·
      refine ⟨3770851912948949279614231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5027802550598599039485641 3770851912948949279614231)
      ·
        refine ⟨5656277869423423919421347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3770851912948949279614231 5656277869423423919421347)
        ·
          refine ⟨8484416804135135879132021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656277869423423919421347 8484416804135135879132021)
          ·
            refine ⟨795414075387668988668627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8484416804135135879132021 795414075387668988668627)
            ·
              refine ⟨1193121113081503483002941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795414075387668988668627 1193121113081503483002941)
              ·
                refine ⟨447420417405563806126103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1193121113081503483002941 447420417405563806126103)
                ·
                  refine ⟨671130626108345709189155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447420417405563806126103 671130626108345709189155)
                  ·
                    refine ⟨1006695939162518563783733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 671130626108345709189155 1006695939162518563783733)
                    ·
                      refine ⟨94377744296486115354725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1006695939162518563783733 94377744296486115354725)
                      ·
                        rfl

theorem cell23_183800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_183800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183800 prefixEnd_183800 := by exact prefixLift 183800
  have htrace : WordTrace (prefixWord ++ tailWord_183800) baseStart_183800 baseEnd_183800 := by
    simpa [prefixWord, tailWord_183800, baseEnd_183800] using wordTrace_append hprefix tailTrace_183800
  have hstable : (prefixWord ++ tailWord_183800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183800).length < 2 ^ (prefixWord ++ tailWord_183800).sum := by decide
  have hdescent : baseEnd_183800 < baseStart_183800 := by decide
  rcases family_descends (prefixWord ++ tailWord_183800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183828 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_183828 : Nat := 118140960795 + 183828 * 2 ^ 59
def prefixEnd_183828 : Nat := 4983230072969 + 3 ^ 40 * 183828 * 2
def baseEnd_183828 : Nat := 31464040584937335268199

theorem tailTrace_183828 : CollatzResearch.WordTrace tailWord_183828 prefixEnd_183828 31464040584937335268199 := by
  unfold tailWord_183828
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352378989015013084000069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4469838652020017445333425 3352378989015013084000069)
  ·
    refine ⟨628571060440314953250013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3352378989015013084000069 628571060440314953250013)
    ·
      refine ⟨235714147665118107468755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 628571060440314953250013 235714147665118107468755)
      ·
        refine ⟨353571221497677161203133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235714147665118107468755 353571221497677161203133)
        ·
          refine ⟨132589208061628935451175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 353571221497677161203133 132589208061628935451175)
          ·
            refine ⟨198883812092443403176763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132589208061628935451175 198883812092443403176763)
            ·
              refine ⟨298325718138665104765145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198883812092443403176763 298325718138665104765145)
              ·
                refine ⟨223744288603998828573859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298325718138665104765145 223744288603998828573859)
                ·
                  refine ⟨335616432905998242860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223744288603998828573859 335616432905998242860789)
                  ·
                    refine ⟨31464040584937335268199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 335616432905998242860789 31464040584937335268199)
                    ·
                      rfl

theorem cell23_183828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_183828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183828 prefixEnd_183828 := by exact prefixLift 183828
  have htrace : WordTrace (prefixWord ++ tailWord_183828) baseStart_183828 baseEnd_183828 := by
    simpa [prefixWord, tailWord_183828, baseEnd_183828] using wordTrace_append hprefix tailTrace_183828
  have hstable : (prefixWord ++ tailWord_183828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183828).length < 2 ^ (prefixWord ++ tailWord_183828).sum := by decide
  have hdescent : baseEnd_183828 < baseStart_183828 := by decide
  rcases family_descends (prefixWord ++ tailWord_183828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183864 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_183864 : Nat := 118140960795 + 183864 * 2 ^ 59
def prefixEnd_183864 : Nat := 4983230072969 + 3 ^ 40 * 183864 * 2
def baseEnd_183864 : Nat := 94410607058373864954431

theorem tailTrace_183864 : CollatzResearch.WordTrace tailWord_183864 prefixEnd_183864 94410607058373864954431 := by
  unfold tailWord_183864
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353035502949802158155323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4470714003933069544207097 3353035502949802158155323)
  ·
    refine ⟨5029553254424703237232985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353035502949802158155323 5029553254424703237232985)
    ·
      refine ⟨3772164940818527427924739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5029553254424703237232985 3772164940818527427924739)
      ·
        refine ⟨5658247411227791141887109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772164940818527427924739 5658247411227791141887109)
        ·
          refine ⟨1060921389605210839103833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5658247411227791141887109 1060921389605210839103833)
          ·
            refine ⟨795691042203908129327875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060921389605210839103833 795691042203908129327875)
            ·
              refine ⟨1193536563305862193991813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795691042203908129327875 1193536563305862193991813)
              ·
                refine ⟨223788105619849161373465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1193536563305862193991813 223788105619849161373465)
                ·
                  refine ⟨167841079214886871030099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223788105619849161373465 167841079214886871030099)
                  ·
                    refine ⟨251761618822330306545149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167841079214886871030099 251761618822330306545149)
                    ·
                      refine ⟨94410607058373864954431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 251761618822330306545149 94410607058373864954431)
                      ·
                        rfl

theorem cell23_183864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_183864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183864 prefixEnd_183864 := by exact prefixLift 183864
  have htrace : WordTrace (prefixWord ++ tailWord_183864) baseStart_183864 baseEnd_183864 := by
    simpa [prefixWord, tailWord_183864, baseEnd_183864] using wordTrace_append hprefix tailTrace_183864
  have hstable : (prefixWord ++ tailWord_183864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183864).length < 2 ^ (prefixWord ++ tailWord_183864).sum := by decide
  have hdescent : baseEnd_183864 < baseStart_183864 := by decide
  rcases family_descends (prefixWord ++ tailWord_183864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183865 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 1, 2, 2]
def baseStart_183865 : Nat := 118140960795 + 183865 * 2 ^ 59
def prefixEnd_183865 : Nat := 4983230072969 + 3 ^ 40 * 183865 * 2
def baseEnd_183865 : Nat := 94411120539028361041927

theorem tailTrace_183865 : CollatzResearch.WordTrace tailWord_183865 prefixEnd_183865 94411120539028361041927 := by
  unfold tailWord_183865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706107478895981487097049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4470738319263987658064699 6706107478895981487097049)
  ·
    refine ⟨5029580609171986115322787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6706107478895981487097049 5029580609171986115322787)
    ·
      refine ⟨7544370913757979172984181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029580609171986115322787 7544370913757979172984181)
      ·
        refine ⟨707284773164810547467267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7544370913757979172984181 707284773164810547467267)
        ·
          refine ⟨1060927159747215821200901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707284773164810547467267 1060927159747215821200901)
          ·
            refine ⟨198923842452602966475169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1060927159747215821200901 198923842452602966475169)
            ·
              refine ⟨149192881839452224856377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198923842452602966475169 149192881839452224856377)
              ·
                refine ⟨111894661379589168642283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149192881839452224856377 111894661379589168642283)
                ·
                  refine ⟨167841992069383752963425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111894661379589168642283 167841992069383752963425)
                  ·
                    refine ⟨125881494052037814722569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167841992069383752963425 125881494052037814722569)
                    ·
                      refine ⟨94411120539028361041927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125881494052037814722569 94411120539028361041927)
                      ·
                        rfl

theorem cell23_183865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_183865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183865 prefixEnd_183865 := by exact prefixLift 183865
  have htrace : WordTrace (prefixWord ++ tailWord_183865) baseStart_183865 baseEnd_183865 := by
    simpa [prefixWord, tailWord_183865, baseEnd_183865] using wordTrace_append hprefix tailTrace_183865
  have hstable : (prefixWord ++ tailWord_183865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183865).length < 2 ^ (prefixWord ++ tailWord_183865).sum := by decide
  have hdescent : baseEnd_183865 < baseStart_183865 := by decide
  rcases family_descends (prefixWord ++ tailWord_183865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183904 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2]
def baseStart_183904 : Nat := 118140960795 + 183904 * 2 ^ 59
def prefixEnd_183904 : Nat := 4983230072969 + 3 ^ 40 * 183904 * 2
def baseEnd_183904 : Nat := 94431146284553708454247

theorem tailTrace_183904 : CollatzResearch.WordTrace tailWord_183904 prefixEnd_183904 94431146284553708454247 := by
  unfold tailWord_183904
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353764962877345573883383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4471686617169794098511177 3353764962877345573883383)
  ·
    refine ⟨5030647444316018360825075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353764962877345573883383 5030647444316018360825075)
    ·
      refine ⟨7545971166474027541237613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030647444316018360825075 7545971166474027541237613)
      ·
        refine ⟨2829739187427760327964105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7545971166474027541237613 2829739187427760327964105)
        ·
          refine ⟨2122304390570820245973079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829739187427760327964105 2122304390570820245973079)
          ·
            refine ⟨3183456585856230368959619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122304390570820245973079 3183456585856230368959619)
            ·
              refine ⟨4775184878784345553439429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183456585856230368959619 4775184878784345553439429)
              ·
                refine ⟨895347164772064791269893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4775184878784345553439429 895347164772064791269893)
                ·
                  refine ⟨167877593394762148363105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 895347164772064791269893 167877593394762148363105)
                  ·
                    refine ⟨125908195046071611272329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 167877593394762148363105 125908195046071611272329)
                    ·
                      refine ⟨94431146284553708454247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125908195046071611272329 94431146284553708454247)
                      ·
                        rfl

theorem cell23_183904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_183904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183904 prefixEnd_183904 := by exact prefixLift 183904
  have htrace : WordTrace (prefixWord ++ tailWord_183904) baseStart_183904 baseEnd_183904 := by
    simpa [prefixWord, tailWord_183904, baseEnd_183904] using wordTrace_append hprefix tailTrace_183904
  have hstable : (prefixWord ++ tailWord_183904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183904).length < 2 ^ (prefixWord ++ tailWord_183904).sum := by decide
  have hdescent : baseEnd_183904 < baseStart_183904 := by decide
  rcases family_descends (prefixWord ++ tailWord_183904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_183908 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_183908 : Nat := 118140960795 + 183908 * 2 ^ 59
def prefixEnd_183908 : Nat := 4983230072969 + 3 ^ 40 * 183908 * 2
def baseEnd_183908 : Nat := 94433200207171692804229

theorem tailTrace_183908 : CollatzResearch.WordTrace tailWord_183908 prefixEnd_183908 94433200207171692804229 := by
  unfold tailWord_183908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353837908870099915456189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4471783878493466553941585 3353837908870099915456189)
  ·
    refine ⟨1257689215826287468296071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3353837908870099915456189 1257689215826287468296071)
    ·
      refine ⟨1886533823739431202444107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257689215826287468296071 1886533823739431202444107)
      ·
        refine ⟨2829800735609146803666161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886533823739431202444107 2829800735609146803666161)
        ·
          refine ⟨2122350551706860102749621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829800735609146803666161 2122350551706860102749621)
          ·
            refine ⟨198970364222518134632777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2122350551706860102749621 198970364222518134632777)
            ·
              refine ⟨149227773166888600974583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198970364222518134632777 149227773166888600974583)
              ·
                refine ⟨223841659750332901461875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149227773166888600974583 223841659750332901461875)
                ·
                  refine ⟨335762489625499352192813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223841659750332901461875 335762489625499352192813)
                  ·
                    refine ⟨125910933609562257072305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335762489625499352192813 125910933609562257072305)
                    ·
                      refine ⟨94433200207171692804229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 125910933609562257072305 94433200207171692804229)
                      ·
                        rfl

theorem cell23_183908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_183908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_183908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_183908 prefixEnd_183908 := by exact prefixLift 183908
  have htrace : WordTrace (prefixWord ++ tailWord_183908) baseStart_183908 baseEnd_183908 := by
    simpa [prefixWord, tailWord_183908, baseEnd_183908] using wordTrace_append hprefix tailTrace_183908
  have hstable : (prefixWord ++ tailWord_183908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_183908).length < 2 ^ (prefixWord ++ tailWord_183908).sum := by decide
  have hdescent : baseEnd_183908 < baseStart_183908 := by decide
  rcases family_descends (prefixWord ++ tailWord_183908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184004 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_184004 : Nat := 118140960795 + 184004 * 2 ^ 59
def prefixEnd_184004 : Nat := 4983230072969 + 3 ^ 40 * 184004 * 2
def baseEnd_184004 : Nat := 31494164783334439067929

theorem tailTrace_184004 : CollatzResearch.WordTrace tailWord_184004 prefixEnd_184004 31494164783334439067929 := by
  unfold tailWord_184004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355588612696204113203533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4474118150261605484271377 3355588612696204113203533)
  ·
    refine ⟨1258345729761076542451325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3355588612696204113203533 1258345729761076542451325)
    ·
      refine ⟨471879648660403703419247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1258345729761076542451325 471879648660403703419247)
      ·
        refine ⟨707819472990605555128871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471879648660403703419247 707819472990605555128871)
        ·
          refine ⟨1061729209485908332693307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707819472990605555128871 1061729209485908332693307)
          ·
            refine ⟨1592593814228862499039961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061729209485908332693307 1592593814228862499039961)
            ·
              refine ⟨1194445360671646874279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592593814228862499039961 1194445360671646874279971)
              ·
                refine ⟨1791668041007470311419957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194445360671646874279971 1791668041007470311419957)
                ·
                  refine ⟨167968878844450341695621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1791668041007470311419957 167968878844450341695621)
                  ·
                    refine ⟨31494164783334439067929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 167968878844450341695621 31494164783334439067929)
                    ·
                      rfl

theorem cell23_184004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_184004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184004 prefixEnd_184004 := by exact prefixLift 184004
  have htrace : WordTrace (prefixWord ++ tailWord_184004) baseStart_184004 baseEnd_184004 := by
    simpa [prefixWord, tailWord_184004, baseEnd_184004] using wordTrace_append hprefix tailTrace_184004
  have hstable : (prefixWord ++ tailWord_184004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184004).length < 2 ^ (prefixWord ++ tailWord_184004).sum := by decide
  have hdescent : baseEnd_184004 < baseStart_184004 := by decide
  rcases family_descends (prefixWord ++ tailWord_184004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184037 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_184037 : Nat := 118140960795 + 184037 * 2 ^ 59
def prefixEnd_184037 : Nat := 4983230072969 + 3 ^ 40 * 184037 * 2
def baseEnd_184037 : Nat := 94499439211601688091135

theorem tailTrace_184037 : CollatzResearch.WordTrace tailWord_184037 prefixEnd_184037 94499439211601688091135 := by
  unfold tailWord_184037
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712380834272854862358365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4474920556181903241572243 6712380834272854862358365)
  ·
    refine ⟨2517142812852320573384387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6712380834272854862358365 2517142812852320573384387)
    ·
      refine ⟨3775714219278480860076581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2517142812852320573384387 3775714219278480860076581)
      ·
        refine ⟨707946416114715161264359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3775714219278480860076581 707946416114715161264359)
        ·
          refine ⟨1061919624172072741896539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707946416114715161264359 1061919624172072741896539)
          ·
            refine ⟨1592879436258109112844809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061919624172072741896539 1592879436258109112844809)
            ·
              refine ⟨1194659577193581834633607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592879436258109112844809 1194659577193581834633607)
              ·
                refine ⟨1791989365790372751950411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194659577193581834633607 1791989365790372751950411)
                ·
                  refine ⟨2687984048685559127925617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791989365790372751950411 2687984048685559127925617)
                  ·
                    refine ⟨2015988036514169345944213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2687984048685559127925617 2015988036514169345944213)
                    ·
                      refine ⟨94499439211601688091135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2015988036514169345944213 94499439211601688091135)
                      ·
                        rfl

theorem cell23_184037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_184037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184037 prefixEnd_184037 := by exact prefixLift 184037
  have htrace : WordTrace (prefixWord ++ tailWord_184037) baseStart_184037 baseEnd_184037 := by
    simpa [prefixWord, tailWord_184037, baseEnd_184037] using wordTrace_append hprefix tailTrace_184037
  have hstable : (prefixWord ++ tailWord_184037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184037).length < 2 ^ (prefixWord ++ tailWord_184037).sum := by decide
  have hdescent : baseEnd_184037 < baseStart_184037 := by decide
  rcases family_descends (prefixWord ++ tailWord_184037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184047 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 5, 5]
def baseStart_184047 : Nat := 118140960795 + 184047 * 2 ^ 59
def prefixEnd_184047 : Nat := 4983230072969 + 3 ^ 40 * 184047 * 2
def baseEnd_184047 : Nat := 31501524672715549655363

theorem tailTrace_184047 : CollatzResearch.WordTrace tailWord_184047 prefixEnd_184047 31501524672715549655363 := by
  unfold tailWord_184047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712745564236626570222395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4475163709491084380148263 6712745564236626570222395)
  ·
    refine ⟨10069118346354939855333593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712745564236626570222395 10069118346354939855333593)
    ·
      refine ⟨7551838759766204891500195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10069118346354939855333593 7551838759766204891500195)
      ·
        refine ⟨11327758139649307337250293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551838759766204891500195 11327758139649307337250293)
        ·
          refine ⟨1061977325592122562867215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11327758139649307337250293 1061977325592122562867215)
          ·
            refine ⟨1592965988388183844300823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061977325592122562867215 1592965988388183844300823)
            ·
              refine ⟨2389448982582275766451235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592965988388183844300823 2389448982582275766451235)
              ·
                refine ⟨3584173473873413649676853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389448982582275766451235 3584173473873413649676853)
                ·
                  refine ⟨336016263175632529657205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3584173473873413649676853 336016263175632529657205)
                  ·
                    refine ⟨31501524672715549655363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 336016263175632529657205 31501524672715549655363)
                    ·
                      rfl

theorem cell23_184047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 5].length) (baseStart_184047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184047 prefixEnd_184047 := by exact prefixLift 184047
  have htrace : WordTrace (prefixWord ++ tailWord_184047) baseStart_184047 baseEnd_184047 := by
    simpa [prefixWord, tailWord_184047, baseEnd_184047] using wordTrace_append hprefix tailTrace_184047
  have hstable : (prefixWord ++ tailWord_184047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184047).length < 2 ^ (prefixWord ++ tailWord_184047).sum := by decide
  have hdescent : baseEnd_184047 < baseStart_184047 := by decide
  rcases family_descends (prefixWord ++ tailWord_184047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184078 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_184078 : Nat := 118140960795 + 184078 * 2 ^ 59
def prefixEnd_184078 : Nat := 4983230072969 + 3 ^ 40 * 184078 * 2
def baseEnd_184078 : Nat := 94520491918436027678447

theorem tailTrace_184078 : CollatzResearch.WordTrace tailWord_184078 prefixEnd_184078 94520491918436027678447 := by
  unfold tailWord_184078
  simp only [CollatzResearch.WordTrace]
  refine ⟨839234528390539858075111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4475917484749545909733925 839234528390539858075111)
  ·
    refine ⟨1258851792585809787112667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 839234528390539858075111 1258851792585809787112667)
    ·
      refine ⟨1888277688878714680669001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258851792585809787112667 1888277688878714680669001)
      ·
        refine ⟨1416208266659036010501751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888277688878714680669001 1416208266659036010501751)
        ·
          refine ⟨2124312399988554015752627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416208266659036010501751 2124312399988554015752627)
          ·
            refine ⟨3186468599982831023628941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124312399988554015752627 3186468599982831023628941)
            ·
              refine ⟨1194925724993561633860853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3186468599982831023628941 1194925724993561633860853)
              ·
                refine ⟨112024286718146403174455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194925724993561633860853 112024286718146403174455)
                ·
                  refine ⟨168036430077219604761683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112024286718146403174455 168036430077219604761683)
                  ·
                    refine ⟨252054645115829407142525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168036430077219604761683 252054645115829407142525)
                    ·
                      refine ⟨94520491918436027678447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252054645115829407142525 94520491918436027678447)
                      ·
                        rfl

theorem cell23_184078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_184078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184078 prefixEnd_184078 := by exact prefixLift 184078
  have htrace : WordTrace (prefixWord ++ tailWord_184078) baseStart_184078 baseEnd_184078 := by
    simpa [prefixWord, tailWord_184078, baseEnd_184078] using wordTrace_append hprefix tailTrace_184078
  have hstable : (prefixWord ++ tailWord_184078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184078).length < 2 ^ (prefixWord ++ tailWord_184078).sum := by decide
  have hdescent : baseEnd_184078 < baseStart_184078 := by decide
  rcases family_descends (prefixWord ++ tailWord_184078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184104 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_184104 : Nat := 118140960795 + 184104 * 2 ^ 59
def prefixEnd_184104 : Nat := 4983230072969 + 3 ^ 40 * 184104 * 2
def baseEnd_184104 : Nat := 94533842415452925953327

theorem tailTrace_184104 : CollatzResearch.WordTrace tailWord_184104 prefixEnd_184104 94533842415452925953327 := by
  unfold tailWord_184104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357412262515062652523683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4476549683353416870031577 3357412262515062652523683)
  ·
    refine ⟨5036118393772593978785525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357412262515062652523683 5036118393772593978785525)
    ·
      refine ⟨472136099416180685511143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5036118393772593978785525 472136099416180685511143)
      ·
        refine ⟨708204149124271028266715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472136099416180685511143 708204149124271028266715)
        ·
          refine ⟨1062306223686406542400073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708204149124271028266715 1062306223686406542400073)
          ·
            refine ⟨796729667764804906800055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062306223686406542400073 796729667764804906800055)
            ·
              refine ⟨1195094501647207360200083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796729667764804906800055 1195094501647207360200083)
              ·
                refine ⟨1792641752470811040300125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195094501647207360200083 1792641752470811040300125)
                ·
                  refine ⟨672240657176554140112547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1792641752470811040300125 672240657176554140112547)
                  ·
                    refine ⟨1008360985764831210168821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 672240657176554140112547 1008360985764831210168821)
                    ·
                      refine ⟨94533842415452925953327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1008360985764831210168821 94533842415452925953327)
                      ·
                        rfl

theorem cell23_184104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_184104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184104 prefixEnd_184104 := by exact prefixLift 184104
  have htrace : WordTrace (prefixWord ++ tailWord_184104) baseStart_184104 baseEnd_184104 := by
    simpa [prefixWord, tailWord_184104, baseEnd_184104] using wordTrace_append hprefix tailTrace_184104
  have hstable : (prefixWord ++ tailWord_184104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184104).length < 2 ^ (prefixWord ++ tailWord_184104).sum := by decide
  have hdescent : baseEnd_184104 < baseStart_184104 := by decide
  rcases family_descends (prefixWord ++ tailWord_184104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184114 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_184114 : Nat := 118140960795 + 184114 * 2 ^ 59
def prefixEnd_184114 : Nat := 4983230072969 + 3 ^ 40 * 184114 * 2
def baseEnd_184114 : Nat := 94538977221997886828281

theorem tailTrace_184114 : CollatzResearch.WordTrace tailWord_184114 prefixEnd_184114 94538977221997886828281 := by
  unfold tailWord_184114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678797313748474253227849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4476792836662598008607597 1678797313748474253227849)
  ·
    refine ⟨1259097985311355689920887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1678797313748474253227849 1259097985311355689920887)
    ·
      refine ⟨1888646977967033534881331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259097985311355689920887 1888646977967033534881331)
      ·
        refine ⟨2832970466950550302321997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888646977967033534881331 2832970466950550302321997)
        ·
          refine ⟨1062363925106456363370749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2832970466950550302321997 1062363925106456363370749)
          ·
            refine ⟨398386471914921136264031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1062363925106456363370749 398386471914921136264031)
            ·
              refine ⟨597579707872381704396047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398386471914921136264031 597579707872381704396047)
              ·
                refine ⟨896369561808572556594071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597579707872381704396047 896369561808572556594071)
                ·
                  refine ⟨1344554342712858834891107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896369561808572556594071 1344554342712858834891107)
                  ·
                    refine ⟨2016831514069288252336661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344554342712858834891107 2016831514069288252336661)
                    ·
                      refine ⟨94538977221997886828281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2016831514069288252336661 94538977221997886828281)
                      ·
                        rfl

theorem cell23_184114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_184114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184114 prefixEnd_184114 := by exact prefixLift 184114
  have htrace : WordTrace (prefixWord ++ tailWord_184114) baseStart_184114 baseEnd_184114 := by
    simpa [prefixWord, tailWord_184114, baseEnd_184114] using wordTrace_append hprefix tailTrace_184114
  have hstable : (prefixWord ++ tailWord_184114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184114).length < 2 ^ (prefixWord ++ tailWord_184114).sum := by decide
  have hdescent : baseEnd_184114 < baseStart_184114 := by decide
  rcases family_descends (prefixWord ++ tailWord_184114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184118 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_184118 : Nat := 118140960795 + 184118 * 2 ^ 59
def prefixEnd_184118 : Nat := 4983230072969 + 3 ^ 40 * 184118 * 2
def baseEnd_184118 : Nat := 94541031144615871178263

theorem tailTrace_184118 : CollatzResearch.WordTrace tailWord_184118 prefixEnd_184118 94541031144615871178263 := by
  unfold tailWord_184118
  simp only [CollatzResearch.WordTrace]
  refine ⟨419708446686212856003563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4476890097986270464038005 419708446686212856003563)
  ·
    refine ⟨629562670029319284005345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419708446686212856003563 629562670029319284005345)
    ·
      refine ⟨472172002521989463004009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 629562670029319284005345 472172002521989463004009)
      ·
        refine ⟨354129001891492097253007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472172002521989463004009 354129001891492097253007)
        ·
          refine ⟨531193502837238145879511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354129001891492097253007 531193502837238145879511)
          ·
            refine ⟨796790254255857218819267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531193502837238145879511 796790254255857218819267)
            ·
              refine ⟨1195185381383785828228901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796790254255857218819267 1195185381383785828228901)
              ·
                refine ⟨224097259009459842792919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1195185381383785828228901 224097259009459842792919)
                ·
                  refine ⟨336145888514189764189379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224097259009459842792919 336145888514189764189379)
                  ·
                    refine ⟨504218832771284646284069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336145888514189764189379 504218832771284646284069)
                    ·
                      refine ⟨94541031144615871178263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 504218832771284646284069 94541031144615871178263)
                      ·
                        rfl

theorem cell23_184118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_184118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184118 prefixEnd_184118 := by exact prefixLift 184118
  have htrace : WordTrace (prefixWord ++ tailWord_184118) baseStart_184118 baseEnd_184118 := by
    simpa [prefixWord, tailWord_184118, baseEnd_184118] using wordTrace_append hprefix tailTrace_184118
  have hstable : (prefixWord ++ tailWord_184118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184118).length < 2 ^ (prefixWord ++ tailWord_184118).sum := by decide
  have hdescent : baseEnd_184118 < baseStart_184118 := by decide
  rcases family_descends (prefixWord ++ tailWord_184118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184124 : List Nat := [2, 2, 2, 2, 1, 1, 6, 7]
def baseStart_184124 : Nat := 118140960795 + 184124 * 2 ^ 59
def prefixEnd_184124 : Nat := 4983230072969 + 3 ^ 40 * 184124 * 2
def baseEnd_184124 : Nat := 3501633778834920285305

theorem tailTrace_184124 : CollatzResearch.WordTrace tailWord_184124 prefixEnd_184124 3501633778834920285305 := by
  unfold tailWord_184124
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357776992478834360387713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4477035989971779147183617 3357776992478834360387713)
  ·
    refine ⟨2518332744359125770290785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357776992478834360387713 2518332744359125770290785)
    ·
      refine ⟨1888749558269344327718089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2518332744359125770290785 1888749558269344327718089)
      ·
        refine ⟨1416562168702008245788567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1888749558269344327718089 1416562168702008245788567)
        ·
          refine ⟨2124843253053012368682851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1416562168702008245788567 2124843253053012368682851)
          ·
            refine ⟨3187264879579518553024277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124843253053012368682851 3187264879579518553024277)
            ·
              refine ⟨149403041230289932173013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3187264879579518553024277 149403041230289932173013)
              ·
                refine ⟨3501633778834920285305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149403041230289932173013 3501633778834920285305)
                ·
                  rfl

theorem cell23_184124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 7].length) (baseStart_184124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184124 prefixEnd_184124 := by exact prefixLift 184124
  have htrace : WordTrace (prefixWord ++ tailWord_184124) baseStart_184124 baseEnd_184124 := by
    simpa [prefixWord, tailWord_184124, baseEnd_184124] using wordTrace_append hprefix tailTrace_184124
  have hstable : (prefixWord ++ tailWord_184124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184124).length < 2 ^ (prefixWord ++ tailWord_184124).sum := by decide
  have hdescent : baseEnd_184124 < baseStart_184124 := by decide
  rcases family_descends (prefixWord ++ tailWord_184124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184135 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_184135 : Nat := 118140960795 + 184135 * 2 ^ 59
def prefixEnd_184135 : Nat := 4983230072969 + 3 ^ 40 * 184135 * 2
def baseEnd_184135 : Nat := 94549760315742304665685

theorem tailTrace_184135 : CollatzResearch.WordTrace tailWord_184135 prefixEnd_184135 94549760315742304665685 := by
  unfold tailWord_184135
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715955187917817599425859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477303458611878399617239 6715955187917817599425859)
  ·
    refine ⟨10073932781876726399138789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715955187917817599425859 10073932781876726399138789)
    ·
      refine ⟨1888862396601886199838523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10073932781876726399138789 1888862396601886199838523)
      ·
        refine ⟨2833293594902829299757785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888862396601886199838523 2833293594902829299757785)
        ·
          refine ⟨2124970196177121974818339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2833293594902829299757785 2124970196177121974818339)
          ·
            refine ⟨3187455294265682962227509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124970196177121974818339 3187455294265682962227509)
            ·
              refine ⟨298823933837407777708829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3187455294265682962227509 298823933837407777708829)
              ·
                refine ⟨112058975189027916640811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 298823933837407777708829 112058975189027916640811)
                ·
                  refine ⟨168088462783541874961217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112058975189027916640811 168088462783541874961217)
                  ·
                    refine ⟨126066347087656406220913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168088462783541874961217 126066347087656406220913)
                    ·
                      refine ⟨94549760315742304665685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126066347087656406220913 94549760315742304665685)
                      ·
                        rfl

theorem cell23_184135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_184135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184135 prefixEnd_184135 := by exact prefixLift 184135
  have htrace : WordTrace (prefixWord ++ tailWord_184135) baseStart_184135 baseEnd_184135 := by
    simpa [prefixWord, tailWord_184135, baseEnd_184135] using wordTrace_append hprefix tailTrace_184135
  have hstable : (prefixWord ++ tailWord_184135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184135).length < 2 ^ (prefixWord ++ tailWord_184135).sum := by decide
  have hdescent : baseEnd_184135 < baseStart_184135 := by decide
  rcases family_descends (prefixWord ++ tailWord_184135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
