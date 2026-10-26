import V185TrunkScan23Chunk0030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_184141 : List Nat := [1, 6, 1, 2, 1, 3, 9]
def baseStart_184141 : Nat := 118140960795 + 184141 * 2 ^ 59
def prefixEnd_184141 : Nat := 4983230072969 + 3 ^ 40 * 184141 * 2
def baseEnd_184141 : Nat := 1167319027156410878897

theorem tailTrace_184141 : CollatzResearch.WordTrace tailWord_184141 prefixEnd_184141 1167319027156410878897 := by
  unfold tailWord_184141
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716174025896080624144277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477449350597387082762851 6716174025896080624144277)
  ·
    refine ⟨314820657463878779256763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6716174025896080624144277 314820657463878779256763)
    ·
      refine ⟨472230986195818168885145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 314820657463878779256763 472230986195818168885145)
      ·
        refine ⟨354173239646863626663859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 472230986195818168885145 354173239646863626663859)
        ·
          refine ⟨531259859470295439995789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354173239646863626663859 531259859470295439995789)
          ·
            refine ⟨199222447301360789998421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 531259859470295439995789 199222447301360789998421)
            ·
              refine ⟨1167319027156410878897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 199222447301360789998421 1167319027156410878897)
              ·
                rfl

theorem cell23_184141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 9].length) (baseStart_184141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184141 prefixEnd_184141 := by exact prefixLift 184141
  have htrace : WordTrace (prefixWord ++ tailWord_184141) baseStart_184141 baseEnd_184141 := by
    simpa [prefixWord, tailWord_184141, baseEnd_184141] using wordTrace_append hprefix tailTrace_184141
  have hstable : (prefixWord ++ tailWord_184141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184141).length < 2 ^ (prefixWord ++ tailWord_184141).sum := by decide
  have hdescent : baseEnd_184141 < baseStart_184141 := by decide
  rcases family_descends (prefixWord ++ tailWord_184141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184161 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_184161 : Nat := 118140960795 + 184161 * 2 ^ 59
def prefixEnd_184161 : Nat := 4983230072969 + 3 ^ 40 * 184161 * 2
def baseEnd_184161 : Nat := 94563110812759202940565

theorem tailTrace_184161 : CollatzResearch.WordTrace tailWord_184161 prefixEnd_184161 94563110812759202940565 := by
  unfold tailWord_184161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6716903485823624039872337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4477935657215749359914891 6716903485823624039872337)
  ·
    refine ⟨5037677614367718029904253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6716903485823624039872337 5037677614367718029904253)
    ·
      refine ⟨1889129105387894261214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5037677614367718029904253 1889129105387894261214095)
      ·
        refine ⟨2833693658081841391821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1889129105387894261214095 2833693658081841391821143)
        ·
          refine ⟨4250540487122762087731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833693658081841391821143 4250540487122762087731715)
          ·
            refine ⟨6375810730684143131597573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250540487122762087731715 6375810730684143131597573)
            ·
              refine ⟨1195464512003276837174545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6375810730684143131597573 1195464512003276837174545)
              ·
                refine ⟨896598384002457627880909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195464512003276837174545 896598384002457627880909)
                ·
                  refine ⟨336224394000921610455341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896598384002457627880909 336224394000921610455341)
                  ·
                    refine ⟨126084147750345603920753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336224394000921610455341 126084147750345603920753)
                    ·
                      refine ⟨94563110812759202940565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126084147750345603920753 94563110812759202940565)
                      ·
                        rfl

theorem cell23_184161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_184161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184161 prefixEnd_184161 := by exact prefixLift 184161
  have htrace : WordTrace (prefixWord ++ tailWord_184161) baseStart_184161 baseEnd_184161 := by
    simpa [prefixWord, tailWord_184161, baseEnd_184161] using wordTrace_append hprefix tailTrace_184161
  have hstable : (prefixWord ++ tailWord_184161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184161).length < 2 ^ (prefixWord ++ tailWord_184161).sum := by decide
  have hdescent : baseEnd_184161 < baseStart_184161 := by decide
  rcases family_descends (prefixWord ++ tailWord_184161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184168 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_184168 : Nat := 118140960795 + 184168 * 2 ^ 59
def prefixEnd_184168 : Nat := 4983230072969 + 3 ^ 40 * 184168 * 2
def baseEnd_184168 : Nat := 94566705177340675553033

theorem tailTrace_184168 : CollatzResearch.WordTrace tailWord_184168 prefixEnd_184168 94566705177340675553033 := by
  unfold tailWord_184168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358579398399132117688579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4478105864532176156918105 3358579398399132117688579)
  ·
    refine ⟨5037869097598698176532869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3358579398399132117688579 5037869097598698176532869)
    ·
      refine ⟨944600455799755908099913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5037869097598698176532869 944600455799755908099913)
      ·
        refine ⟨708450341849816931074935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944600455799755908099913 708450341849816931074935)
        ·
          refine ⟨1062675512774725396612403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708450341849816931074935 1062675512774725396612403)
          ·
            refine ⟨1594013269162088094918605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062675512774725396612403 1594013269162088094918605)
            ·
              refine ⟨597754975935783035594477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1594013269162088094918605 597754975935783035594477)
              ·
                refine ⟨224158115975918638347929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 597754975935783035594477 224158115975918638347929)
                ·
                  refine ⟨168118586981938978760947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224158115975918638347929 168118586981938978760947)
                  ·
                    refine ⟨252177880472908468141421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168118586981938978760947 252177880472908468141421)
                    ·
                      refine ⟨94566705177340675553033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252177880472908468141421 94566705177340675553033)
                      ·
                        rfl

theorem cell23_184168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_184168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184168 prefixEnd_184168 := by exact prefixLift 184168
  have htrace : WordTrace (prefixWord ++ tailWord_184168) baseStart_184168 baseEnd_184168 := by
    simpa [prefixWord, tailWord_184168, baseEnd_184168] using wordTrace_append hprefix tailTrace_184168
  have hstable : (prefixWord ++ tailWord_184168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184168).length < 2 ^ (prefixWord ++ tailWord_184168).sum := by decide
  have hdescent : baseEnd_184168 < baseStart_184168 := by decide
  rcases family_descends (prefixWord ++ tailWord_184168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184195 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 1, 3, 2]
def baseStart_184195 : Nat := 118140960795 + 184195 * 2 ^ 59
def prefixEnd_184195 : Nat := 4983230072969 + 3 ^ 40 * 184195 * 2
def baseEnd_184195 : Nat := 94580569155012069915409

theorem tailTrace_184195 : CollatzResearch.WordTrace tailWord_184195 prefixEnd_184195 94580569155012069915409 := by
  unfold tailWord_184195
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718143567700447846610039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4478762378466965231073359 6718143567700447846610039)
  ·
    refine ⟨10077215351550671769915059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6718143567700447846610039 10077215351550671769915059)
    ·
      refine ⟨15115823027326007654872589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10077215351550671769915059 15115823027326007654872589)
      ·
        refine ⟨5668433635247252870577221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15115823027326007654872589 5668433635247252870577221)
        ·
          refine ⟨1062831306608859913233229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5668433635247252870577221 1062831306608859913233229)
          ·
            refine ⟨398561739978322467462461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1062831306608859913233229 398561739978322467462461)
            ·
              refine ⟨149460652491870925298423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 398561739978322467462461 149460652491870925298423)
              ·
                refine ⟨224190978737806387947635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149460652491870925298423 224190978737806387947635)
                ·
                  refine ⟨336286468106709581921453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 224190978737806387947635 336286468106709581921453)
                  ·
                    refine ⟨126107425540016093220545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 336286468106709581921453 126107425540016093220545)
                    ·
                      refine ⟨94580569155012069915409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126107425540016093220545 94580569155012069915409)
                      ·
                        rfl

theorem cell23_184195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_184195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184195 prefixEnd_184195 := by exact prefixLift 184195
  have htrace : WordTrace (prefixWord ++ tailWord_184195) baseStart_184195 baseEnd_184195 := by
    simpa [prefixWord, tailWord_184195, baseEnd_184195] using wordTrace_append hprefix tailTrace_184195
  have hstable : (prefixWord ++ tailWord_184195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184195).length < 2 ^ (prefixWord ++ tailWord_184195).sum := by decide
  have hdescent : baseEnd_184195 < baseStart_184195 := by decide
  rcases family_descends (prefixWord ++ tailWord_184195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184204 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_184204 : Nat := 118140960795 + 184204 * 2 ^ 59
def prefixEnd_184204 : Nat := 4983230072969 + 3 ^ 40 * 184204 * 2
def baseEnd_184204 : Nat := 94585190480902534702867

theorem tailTrace_184204 : CollatzResearch.WordTrace tailWord_184204 prefixEnd_184204 94585190480902534702867 := by
  unfold tailWord_184204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359235912333921191843833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4478981216445228255791777 3359235912333921191843833)
  ·
    refine ⟨2519426934250440893882875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3359235912333921191843833 2519426934250440893882875)
    ·
      refine ⟨3779140401375661340824313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519426934250440893882875 3779140401375661340824313)
      ·
        refine ⟨2834355301031746005618235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779140401375661340824313 2834355301031746005618235)
        ·
          refine ⟨4251532951547619008427353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834355301031746005618235 4251532951547619008427353)
          ·
            refine ⟨3188649713660714256320515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4251532951547619008427353 3188649713660714256320515)
            ·
              refine ⟨4782974570491071384480773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188649713660714256320515 4782974570491071384480773)
              ·
                refine ⟨896807731967075884590145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4782974570491071384480773 896807731967075884590145)
                ·
                  refine ⟨672605798975306913442609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896807731967075884590145 672605798975306913442609)
                  ·
                    refine ⟨504454349231480185081957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672605798975306913442609 504454349231480185081957)
                    ·
                      refine ⟨94585190480902534702867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 504454349231480185081957 94585190480902534702867)
                      ·
                        rfl

theorem cell23_184204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_184204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184204 prefixEnd_184204 := by exact prefixLift 184204
  have htrace : WordTrace (prefixWord ++ tailWord_184204) baseStart_184204 baseEnd_184204 := by
    simpa [prefixWord, tailWord_184204, baseEnd_184204] using wordTrace_append hprefix tailTrace_184204
  have hstable : (prefixWord ++ tailWord_184204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184204).length < 2 ^ (prefixWord ++ tailWord_184204).sum := by decide
  have hdescent : baseEnd_184204 < baseStart_184204 := by decide
  rcases family_descends (prefixWord ++ tailWord_184204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184208 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2]
def baseStart_184208 : Nat := 118140960795 + 184208 * 2 ^ 59
def prefixEnd_184208 : Nat := 4983230072969 + 3 ^ 40 * 184208 * 2
def baseEnd_184208 : Nat := 94587244403520519052849

theorem tailTrace_184208 : CollatzResearch.WordTrace tailWord_184208 prefixEnd_184208 94587244403520519052849 := by
  unfold tailWord_184208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359308858326675533416639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4479078477768900711222185 3359308858326675533416639)
  ·
    refine ⟨5038963287490013300124959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359308858326675533416639 5038963287490013300124959)
    ·
      refine ⟨7558444931235019950187439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5038963287490013300124959 7558444931235019950187439)
      ·
        refine ⟨11337667396852529925281159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558444931235019950187439 11337667396852529925281159)
        ·
          refine ⟨17006501095278794887921739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11337667396852529925281159 17006501095278794887921739)
          ·
            refine ⟨25509751642918192331882609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17006501095278794887921739 25509751642918192331882609)
            ·
              refine ⟨19132313732188644248911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25509751642918192331882609 19132313732188644248911957)
              ·
                refine ⟨224206801549085674791937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 19132313732188644248911957 224206801549085674791937)
                ·
                  refine ⟨168155101161814256093953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224206801549085674791937 168155101161814256093953)
                  ·
                    refine ⟨126116325871360692070465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168155101161814256093953 126116325871360692070465)
                    ·
                      refine ⟨94587244403520519052849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126116325871360692070465 94587244403520519052849)
                      ·
                        rfl

theorem cell23_184208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 2, 2, 2].length) (baseStart_184208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184208 prefixEnd_184208 := by exact prefixLift 184208
  have htrace : WordTrace (prefixWord ++ tailWord_184208) baseStart_184208 baseEnd_184208 := by
    simpa [prefixWord, tailWord_184208, baseEnd_184208] using wordTrace_append hprefix tailTrace_184208
  have hstable : (prefixWord ++ tailWord_184208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184208).length < 2 ^ (prefixWord ++ tailWord_184208).sum := by decide
  have hdescent : baseEnd_184208 < baseStart_184208 := by decide
  rcases family_descends (prefixWord ++ tailWord_184208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184221 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_184221 : Nat := 118140960795 + 184221 * 2 ^ 59
def prefixEnd_184221 : Nat := 4983230072969 + 3 ^ 40 * 184221 * 2
def baseEnd_184221 : Nat := 94593919652028968190289

theorem tailTrace_184221 : CollatzResearch.WordTrace tailWord_184221 prefixEnd_184221 94593919652028968190289 := by
  unfold tailWord_184221
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719091865606254287056517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479394577070836191371011 6719091865606254287056517)
  ·
    refine ⟨1259829724801172678823097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6719091865606254287056517 1259829724801172678823097)
    ·
      refine ⟨944872293600879509117323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259829724801172678823097 944872293600879509117323)
      ·
        refine ⟨1417308440401319263675985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944872293600879509117323 1417308440401319263675985)
        ·
          refine ⟨1062981330300989447756989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1417308440401319263675985 1062981330300989447756989)
          ·
            refine ⟨398617998862871042908871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1062981330300989447756989 398617998862871042908871)
            ·
              refine ⟨597926998294306564363307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398617998862871042908871 597926998294306564363307)
              ·
                refine ⟨896890497441459846544961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597926998294306564363307 896890497441459846544961)
                ·
                  refine ⟨672667873081094884908721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 896890497441459846544961 672667873081094884908721)
                  ·
                    refine ⟨504500904810821163681541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 672667873081094884908721 504500904810821163681541)
                    ·
                      refine ⟨94593919652028968190289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 504500904810821163681541 94593919652028968190289)
                      ·
                        rfl

theorem cell23_184221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_184221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184221 prefixEnd_184221 := by exact prefixLift 184221
  have htrace : WordTrace (prefixWord ++ tailWord_184221) baseStart_184221 baseEnd_184221 := by
    simpa [prefixWord, tailWord_184221, baseEnd_184221] using wordTrace_append hprefix tailTrace_184221
  have hstable : (prefixWord ++ tailWord_184221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184221).length < 2 ^ (prefixWord ++ tailWord_184221).sum := by decide
  have hdescent : baseEnd_184221 < baseStart_184221 := by decide
  rcases family_descends (prefixWord ++ tailWord_184221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184225 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_184225 : Nat := 118140960795 + 184225 * 2 ^ 59
def prefixEnd_184225 : Nat := 4983230072969 + 3 ^ 40 * 184225 * 2
def baseEnd_184225 : Nat := 94595973574646952540271

theorem tailTrace_184225 : CollatzResearch.WordTrace tailWord_184225 prefixEnd_184225 94595973574646952540271 := by
  unfold tailWord_184225
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719237757591762970202129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479491838394508646801419 6719237757591762970202129)
  ·
    refine ⟨5039428318193822227651597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6719237757591762970202129 5039428318193822227651597)
    ·
      refine ⟨1889785619322683335369349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5039428318193822227651597 1889785619322683335369349)
      ·
        refine ⟨354334803623003125381753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1889785619322683335369349 354334803623003125381753)
        ·
          refine ⟨265751102717252344036315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 354334803623003125381753 265751102717252344036315)
          ·
            refine ⟨398626654075878516054473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 265751102717252344036315 398626654075878516054473)
            ·
              refine ⟨298969990556908887040855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 398626654075878516054473 298969990556908887040855)
              ·
                refine ⟨448454985835363330561283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298969990556908887040855 448454985835363330561283)
                ·
                  refine ⟨672682478753044995841925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448454985835363330561283 672682478753044995841925)
                  ·
                    refine ⟨126127964766195936720361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 672682478753044995841925 126127964766195936720361)
                    ·
                      refine ⟨94595973574646952540271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126127964766195936720361 94595973574646952540271)
                      ·
                        rfl

theorem cell23_184225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_184225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184225 prefixEnd_184225 := by exact prefixLift 184225
  have htrace : WordTrace (prefixWord ++ tailWord_184225) baseStart_184225 baseEnd_184225 := by
    simpa [prefixWord, tailWord_184225, baseEnd_184225] using wordTrace_append hprefix tailTrace_184225
  have hstable : (prefixWord ++ tailWord_184225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184225).length < 2 ^ (prefixWord ++ tailWord_184225).sum := by decide
  have hdescent : baseEnd_184225 < baseStart_184225 := by decide
  rcases family_descends (prefixWord ++ tailWord_184225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184231 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 7]
def baseStart_184231 : Nat := 118140960795 + 184231 * 2 ^ 59
def prefixEnd_184231 : Nat := 4983230072969 + 3 ^ 40 * 184231 * 2
def baseEnd_184231 : Nat := 10511006050952658785027

theorem tailTrace_184231 : CollatzResearch.WordTrace tailWord_184231 prefixEnd_184231 10511006050952658785027 := by
  unfold tailWord_184231
  simp only [CollatzResearch.WordTrace]
  refine ⟨6719456595570025994920547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4479637730380017329947031 6719456595570025994920547)
  ·
    refine ⟨10079184893355038992380821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6719456595570025994920547 10079184893355038992380821)
    ·
      refine ⟨472461791876017452767851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10079184893355038992380821 472461791876017452767851)
      ·
        refine ⟨708692687814026179151777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472461791876017452767851 708692687814026179151777)
        ·
          refine ⟨531519515860519634363833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 708692687814026179151777 531519515860519634363833)
          ·
            refine ⟨398639636895389725772875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 531519515860519634363833 398639636895389725772875)
            ·
              refine ⟨597959455343084588659313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 398639636895389725772875 597959455343084588659313)
              ·
                refine ⟨448469591507313441494485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597959455343084588659313 448469591507313441494485)
                ·
                  refine ⟨10511006050952658785027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 448469591507313441494485 10511006050952658785027)
                  ·
                    rfl

theorem cell23_184231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 7].length) (baseStart_184231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184231 prefixEnd_184231 := by exact prefixLift 184231
  have htrace : WordTrace (prefixWord ++ tailWord_184231) baseStart_184231 baseEnd_184231 := by
    simpa [prefixWord, tailWord_184231, baseEnd_184231] using wordTrace_append hprefix tailTrace_184231
  have hstable : (prefixWord ++ tailWord_184231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184231).length < 2 ^ (prefixWord ++ tailWord_184231).sum := by decide
  have hdescent : baseEnd_184231 < baseStart_184231 := by decide
  rcases family_descends (prefixWord ++ tailWord_184231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184304 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 8]
def baseStart_184304 : Nat := 118140960795 + 184304 * 2 ^ 59
def prefixEnd_184304 : Nat := 4983230072969 + 3 ^ 40 * 184304 * 2
def baseEnd_184304 : Nat := 10515170949594682605823

theorem tailTrace_184304 : CollatzResearch.WordTrace tailWord_184304 prefixEnd_184304 10515170949594682605823 := by
  unfold tailWord_184304
  simp only [CollatzResearch.WordTrace]
  refine ⟨3361059562152779731163983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4481412749537039641551977 3361059562152779731163983)
  ·
    refine ⟨5041589343229169596745975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3361059562152779731163983 5041589343229169596745975)
    ·
      refine ⟨7562384014843754395118963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041589343229169596745975 7562384014843754395118963)
      ·
        refine ⟨11343576022265631592678445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562384014843754395118963 11343576022265631592678445)
        ·
          refine ⟨4253841008349611847254417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11343576022265631592678445 4253841008349611847254417)
          ·
            refine ⟨3190380756262208885440813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4253841008349611847254417 3190380756262208885440813)
            ·
              refine ⟨1196392783598328332040305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3190380756262208885440813 1196392783598328332040305)
              ·
                refine ⟨897294587698746249030229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196392783598328332040305 897294587698746249030229)
                ·
                  refine ⟨10515170949594682605823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 897294587698746249030229 10515170949594682605823)
                  ·
                    rfl

theorem cell23_184304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 8].length) (baseStart_184304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184304 prefixEnd_184304 := by exact prefixLift 184304
  have htrace : WordTrace (prefixWord ++ tailWord_184304) baseStart_184304 baseEnd_184304 := by
    simpa [prefixWord, tailWord_184304, baseEnd_184304] using wordTrace_append hprefix tailTrace_184304
  have hstable : (prefixWord ++ tailWord_184304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184304).length < 2 ^ (prefixWord ++ tailWord_184304).sum := by decide
  have hdescent : baseEnd_184304 < baseStart_184304 := by decide
  rcases family_descends (prefixWord ++ tailWord_184304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184321 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 6]
def baseStart_184321 : Nat := 118140960795 + 184321 * 2 ^ 59
def prefixEnd_184321 : Nat := 4983230072969 + 3 ^ 40 * 184321 * 2
def baseEnd_184321 : Nat := 10516140857497619659981

theorem tailTrace_184321 : CollatzResearch.WordTrace tailWord_184321 prefixEnd_184321 10516140857497619659981 := by
  unfold tailWord_184321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722739165243971365696817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4481826110162647577131211 6722739165243971365696817)
  ·
    refine ⟨5042054373932978524272613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6722739165243971365696817 5042054373932978524272613)
    ·
      refine ⟨945385195112433473301115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5042054373932978524272613 945385195112433473301115)
      ·
        refine ⟨1418077792668650209951673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945385195112433473301115 1418077792668650209951673)
        ·
          refine ⟨1063558344501487657463755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418077792668650209951673 1063558344501487657463755)
          ·
            refine ⟨1595337516752231486195633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063558344501487657463755 1595337516752231486195633)
            ·
              refine ⟨1196503137564173614646725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595337516752231486195633 1196503137564173614646725)
              ·
                refine ⟨224344338293282552746261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1196503137564173614646725 224344338293282552746261)
                ·
                  refine ⟨10516140857497619659981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 224344338293282552746261 10516140857497619659981)
                  ·
                    rfl

theorem cell23_184321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 6].length) (baseStart_184321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184321 prefixEnd_184321 := by exact prefixLift 184321
  have htrace : WordTrace (prefixWord ++ tailWord_184321) baseStart_184321 baseEnd_184321 := by
    simpa [prefixWord, tailWord_184321, baseEnd_184321] using wordTrace_append hprefix tailTrace_184321
  have hstable : (prefixWord ++ tailWord_184321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184321).length < 2 ^ (prefixWord ++ tailWord_184321).sum := by decide
  have hdescent : baseEnd_184321 < baseStart_184321 := by decide
  rcases family_descends (prefixWord ++ tailWord_184321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184351 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 3, 5]
def baseStart_184351 : Nat := 118140960795 + 184351 * 2 ^ 59
def prefixEnd_184351 : Nat := 4983230072969 + 3 ^ 40 * 184351 * 2
def baseEnd_184351 : Nat := 31553557379037819854897

theorem tailTrace_184351 : CollatzResearch.WordTrace tailWord_184351 prefixEnd_184351 31553557379037819854897 := by
  unfold tailWord_184351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6723833355135286489288907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4482555570090190992859271 6723833355135286489288907)
  ·
    refine ⟨10085750032702929733933361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6723833355135286489288907 10085750032702929733933361)
    ·
      refine ⟨7564312524527197300450021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10085750032702929733933361 7564312524527197300450021)
      ·
        refine ⟨1418308598348849493834379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7564312524527197300450021 1418308598348849493834379)
        ·
          refine ⟨2127462897523274240751569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418308598348849493834379 2127462897523274240751569)
          ·
            refine ⟨1595597173142455680563677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2127462897523274240751569 1595597173142455680563677)
            ·
              refine ⟨598348939928420880211379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1595597173142455680563677 598348939928420880211379)
              ·
                refine ⟨897523409892631320317069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598348939928420880211379 897523409892631320317069)
                ·
                  refine ⟨336571278709736745118901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897523409892631320317069 336571278709736745118901)
                  ·
                    refine ⟨31553557379037819854897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 336571278709736745118901 31553557379037819854897)
                    ·
                      rfl

theorem cell23_184351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 5].length) (baseStart_184351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184351 prefixEnd_184351 := by exact prefixLift 184351
  have htrace : WordTrace (prefixWord ++ tailWord_184351) baseStart_184351 baseEnd_184351 := by
    simpa [prefixWord, tailWord_184351, baseEnd_184351] using wordTrace_append hprefix tailTrace_184351
  have hstable : (prefixWord ++ tailWord_184351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184351).length < 2 ^ (prefixWord ++ tailWord_184351).sum := by decide
  have hdescent : baseEnd_184351 < baseStart_184351 := by decide
  rcases family_descends (prefixWord ++ tailWord_184351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184381 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_184381 : Nat := 118140960795 + 184381 * 2 ^ 59
def prefixEnd_184381 : Nat := 4983230072969 + 3 ^ 40 * 184381 * 2
def baseEnd_184381 : Nat := 31558692185582780729851

theorem tailTrace_184381 : CollatzResearch.WordTrace tailWord_184381 prefixEnd_184381 31558692185582780729851 := by
  unfold tailWord_184381
  simp only [CollatzResearch.WordTrace]
  refine ⟨6724927545026601612880997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4483285030017734408587331 6724927545026601612880997)
  ·
    refine ⟨1260923914692487802415187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6724927545026601612880997 1260923914692487802415187)
    ·
      refine ⟨1891385872038731703622781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1260923914692487802415187 1891385872038731703622781)
      ·
        refine ⟨709269702014524388858543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1891385872038731703622781 709269702014524388858543)
        ·
          refine ⟨1063904553021786583287815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709269702014524388858543 1063904553021786583287815)
          ·
            refine ⟨1595856829532679874931723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063904553021786583287815 1595856829532679874931723)
            ·
              refine ⟨2393785244299019812397585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1595856829532679874931723 2393785244299019812397585)
              ·
                refine ⟨1795338933224264859298189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2393785244299019812397585 1795338933224264859298189)
                ·
                  refine ⟨673252099959099322236821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1795338933224264859298189 673252099959099322236821)
                  ·
                    refine ⟨31558692185582780729851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 673252099959099322236821 31558692185582780729851)
                    ·
                      rfl

theorem cell23_184381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_184381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184381 prefixEnd_184381 := by exact prefixLift 184381
  have htrace : WordTrace (prefixWord ++ tailWord_184381) baseStart_184381 baseEnd_184381 := by
    simpa [prefixWord, tailWord_184381, baseEnd_184381] using wordTrace_append hprefix tailTrace_184381
  have hstable : (prefixWord ++ tailWord_184381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184381).length < 2 ^ (prefixWord ++ tailWord_184381).sum := by decide
  have hdescent : baseEnd_184381 < baseStart_184381 := by decide
  rcases family_descends (prefixWord ++ tailWord_184381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184391 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_184391 : Nat := 118140960795 + 184391 * 2 ^ 59
def prefixEnd_184391 : Nat := 4983230072969 + 3 ^ 40 * 184391 * 2
def baseEnd_184391 : Nat := 94681211363293303064507

theorem tailTrace_184391 : CollatzResearch.WordTrace tailWord_184391 prefixEnd_184391 94681211363293303064507 := by
  unfold tailWord_184391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725292274990373320745027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4483528183326915547163351 6725292274990373320745027)
  ·
    refine ⟨10087938412485559981117541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6725292274990373320745027 10087938412485559981117541)
    ·
      refine ⟨1891488452341042496459539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10087938412485559981117541 1891488452341042496459539)
      ·
        refine ⟨2837232678511563744689309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891488452341042496459539 2837232678511563744689309)
        ·
          refine ⟨1063962254441836404258491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2837232678511563744689309 1063962254441836404258491)
          ·
            refine ⟨1595943381662754606387737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063962254441836404258491 1595943381662754606387737)
            ·
              refine ⟨1196957536247065954790803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595943381662754606387737 1196957536247065954790803)
              ·
                refine ⟨1795436304370598932186205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196957536247065954790803 1795436304370598932186205)
                ·
                  refine ⟨673288614138974599569827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1795436304370598932186205 673288614138974599569827)
                  ·
                    refine ⟨1009932921208461899354741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 673288614138974599569827 1009932921208461899354741)
                    ·
                      refine ⟨94681211363293303064507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1009932921208461899354741 94681211363293303064507)
                      ·
                        rfl

theorem cell23_184391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_184391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184391 prefixEnd_184391 := by exact prefixLift 184391
  have htrace : WordTrace (prefixWord ++ tailWord_184391) baseStart_184391 baseEnd_184391 := by
    simpa [prefixWord, tailWord_184391, baseEnd_184391] using wordTrace_append hprefix tailTrace_184391
  have hstable : (prefixWord ++ tailWord_184391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184391).length < 2 ^ (prefixWord ++ tailWord_184391).sum := by decide
  have hdescent : baseEnd_184391 < baseStart_184391 := by decide
  rcases family_descends (prefixWord ++ tailWord_184391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184398 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_184398 : Nat := 118140960795 + 184398 * 2 ^ 59
def prefixEnd_184398 : Nat := 4983230072969 + 3 ^ 40 * 184398 * 2
def baseEnd_184398 : Nat := 31561601909291591892325

theorem tailTrace_184398 : CollatzResearch.WordTrace tailWord_184398 prefixEnd_184398 31561601909291591892325 := by
  unfold tailWord_184398
  simp only [CollatzResearch.WordTrace]
  refine ⟨840693448245626689531231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4483698390643342344166565 840693448245626689531231)
  ·
    refine ⟨1261040172368440034296847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840693448245626689531231 1261040172368440034296847)
    ·
      refine ⟨1891560258552660051445271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261040172368440034296847 1891560258552660051445271)
      ·
        refine ⟨2837340387828990077167907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891560258552660051445271 2837340387828990077167907)
        ·
          refine ⟨4256010581743485115751861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837340387828990077167907 4256010581743485115751861)
          ·
            refine ⟨399000992038451729601737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4256010581743485115751861 399000992038451729601737)
            ·
              refine ⟨299250744028838797201303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399000992038451729601737 299250744028838797201303)
              ·
                refine ⟨448876116043258195801955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299250744028838797201303 448876116043258195801955)
                ·
                  refine ⟨673314174064887293702933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 448876116043258195801955 673314174064887293702933)
                  ·
                    refine ⟨31561601909291591892325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 673314174064887293702933 31561601909291591892325)
                    ·
                      rfl

theorem cell23_184398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_184398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184398 prefixEnd_184398 := by exact prefixLift 184398
  have htrace : WordTrace (prefixWord ++ tailWord_184398) baseStart_184398 baseEnd_184398 := by
    simpa [prefixWord, tailWord_184398, baseEnd_184398] using wordTrace_append hprefix tailTrace_184398
  have hstable : (prefixWord ++ tailWord_184398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184398).length < 2 ^ (prefixWord ++ tailWord_184398).sum := by decide
  have hdescent : baseEnd_184398 < baseStart_184398 := by decide
  rcases family_descends (prefixWord ++ tailWord_184398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184405 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 5, 2, 2]
def baseStart_184405 : Nat := 118140960795 + 184405 * 2 ^ 59
def prefixEnd_184405 : Nat := 4983230072969 + 3 ^ 40 * 184405 * 2
def baseEnd_184405 : Nat := 94688400092456248289443

theorem tailTrace_184405 : CollatzResearch.WordTrace tailWord_184405 prefixEnd_184405 94688400092456248289443 := by
  unfold tailWord_184405
  simp only [CollatzResearch.WordTrace]
  refine ⟨6725802896939653711754669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4483868597959769141169779 6725802896939653711754669)
  ·
    refine ⟨2522176086352370141908001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6725802896939653711754669 2522176086352370141908001)
    ·
      refine ⟨1891632064764277606431001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2522176086352370141908001 1891632064764277606431001)
      ·
        refine ⟨1418724048573208204823251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1891632064764277606431001 1418724048573208204823251)
        ·
          refine ⟨2128086072859812307234877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418724048573208204823251 2128086072859812307234877)
          ·
            refine ⟨798032277322429615213079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2128086072859812307234877 798032277322429615213079)
            ·
              refine ⟨1197048415983644422819619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798032277322429615213079 1197048415983644422819619)
              ·
                refine ⟨1795572623975466634229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197048415983644422819619 1795572623975466634229429)
                ·
                  refine ⟨168334933497699996959009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1795572623975466634229429 168334933497699996959009)
                  ·
                    refine ⟨126251200123274997719257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168334933497699996959009 126251200123274997719257)
                    ·
                      refine ⟨94688400092456248289443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126251200123274997719257 94688400092456248289443)
                      ·
                        rfl

theorem cell23_184405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_184405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184405 prefixEnd_184405 := by exact prefixLift 184405
  have htrace : WordTrace (prefixWord ++ tailWord_184405) baseStart_184405 baseEnd_184405 := by
    simpa [prefixWord, tailWord_184405, baseEnd_184405] using wordTrace_append hprefix tailTrace_184405
  have hstable : (prefixWord ++ tailWord_184405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184405).length < 2 ^ (prefixWord ++ tailWord_184405).sum := by decide
  have hdescent : baseEnd_184405 < baseStart_184405 := by decide
  rcases family_descends (prefixWord ++ tailWord_184405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184408 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_184408 : Nat := 118140960795 + 184408 * 2 ^ 59
def prefixEnd_184408 : Nat := 4983230072969 + 3 ^ 40 * 184408 * 2
def baseEnd_184408 : Nat := 94689940534419736551929

theorem tailTrace_184408 : CollatzResearch.WordTrace tailWord_184408 prefixEnd_184408 94689940534419736551929 := by
  unfold tailWord_184408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362956157964392612056939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4483941543952523482742585 3362956157964392612056939)
  ·
    refine ⟨5044434236946588918085409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3362956157964392612056939 5044434236946588918085409)
    ·
      refine ⟨3783325677709941688564057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5044434236946588918085409 3783325677709941688564057)
      ·
        refine ⟨2837494258282456266423043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783325677709941688564057 2837494258282456266423043)
        ·
          refine ⟨4256241387423684399634565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837494258282456266423043 4256241387423684399634565)
          ·
            refine ⟨798045260141940824931481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4256241387423684399634565 798045260141940824931481)
            ·
              refine ⟨598533945106455618698611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798045260141940824931481 598533945106455618698611)
              ·
                refine ⟨897800917659683428047917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598533945106455618698611 897800917659683428047917)
                ·
                  refine ⟨336675344122381285517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897800917659683428047917 336675344122381285517969)
                  ·
                    refine ⟨252506508091785964138477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 336675344122381285517969 252506508091785964138477)
                    ·
                      refine ⟨94689940534419736551929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252506508091785964138477 94689940534419736551929)
                      ·
                        rfl

theorem cell23_184408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_184408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184408 prefixEnd_184408 := by exact prefixLift 184408
  have htrace : WordTrace (prefixWord ++ tailWord_184408) baseStart_184408 baseEnd_184408 := by
    simpa [prefixWord, tailWord_184408, baseEnd_184408] using wordTrace_append hprefix tailTrace_184408
  have hstable : (prefixWord ++ tailWord_184408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184408).length < 2 ^ (prefixWord ++ tailWord_184408).sum := by decide
  have hdescent : baseEnd_184408 < baseStart_184408 := by decide
  rcases family_descends (prefixWord ++ tailWord_184408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184455 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_184455 : Nat := 118140960795 + 184455 * 2 ^ 59
def prefixEnd_184455 : Nat := 4983230072969 + 3 ^ 40 * 184455 * 2
def baseEnd_184455 : Nat := 94714074125181052664213

theorem tailTrace_184455 : CollatzResearch.WordTrace tailWord_184455 prefixEnd_184455 94714074125181052664213 := by
  unfold tailWord_184455
  simp only [CollatzResearch.WordTrace]
  refine ⟨6727626546758512251074819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4485084364505674834049879 6727626546758512251074819)
  ·
    refine ⟨10091439820137768376612229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6727626546758512251074819 10091439820137768376612229)
    ·
      refine ⟨1892144966275831570614793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10091439820137768376612229 1892144966275831570614793)
      ·
        refine ⟨1419108724706873677961095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1892144966275831570614793 1419108724706873677961095)
        ·
          refine ⟨2128663087060310516941643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419108724706873677961095 2128663087060310516941643)
          ·
            refine ⟨3192994630590465775412465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2128663087060310516941643 3192994630590465775412465)
            ·
              refine ⟨2394745972942849331559349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192994630590465775412465 2394745972942849331559349)
              ·
                refine ⟨224507434963392124833689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2394745972942849331559349 224507434963392124833689)
                ·
                  refine ⟨168380576222544093625267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224507434963392124833689 168380576222544093625267)
                  ·
                    refine ⟨252570864333816140437901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168380576222544093625267 252570864333816140437901)
                    ·
                      refine ⟨94714074125181052664213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252570864333816140437901 94714074125181052664213)
                      ·
                        rfl

theorem cell23_184455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_184455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184455 prefixEnd_184455 := by exact prefixLift 184455
  have htrace : WordTrace (prefixWord ++ tailWord_184455) baseStart_184455 baseEnd_184455 := by
    simpa [prefixWord, tailWord_184455, baseEnd_184455] using wordTrace_append hprefix tailTrace_184455
  have hstable : (prefixWord ++ tailWord_184455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184455).length < 2 ^ (prefixWord ++ tailWord_184455).sum := by decide
  have hdescent : baseEnd_184455 < baseStart_184455 := by decide
  rcases family_descends (prefixWord ++ tailWord_184455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184462 : List Nat := [4, 1, 1, 3, 4, 1, 2, 7]
def baseStart_184462 : Nat := 118140960795 + 184462 * 2 ^ 59
def prefixEnd_184462 : Nat := 4983230072969 + 3 ^ 40 * 184462 * 2
def baseEnd_184462 : Nat := 3508061795917130565803

theorem tailTrace_184462 : CollatzResearch.WordTrace tailWord_184462 prefixEnd_184462 3508061795917130565803 := by
  unfold tailWord_184462
  simp only [CollatzResearch.WordTrace]
  refine ⟨840985232216644055822455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4485254571822101631053093 840985232216644055822455)
  ·
    refine ⟨1261477848324966083733683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 840985232216644055822455 1261477848324966083733683)
    ·
      refine ⟨1892216772487449125600525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261477848324966083733683 1892216772487449125600525)
      ·
        refine ⟨709581289682793422100197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1892216772487449125600525 709581289682793422100197)
        ·
          refine ⟨133046491815523766643787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 709581289682793422100197 133046491815523766643787)
          ·
            refine ⟨199569737723285649965681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133046491815523766643787 199569737723285649965681)
            ·
              refine ⟨149677303292464237474261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199569737723285649965681 149677303292464237474261)
              ·
                refine ⟨3508061795917130565803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149677303292464237474261 3508061795917130565803)
                ·
                  rfl

theorem cell23_184462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_184462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184462 prefixEnd_184462 := by exact prefixLift 184462
  have htrace : WordTrace (prefixWord ++ tailWord_184462) baseStart_184462 baseEnd_184462 := by
    simpa [prefixWord, tailWord_184462, baseEnd_184462] using wordTrace_append hprefix tailTrace_184462
  have hstable : (prefixWord ++ tailWord_184462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184462).length < 2 ^ (prefixWord ++ tailWord_184462).sum := by decide
  have hdescent : baseEnd_184462 < baseStart_184462 := by decide
  rcases family_descends (prefixWord ++ tailWord_184462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184498 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_184498 : Nat := 118140960795 + 184498 * 2 ^ 59
def prefixEnd_184498 : Nat := 4983230072969 + 3 ^ 40 * 184498 * 2
def baseEnd_184498 : Nat := 94736153793324384426515

theorem tailTrace_184498 : CollatzResearch.WordTrace tailWord_184498 prefixEnd_184498 94736153793324384426515 := by
  unfold tailWord_184498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682298721400682648722537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4486129923735153729926765 1682298721400682648722537)
  ·
    refine ⟨1261724041050511986541903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1682298721400682648722537 1261724041050511986541903)
    ·
      refine ⟨1892586061575767979812855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261724041050511986541903 1892586061575767979812855)
      ·
        refine ⟨2838879092363651969719283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892586061575767979812855 2838879092363651969719283)
        ·
          refine ⟨4258318638545477954578925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2838879092363651969719283 4258318638545477954578925)
          ·
            refine ⟨1596869489454554232967097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4258318638545477954578925 1596869489454554232967097)
            ·
              refine ⟨1197652117090915674725323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596869489454554232967097 1197652117090915674725323)
              ·
                refine ⟨1796478175636373512087985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197652117090915674725323 1796478175636373512087985)
                ·
                  refine ⟨1347358631727280134065989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1796478175636373512087985 1347358631727280134065989)
                  ·
                    refine ⟨252629743448865025137373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1347358631727280134065989 252629743448865025137373)
                    ·
                      refine ⟨94736153793324384426515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252629743448865025137373 94736153793324384426515)
                      ·
                        rfl

theorem cell23_184498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_184498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184498 prefixEnd_184498 := by exact prefixLift 184498
  have htrace : WordTrace (prefixWord ++ tailWord_184498) baseStart_184498 baseEnd_184498 := by
    simpa [prefixWord, tailWord_184498, baseEnd_184498] using wordTrace_append hprefix tailTrace_184498
  have hstable : (prefixWord ++ tailWord_184498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184498).length < 2 ^ (prefixWord ++ tailWord_184498).sum := by decide
  have hdescent : baseEnd_184498 < baseStart_184498 := by decide
  rcases family_descends (prefixWord ++ tailWord_184498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184500 : List Nat := [2, 5, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_184500 : Nat := 118140960795 + 184500 * 2 ^ 59
def prefixEnd_184500 : Nat := 4983230072969 + 3 ^ 40 * 184500 * 2
def baseEnd_184500 : Nat := 31579060251544458867169

theorem tailTrace_184500 : CollatzResearch.WordTrace tailWord_184500 prefixEnd_184500 31579060251544458867169 := by
  unfold tailWord_184500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3364633915797742468231477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4486178554396989957641969 3364633915797742468231477)
  ·
    refine ⟨315434429606038356396701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3364633915797742468231477 315434429606038356396701)
    ·
      refine ⟨118287911102264383648763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 315434429606038356396701 118287911102264383648763)
      ·
        refine ⟨177431866653396575473145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118287911102264383648763 177431866653396575473145)
        ·
          refine ⟨133073899990047431604859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177431866653396575473145 133073899990047431604859)
          ·
            refine ⟨199610849985071147407289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133073899990047431604859 199610849985071147407289)
            ·
              refine ⟨149708137488803360555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 199610849985071147407289 149708137488803360555467)
              ·
                refine ⟨224562206233205040833201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149708137488803360555467 224562206233205040833201)
                ·
                  refine ⟨168421654674903780624901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224562206233205040833201 168421654674903780624901)
                  ·
                    refine ⟨31579060251544458867169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168421654674903780624901 31579060251544458867169)
                    ·
                      rfl

theorem cell23_184500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_184500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184500 prefixEnd_184500 := by exact prefixLift 184500
  have htrace : WordTrace (prefixWord ++ tailWord_184500) baseStart_184500 baseEnd_184500 := by
    simpa [prefixWord, tailWord_184500, baseEnd_184500] using wordTrace_append hprefix tailTrace_184500
  have hstable : (prefixWord ++ tailWord_184500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184500).length < 2 ^ (prefixWord ++ tailWord_184500).sum := by decide
  have hdescent : baseEnd_184500 < baseStart_184500 := by decide
  rcases family_descends (prefixWord ++ tailWord_184500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184552 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 5]
def baseStart_184552 : Nat := 118140960795 + 184552 * 2 ^ 59
def prefixEnd_184552 : Nat := 4983230072969 + 3 ^ 40 * 184552 * 2
def baseEnd_184552 : Nat := 10529320194296352572363

theorem tailTrace_184552 : CollatzResearch.WordTrace tailWord_184552 prefixEnd_184552 10529320194296352572363 := by
  unfold tailWord_184552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365582213703548908677955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4487442951604731878237273 3365582213703548908677955)
  ·
    refine ⟨5048373320555323363016933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365582213703548908677955 5048373320555323363016933)
    ·
      refine ⟨946569997604123130565675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5048373320555323363016933 946569997604123130565675)
      ·
        refine ⟨1419854996406184695848513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946569997604123130565675 1419854996406184695848513)
        ·
          refine ⟨1064891247304638521886385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1419854996406184695848513 1064891247304638521886385)
          ·
            refine ⟨798668435478478891414789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064891247304638521886385 798668435478478891414789)
            ·
              refine ⟨149750331652214792140273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 798668435478478891414789 149750331652214792140273)
              ·
                refine ⟨112312748739161094105205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149750331652214792140273 112312748739161094105205)
                ·
                  refine ⟨10529320194296352572363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112312748739161094105205 10529320194296352572363)
                  ·
                    rfl

theorem cell23_184552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 5].length) (baseStart_184552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184552 prefixEnd_184552 := by exact prefixLift 184552
  have htrace : WordTrace (prefixWord ++ tailWord_184552) baseStart_184552 baseEnd_184552 := by
    simpa [prefixWord, tailWord_184552, baseEnd_184552] using wordTrace_append hprefix tailTrace_184552
  have hstable : (prefixWord ++ tailWord_184552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184552).length < 2 ^ (prefixWord ++ tailWord_184552).sum := by decide
  have hdescent : baseEnd_184552 < baseStart_184552 := by decide
  rcases family_descends (prefixWord ++ tailWord_184552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184568 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_184568 : Nat := 118140960795 + 184568 * 2 ^ 59
def prefixEnd_184568 : Nat := 4983230072969 + 3 ^ 40 * 184568 * 2
def baseEnd_184568 : Nat := 94772097439139110551193

theorem tailTrace_184568 : CollatzResearch.WordTrace tailWord_184568 prefixEnd_184568 94772097439139110551193 := by
  unfold tailWord_184568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365873997674566274969179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4487831996899421699958905 3365873997674566274969179)
  ·
    refine ⟨5048810996511849412453769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3365873997674566274969179 5048810996511849412453769)
    ·
      refine ⟨3786608247383887059340327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5048810996511849412453769 3786608247383887059340327)
      ·
        refine ⟨5679912371075830589010491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3786608247383887059340327 5679912371075830589010491)
        ·
          refine ⟨8519868556613745883515737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5679912371075830589010491 8519868556613745883515737)
          ·
            refine ⟨6389901417460309412636803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8519868556613745883515737 6389901417460309412636803)
            ·
              refine ⟨9584852126190464118955205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6389901417460309412636803 9584852126190464118955205)
              ·
                refine ⟨1797159773660712022304101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9584852126190464118955205 1797159773660712022304101)
                ·
                  refine ⟨336967457561383504182019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797159773660712022304101 336967457561383504182019)
                  ·
                    refine ⟨505451186342075256273029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336967457561383504182019 505451186342075256273029)
                    ·
                      refine ⟨94772097439139110551193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 505451186342075256273029 94772097439139110551193)
                      ·
                        rfl

theorem cell23_184568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_184568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184568 prefixEnd_184568 := by exact prefixLift 184568
  have htrace : WordTrace (prefixWord ++ tailWord_184568) baseStart_184568 baseEnd_184568 := by
    simpa [prefixWord, tailWord_184568, baseEnd_184568] using wordTrace_append hprefix tailTrace_184568
  have hstable : (prefixWord ++ tailWord_184568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184568).length < 2 ^ (prefixWord ++ tailWord_184568).sum := by decide
  have hdescent : baseEnd_184568 < baseStart_184568 := by decide
  rcases family_descends (prefixWord ++ tailWord_184568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184585 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 4]
def baseStart_184585 : Nat := 118140960795 + 184585 * 2 ^ 59
def prefixEnd_184585 : Nat := 4983230072969 + 3 ^ 40 * 184585 * 2
def baseEnd_184585 : Nat := 94780826610265544038615

theorem tailTrace_184585 : CollatzResearch.WordTrace tailWord_184585 prefixEnd_184585 94780826610265544038615 := by
  unfold tailWord_184585
  simp only [CollatzResearch.WordTrace]
  refine ⟨6732368036287544453307209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4488245357525029635538139 6732368036287544453307209)
  ·
    refine ⟨5049276027215658339980407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6732368036287544453307209 5049276027215658339980407)
    ·
      refine ⟨7573914040823487509970611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5049276027215658339980407 7573914040823487509970611)
      ·
        refine ⟨11360871061235231264955917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573914040823487509970611 11360871061235231264955917)
        ·
          refine ⟨4260326647963211724358469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11360871061235231264955917 4260326647963211724358469)
          ·
            refine ⟨798811246493102198317213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4260326647963211724358469 798811246493102198317213)
            ·
              refine ⟨299554217434913324368955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 798811246493102198317213 299554217434913324368955)
              ·
                refine ⟨449331326152369986553433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299554217434913324368955 449331326152369986553433)
                ·
                  refine ⟨336998494614277489915075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449331326152369986553433 336998494614277489915075)
                  ·
                    refine ⟨505497741921416234872613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 336998494614277489915075 505497741921416234872613)
                    ·
                      refine ⟨94780826610265544038615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 505497741921416234872613 94780826610265544038615)
                      ·
                        rfl

theorem cell23_184585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_184585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184585 prefixEnd_184585 := by exact prefixLift 184585
  have htrace : WordTrace (prefixWord ++ tailWord_184585) baseStart_184585 baseEnd_184585 := by
    simpa [prefixWord, tailWord_184585, baseEnd_184585] using wordTrace_append hprefix tailTrace_184585
  have hstable : (prefixWord ++ tailWord_184585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184585).length < 2 ^ (prefixWord ++ tailWord_184585).sum := by decide
  have hdescent : baseEnd_184585 < baseStart_184585 := by decide
  rcases family_descends (prefixWord ++ tailWord_184585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184612 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_184612 : Nat := 118140960795 + 184612 * 2 ^ 59
def prefixEnd_184612 : Nat := 4983230072969 + 3 ^ 40 * 184612 * 2
def baseEnd_184612 : Nat := 31598230195978979466997

theorem tailTrace_184612 : CollatzResearch.WordTrace tailWord_184612 prefixEnd_184612 31598230195978979466997 := by
  unfold tailWord_184612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366676403594864032270045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4488901871459818709693393 3366676403594864032270045)
  ·
    refine ⟨1262503651348074012101267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3366676403594864032270045 1262503651348074012101267)
    ·
      refine ⟨1893755477022111018151901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262503651348074012101267 1893755477022111018151901)
      ·
        refine ⟨710158303883291631806963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1893755477022111018151901 710158303883291631806963)
        ·
          refine ⟨1065237455824937447710445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710158303883291631806963 1065237455824937447710445)
          ·
            refine ⟨399464045934351542891417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1065237455824937447710445 399464045934351542891417)
            ·
              refine ⟨299598034450763657168563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 399464045934351542891417 299598034450763657168563)
              ·
                refine ⟨449397051676145485752845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299598034450763657168563 449397051676145485752845)
                ·
                  refine ⟨168523894378554557157317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 449397051676145485752845 168523894378554557157317)
                  ·
                    refine ⟨31598230195978979466997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168523894378554557157317 31598230195978979466997)
                    ·
                      rfl

theorem cell23_184612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_184612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184612 prefixEnd_184612 := by exact prefixLift 184612
  have htrace : WordTrace (prefixWord ++ tailWord_184612) baseStart_184612 baseEnd_184612 := by
    simpa [prefixWord, tailWord_184612, baseEnd_184612] using wordTrace_append hprefix tailTrace_184612
  have hstable : (prefixWord ++ tailWord_184612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184612).length < 2 ^ (prefixWord ++ tailWord_184612).sum := by decide
  have hdescent : baseEnd_184612 < baseStart_184612 := by decide
  rcases family_descends (prefixWord ++ tailWord_184612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184675 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4]
def baseStart_184675 : Nat := 118140960795 + 184675 * 2 ^ 59
def prefixEnd_184675 : Nat := 4983230072969 + 3 ^ 40 * 184675 * 2
def baseEnd_184675 : Nat := 94827039869170191913201

theorem tailTrace_184675 : CollatzResearch.WordTrace tailWord_184675 prefixEnd_184675 94827039869170191913201 := by
  unfold tailWord_184675
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735650605961489824083479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4490433737307659882722319 6735650605961489824083479)
  ·
    refine ⟨10103475908942234736125219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6735650605961489824083479 10103475908942234736125219)
    ·
      refine ⟨15155213863413352104187829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10103475908942234736125219 15155213863413352104187829)
      ·
        refine ⟨1420801299695001759767609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15155213863413352104187829 1420801299695001759767609)
        ·
          refine ⟨1065600974771251319825707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420801299695001759767609 1065600974771251319825707)
          ·
            refine ⟨1598401462156876979738561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065600974771251319825707 1598401462156876979738561)
            ·
              refine ⟨1198801096617657734803921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598401462156876979738561 1198801096617657734803921)
              ·
                refine ⟨899100822463243301102941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198801096617657734803921 899100822463243301102941)
                ·
                  refine ⟨337162808423716237913603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899100822463243301102941 337162808423716237913603)
                  ·
                    refine ⟨505744212635574356870405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 337162808423716237913603 505744212635574356870405)
                    ·
                      refine ⟨94827039869170191913201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 505744212635574356870405 94827039869170191913201)
                      ·
                        rfl

theorem cell23_184675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_184675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184675 prefixEnd_184675 := by exact prefixLift 184675
  have htrace : WordTrace (prefixWord ++ tailWord_184675) baseStart_184675 baseEnd_184675 := by
    simpa [prefixWord, tailWord_184675, baseEnd_184675] using wordTrace_append hprefix tailTrace_184675
  have hstable : (prefixWord ++ tailWord_184675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184675).length < 2 ^ (prefixWord ++ tailWord_184675).sum := by decide
  have hdescent : baseEnd_184675 < baseStart_184675 := by decide
  rcases family_descends (prefixWord ++ tailWord_184675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184685 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_184685 : Nat := 118140960795 + 184685 * 2 ^ 59
def prefixEnd_184685 : Nat := 4983230072969 + 3 ^ 40 * 184685 * 2
def baseEnd_184685 : Nat := 31610724891905050929385

theorem tailTrace_184685 : CollatzResearch.WordTrace tailWord_184685 prefixEnd_184685 31610724891905050929385 := by
  unfold tailWord_184685
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736015335925261531947509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4490676890616841021298339 6736015335925261531947509)
  ·
    refine ⟨631501437742993268620079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6736015335925261531947509 631501437742993268620079)
    ·
      refine ⟨947252156614489902930119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 631501437742993268620079 947252156614489902930119)
      ·
        refine ⟨1420878234921734854395179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947252156614489902930119 1420878234921734854395179)
        ·
          refine ⟨2131317352382602281592769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420878234921734854395179 2131317352382602281592769)
          ·
            refine ⟨1598488014286951711194577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131317352382602281592769 1598488014286951711194577)
            ·
              refine ⟨1198866010715213783395933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598488014286951711194577 1198866010715213783395933)
              ·
                refine ⟨449574754018205168773475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198866010715213783395933 449574754018205168773475)
                ·
                  refine ⟨674362131027307753160213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449574754018205168773475 674362131027307753160213)
                  ·
                    refine ⟨31610724891905050929385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 674362131027307753160213 31610724891905050929385)
                    ·
                      rfl

theorem cell23_184685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_184685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184685 prefixEnd_184685 := by exact prefixLift 184685
  have htrace : WordTrace (prefixWord ++ tailWord_184685) baseStart_184685 baseEnd_184685 := by
    simpa [prefixWord, tailWord_184685, baseEnd_184685] using wordTrace_append hprefix tailTrace_184685
  have hstable : (prefixWord ++ tailWord_184685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184685).length < 2 ^ (prefixWord ++ tailWord_184685).sum := by decide
  have hdescent : baseEnd_184685 < baseStart_184685 := by decide
  rcases family_descends (prefixWord ++ tailWord_184685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184725 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_184725 : Nat := 118140960795 + 184725 * 2 ^ 59
def prefixEnd_184725 : Nat := 4983230072969 + 3 ^ 40 * 184725 * 2
def baseEnd_184725 : Nat := 94852713901894996287971

theorem tailTrace_184725 : CollatzResearch.WordTrace tailWord_184725 prefixEnd_184725 94852713901894996287971 := by
  unfold tailWord_184725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737474255780348363403629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4491649503853565575602419 6737474255780348363403629)
  ·
    refine ⟨2526552845917630636276361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6737474255780348363403629 2526552845917630636276361)
    ·
      refine ⟨1894914634438222977207271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2526552845917630636276361 1894914634438222977207271)
      ·
        refine ⟨2842371951657334465810907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894914634438222977207271 2842371951657334465810907)
        ·
          refine ⟨4263557927486001698716361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842371951657334465810907 4263557927486001698716361)
          ·
            refine ⟨3197668445614501274037271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4263557927486001698716361 3197668445614501274037271)
            ·
              refine ⟨4796502668421751911055907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3197668445614501274037271 4796502668421751911055907)
              ·
                refine ⟨7194754002632627866583861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4796502668421751911055907 7194754002632627866583861)
                ·
                  refine ⟨674508187746808862492237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7194754002632627866583861 674508187746808862492237)
                  ·
                    refine ⟨252940570405053323434589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 674508187746808862492237 252940570405053323434589)
                    ·
                      refine ⟨94852713901894996287971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 252940570405053323434589 94852713901894996287971)
                      ·
                        rfl

theorem cell23_184725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_184725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184725 prefixEnd_184725 := by exact prefixLift 184725
  have htrace : WordTrace (prefixWord ++ tailWord_184725) baseStart_184725 baseEnd_184725 := by
    simpa [prefixWord, tailWord_184725, baseEnd_184725] using wordTrace_append hprefix tailTrace_184725
  have hstable : (prefixWord ++ tailWord_184725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184725).length < 2 ^ (prefixWord ++ tailWord_184725).sum := by decide
  have hdescent : baseEnd_184725 < baseStart_184725 := by decide
  rcases family_descends (prefixWord ++ tailWord_184725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184749 : List Nat := [1, 5, 2, 2, 2, 1, 3, 7]
def baseStart_184749 : Nat := 118140960795 + 184749 * 2 ^ 59
def prefixEnd_184749 : Nat := 4983230072969 + 3 ^ 40 * 184749 * 2
def baseEnd_184749 : Nat := 3513519905096403792143

theorem tailTrace_184749 : CollatzResearch.WordTrace tailWord_184749 prefixEnd_184749 3513519905096403792143 := by
  unfold tailWord_184749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738349607693400462277301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492233071795600308184867 6738349607693400462277301)
  ·
    refine ⟨631720275721256293338497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6738349607693400462277301 631720275721256293338497)
    ·
      refine ⟨473790206790942220003873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 631720275721256293338497 473790206790942220003873)
      ·
        refine ⟨355342655093206665002905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 473790206790942220003873 355342655093206665002905)
        ·
          refine ⟨266506991319904998752179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355342655093206665002905 266506991319904998752179)
          ·
            refine ⟨399760486979857498128269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266506991319904998752179 399760486979857498128269)
            ·
              refine ⟨149910182617446561798101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399760486979857498128269 149910182617446561798101)
              ·
                refine ⟨3513519905096403792143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149910182617446561798101 3513519905096403792143)
                ·
                  rfl

theorem cell23_184749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 7].length) (baseStart_184749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184749 prefixEnd_184749 := by exact prefixLift 184749
  have htrace : WordTrace (prefixWord ++ tailWord_184749) baseStart_184749 baseEnd_184749 := by
    simpa [prefixWord, tailWord_184749, baseEnd_184749] using wordTrace_append hprefix tailTrace_184749
  have hstable : (prefixWord ++ tailWord_184749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184749).length < 2 ^ (prefixWord ++ tailWord_184749).sum := by decide
  have hdescent : baseEnd_184749 < baseStart_184749 := by decide
  rcases family_descends (prefixWord ++ tailWord_184749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184775 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 2, 6]
def baseStart_184775 : Nat := 118140960795 + 184775 * 2 ^ 59
def prefixEnd_184775 : Nat := 4983230072969 + 3 ^ 40 * 184775 * 2
def baseEnd_184775 : Nat := 31626129311539933554247

theorem tailTrace_184775 : CollatzResearch.WordTrace tailWord_184775 prefixEnd_184775 31626129311539933554247 := by
  unfold tailWord_184775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739297905599206902723779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4492865270399471268482519 6739297905599206902723779)
  ·
    refine ⟨10108946858398810354085669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6739297905599206902723779 10108946858398810354085669)
    ·
      refine ⟨1895427535949776941391063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10108946858398810354085669 1895427535949776941391063)
      ·
        refine ⟨2843141303924665412086595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895427535949776941391063 2843141303924665412086595)
        ·
          refine ⟨4264711955886998118129893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2843141303924665412086595 4264711955886998118129893)
          ·
            refine ⟨799633491728812147149355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4264711955886998118129893 799633491728812147149355)
            ·
              refine ⟨1199450237593218220724033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799633491728812147149355 1199450237593218220724033)
              ·
                refine ⟨899587678194913665543025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199450237593218220724033 899587678194913665543025)
                ·
                  refine ⟨674690758646185249157269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 899587678194913665543025 674690758646185249157269)
                  ·
                    refine ⟨31626129311539933554247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 674690758646185249157269 31626129311539933554247)
                    ·
                      rfl

theorem cell23_184775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_184775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184775 prefixEnd_184775 := by exact prefixLift 184775
  have htrace : WordTrace (prefixWord ++ tailWord_184775) baseStart_184775 baseEnd_184775 := by
    simpa [prefixWord, tailWord_184775, baseEnd_184775] using wordTrace_append hprefix tailTrace_184775
  have hstable : (prefixWord ++ tailWord_184775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184775).length < 2 ^ (prefixWord ++ tailWord_184775).sum := by decide
  have hdescent : baseEnd_184775 < baseStart_184775 := by decide
  rcases family_descends (prefixWord ++ tailWord_184775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184776 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_184776 : Nat := 118140960795 + 184776 * 2 ^ 59
def prefixEnd_184776 : Nat := 4983230072969 + 3 ^ 40 * 184776 * 2
def baseEnd_184776 : Nat := 94878901415274296750237

theorem tailTrace_184776 : CollatzResearch.WordTrace tailWord_184776 prefixEnd_184776 94878901415274296750237 := by
  unfold tailWord_184776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369667189297792036755091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4492889585730389382340121 3369667189297792036755091)
  ·
    refine ⟨5054500783946688055132637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369667189297792036755091 5054500783946688055132637)
    ·
      refine ⟨1895437793980008020674739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5054500783946688055132637 1895437793980008020674739)
      ·
        refine ⟨2843156690970012031012109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1895437793980008020674739 2843156690970012031012109)
        ·
          refine ⟨1066183759113754511629541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843156690970012031012109 1066183759113754511629541)
          ·
            refine ⟨199909454833828970930539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1066183759113754511629541 199909454833828970930539)
            ·
              refine ⟨299864182250743456395809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199909454833828970930539 299864182250743456395809)
              ·
                refine ⟨224898136688057592296857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 299864182250743456395809 224898136688057592296857)
                ·
                  refine ⟨168673602516043194222643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 224898136688057592296857 168673602516043194222643)
                  ·
                    refine ⟨253010403774064791333965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168673602516043194222643 253010403774064791333965)
                    ·
                      refine ⟨94878901415274296750237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 253010403774064791333965 94878901415274296750237)
                      ·
                        rfl

theorem cell23_184776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_184776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184776 prefixEnd_184776 := by exact prefixLift 184776
  have htrace : WordTrace (prefixWord ++ tailWord_184776) baseStart_184776 baseEnd_184776 := by
    simpa [prefixWord, tailWord_184776, baseEnd_184776] using wordTrace_append hprefix tailTrace_184776
  have hstable : (prefixWord ++ tailWord_184776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184776).length < 2 ^ (prefixWord ++ tailWord_184776).sum := by decide
  have hdescent : baseEnd_184776 < baseStart_184776 := by decide
  rcases family_descends (prefixWord ++ tailWord_184776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184785 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_184785 : Nat := 118140960795 + 184785 * 2 ^ 59
def prefixEnd_184785 : Nat := 4983230072969 + 3 ^ 40 * 184785 * 2
def baseEnd_184785 : Nat := 94883522741164761537695

theorem tailTrace_184785 : CollatzResearch.WordTrace tailWord_184785 prefixEnd_184785 94883522741164761537695 := by
  unfold tailWord_184785
  simp only [CollatzResearch.WordTrace]
  refine ⟨6739662635562978610587809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4493108423708652407058539 6739662635562978610587809)
  ·
    refine ⟨5054746976672233957940857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6739662635562978610587809 5054746976672233957940857)
    ·
      refine ⟨3791060232504175468455643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5054746976672233957940857 3791060232504175468455643)
      ·
        refine ⟨5686590348756263202683465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791060232504175468455643 5686590348756263202683465)
        ·
          refine ⟨4264942761567197402012599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5686590348756263202683465 4264942761567197402012599)
          ·
            refine ⟨6397414142350796103018899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264942761567197402012599 6397414142350796103018899)
            ·
              refine ⟨9596121213526194154528349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6397414142350796103018899 9596121213526194154528349)
              ·
                refine ⟨3598545455072322807948131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9596121213526194154528349 3598545455072322807948131)
                ·
                  refine ⟨5397818182608484211922197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3598545455072322807948131 5397818182608484211922197)
                  ·
                    refine ⟨253022727309772697433853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5397818182608484211922197 253022727309772697433853)
                    ·
                      refine ⟨94883522741164761537695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 253022727309772697433853 94883522741164761537695)
                      ·
                        rfl

theorem cell23_184785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_184785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184785 prefixEnd_184785 := by exact prefixLift 184785
  have htrace : WordTrace (prefixWord ++ tailWord_184785) baseStart_184785 baseEnd_184785 := by
    simpa [prefixWord, tailWord_184785, baseEnd_184785] using wordTrace_append hprefix tailTrace_184785
  have hstable : (prefixWord ++ tailWord_184785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184785).length < 2 ^ (prefixWord ++ tailWord_184785).sum := by decide
  have hdescent : baseEnd_184785 < baseStart_184785 := by decide
  rcases family_descends (prefixWord ++ tailWord_184785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184799 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 1, 4, 2]
def baseStart_184799 : Nat := 118140960795 + 184799 * 2 ^ 59
def prefixEnd_184799 : Nat := 4983230072969 + 3 ^ 40 * 184799 * 2
def baseEnd_184799 : Nat := 94890711470327706762631

theorem tailTrace_184799 : CollatzResearch.WordTrace tailWord_184799 prefixEnd_184799 94890711470327706762631 := by
  unfold tailWord_184799
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740173257512259001597451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4493448838341506001064967 6740173257512259001597451)
  ·
    refine ⟨10110259886268388502396177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6740173257512259001597451 10110259886268388502396177)
    ·
      refine ⟨7582694914701291376797133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10110259886268388502396177 7582694914701291376797133)
      ·
        refine ⟨2843510593012984266298925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7582694914701291376797133 2843510593012984266298925)
        ·
          refine ⟨1066316472379869099862097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843510593012984266298925 1066316472379869099862097)
          ·
            refine ⟨799737354284901824896573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066316472379869099862097 799737354284901824896573)
            ·
              refine ⟨299901507856838184336215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 799737354284901824896573 299901507856838184336215)
              ·
                refine ⟨449852261785257276504323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299901507856838184336215 449852261785257276504323)
                ·
                  refine ⟨674778392677885914756485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 449852261785257276504323 674778392677885914756485)
                  ·
                    refine ⟨126520948627103609016841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 674778392677885914756485 126520948627103609016841)
                    ·
                      refine ⟨94890711470327706762631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126520948627103609016841 94890711470327706762631)
                      ·
                        rfl

theorem cell23_184799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_184799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184799 prefixEnd_184799 := by exact prefixLift 184799
  have htrace : WordTrace (prefixWord ++ tailWord_184799) baseStart_184799 baseEnd_184799 := by
    simpa [prefixWord, tailWord_184799, baseEnd_184799] using wordTrace_append hprefix tailTrace_184799
  have hstable : (prefixWord ++ tailWord_184799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184799).length < 2 ^ (prefixWord ++ tailWord_184799).sum := by decide
  have hdescent : baseEnd_184799 < baseStart_184799 := by decide
  rcases family_descends (prefixWord ++ tailWord_184799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184839 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 7]
def baseStart_184839 : Nat := 118140960795 + 184839 * 2 ^ 59
def prefixEnd_184839 : Nat := 4983230072969 + 3 ^ 40 * 184839 * 2
def baseEnd_184839 : Nat := 10545694521834172251383

theorem tailTrace_184839 : CollatzResearch.WordTrace tailWord_184839 prefixEnd_184839 10545694521834172251383 := by
  unfold tailWord_184839
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741632177367345833053571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4494421451578230555369047 6741632177367345833053571)
  ·
    refine ⟨10112448266051018749580357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6741632177367345833053571 10112448266051018749580357)
    ·
      refine ⟨1896084049884566015546317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10112448266051018749580357 1896084049884566015546317)
      ·
        refine ⟨711031518706712255829869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1896084049884566015546317 711031518706712255829869)
        ·
          refine ⟨266636819515017095936201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 711031518706712255829869 266636819515017095936201)
          ·
            refine ⟨199977614636262821952151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266636819515017095936201 199977614636262821952151)
            ·
              refine ⟨299966421954394232928227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 199977614636262821952151 299966421954394232928227)
              ·
                refine ⟨449949632931591349392341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 299966421954394232928227 449949632931591349392341)
                ·
                  refine ⟨10545694521834172251383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 449949632931591349392341 10545694521834172251383)
                  ·
                    rfl

theorem cell23_184839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 7].length) (baseStart_184839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184839 prefixEnd_184839 := by exact prefixLift 184839
  have htrace : WordTrace (prefixWord ++ tailWord_184839) baseStart_184839 baseEnd_184839 := by
    simpa [prefixWord, tailWord_184839, baseEnd_184839] using wordTrace_append hprefix tailTrace_184839
  have hstable : (prefixWord ++ tailWord_184839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184839).length < 2 ^ (prefixWord ++ tailWord_184839).sum := by decide
  have hdescent : baseEnd_184839 < baseStart_184839 := by decide
  rcases family_descends (prefixWord ++ tailWord_184839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184889 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 2, 4, 2]
def baseStart_184889 : Nat := 118140960795 + 184889 * 2 ^ 59
def prefixEnd_184889 : Nat := 4983230072969 + 3 ^ 40 * 184889 * 2
def baseEnd_184889 : Nat := 94936924729232354637217

theorem tailTrace_184889 : CollatzResearch.WordTrace tailWord_184889 prefixEnd_184889 94936924729232354637217 := by
  unfold tailWord_184889
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743455827186204372373721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4495637218124136248249147 6743455827186204372373721)
  ·
    refine ⟨5057591870389653279280291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6743455827186204372373721 5057591870389653279280291)
    ·
      refine ⟨7586387805584479918920437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057591870389653279280291 7586387805584479918920437)
      ·
        refine ⟨711223856773544992398791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7586387805584479918920437 711223856773544992398791)
        ·
          refine ⟨1066835785160317488598187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711223856773544992398791 1066835785160317488598187)
          ·
            refine ⟨1600253677740476232897281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066835785160317488598187 1600253677740476232897281)
            ·
              refine ⟨1200190258305357174672961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600253677740476232897281 1200190258305357174672961)
              ·
                refine ⟨900142693729017881004721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200190258305357174672961 900142693729017881004721)
                ·
                  refine ⟨675107020296763410753541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900142693729017881004721 675107020296763410753541)
                  ·
                    refine ⟨126582566305643139516289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675107020296763410753541 126582566305643139516289)
                    ·
                      refine ⟨94936924729232354637217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126582566305643139516289 94936924729232354637217)
                      ·
                        rfl

theorem cell23_184889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_184889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184889 prefixEnd_184889 := by exact prefixLift 184889
  have htrace : WordTrace (prefixWord ++ tailWord_184889) baseStart_184889 baseEnd_184889 := by
    simpa [prefixWord, tailWord_184889, baseEnd_184889] using wordTrace_append hprefix tailTrace_184889
  have hstable : (prefixWord ++ tailWord_184889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184889).length < 2 ^ (prefixWord ++ tailWord_184889).sum := by decide
  have hdescent : baseEnd_184889 < baseStart_184889 := by decide
  rcases family_descends (prefixWord ++ tailWord_184889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184933 : List Nat := [1, 3, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_184933 : Nat := 118140960795 + 184933 * 2 ^ 59
def prefixEnd_184933 : Nat := 4983230072969 + 3 ^ 40 * 184933 * 2
def baseEnd_184933 : Nat := 31653172626010060829005

theorem tailTrace_184933 : CollatzResearch.WordTrace tailWord_184933 prefixEnd_184933 31653172626010060829005 := by
  unfold tailWord_184933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745060639026799886975453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4496707092684533257983635 6745060639026799886975453)
  ·
    refine ⟨2529397739635049957615795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6745060639026799886975453 2529397739635049957615795)
    ·
      refine ⟨3794096609452574936423693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529397739635049957615795 3794096609452574936423693)
      ·
        refine ⟨1422786228544715601158885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3794096609452574936423693 1422786228544715601158885)
        ·
          refine ⟨266772417852134175217291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1422786228544715601158885 266772417852134175217291)
          ·
            refine ⟨400158626778201262825937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266772417852134175217291 400158626778201262825937)
            ·
              refine ⟨300118970083650947119453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400158626778201262825937 300118970083650947119453)
              ·
                refine ⟨112544613781369105169795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300118970083650947119453 112544613781369105169795)
                ·
                  refine ⟨168816920672053657754693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112544613781369105169795 168816920672053657754693)
                  ·
                    refine ⟨31653172626010060829005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168816920672053657754693 31653172626010060829005)
                    ·
                      rfl

theorem cell23_184933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_184933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184933 prefixEnd_184933 := by exact prefixLift 184933
  have htrace : WordTrace (prefixWord ++ tailWord_184933) baseStart_184933 baseEnd_184933 := by
    simpa [prefixWord, tailWord_184933, baseEnd_184933] using wordTrace_append hprefix tailTrace_184933
  have hstable : (prefixWord ++ tailWord_184933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184933).length < 2 ^ (prefixWord ++ tailWord_184933).sum := by decide
  have hdescent : baseEnd_184933 < baseStart_184933 := by decide
  rcases family_descends (prefixWord ++ tailWord_184933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184946 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_184946 : Nat := 118140960795 + 184946 * 2 ^ 59
def prefixEnd_184946 : Nat := 4983230072969 + 3 ^ 40 * 184946 * 2
def baseEnd_184946 : Nat := 10551799236282070180495

theorem tailTrace_184946 : CollatzResearch.WordTrace tailWord_184946 prefixEnd_184946 10551799236282070180495 := by
  unfold tailWord_184946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686383696994925776799673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4497023191986468738132461 1686383696994925776799673)
  ·
    refine ⟨1264787772746194332599755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1686383696994925776799673 1264787772746194332599755)
    ·
      refine ⟨1897181659119291498899633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264787772746194332599755 1897181659119291498899633)
      ·
        refine ⟨1422886244339468624174725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897181659119291498899633 1422886244339468624174725)
        ·
          refine ⟨266791170813650367032761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1422886244339468624174725 266791170813650367032761)
          ·
            refine ⟨200093378110237775274571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266791170813650367032761 200093378110237775274571)
            ·
              refine ⟨300140067165356662911857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200093378110237775274571 300140067165356662911857)
              ·
                refine ⟨225105050374017497183893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300140067165356662911857 225105050374017497183893)
                ·
                  refine ⟨10551799236282070180495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225105050374017497183893 10551799236282070180495)
                  ·
                    rfl

theorem cell23_184946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_184946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184946 prefixEnd_184946 := by exact prefixLift 184946
  have htrace : WordTrace (prefixWord ++ tailWord_184946) baseStart_184946 baseEnd_184946 := by
    simpa [prefixWord, tailWord_184946, baseEnd_184946] using wordTrace_append hprefix tailTrace_184946
  have hstable : (prefixWord ++ tailWord_184946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184946).length < 2 ^ (prefixWord ++ tailWord_184946).sum := by decide
  have hdescent : baseEnd_184946 < baseStart_184946 := by decide
  rcases family_descends (prefixWord ++ tailWord_184946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184972 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_184972 : Nat := 118140960795 + 184972 * 2 ^ 59
def prefixEnd_184972 : Nat := 4983230072969 + 3 ^ 40 * 184972 * 2
def baseEnd_184972 : Nat := 31659847874518509966445

theorem tailTrace_184972 : CollatzResearch.WordTrace tailWord_184972 prefixEnd_184972 31659847874518509966445 := by
  unfold tailWord_184972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3373241542942754773822585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4497655390590339698430113 3373241542942754773822585)
  ·
    refine ⟨2529931157207066080366939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3373241542942754773822585 2529931157207066080366939)
    ·
      refine ⟨3794896735810599120550409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2529931157207066080366939 3794896735810599120550409)
      ·
        refine ⟨2846172551857949340412807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794896735810599120550409 2846172551857949340412807)
        ·
          refine ⟨4269258827786924010619211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846172551857949340412807 4269258827786924010619211)
          ·
            refine ⟨6403888241680386015928817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269258827786924010619211 6403888241680386015928817)
            ·
              refine ⟨4802916181260289511946613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6403888241680386015928817 4802916181260289511946613)
              ·
                refine ⟨450273391993152141744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4802916181260289511946613 450273391993152141744995)
                ·
                  refine ⟨675410087989728212617493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450273391993152141744995 675410087989728212617493)
                  ·
                    refine ⟨31659847874518509966445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 675410087989728212617493 31659847874518509966445)
                    ·
                      rfl

theorem cell23_184972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_184972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184972 prefixEnd_184972 := by exact prefixLift 184972
  have htrace : WordTrace (prefixWord ++ tailWord_184972) baseStart_184972 baseEnd_184972 := by
    simpa [prefixWord, tailWord_184972, baseEnd_184972] using wordTrace_append hprefix tailTrace_184972
  have hstable : (prefixWord ++ tailWord_184972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184972).length < 2 ^ (prefixWord ++ tailWord_184972).sum := by decide
  have hdescent : baseEnd_184972 < baseStart_184972 := by decide
  rcases family_descends (prefixWord ++ tailWord_184972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_184989 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_184989 : Nat := 118140960795 + 184989 * 2 ^ 59
def prefixEnd_184989 : Nat := 4983230072969 + 3 ^ 40 * 184989 * 2
def baseEnd_184989 : Nat := 31662757598227321128919

theorem tailTrace_184989 : CollatzResearch.WordTrace tailWord_184989 prefixEnd_184989 31662757598227321128919 := by
  unfold tailWord_184989
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747103126823921451014021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4498068751215947634009347 6747103126823921451014021)
  ·
    refine ⟨1265081836279485272065129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6747103126823921451014021 1265081836279485272065129)
    ·
      refine ⟨948811377209613954048847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1265081836279485272065129 948811377209613954048847)
      ·
        refine ⟨1423217065814420931073271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948811377209613954048847 1423217065814420931073271)
        ·
          refine ⟨2134825598721631396609907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423217065814420931073271 2134825598721631396609907)
          ·
            refine ⟨3202238398082447094914861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134825598721631396609907 3202238398082447094914861)
            ·
              refine ⟨1200839399280917660593073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3202238398082447094914861 1200839399280917660593073)
              ·
                refine ⟨900629549460688245444805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200839399280917660593073 900629549460688245444805)
                ·
                  refine ⟨168868040523879046020901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 900629549460688245444805 168868040523879046020901)
                  ·
                    refine ⟨31662757598227321128919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168868040523879046020901 31662757598227321128919)
                    ·
                      rfl

theorem cell23_184989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_184989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_184989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_184989 prefixEnd_184989 := by exact prefixLift 184989
  have htrace : WordTrace (prefixWord ++ tailWord_184989) baseStart_184989 baseEnd_184989 := by
    simpa [prefixWord, tailWord_184989, baseEnd_184989] using wordTrace_append hprefix tailTrace_184989
  have hstable : (prefixWord ++ tailWord_184989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_184989).length < 2 ^ (prefixWord ++ tailWord_184989).sum := by decide
  have hdescent : baseEnd_184989 < baseStart_184989 := by decide
  rcases family_descends (prefixWord ++ tailWord_184989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185023 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 2, 4]
def baseStart_185023 : Nat := 118140960795 + 185023 * 2 ^ 59
def prefixEnd_185023 : Nat := 4983230072969 + 3 ^ 40 * 185023 * 2
def baseEnd_185023 : Nat := 31668577045644943453867

theorem tailTrace_185023 : CollatzResearch.WordTrace tailWord_185023 prefixEnd_185023 31668577045644943453867 := by
  unfold tailWord_185023
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748343208700745257751723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4498895472467163505167815 6748343208700745257751723)
  ·
    refine ⟨10122514813051117886627585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748343208700745257751723 10122514813051117886627585)
    ·
      refine ⟨7591886109788338414970689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10122514813051117886627585 7591886109788338414970689)
      ·
        refine ⟨5693914582341253811228017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7591886109788338414970689 5693914582341253811228017)
        ·
          refine ⟨4270435936755940358421013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693914582341253811228017 4270435936755940358421013)
          ·
            refine ⟨200176684535434704300985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4270435936755940358421013 200176684535434704300985)
            ·
              refine ⟨150132513401576028225739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200176684535434704300985 150132513401576028225739)
              ·
                refine ⟨225198770102364042338609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150132513401576028225739 225198770102364042338609)
                ·
                  refine ⟨168899077576773031753957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225198770102364042338609 168899077576773031753957)
                  ·
                    refine ⟨31668577045644943453867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168899077576773031753957 31668577045644943453867)
                    ·
                      rfl

theorem cell23_185023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 4].length) (baseStart_185023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185023 prefixEnd_185023 := by exact prefixLift 185023
  have htrace : WordTrace (prefixWord ++ tailWord_185023) baseStart_185023 baseEnd_185023 := by
    simpa [prefixWord, tailWord_185023, baseEnd_185023] using wordTrace_append hprefix tailTrace_185023
  have hstable : (prefixWord ++ tailWord_185023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185023).length < 2 ^ (prefixWord ++ tailWord_185023).sum := by decide
  have hdescent : baseEnd_185023 < baseStart_185023 := by decide
  rcases family_descends (prefixWord ++ tailWord_185023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185030 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_185030 : Nat := 118140960795 + 185030 * 2 ^ 59
def prefixEnd_185030 : Nat := 4983230072969 + 3 ^ 40 * 185030 * 2
def baseEnd_185030 : Nat := 95009325501516302974069

theorem tailTrace_185030 : CollatzResearch.WordTrace tailWord_185030 prefixEnd_185030 95009325501516302974069 := by
  unfold tailWord_185030
  simp only [CollatzResearch.WordTrace]
  refine ⟨210893703739855795414267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4499065679783590302171029 210893703739855795414267)
  ·
    refine ⟨316340555609783693121401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210893703739855795414267 316340555609783693121401)
    ·
      refine ⟨237255416707337769841051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316340555609783693121401 237255416707337769841051)
      ·
        refine ⟨355883125061006654761577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237255416707337769841051 355883125061006654761577)
        ·
          refine ⟨266912343795754991071183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355883125061006654761577 266912343795754991071183)
          ·
            refine ⟨400368515693632486606775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266912343795754991071183 400368515693632486606775)
            ·
              refine ⟨600552773540448729910163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400368515693632486606775 600552773540448729910163)
              ·
                refine ⟨900829160310673094865245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600552773540448729910163 900829160310673094865245)
                ·
                  refine ⟨337810935116502410574467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900829160310673094865245 337810935116502410574467)
                  ·
                    refine ⟨506716402674753615861701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 337810935116502410574467 506716402674753615861701)
                    ·
                      refine ⟨95009325501516302974069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 506716402674753615861701 95009325501516302974069)
                      ·
                        rfl

theorem cell23_185030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_185030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185030 prefixEnd_185030 := by exact prefixLift 185030
  have htrace : WordTrace (prefixWord ++ tailWord_185030) baseStart_185030 baseEnd_185030 := by
    simpa [prefixWord, tailWord_185030, baseEnd_185030] using wordTrace_append hprefix tailTrace_185030
  have hstable : (prefixWord ++ tailWord_185030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185030).length < 2 ^ (prefixWord ++ tailWord_185030).sum := by decide
  have hdescent : baseEnd_185030 < baseStart_185030 := by decide
  rcases family_descends (prefixWord ++ tailWord_185030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185064 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_185064 : Nat := 118140960795 + 185064 * 2 ^ 59
def prefixEnd_185064 : Nat := 4983230072969 + 3 ^ 40 * 185064 * 2
def baseEnd_185064 : Nat := 95026783843769169948913

theorem tailTrace_185064 : CollatzResearch.WordTrace tailWord_185064 prefixEnd_185064 95026783843769169948913 := by
  unfold tailWord_185064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374919300776104629997123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4499892401034806173329497 3374919300776104629997123)
  ·
    refine ⟨5062378951164156944995685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3374919300776104629997123 5062378951164156944995685)
    ·
      refine ⟨949196053343279427186691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5062378951164156944995685 949196053343279427186691)
      ·
        refine ⟨1423794080014919140780037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949196053343279427186691 1423794080014919140780037)
        ·
          refine ⟨266961390002797338896257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1423794080014919140780037 266961390002797338896257)
          ·
            refine ⟨200221042502098004172193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266961390002797338896257 200221042502098004172193)
            ·
              refine ⟨150165781876573503129145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200221042502098004172193 150165781876573503129145)
              ·
                refine ⟨112624336407430127346859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150165781876573503129145 112624336407430127346859)
                ·
                  refine ⟨168936504611145191020289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112624336407430127346859 168936504611145191020289)
                  ·
                    refine ⟨126702378458358893265217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168936504611145191020289 126702378458358893265217)
                    ·
                      refine ⟨95026783843769169948913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126702378458358893265217 95026783843769169948913)
                      ·
                        rfl

theorem cell23_185064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_185064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185064 prefixEnd_185064 := by exact prefixLift 185064
  have htrace : WordTrace (prefixWord ++ tailWord_185064) baseStart_185064 baseEnd_185064 := by
    simpa [prefixWord, tailWord_185064, baseEnd_185064] using wordTrace_append hprefix tailTrace_185064
  have hstable : (prefixWord ++ tailWord_185064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185064).length < 2 ^ (prefixWord ++ tailWord_185064).sum := by decide
  have hdescent : baseEnd_185064 < baseStart_185064 := by decide
  rcases family_descends (prefixWord ++ tailWord_185064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185069 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_185069 : Nat := 118140960795 + 185069 * 2 ^ 59
def prefixEnd_185069 : Nat := 4983230072969 + 3 ^ 40 * 185069 * 2
def baseEnd_185069 : Nat := 95029351247041650386389

theorem tailTrace_185069 : CollatzResearch.WordTrace tailWord_185069 prefixEnd_185069 95029351247041650386389 := by
  unfold tailWord_185069
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750020966534095113926261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4500013977689396742617507 6750020966534095113926261)
  ·
    refine ⟨632814465612571416930587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6750020966534095113926261 632814465612571416930587)
    ·
      refine ⟨949221698418857125395881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 632814465612571416930587 949221698418857125395881)
      ·
        refine ⟨711916273814142844046911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 949221698418857125395881 711916273814142844046911)
        ·
          refine ⟨1067874410721214266070367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711916273814142844046911 1067874410721214266070367)
          ·
            refine ⟨1601811616081821399105551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067874410721214266070367 1601811616081821399105551)
            ·
              refine ⟨2402717424122732098658327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601811616081821399105551 2402717424122732098658327)
              ·
                refine ⟨3604076136184098147987491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402717424122732098658327 3604076136184098147987491)
                ·
                  refine ⟨5406114204276147221981237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604076136184098147987491 5406114204276147221981237)
                  ·
                    refine ⟨506823206650888802060741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5406114204276147221981237 506823206650888802060741)
                    ·
                      refine ⟨95029351247041650386389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 506823206650888802060741 95029351247041650386389)
                      ·
                        rfl

theorem cell23_185069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_185069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185069 prefixEnd_185069 := by exact prefixLift 185069
  have htrace : WordTrace (prefixWord ++ tailWord_185069) baseStart_185069 baseEnd_185069 := by
    simpa [prefixWord, tailWord_185069, baseEnd_185069] using wordTrace_append hprefix tailTrace_185069
  have hstable : (prefixWord ++ tailWord_185069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185069).length < 2 ^ (prefixWord ++ tailWord_185069).sum := by decide
  have hdescent : baseEnd_185069 < baseStart_185069 := by decide
  rcases family_descends (prefixWord ++ tailWord_185069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185089 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_185089 : Nat := 118140960795 + 185089 * 2 ^ 59
def prefixEnd_185089 : Nat := 4983230072969 + 3 ^ 40 * 185089 * 2
def baseEnd_185089 : Nat := 95039620860131572136297

theorem tailTrace_185089 : CollatzResearch.WordTrace tailWord_185089 prefixEnd_185089 95039620860131572136297 := by
  unfold tailWord_185089
  simp only [CollatzResearch.WordTrace]
  refine ⟨6750750426461638529654321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4500500284307759019769547 6750750426461638529654321)
  ·
    refine ⟨5063062819846228897240741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6750750426461638529654321 5063062819846228897240741)
    ·
      refine ⟨949324278721167918232639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5063062819846228897240741 949324278721167918232639)
      ·
        refine ⟨1423986418081751877348959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 949324278721167918232639 1423986418081751877348959)
        ·
          refine ⟨2135979627122627816023439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423986418081751877348959 2135979627122627816023439)
          ·
            refine ⟨3203969440683941724035159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135979627122627816023439 3203969440683941724035159)
            ·
              refine ⟨4805954161025912586052739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203969440683941724035159 4805954161025912586052739)
              ·
                refine ⟨7208931241538868879079109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805954161025912586052739 7208931241538868879079109)
                ·
                  refine ⟨1351674607788537914827333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7208931241538868879079109 1351674607788537914827333)
                  ·
                    refine ⟨253438988960350859030125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1351674607788537914827333 253438988960350859030125)
                    ·
                      refine ⟨95039620860131572136297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 253438988960350859030125 95039620860131572136297)
                      ·
                        rfl

theorem cell23_185089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_185089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185089 prefixEnd_185089 := by exact prefixLift 185089
  have htrace : WordTrace (prefixWord ++ tailWord_185089) baseStart_185089 baseEnd_185089 := by
    simpa [prefixWord, tailWord_185089, baseEnd_185089] using wordTrace_append hprefix tailTrace_185089
  have hstable : (prefixWord ++ tailWord_185089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185089).length < 2 ^ (prefixWord ++ tailWord_185089).sum := by decide
  have hdescent : baseEnd_185089 < baseStart_185089 := by decide
  rcases family_descends (prefixWord ++ tailWord_185089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185120 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2]
def baseStart_185120 : Nat := 118140960795 + 185120 * 2 ^ 59
def prefixEnd_185120 : Nat := 4983230072969 + 3 ^ 40 * 185120 * 2
def baseEnd_185120 : Nat := 95055538760420950848655

theorem tailTrace_185120 : CollatzResearch.WordTrace tailWord_185120 prefixEnd_185120 95055538760420950848655 := by
  unfold tailWord_185120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375940544674665412016407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4501254059566220549355209 3375940544674665412016407)
  ·
    refine ⟨5063910817011998118024611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375940544674665412016407 5063910817011998118024611)
    ·
      refine ⟨7595866225517997177036917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063910817011998118024611 7595866225517997177036917)
      ·
        refine ⟨712112458642312235347211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7595866225517997177036917 712112458642312235347211)
        ·
          refine ⟨1068168687963468353020817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712112458642312235347211 1068168687963468353020817)
          ·
            refine ⟨801126515972601264765613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068168687963468353020817 801126515972601264765613)
            ·
              refine ⟨300422443489725474287105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 801126515972601264765613 300422443489725474287105)
              ·
                refine ⟨225316832617294105715329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300422443489725474287105 225316832617294105715329)
                ·
                  refine ⟨168987624462970579286497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225316832617294105715329 168987624462970579286497)
                  ·
                    refine ⟨126740718347227934464873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 168987624462970579286497 126740718347227934464873)
                    ·
                      refine ⟨95055538760420950848655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126740718347227934464873 95055538760420950848655)
                      ·
                        rfl

theorem cell23_185120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_185120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185120 prefixEnd_185120 := by exact prefixLift 185120
  have htrace : WordTrace (prefixWord ++ tailWord_185120) baseStart_185120 baseEnd_185120 := by
    simpa [prefixWord, tailWord_185120, baseEnd_185120] using wordTrace_append hprefix tailTrace_185120
  have hstable : (prefixWord ++ tailWord_185120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185120).length < 2 ^ (prefixWord ++ tailWord_185120).sum := by decide
  have hdescent : baseEnd_185120 < baseStart_185120 := by decide
  rcases family_descends (prefixWord ++ tailWord_185120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185139 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 7]
def baseStart_185139 : Nat := 118140960795 + 185139 * 2 ^ 59
def prefixEnd_185139 : Nat := 4983230072969 + 3 ^ 40 * 185139 * 2
def baseEnd_185139 : Nat := 31688431630952125503689

theorem tailTrace_185139 : CollatzResearch.WordTrace tailWord_185139 prefixEnd_185139 31688431630952125503689 := by
  unfold tailWord_185139
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752574076280497068974471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4501716050853664712649647 6752574076280497068974471)
  ·
    refine ⟨10128861114420745603461707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752574076280497068974471 10128861114420745603461707)
    ·
      refine ⟨15193291671631118405192561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128861114420745603461707 15193291671631118405192561)
      ·
        refine ⟨11394968753723338803894421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15193291671631118405192561 11394968753723338803894421)
        ·
          refine ⟨534139160330781506432551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11394968753723338803894421 534139160330781506432551)
          ·
            refine ⟨801208740496172259648827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534139160330781506432551 801208740496172259648827)
            ·
              refine ⟨1201813110744258389473241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801208740496172259648827 1201813110744258389473241)
              ·
                refine ⟨901359833058193792104931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201813110744258389473241 901359833058193792104931)
                ·
                  refine ⟨1352039749587290688157397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 901359833058193792104931 1352039749587290688157397)
                  ·
                    refine ⟨31688431630952125503689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1352039749587290688157397 31688431630952125503689)
                    ·
                      rfl

theorem cell23_185139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 7].length) (baseStart_185139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185139 prefixEnd_185139 := by exact prefixLift 185139
  have htrace : WordTrace (prefixWord ++ tailWord_185139) baseStart_185139 baseEnd_185139 := by
    simpa [prefixWord, tailWord_185139, baseEnd_185139] using wordTrace_append hprefix tailTrace_185139
  have hstable : (prefixWord ++ tailWord_185139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185139).length < 2 ^ (prefixWord ++ tailWord_185139).sum := by decide
  have hdescent : baseEnd_185139 < baseStart_185139 := by decide
  rcases family_descends (prefixWord ++ tailWord_185139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185176 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2]
def baseStart_185176 : Nat := 118140960795 + 185176 * 2 ^ 59
def prefixEnd_185176 : Nat := 4983230072969 + 3 ^ 40 * 185176 * 2
def baseEnd_185176 : Nat := 95084293677072731748397

theorem tailTrace_185176 : CollatzResearch.WordTrace tailWord_185176 prefixEnd_185176 95084293677072731748397 := by
  unfold tailWord_185176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376961788573226194035691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4502615718097634925380921 3376961788573226194035691)
  ·
    refine ⟨5065442682859839291053537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376961788573226194035691 5065442682859839291053537)
    ·
      refine ⟨3799082012144879468290153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5065442682859839291053537 3799082012144879468290153)
      ·
        refine ⟨2849311509108659601217615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3799082012144879468290153 2849311509108659601217615)
        ·
          refine ⟨4273967263662989401826423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2849311509108659601217615 4273967263662989401826423)
          ·
            refine ⟨6410950895494484102739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273967263662989401826423 6410950895494484102739635)
            ·
              refine ⟨9616426343241726154109453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410950895494484102739635 9616426343241726154109453)
              ·
                refine ⟨3606159878715647307791045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9616426343241726154109453 3606159878715647307791045)
                ·
                  refine ⟨676154977259183870210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3606159878715647307791045 676154977259183870210821)
                  ·
                    refine ⟨126779058236096975664529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 676154977259183870210821 126779058236096975664529)
                    ·
                      refine ⟨95084293677072731748397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126779058236096975664529 95084293677072731748397)
                      ·
                        rfl

theorem cell23_185176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4, 4, 2].length) (baseStart_185176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185176 prefixEnd_185176 := by exact prefixLift 185176
  have htrace : WordTrace (prefixWord ++ tailWord_185176) baseStart_185176 baseEnd_185176 := by
    simpa [prefixWord, tailWord_185176, baseEnd_185176] using wordTrace_append hprefix tailTrace_185176
  have hstable : (prefixWord ++ tailWord_185176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185176).length < 2 ^ (prefixWord ++ tailWord_185176).sum := by decide
  have hdescent : baseEnd_185176 < baseStart_185176 := by decide
  rcases family_descends (prefixWord ++ tailWord_185176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185189 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_185189 : Nat := 118140960795 + 185189 * 2 ^ 59
def prefixEnd_185189 : Nat := 4983230072969 + 3 ^ 40 * 185189 * 2
def baseEnd_185189 : Nat := 95090968925581180885837

theorem tailTrace_185189 : CollatzResearch.WordTrace tailWord_185189 prefixEnd_185189 95090968925581180885837 := by
  unfold tailWord_185189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754397726099355608294621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4502931817399570405529747 6754397726099355608294621)
  ·
    refine ⟨2532899147287258353110483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6754397726099355608294621 2532899147287258353110483)
    ·
      refine ⟨3799348720930887529665725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532899147287258353110483 3799348720930887529665725)
      ·
        refine ⟨1424755770349082823624647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3799348720930887529665725 1424755770349082823624647)
        ·
          refine ⟨2137133655523624235436971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424755770349082823624647 2137133655523624235436971)
          ·
            refine ⟨3205700483285436353155457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137133655523624235436971 3205700483285436353155457)
            ·
              refine ⟨2404275362464077264866593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205700483285436353155457 2404275362464077264866593)
              ·
                refine ⟨1803206521848057948649945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404275362464077264866593 1803206521848057948649945)
                ·
                  refine ⟨1352404891386043461487459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1803206521848057948649945 1352404891386043461487459)
                  ·
                    refine ⟨2028607337079065192231189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1352404891386043461487459 2028607337079065192231189)
                    ·
                      refine ⟨95090968925581180885837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2028607337079065192231189 95090968925581180885837)
                      ·
                        rfl

theorem cell23_185189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_185189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185189 prefixEnd_185189 := by exact prefixLift 185189
  have htrace : WordTrace (prefixWord ++ tailWord_185189) baseStart_185189 baseEnd_185189 := by
    simpa [prefixWord, tailWord_185189, baseEnd_185189] using wordTrace_append hprefix tailTrace_185189
  have hstable : (prefixWord ++ tailWord_185189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185189).length < 2 ^ (prefixWord ++ tailWord_185189).sum := by decide
  have hdescent : baseEnd_185189 < baseStart_185189 := by decide
  rcases family_descends (prefixWord ++ tailWord_185189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185196 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_185196 : Nat := 118140960795 + 185196 * 2 ^ 59
def prefixEnd_185196 : Nat := 4983230072969 + 3 ^ 40 * 185196 * 2
def baseEnd_185196 : Nat := 95094563290162653498305

theorem tailTrace_185196 : CollatzResearch.WordTrace tailWord_185196 prefixEnd_185196 95094563290162653498305 := by
  unfold tailWord_185196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377326518536997901899721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4503102024715997202532961 3377326518536997901899721)
  ·
    refine ⟨2532994888902748426424791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377326518536997901899721 2532994888902748426424791)
    ·
      refine ⟨3799492333354122639637187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532994888902748426424791 3799492333354122639637187)
      ·
        refine ⟨5699238500031183959455781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799492333354122639637187 5699238500031183959455781)
        ·
          refine ⟨1068607218755846992397959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5699238500031183959455781 1068607218755846992397959)
          ·
            refine ⟨1602910828133770488596939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068607218755846992397959 1602910828133770488596939)
            ·
              refine ⟨2404366242200655732895409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602910828133770488596939 2404366242200655732895409)
              ·
                refine ⟨1803274681650491799671557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404366242200655732895409 1803274681650491799671557)
                ·
                  refine ⟨338114002809467212438417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803274681650491799671557 338114002809467212438417)
                  ·
                    refine ⟨253585502107100409328813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338114002809467212438417 253585502107100409328813)
                    ·
                      refine ⟨95094563290162653498305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 253585502107100409328813 95094563290162653498305)
                      ·
                        rfl

theorem cell23_185196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_185196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185196 prefixEnd_185196 := by exact prefixLift 185196
  have htrace : WordTrace (prefixWord ++ tailWord_185196) baseStart_185196 baseEnd_185196 := by
    simpa [prefixWord, tailWord_185196, baseEnd_185196] using wordTrace_append hprefix tailTrace_185196
  have hstable : (prefixWord ++ tailWord_185196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185196).length < 2 ^ (prefixWord ++ tailWord_185196).sum := by decide
  have hdescent : baseEnd_185196 < baseStart_185196 := by decide
  rcases family_descends (prefixWord ++ tailWord_185196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185236 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_185236 : Nat := 118140960795 + 185236 * 2 ^ 59
def prefixEnd_185236 : Nat := 4983230072969 + 3 ^ 40 * 185236 * 2
def baseEnd_185236 : Nat := 95115102516342496998121

theorem tailTrace_185236 : CollatzResearch.WordTrace tailWord_185236 prefixEnd_185236 95115102516342496998121 := by
  unfold tailWord_185236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378055978464541317627781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4504074637952721756837041 3378055978464541317627781)
  ·
    refine ⟨633385495962101497055209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3378055978464541317627781 633385495962101497055209)
    ·
      refine ⟨475039121971576122791407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 633385495962101497055209 475039121971576122791407)
      ·
        refine ⟨712558682957364184187111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475039121971576122791407 712558682957364184187111)
        ·
          refine ⟨1068838024436046276280667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712558682957364184187111 1068838024436046276280667)
          ·
            refine ⟨1603257036654069414421001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068838024436046276280667 1603257036654069414421001)
            ·
              refine ⟨1202442777490552060815751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1603257036654069414421001 1202442777490552060815751)
              ·
                refine ⟨1803664166235828091223627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202442777490552060815751 1803664166235828091223627)
                ·
                  refine ⟨2705496249353742136835441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803664166235828091223627 2705496249353742136835441)
                  ·
                    refine ⟨2029122187015306602626581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2705496249353742136835441 2029122187015306602626581)
                    ·
                      refine ⟨95115102516342496998121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2029122187015306602626581 95115102516342496998121)
                      ·
                        rfl

theorem cell23_185236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_185236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185236 prefixEnd_185236 := by exact prefixLift 185236
  have htrace : WordTrace (prefixWord ++ tailWord_185236) baseStart_185236 baseEnd_185236 := by
    simpa [prefixWord, tailWord_185236, baseEnd_185236] using wordTrace_append hprefix tailTrace_185236
  have hstable : (prefixWord ++ tailWord_185236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185236).length < 2 ^ (prefixWord ++ tailWord_185236).sum := by decide
  have hdescent : baseEnd_185236 < baseStart_185236 := by decide
  rcases family_descends (prefixWord ++ tailWord_185236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185237 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_185237 : Nat := 118140960795 + 185237 * 2 ^ 59
def prefixEnd_185237 : Nat := 4983230072969 + 3 ^ 40 * 185237 * 2
def baseEnd_185237 : Nat := 31705205332332331028539

theorem tailTrace_185237 : CollatzResearch.WordTrace tailWord_185237 prefixEnd_185237 31705205332332331028539 := by
  unfold tailWord_185237
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756148429925459806041965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4504098953283639870694643 6756148429925459806041965)
  ·
    refine ⟨2533555661222047427265737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6756148429925459806041965 2533555661222047427265737)
    ·
      refine ⟨1900166745916535570449303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2533555661222047427265737 1900166745916535570449303)
      ·
        refine ⟨2850250118874803355673955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1900166745916535570449303 2850250118874803355673955)
        ·
          refine ⟨4275375178312205033510933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2850250118874803355673955 4275375178312205033510933)
          ·
            refine ⟨200408211483384610945825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4275375178312205033510933 200408211483384610945825)
            ·
              refine ⟨150306158612538458209369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200408211483384610945825 150306158612538458209369)
              ·
                refine ⟨112729618959403843657027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150306158612538458209369 112729618959403843657027)
                ·
                  refine ⟨169094428439105765485541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112729618959403843657027 169094428439105765485541)
                  ·
                    refine ⟨31705205332332331028539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169094428439105765485541 31705205332332331028539)
                    ·
                      rfl

theorem cell23_185237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_185237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185237 prefixEnd_185237 := by exact prefixLift 185237
  have htrace : WordTrace (prefixWord ++ tailWord_185237) baseStart_185237 baseEnd_185237 := by
    simpa [prefixWord, tailWord_185237, baseEnd_185237] using wordTrace_append hprefix tailTrace_185237
  have hstable : (prefixWord ++ tailWord_185237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185237).length < 2 ^ (prefixWord ++ tailWord_185237).sum := by decide
  have hdescent : baseEnd_185237 < baseStart_185237 := by decide
  rcases family_descends (prefixWord ++ tailWord_185237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185259 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 6]
def baseStart_185259 : Nat := 118140960795 + 185259 * 2 ^ 59
def prefixEnd_185259 : Nat := 4983230072969 + 3 ^ 40 * 185259 * 2
def baseEnd_185259 : Nat := 31708970857131969003505

theorem tailTrace_185259 : CollatzResearch.WordTrace tailWord_185259 prefixEnd_185259 31708970857131969003505 := by
  unfold tailWord_185259
  simp only [CollatzResearch.WordTrace]
  refine ⟨6756950835845757563342831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4504633890563838375561887 6756950835845757563342831)
  ·
    refine ⟨10135426253768636345014247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6756950835845757563342831 10135426253768636345014247)
    ·
      refine ⟨15203139380652954517521371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10135426253768636345014247 15203139380652954517521371)
      ·
        refine ⟨22804709070979431776282057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203139380652954517521371 22804709070979431776282057)
        ·
          refine ⟨17103531803234573832211543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22804709070979431776282057 17103531803234573832211543)
          ·
            refine ⟨25655297704851860748317315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17103531803234573832211543 25655297704851860748317315)
            ·
              refine ⟨38482946557277791122475973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25655297704851860748317315 38482946557277791122475973)
              ·
                refine ⟨7215552479489585835464245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38482946557277791122475973 7215552479489585835464245)
                ·
                  refine ⟨676458044952148672074773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7215552479489585835464245 676458044952148672074773)
                  ·
                    refine ⟨31708970857131969003505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 676458044952148672074773 31708970857131969003505)
                    ·
                      rfl

theorem cell23_185259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 6].length) (baseStart_185259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185259 prefixEnd_185259 := by exact prefixLift 185259
  have htrace : WordTrace (prefixWord ++ tailWord_185259) baseStart_185259 baseEnd_185259 := by
    simpa [prefixWord, tailWord_185259, baseEnd_185259] using wordTrace_append hprefix tailTrace_185259
  have hstable : (prefixWord ++ tailWord_185259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185259).length < 2 ^ (prefixWord ++ tailWord_185259).sum := by decide
  have hdescent : baseEnd_185259 < baseStart_185259 := by decide
  rcases family_descends (prefixWord ++ tailWord_185259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185280 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 1, 5]
def baseStart_185280 : Nat := 118140960795 + 185280 * 2 ^ 59
def prefixEnd_185280 : Nat := 4983230072969 + 3 ^ 40 * 185280 * 2
def baseEnd_185280 : Nat := 31712565221713441615973

theorem tailTrace_185280 : CollatzResearch.WordTrace tailWord_185280 prefixEnd_185280 31712565221713441615973 := by
  unfold tailWord_185280
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378858384384839074928647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4505144512513118766571529 3378858384384839074928647)
  ·
    refine ⟨5068287576577258612392971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3378858384384839074928647 5068287576577258612392971)
    ·
      refine ⟨7602431364865887918589457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5068287576577258612392971 7602431364865887918589457)
      ·
        refine ⟨5701823523649415938942093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7602431364865887918589457 5701823523649415938942093)
        ·
          refine ⟨2138183821368530977103285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5701823523649415938942093 2138183821368530977103285)
          ·
            refine ⟨200454733253299779103433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2138183821368530977103285 200454733253299779103433)
            ·
              refine ⟨150341049939974834327575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200454733253299779103433 150341049939974834327575)
              ·
                refine ⟨225511574909962251491363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150341049939974834327575 225511574909962251491363)
                ·
                  refine ⟨338267362364943377237045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225511574909962251491363 338267362364943377237045)
                  ·
                    refine ⟨31712565221713441615973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 338267362364943377237045 31712565221713441615973)
                    ·
                      rfl

theorem cell23_185280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 5].length) (baseStart_185280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185280 prefixEnd_185280 := by exact prefixLift 185280
  have htrace : WordTrace (prefixWord ++ tailWord_185280) baseStart_185280 baseEnd_185280 := by
    simpa [prefixWord, tailWord_185280, baseEnd_185280] using wordTrace_append hprefix tailTrace_185280
  have hstable : (prefixWord ++ tailWord_185280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185280).length < 2 ^ (prefixWord ++ tailWord_185280).sum := by decide
  have hdescent : baseEnd_185280 < baseStart_185280 := by decide
  rcases family_descends (prefixWord ++ tailWord_185280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185317 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 4]
def baseStart_185317 : Nat := 118140960795 + 185317 * 2 ^ 59
def prefixEnd_185317 : Nat := 4983230072969 + 3 ^ 40 * 185317 * 2
def baseEnd_185317 : Nat := 95156694449356680085249

theorem tailTrace_185317 : CollatzResearch.WordTrace tailWord_185317 prefixEnd_185317 95156694449356680085249 := by
  unfold tailWord_185317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759066269635633468954205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4506044179757088979302803 6759066269635633468954205)
  ·
    refine ⟨2534649851113362550857827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6759066269635633468954205 2534649851113362550857827)
    ·
      refine ⟨3801974776670043826286741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2534649851113362550857827 3801974776670043826286741)
      ·
        refine ⟨178217567656408304357191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3801974776670043826286741 178217567656408304357191)
        ·
          refine ⟨267326351484612456535787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178217567656408304357191 267326351484612456535787)
          ·
            refine ⟨400989527226918684803681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267326351484612456535787 400989527226918684803681)
            ·
              refine ⟨300742145420189013602761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400989527226918684803681 300742145420189013602761)
              ·
                refine ⟨225556609065141760202071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300742145420189013602761 225556609065141760202071)
                ·
                  refine ⟨338334913597712640303107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225556609065141760202071 338334913597712640303107)
                  ·
                    refine ⟨507502370396568960454661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338334913597712640303107 507502370396568960454661)
                    ·
                      refine ⟨95156694449356680085249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 507502370396568960454661 95156694449356680085249)
                      ·
                        rfl

theorem cell23_185317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_185317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185317 prefixEnd_185317 := by exact prefixLift 185317
  have htrace : WordTrace (prefixWord ++ tailWord_185317) baseStart_185317 baseEnd_185317 := by
    simpa [prefixWord, tailWord_185317, baseEnd_185317] using wordTrace_append hprefix tailTrace_185317
  have hstable : (prefixWord ++ tailWord_185317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185317).length < 2 ^ (prefixWord ++ tailWord_185317).sum := by decide
  have hdescent : baseEnd_185317 < baseStart_185317 := by decide
  rcases family_descends (prefixWord ++ tailWord_185317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185343 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 7, 3, 2]
def baseStart_185343 : Nat := 118140960795 + 185343 * 2 ^ 59
def prefixEnd_185343 : Nat := 4983230072969 + 3 ^ 40 * 185343 * 2
def baseEnd_185343 : Nat := 95170044946373578360129

theorem tailTrace_185343 : CollatzResearch.WordTrace tailWord_185343 prefixEnd_185343 95170044946373578360129 := by
  unfold tailWord_185343
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760014567541439909400683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4506676378360959939600455 6760014567541439909400683)
  ·
    refine ⟨10140021851312159864101025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6760014567541439909400683 10140021851312159864101025)
    ·
      refine ⟨7605016388484119898075769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10140021851312159864101025 7605016388484119898075769)
      ·
        refine ⟨5703762291363089923556827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7605016388484119898075769 5703762291363089923556827)
        ·
          refine ⟨8555643437044634885335241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5703762291363089923556827 8555643437044634885335241)
          ·
            refine ⟨6416732577783476164001431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555643437044634885335241 6416732577783476164001431)
            ·
              refine ⟨9625098866675214246002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416732577783476164001431 9625098866675214246002147)
              ·
                refine ⟨14437648300012821369003221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625098866675214246002147 14437648300012821369003221)
                ·
                  refine ⟨338382382031550500836013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14437648300012821369003221 338382382031550500836013)
                  ·
                    refine ⟨126893393261831437813505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338382382031550500836013 126893393261831437813505)
                    ·
                      refine ⟨95170044946373578360129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126893393261831437813505 95170044946373578360129)
                      ·
                        rfl

theorem cell23_185343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_185343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185343 prefixEnd_185343 := by exact prefixLift 185343
  have htrace : WordTrace (prefixWord ++ tailWord_185343) baseStart_185343 baseEnd_185343 := by
    simpa [prefixWord, tailWord_185343, baseEnd_185343] using wordTrace_append hprefix tailTrace_185343
  have hstable : (prefixWord ++ tailWord_185343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185343).length < 2 ^ (prefixWord ++ tailWord_185343).sum := by decide
  have hdescent : baseEnd_185343 < baseStart_185343 := by decide
  rcases family_descends (prefixWord ++ tailWord_185343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185367 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 3]
def baseStart_185367 : Nat := 118140960795 + 185367 * 2 ^ 59
def prefixEnd_185367 : Nat := 4983230072969 + 3 ^ 40 * 185367 * 2
def baseEnd_185367 : Nat := 95182368482081484460019

theorem tailTrace_185367 : CollatzResearch.WordTrace tailWord_185367 prefixEnd_185367 95182368482081484460019 := by
  unfold tailWord_185367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6760889919454492008274355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4507259946302994672182903 6760889919454492008274355)
  ·
    refine ⟨10141334879181738012411533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6760889919454492008274355 10141334879181738012411533)
    ·
      refine ⟨3803000579693151754654325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10141334879181738012411533 3803000579693151754654325)
      ·
        refine ⟨356531304346232976998843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3803000579693151754654325 356531304346232976998843)
        ·
          refine ⟨534796956519349465498265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356531304346232976998843 534796956519349465498265)
          ·
            refine ⟨401097717389512099123699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534796956519349465498265 401097717389512099123699)
            ·
              refine ⟨601646576084268148685549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401097717389512099123699 601646576084268148685549)
              ·
                refine ⟨225617466031600555757081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 601646576084268148685549 225617466031600555757081)
                ·
                  refine ⟨169213099523700416817811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225617466031600555757081 169213099523700416817811)
                  ·
                    refine ⟨253819649285550625226717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169213099523700416817811 253819649285550625226717)
                    ·
                      refine ⟨95182368482081484460019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 253819649285550625226717 95182368482081484460019)
                      ·
                        rfl

theorem cell23_185367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_185367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185367 prefixEnd_185367 := by exact prefixLift 185367
  have htrace : WordTrace (prefixWord ++ tailWord_185367) baseStart_185367 baseEnd_185367 := by
    simpa [prefixWord, tailWord_185367, baseEnd_185367] using wordTrace_append hprefix tailTrace_185367
  have hstable : (prefixWord ++ tailWord_185367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185367).length < 2 ^ (prefixWord ++ tailWord_185367).sum := by decide
  have hdescent : baseEnd_185367 < baseStart_185367 := by decide
  rcases family_descends (prefixWord ++ tailWord_185367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185377 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_185377 : Nat := 118140960795 + 185377 * 2 ^ 59
def prefixEnd_185377 : Nat := 4983230072969 + 3 ^ 40 * 185377 * 2
def baseEnd_185377 : Nat := 95187503288626445334973

theorem tailTrace_185377 : CollatzResearch.WordTrace tailWord_185377 prefixEnd_185377 95187503288626445334973 := by
  unfold tailWord_185377
  simp only [CollatzResearch.WordTrace]
  refine ⟨6761254649418263716138385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4507503099612175810758923 6761254649418263716138385)
  ·
    refine ⟨5070940987063697787103789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6761254649418263716138385 5070940987063697787103789)
    ·
      refine ⟨1901602870148886670163921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5070940987063697787103789 1901602870148886670163921)
      ·
        refine ⟨1426202152611665002622941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1901602870148886670163921 1426202152611665002622941)
        ·
          refine ⟨534825807229374375983603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1426202152611665002622941 534825807229374375983603)
          ·
            refine ⟨802238710844061563975405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534825807229374375983603 802238710844061563975405)
            ·
              refine ⟨300839516566523086490777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 802238710844061563975405 300839516566523086490777)
              ·
                refine ⟨225629637424892314868083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300839516566523086490777 225629637424892314868083)
                ·
                  refine ⟨338444456137338472302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225629637424892314868083 338444456137338472302125)
                  ·
                    refine ⟨126916671051501927113297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338444456137338472302125 126916671051501927113297)
                    ·
                      refine ⟨95187503288626445334973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 126916671051501927113297 95187503288626445334973)
                      ·
                        rfl

theorem cell23_185377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_185377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185377 prefixEnd_185377 := by exact prefixLift 185377
  have htrace : WordTrace (prefixWord ++ tailWord_185377) baseStart_185377 baseEnd_185377 := by
    simpa [prefixWord, tailWord_185377, baseEnd_185377] using wordTrace_append hprefix tailTrace_185377
  have hstable : (prefixWord ++ tailWord_185377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185377).length < 2 ^ (prefixWord ++ tailWord_185377).sum := by decide
  have hdescent : baseEnd_185377 < baseStart_185377 := by decide
  rcases family_descends (prefixWord ++ tailWord_185377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185463 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_185463 : Nat := 118140960795 + 185463 * 2 ^ 59
def prefixEnd_185463 : Nat := 4983230072969 + 3 ^ 40 * 185463 * 2
def baseEnd_185463 : Nat := 95231662624913108859577

theorem tailTrace_185463 : CollatzResearch.WordTrace tailWord_185463 prefixEnd_185463 95231662624913108859577 := by
  unfold tailWord_185463
  simp only [CollatzResearch.WordTrace]
  refine ⟨6764391327106700403769043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4509594218071133602512695 6764391327106700403769043)
  ·
    refine ⟨10146586990660050605653565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6764391327106700403769043 10146586990660050605653565)
    ·
      refine ⟨3804970121497518977120087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10146586990660050605653565 3804970121497518977120087)
      ·
        refine ⟨5707455182246278465680131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3804970121497518977120087 5707455182246278465680131)
        ·
          refine ⟨8561182773369417698520197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5707455182246278465680131 8561182773369417698520197)
          ·
            refine ⟨1605221770006765818472537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8561182773369417698520197 1605221770006765818472537)
            ·
              refine ⟨1203916327505074363854403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1605221770006765818472537 1203916327505074363854403)
              ·
                refine ⟨1805874491257611545781605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1203916327505074363854403 1805874491257611545781605)
                ·
                  refine ⟨338601467110802164834051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1805874491257611545781605 338601467110802164834051)
                  ·
                    refine ⟨507902200666203247251077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 338601467110802164834051 507902200666203247251077)
                    ·
                      refine ⟨95231662624913108859577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 507902200666203247251077 95231662624913108859577)
                      ·
                        rfl

theorem cell23_185463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_185463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185463 prefixEnd_185463 := by exact prefixLift 185463
  have htrace : WordTrace (prefixWord ++ tailWord_185463) baseStart_185463 baseEnd_185463 := by
    simpa [prefixWord, tailWord_185463, baseEnd_185463] using wordTrace_append hprefix tailTrace_185463
  have hstable : (prefixWord ++ tailWord_185463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185463).length < 2 ^ (prefixWord ++ tailWord_185463).sum := by decide
  have hdescent : baseEnd_185463 < baseStart_185463 := by decide
  rcases family_descends (prefixWord ++ tailWord_185463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185500 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_185500 : Nat := 118140960795 + 185500 * 2 ^ 59
def prefixEnd_185500 : Nat := 4983230072969 + 3 ^ 40 * 185500 * 2
def baseEnd_185500 : Nat := 95250661409129464096907

theorem tailTrace_185500 : CollatzResearch.WordTrace tailWord_185500 prefixEnd_185500 95250661409129464096907 := by
  unfold tailWord_185500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382870413986327861432977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4510493885315103815243969 3382870413986327861432977)
  ·
    refine ⟨2537152810489745896074733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3382870413986327861432977 2537152810489745896074733)
    ·
      refine ⟨951432303933654711028025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2537152810489745896074733 951432303933654711028025)
      ·
        refine ⟨713574227950241033271019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951432303933654711028025 713574227950241033271019)
        ·
          refine ⟨1070361341925361549906529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 713574227950241033271019 1070361341925361549906529)
          ·
            refine ⟨802771006444021162429897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1070361341925361549906529 802771006444021162429897)
            ·
              refine ⟨602078254833015871822423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 802771006444021162429897 602078254833015871822423)
              ·
                refine ⟨903117382249523807733635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602078254833015871822423 903117382249523807733635)
                ·
                  refine ⟨1354676073374285711600453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 903117382249523807733635 1354676073374285711600453)
                  ·
                    refine ⟨254001763757678570925085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1354676073374285711600453 254001763757678570925085)
                    ·
                      refine ⟨95250661409129464096907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254001763757678570925085 95250661409129464096907)
                      ·
                        rfl

theorem cell23_185500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_185500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185500 prefixEnd_185500 := by exact prefixLift 185500
  have htrace : WordTrace (prefixWord ++ tailWord_185500) baseStart_185500 baseEnd_185500 := by
    simpa [prefixWord, tailWord_185500, baseEnd_185500] using wordTrace_append hprefix tailTrace_185500
  have hstable : (prefixWord ++ tailWord_185500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185500).length < 2 ^ (prefixWord ++ tailWord_185500).sum := by decide
  have hdescent : baseEnd_185500 < baseStart_185500 := by decide
  rcases family_descends (prefixWord ++ tailWord_185500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185537 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 6]
def baseStart_185537 : Nat := 118140960795 + 185537 * 2 ^ 59
def prefixEnd_185537 : Nat := 4983230072969 + 3 ^ 40 * 185537 * 2
def baseEnd_185537 : Nat := 10585517799260646592693

theorem tailTrace_185537 : CollatzResearch.WordTrace tailWord_185537 prefixEnd_185537 10585517799260646592693 := by
  unfold tailWord_185537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6767090328838611041962865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4511393552559074027975243 6767090328838611041962865)
  ·
    refine ⟨5075317746628958281472149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6767090328838611041962865 5075317746628958281472149)
    ·
      refine ⟨237905519373232419444007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5075317746628958281472149 237905519373232419444007)
      ·
        refine ⟨356858279059848629166011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237905519373232419444007 356858279059848629166011)
        ·
          refine ⟨535287418589772943749017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356858279059848629166011 535287418589772943749017)
          ·
            refine ⟨401465563942329707811763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535287418589772943749017 401465563942329707811763)
            ·
              refine ⟨602198345913494561717645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401465563942329707811763 602198345913494561717645)
              ·
                refine ⟨225824379717560460644117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 602198345913494561717645 225824379717560460644117)
                ·
                  refine ⟨10585517799260646592693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225824379717560460644117 10585517799260646592693)
                  ·
                    rfl

theorem cell23_185537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 6].length) (baseStart_185537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185537 prefixEnd_185537 := by exact prefixLift 185537
  have htrace : WordTrace (prefixWord ++ tailWord_185537) baseStart_185537 baseEnd_185537 := by
    simpa [prefixWord, tailWord_185537, baseEnd_185537] using wordTrace_append hprefix tailTrace_185537
  have hstable : (prefixWord ++ tailWord_185537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185537).length < 2 ^ (prefixWord ++ tailWord_185537).sum := by decide
  have hdescent : baseEnd_185537 < baseStart_185537 := by decide
  rcases family_descends (prefixWord ++ tailWord_185537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185581 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 1, 1, 3]
def baseStart_185581 : Nat := 118140960795 + 185581 * 2 ^ 59
def prefixEnd_185581 : Nat := 4983230072969 + 3 ^ 40 * 185581 * 2
def baseEnd_185581 : Nat := 95292253342143647184035

theorem tailTrace_185581 : CollatzResearch.WordTrace tailWord_185581 prefixEnd_185581 95292253342143647184035 := by
  unfold tailWord_185581
  simp only [CollatzResearch.WordTrace]
  refine ⟨6768695140679206556564597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4512463427119471037709731 6768695140679206556564597)
  ·
    refine ⟨634565169438675614677931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6768695140679206556564597 634565169438675614677931)
    ·
      refine ⟨951847754158013422016897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634565169438675614677931 951847754158013422016897)
      ·
        refine ⟨713885815618510066512673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951847754158013422016897 713885815618510066512673)
        ·
          refine ⟨535414361713882549884505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713885815618510066512673 535414361713882549884505)
          ·
            refine ⟨401560771285411912413379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 535414361713882549884505 401560771285411912413379)
            ·
              refine ⟨602341156928117868620069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401560771285411912413379 602341156928117868620069)
              ·
                refine ⟨112938966924022100366263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 602341156928117868620069 112938966924022100366263)
                ·
                  refine ⟨169408450386033150549395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112938966924022100366263 169408450386033150549395)
                  ·
                    refine ⟨254112675579049725824093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169408450386033150549395 254112675579049725824093)
                    ·
                      refine ⟨95292253342143647184035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254112675579049725824093 95292253342143647184035)
                      ·
                        rfl

theorem cell23_185581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_185581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185581 prefixEnd_185581 := by exact prefixLift 185581
  have htrace : WordTrace (prefixWord ++ tailWord_185581) baseStart_185581 baseEnd_185581 := by
    simpa [prefixWord, tailWord_185581, baseEnd_185581] using wordTrace_append hprefix tailTrace_185581
  have hstable : (prefixWord ++ tailWord_185581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185581).length < 2 ^ (prefixWord ++ tailWord_185581).sum := by decide
  have hdescent : baseEnd_185581 < baseStart_185581 := by decide
  rcases family_descends (prefixWord ++ tailWord_185581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185590 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_185590 : Nat := 118140960795 + 185590 * 2 ^ 59
def prefixEnd_185590 : Nat := 4983230072969 + 3 ^ 40 * 185590 * 2
def baseEnd_185590 : Nat := 95296874668034111971493

theorem tailTrace_185590 : CollatzResearch.WordTrace tailWord_185590 prefixEnd_185590 95296874668034111971493 := by
  unfold tailWord_185590
  simp only [CollatzResearch.WordTrace]
  refine ⟨423063962352912568352639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4512682265097734062428149 423063962352912568352639)
  ·
    refine ⟨634595943529368852528959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 423063962352912568352639 634595943529368852528959)
    ·
      refine ⟨951893915294053278793439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634595943529368852528959 951893915294053278793439)
      ·
        refine ⟨1427840872941079918190159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951893915294053278793439 1427840872941079918190159)
        ·
          refine ⟨2141761309411619877285239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427840872941079918190159 2141761309411619877285239)
          ·
            refine ⟨3212641964117429815927859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141761309411619877285239 3212641964117429815927859)
            ·
              refine ⟨4818962946176144723891789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212641964117429815927859 4818962946176144723891789)
              ·
                refine ⟨1807111104816054271459421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818962946176144723891789 1807111104816054271459421)
                ·
                  refine ⟨677666664306020351797283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1807111104816054271459421 677666664306020351797283)
                  ·
                    refine ⟨1016499996459030527695925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 677666664306020351797283 1016499996459030527695925)
                    ·
                      refine ⟨95296874668034111971493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1016499996459030527695925 95296874668034111971493)
                      ·
                        rfl

theorem cell23_185590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_185590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185590 prefixEnd_185590 := by exact prefixLift 185590
  have htrace : WordTrace (prefixWord ++ tailWord_185590) baseStart_185590 baseEnd_185590 := by
    simpa [prefixWord, tailWord_185590, baseEnd_185590] using wordTrace_append hprefix tailTrace_185590
  have hstable : (prefixWord ++ tailWord_185590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185590).length < 2 ^ (prefixWord ++ tailWord_185590).sum := by decide
  have hdescent : baseEnd_185590 < baseStart_185590 := by decide
  rcases family_descends (prefixWord ++ tailWord_185590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185604 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_185604 : Nat := 118140960795 + 185604 * 2 ^ 59
def prefixEnd_185604 : Nat := 4983230072969 + 3 ^ 40 * 185604 * 2
def baseEnd_185604 : Nat := 95304063397197057196429

theorem tailTrace_185604 : CollatzResearch.WordTrace tailWord_185604 prefixEnd_185604 95304063397197057196429 := by
  unfold tailWord_185604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384767009797940742325933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4513022679730587656434577 3384767009797940742325933)
  ·
    refine ⟨1269287628674227778372225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3384767009797940742325933 1269287628674227778372225)
    ·
      refine ⟨951965721505670833779169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1269287628674227778372225 951965721505670833779169)
      ·
        refine ⟨713974291129253125334377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 951965721505670833779169 713974291129253125334377)
        ·
          refine ⟨535480718346939844000783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 713974291129253125334377 535480718346939844000783)
          ·
            refine ⟨803221077520409766001175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535480718346939844000783 803221077520409766001175)
            ·
              refine ⟨1204831616280614649001763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 803221077520409766001175 1204831616280614649001763)
              ·
                refine ⟨1807247424420921973502645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1204831616280614649001763 1807247424420921973502645)
                ·
                  refine ⟨169429446039461435015873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807247424420921973502645 169429446039461435015873)
                  ·
                    refine ⟨127072084529596076261905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 169429446039461435015873 127072084529596076261905)
                    ·
                      refine ⟨95304063397197057196429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127072084529596076261905 95304063397197057196429)
                      ·
                        rfl

theorem cell23_185604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_185604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185604 prefixEnd_185604 := by exact prefixLift 185604
  have htrace : WordTrace (prefixWord ++ tailWord_185604) baseStart_185604 baseEnd_185604 := by
    simpa [prefixWord, tailWord_185604, baseEnd_185604] using wordTrace_append hprefix tailTrace_185604
  have hstable : (prefixWord ++ tailWord_185604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185604).length < 2 ^ (prefixWord ++ tailWord_185604).sum := by decide
  have hdescent : baseEnd_185604 < baseStart_185604 := by decide
  rcases family_descends (prefixWord ++ tailWord_185604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185618 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_185618 : Nat := 118140960795 + 185618 * 2 ^ 59
def prefixEnd_185618 : Nat := 4983230072969 + 3 ^ 40 * 185618 * 2
def baseEnd_185618 : Nat := 31770417375453334140455

theorem tailTrace_185618 : CollatzResearch.WordTrace tailWord_185618 prefixEnd_185618 31770417375453334140455 := by
  unfold tailWord_185618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1692511160386290468915377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4513363094363441250441005 1692511160386290468915377)
  ·
    refine ⟨1269383370289717851686533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1692511160386290468915377 1269383370289717851686533)
    ·
      refine ⟨238009381929322097191225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1269383370289717851686533 238009381929322097191225)
      ·
        refine ⟨178507036446991572893419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238009381929322097191225 178507036446991572893419)
        ·
          refine ⟨267760554670487359340129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178507036446991572893419 267760554670487359340129)
          ·
            refine ⟨200820416002865519505097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 267760554670487359340129 200820416002865519505097)
            ·
              refine ⟨150615312002149139628823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200820416002865519505097 150615312002149139628823)
              ·
                refine ⟨225922968003223709443235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150615312002149139628823 225922968003223709443235)
                ·
                  refine ⟨338884452004835564164853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225922968003223709443235 338884452004835564164853)
                  ·
                    refine ⟨31770417375453334140455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 338884452004835564164853 31770417375453334140455)
                    ·
                      rfl

theorem cell23_185618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_185618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185618 prefixEnd_185618 := by exact prefixLift 185618
  have htrace : WordTrace (prefixWord ++ tailWord_185618) baseStart_185618 baseEnd_185618 := by
    simpa [prefixWord, tailWord_185618, baseEnd_185618] using wordTrace_append hprefix tailTrace_185618
  have hstable : (prefixWord ++ tailWord_185618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185618).length < 2 ^ (prefixWord ++ tailWord_185618).sum := by decide
  have hdescent : baseEnd_185618 < baseStart_185618 := by decide
  rcases family_descends (prefixWord ++ tailWord_185618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185624 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_185624 : Nat := 118140960795 + 185624 * 2 ^ 59
def prefixEnd_185624 : Nat := 4983230072969 + 3 ^ 40 * 185624 * 2
def baseEnd_185624 : Nat := 95314333010286978946337

theorem tailTrace_185624 : CollatzResearch.WordTrace tailWord_185624 prefixEnd_185624 95314333010286978946337 := by
  unfold tailWord_185624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385131739761712450189963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4513508986348949933586617 3385131739761712450189963)
  ·
    refine ⟨5077697609642568675284945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385131739761712450189963 5077697609642568675284945)
    ·
      refine ⟨3808273207231926506463709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5077697609642568675284945 3808273207231926506463709)
      ·
        refine ⟨1428102452711972439923891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3808273207231926506463709 1428102452711972439923891)
        ·
          refine ⟨2142153679067958659885837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1428102452711972439923891 2142153679067958659885837)
          ·
            refine ⟨803307629650484497457189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2142153679067958659885837 803307629650484497457189)
            ·
              refine ⟨150620180559465843273223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 803307629650484497457189 150620180559465843273223)
              ·
                refine ⟨225930270839198764909835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150620180559465843273223 225930270839198764909835)
                ·
                  refine ⟨338895406258798147364753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225930270839198764909835 338895406258798147364753)
                  ·
                    refine ⟨254171554694098610523565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 338895406258798147364753 254171554694098610523565)
                    ·
                      refine ⟨95314333010286978946337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254171554694098610523565 95314333010286978946337)
                      ·
                        rfl

theorem cell23_185624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_185624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185624 prefixEnd_185624 := by exact prefixLift 185624
  have htrace : WordTrace (prefixWord ++ tailWord_185624) baseStart_185624 baseEnd_185624 := by
    simpa [prefixWord, tailWord_185624, baseEnd_185624] using wordTrace_append hprefix tailTrace_185624
  have hstable : (prefixWord ++ tailWord_185624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185624).length < 2 ^ (prefixWord ++ tailWord_185624).sum := by decide
  have hdescent : baseEnd_185624 < baseStart_185624 := by decide
  rcases family_descends (prefixWord ++ tailWord_185624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185631 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 2, 4]
def baseStart_185631 : Nat := 118140960795 + 185631 * 2 ^ 59
def prefixEnd_185631 : Nat := 4983230072969 + 3 ^ 40 * 185631 * 2
def baseEnd_185631 : Nat := 31772642458289483852935

theorem tailTrace_185631 : CollatzResearch.WordTrace tailWord_185631 prefixEnd_185631 31772642458289483852935 := by
  unfold tailWord_185631
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770518790498065095884747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4513679193665376730589831 6770518790498065095884747)
  ·
    refine ⟨10155778185747097643827121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6770518790498065095884747 10155778185747097643827121)
    ·
      refine ⟨7616833639310323232870341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10155778185747097643827121 7616833639310323232870341)
      ·
        refine ⟨1428156307370685606163189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7616833639310323232870341 1428156307370685606163189)
        ·
          refine ⟨133889653816001775577799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1428156307370685606163189 133889653816001775577799)
          ·
            refine ⟨200834480724002663366699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133889653816001775577799 200834480724002663366699)
            ·
              refine ⟨301251721086003995050049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200834480724002663366699 301251721086003995050049)
              ·
                refine ⟨225938790814502996287537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301251721086003995050049 225938790814502996287537)
                ·
                  refine ⟨169454093110877247215653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225938790814502996287537 169454093110877247215653)
                  ·
                    refine ⟨31772642458289483852935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169454093110877247215653 31772642458289483852935)
                    ·
                      rfl

theorem cell23_185631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 4].length) (baseStart_185631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185631 prefixEnd_185631 := by exact prefixLift 185631
  have htrace : WordTrace (prefixWord ++ tailWord_185631) baseStart_185631 baseEnd_185631 := by
    simpa [prefixWord, tailWord_185631, baseEnd_185631] using wordTrace_append hprefix tailTrace_185631
  have hstable : (prefixWord ++ tailWord_185631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185631).length < 2 ^ (prefixWord ++ tailWord_185631).sum := by decide
  have hdescent : baseEnd_185631 < baseStart_185631 := by decide
  rcases family_descends (prefixWord ++ tailWord_185631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185661 : List Nat := [1, 4, 1, 5, 2, 1, 2, 7]
def baseStart_185661 : Nat := 118140960795 + 185661 * 2 ^ 59
def prefixEnd_185661 : Nat := 4983230072969 + 3 ^ 40 * 185661 * 2
def baseEnd_185661 : Nat := 3530864140537160525321

theorem tailTrace_185661 : CollatzResearch.WordTrace tailWord_185661 prefixEnd_185661 3530864140537160525321 := by
  unfold tailWord_185661
  simp only [CollatzResearch.WordTrace]
  refine ⟨6771612980389380219476837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4514408653592920146317891 6771612980389380219476837)
  ·
    refine ⟨1269677433823008791151907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6771612980389380219476837 1269677433823008791151907)
    ·
      refine ⟨1904516150734513186727861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1269677433823008791151907 1904516150734513186727861)
      ·
        refine ⟨178548389131360611255737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1904516150734513186727861 178548389131360611255737)
        ·
          refine ⟨133911291848520458441803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178548389131360611255737 133911291848520458441803)
          ·
            refine ⟨200866937772780687662705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133911291848520458441803 200866937772780687662705)
            ·
              refine ⟨150650203329585515747029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200866937772780687662705 150650203329585515747029)
              ·
                refine ⟨3530864140537160525321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150650203329585515747029 3530864140537160525321)
                ·
                  rfl

theorem cell23_185661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 7].length) (baseStart_185661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185661 prefixEnd_185661 := by exact prefixLift 185661
  have htrace : WordTrace (prefixWord ++ tailWord_185661) baseStart_185661 baseEnd_185661 := by
    simpa [prefixWord, tailWord_185661, baseEnd_185661] using wordTrace_append hprefix tailTrace_185661
  have hstable : (prefixWord ++ tailWord_185661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185661).length < 2 ^ (prefixWord ++ tailWord_185661).sum := by decide
  have hdescent : baseEnd_185661 < baseStart_185661 := by decide
  rcases family_descends (prefixWord ++ tailWord_185661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185664 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2]
def baseStart_185664 : Nat := 118140960795 + 185664 * 2 ^ 59
def prefixEnd_185664 : Nat := 4983230072969 + 3 ^ 40 * 185664 * 2
def baseEnd_185664 : Nat := 95334872236466822446153

theorem tailTrace_185664 : CollatzResearch.WordTrace tailWord_185664 prefixEnd_185664 95334872236466822446153 := by
  unfold tailWord_185664
  simp only [CollatzResearch.WordTrace]
  refine ⟨3385861199689255865918023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4514481599585674487890697 3385861199689255865918023)
  ·
    refine ⟨5078791799533883798877035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3385861199689255865918023 5078791799533883798877035)
    ·
      refine ⟨7618187699300825698315553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5078791799533883798877035 7618187699300825698315553)
      ·
        refine ⟨5713640774475619273736665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7618187699300825698315553 5713640774475619273736665)
        ·
          refine ⟨4285230580856714455302499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5713640774475619273736665 4285230580856714455302499)
          ·
            refine ⟨6427845871285071682953749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285230580856714455302499 6427845871285071682953749)
            ·
              refine ⟨301305275216487735138457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6427845871285071682953749 301305275216487735138457)
              ·
                refine ⟨225978956412365801353843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301305275216487735138457 225978956412365801353843)
                ·
                  refine ⟨338968434618548702030765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225978956412365801353843 338968434618548702030765)
                  ·
                    refine ⟨127113162981955763261537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 338968434618548702030765 127113162981955763261537)
                    ·
                      refine ⟨95334872236466822446153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127113162981955763261537 95334872236466822446153)
                      ·
                        rfl

theorem cell23_185664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_185664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185664 prefixEnd_185664 := by exact prefixLift 185664
  have htrace : WordTrace (prefixWord ++ tailWord_185664) baseStart_185664 baseEnd_185664 := by
    simpa [prefixWord, tailWord_185664, baseEnd_185664] using wordTrace_append hprefix tailTrace_185664
  have hstable : (prefixWord ++ tailWord_185664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185664).length < 2 ^ (prefixWord ++ tailWord_185664).sum := by decide
  have hdescent : baseEnd_185664 < baseStart_185664 := by decide
  rcases family_descends (prefixWord ++ tailWord_185664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185680 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_185680 : Nat := 118140960795 + 185680 * 2 ^ 59
def prefixEnd_185680 : Nat := 4983230072969 + 3 ^ 40 * 185680 * 2
def baseEnd_185680 : Nat := 95343087926938759846079

theorem tailTrace_185680 : CollatzResearch.WordTrace tailWord_185680 prefixEnd_185680 95343087926938759846079 := by
  unfold tailWord_185680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3386152983660273232209247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4514870644880364309612329 3386152983660273232209247)
  ·
    refine ⟨5079229475490409848313871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3386152983660273232209247 5079229475490409848313871)
    ·
      refine ⟨7618844213235614772470807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5079229475490409848313871 7618844213235614772470807)
      ·
        refine ⟨11428266319853422158706211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7618844213235614772470807 11428266319853422158706211)
        ·
          refine ⟨17142399479780133238059317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428266319853422158706211 17142399479780133238059317)
          ·
            refine ⟨1607099951229387491068061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17142399479780133238059317 1607099951229387491068061)
            ·
              refine ⟨602662481711020309150523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1607099951229387491068061 602662481711020309150523)
              ·
                refine ⟨903993722566530463725785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602662481711020309150523 903993722566530463725785)
                ·
                  refine ⟨677995291924897847794339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 903993722566530463725785 677995291924897847794339)
                  ·
                    refine ⟨1016992937887346771691509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 677995291924897847794339 1016992937887346771691509)
                    ·
                      refine ⟨95343087926938759846079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1016992937887346771691509 95343087926938759846079)
                      ·
                        rfl

theorem cell23_185680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_185680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185680 prefixEnd_185680 := by exact prefixLift 185680
  have htrace : WordTrace (prefixWord ++ tailWord_185680) baseStart_185680 baseEnd_185680 := by
    simpa [prefixWord, tailWord_185680, baseEnd_185680] using wordTrace_append hprefix tailTrace_185680
  have hstable : (prefixWord ++ tailWord_185680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185680).length < 2 ^ (prefixWord ++ tailWord_185680).sum := by decide
  have hdescent : baseEnd_185680 < baseStart_185680 := by decide
  rcases family_descends (prefixWord ++ tailWord_185680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185690 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4]
def baseStart_185690 : Nat := 118140960795 + 185690 * 2 ^ 59
def prefixEnd_185690 : Nat := 4983230072969 + 3 ^ 40 * 185690 * 2
def baseEnd_185690 : Nat := 95348222733483720721033

theorem tailTrace_185690 : CollatzResearch.WordTrace tailWord_185690 prefixEnd_185690 95348222733483720721033 := by
  unfold tailWord_185690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1693167674321079543070631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4515113798189545448188349 1693167674321079543070631)
  ·
    refine ⟨2539751511481619314605947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1693167674321079543070631 2539751511481619314605947)
    ·
      refine ⟨3809627267222428971908921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539751511481619314605947 3809627267222428971908921)
      ·
        refine ⟨2857220450416821728931691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3809627267222428971908921 2857220450416821728931691)
        ·
          refine ⟨4285830675625232593397537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857220450416821728931691 4285830675625232593397537)
          ·
            refine ⟨3214373006718924445048153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4285830675625232593397537 3214373006718924445048153)
            ·
              refine ⟨2410779755039193333786115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3214373006718924445048153 2410779755039193333786115)
              ·
                refine ⟨3616169632558790000679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410779755039193333786115 3616169632558790000679173)
                ·
                  refine ⟨678031806104773125127345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3616169632558790000679173 678031806104773125127345)
                  ·
                    refine ⟨508523854578579843845509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 678031806104773125127345 508523854578579843845509)
                    ·
                      refine ⟨95348222733483720721033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 508523854578579843845509 95348222733483720721033)
                      ·
                        rfl

theorem cell23_185690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_185690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185690 prefixEnd_185690 := by exact prefixLift 185690
  have htrace : WordTrace (prefixWord ++ tailWord_185690) baseStart_185690 baseEnd_185690 := by
    simpa [prefixWord, tailWord_185690, baseEnd_185690] using wordTrace_append hprefix tailTrace_185690
  have hstable : (prefixWord ++ tailWord_185690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185690).length < 2 ^ (prefixWord ++ tailWord_185690).sum := by decide
  have hdescent : baseEnd_185690 < baseStart_185690 := by decide
  rcases family_descends (prefixWord ++ tailWord_185690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185740 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_185740 : Nat := 118140960795 + 185740 * 2 ^ 59
def prefixEnd_185740 : Nat := 4983230072969 + 3 ^ 40 * 185740 * 2
def baseEnd_185740 : Nat := 95373896766208525095803

theorem tailTrace_185740 : CollatzResearch.WordTrace tailWord_185740 prefixEnd_185740 95373896766208525095803 := by
  unfold tailWord_185740
  simp only [CollatzResearch.WordTrace]
  refine ⟨3387247173551588355801337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4516329564735451141068449 3387247173551588355801337)
  ·
    refine ⟨2540435380163691266851003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3387247173551588355801337 2540435380163691266851003)
    ·
      refine ⟨3810653070245536900276505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2540435380163691266851003 3810653070245536900276505)
      ·
        refine ⟨2857989802684152675207379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3810653070245536900276505 2857989802684152675207379)
        ·
          refine ⟨4286984704026229012811069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857989802684152675207379 4286984704026229012811069)
          ·
            refine ⟨1607619264009835879804151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4286984704026229012811069 1607619264009835879804151)
            ·
              refine ⟨2411428896014753819706227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1607619264009835879804151 2411428896014753819706227)
              ·
                refine ⟨3617143344022130729559341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411428896014753819706227 3617143344022130729559341)
                ·
                  refine ⟨1356428754008299023584753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3617143344022130729559341 1356428754008299023584753)
                  ·
                    refine ⟨1017321565506224267688565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356428754008299023584753 1017321565506224267688565)
                    ·
                      refine ⟨95373896766208525095803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1017321565506224267688565 95373896766208525095803)
                      ·
                        rfl

theorem cell23_185740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_185740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185740 prefixEnd_185740 := by exact prefixLift 185740
  have htrace : WordTrace (prefixWord ++ tailWord_185740) baseStart_185740 baseEnd_185740 := by
    simpa [prefixWord, tailWord_185740, baseEnd_185740] using wordTrace_append hprefix tailTrace_185740
  have hstable : (prefixWord ++ tailWord_185740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185740).length < 2 ^ (prefixWord ++ tailWord_185740).sum := by decide
  have hdescent : baseEnd_185740 < baseStart_185740 := by decide
  rcases family_descends (prefixWord ++ tailWord_185740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185757 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 5]
def baseStart_185757 : Nat := 118140960795 + 185757 * 2 ^ 59
def prefixEnd_185757 : Nat := 4983230072969 + 3 ^ 40 * 185757 * 2
def baseEnd_185757 : Nat := 95382625937334958583225

theorem tailTrace_185757 : CollatzResearch.WordTrace tailWord_185757 prefixEnd_185757 95382625937334958583225 := by
  unfold tailWord_185757
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775114388041588614971525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4516742925361059076647683 6775114388041588614971525)
  ·
    refine ⟨1270333947757797865307161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6775114388041588614971525 1270333947757797865307161)
    ·
      refine ⟨952750460818348398980371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1270333947757797865307161 952750460818348398980371)
      ·
        refine ⟨1429125691227522598470557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 952750460818348398980371 1429125691227522598470557)
        ·
          refine ⟨535922134210320974426459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429125691227522598470557 535922134210320974426459)
          ·
            refine ⟨803883201315481461639689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 535922134210320974426459 803883201315481461639689)
            ·
              refine ⟨602912400986611096229767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 803883201315481461639689 602912400986611096229767)
              ·
                refine ⟨904368601479916644344651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 602912400986611096229767 904368601479916644344651)
                ·
                  refine ⟨1356552902219874966516977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904368601479916644344651 1356552902219874966516977)
                  ·
                    refine ⟨1017414676664906224887733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1356552902219874966516977 1017414676664906224887733)
                    ·
                      refine ⟨95382625937334958583225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1017414676664906224887733 95382625937334958583225)
                      ·
                        rfl

theorem cell23_185757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_185757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185757 prefixEnd_185757 := by exact prefixLift 185757
  have htrace : WordTrace (prefixWord ++ tailWord_185757) baseStart_185757 baseEnd_185757 := by
    simpa [prefixWord, tailWord_185757, baseEnd_185757] using wordTrace_append hprefix tailTrace_185757
  have hstable : (prefixWord ++ tailWord_185757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185757).length < 2 ^ (prefixWord ++ tailWord_185757).sum := by decide
  have hdescent : baseEnd_185757 < baseStart_185757 := by decide
  rcases family_descends (prefixWord ++ tailWord_185757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185767 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_185767 : Nat := 118140960795 + 185767 * 2 ^ 59
def prefixEnd_185767 : Nat := 4983230072969 + 3 ^ 40 * 185767 * 2
def baseEnd_185767 : Nat := 95387760743879919458179

theorem tailTrace_185767 : CollatzResearch.WordTrace tailWord_185767 prefixEnd_185767 95387760743879919458179 := by
  unfold tailWord_185767
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775479118005360322835555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4516986078670240215223703 6775479118005360322835555)
  ·
    refine ⟨10163218677008040484253333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775479118005360322835555 10163218677008040484253333)
    ·
      refine ⟨476400875484751897699375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10163218677008040484253333 476400875484751897699375)
      ·
        refine ⟨714601313227127846549063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 476400875484751897699375 714601313227127846549063)
        ·
          refine ⟨1071901969840691769823595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 714601313227127846549063 1071901969840691769823595)
          ·
            refine ⟨1607852954761037654735393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1071901969840691769823595 1607852954761037654735393)
            ·
              refine ⟨1205889716070778241051545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1607852954761037654735393 1205889716070778241051545)
              ·
                refine ⟨904417287053083680788659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1205889716070778241051545 904417287053083680788659)
                ·
                  refine ⟨1356625930579625521182989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 904417287053083680788659 1356625930579625521182989)
                  ·
                    refine ⟨508734723967359570443621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1356625930579625521182989 508734723967359570443621)
                    ·
                      refine ⟨95387760743879919458179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 508734723967359570443621 95387760743879919458179)
                      ·
                        rfl

theorem cell23_185767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_185767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185767 prefixEnd_185767 := by exact prefixLift 185767
  have htrace : WordTrace (prefixWord ++ tailWord_185767) baseStart_185767 baseEnd_185767 := by
    simpa [prefixWord, tailWord_185767, baseEnd_185767] using wordTrace_append hprefix tailTrace_185767
  have hstable : (prefixWord ++ tailWord_185767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185767).length < 2 ^ (prefixWord ++ tailWord_185767).sum := by decide
  have hdescent : baseEnd_185767 < baseStart_185767 := by decide
  rcases family_descends (prefixWord ++ tailWord_185767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185807 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 6]
def baseStart_185807 : Nat := 118140960795 + 185807 * 2 ^ 59
def prefixEnd_185807 : Nat := 4983230072969 + 3 ^ 40 * 185807 * 2
def baseEnd_185807 : Nat := 10600922218895529217555

theorem tailTrace_185807 : CollatzResearch.WordTrace tailWord_185807 prefixEnd_185807 10600922218895529217555 := by
  unfold tailWord_185807
  simp only [CollatzResearch.WordTrace]
  refine ⟨6776938037860447154291675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4517958691906964769527783 6776938037860447154291675)
  ·
    refine ⟨10165407056790670731437513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6776938037860447154291675 10165407056790670731437513)
    ·
      refine ⟨7624055292593003048578135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10165407056790670731437513 7624055292593003048578135)
      ·
        refine ⟨11436082938889504572867203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624055292593003048578135 11436082938889504572867203)
        ·
          refine ⟨17154124408334256859300805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11436082938889504572867203 17154124408334256859300805)
          ·
            refine ⟨3216398326562673161118901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17154124408334256859300805 3216398326562673161118901)
            ·
              refine ⟨301537343115250608854897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3216398326562673161118901 301537343115250608854897)
              ·
                refine ⟨226153007336437956641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301537343115250608854897 226153007336437956641173)
                ·
                  refine ⟨10600922218895529217555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 226153007336437956641173 10600922218895529217555)
                  ·
                    rfl

theorem cell23_185807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 6].length) (baseStart_185807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185807 prefixEnd_185807 := by exact prefixLift 185807
  have htrace : WordTrace (prefixWord ++ tailWord_185807) baseStart_185807 baseEnd_185807 := by
    simpa [prefixWord, tailWord_185807, baseEnd_185807] using wordTrace_append hprefix tailTrace_185807
  have hstable : (prefixWord ++ tailWord_185807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185807).length < 2 ^ (prefixWord ++ tailWord_185807).sum := by decide
  have hdescent : baseEnd_185807 < baseStart_185807 := by decide
  rcases family_descends (prefixWord ++ tailWord_185807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185845 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_185845 : Nat := 118140960795 + 185845 * 2 ^ 59
def prefixEnd_185845 : Nat := 4983230072969 + 3 ^ 40 * 185845 * 2
def baseEnd_185845 : Nat := 31809270744976871427607

theorem tailTrace_185845 : CollatzResearch.WordTrace tailWord_185845 prefixEnd_185845 31809270744976871427607 := by
  unfold tailWord_185845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6778324011722779644174989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4518882674481853096116659 6778324011722779644174989)
  ·
    refine ⟨2541871504396042366565621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6778324011722779644174989 2541871504396042366565621)
    ·
      refine ⟨238300453537128971865527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2541871504396042366565621 238300453537128971865527)
      ·
        refine ⟨357450680305693457798291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238300453537128971865527 357450680305693457798291)
        ·
          refine ⟨536176020458540186697437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357450680305693457798291 536176020458540186697437)
          ·
            refine ⟨201066007671952570011539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 536176020458540186697437 201066007671952570011539)
            ·
              refine ⟨301599011507928855017309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201066007671952570011539 301599011507928855017309)
              ·
                refine ⟨113099629315473320631491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301599011507928855017309 113099629315473320631491)
                ·
                  refine ⟨169649443973209980947237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113099629315473320631491 169649443973209980947237)
                  ·
                    refine ⟨31809270744976871427607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169649443973209980947237 31809270744976871427607)
                    ·
                      rfl

theorem cell23_185845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_185845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185845 prefixEnd_185845 := by exact prefixLift 185845
  have htrace : WordTrace (prefixWord ++ tailWord_185845) baseStart_185845 baseEnd_185845 := by
    simpa [prefixWord, tailWord_185845, baseEnd_185845] using wordTrace_append hprefix tailTrace_185845
  have hstable : (prefixWord ++ tailWord_185845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185845).length < 2 ^ (prefixWord ++ tailWord_185845).sum := by decide
  have hdescent : baseEnd_185845 < baseStart_185845 := by decide
  rcases family_descends (prefixWord ++ tailWord_185845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185862 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_185862 : Nat := 118140960795 + 185862 * 2 ^ 59
def prefixEnd_185862 : Nat := 4983230072969 + 3 ^ 40 * 185862 * 2
def baseEnd_185862 : Nat := 31812180468685682590081

theorem tailTrace_185862 : CollatzResearch.WordTrace tailWord_185862 prefixEnd_185862 31812180468685682590081 := by
  unfold tailWord_185862
  simp only [CollatzResearch.WordTrace]
  refine ⟨211842001645662235860745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4519296035107461031695893 211842001645662235860745)
  ·
    refine ⟨158881501234246676895559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 211842001645662235860745 158881501234246676895559)
    ·
      refine ⟨238322251851370015343339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158881501234246676895559 238322251851370015343339)
      ·
        refine ⟨357483377777055023015009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238322251851370015343339 357483377777055023015009)
        ·
          refine ⟨268112533332791267261257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 357483377777055023015009 268112533332791267261257)
          ·
            refine ⟨201084399999593450445943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268112533332791267261257 201084399999593450445943)
            ·
              refine ⟨301626599999390175668915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201084399999593450445943 301626599999390175668915)
              ·
                refine ⟨452439899999085263503373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301626599999390175668915 452439899999085263503373)
                ·
                  refine ⟨169664962499656973813765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452439899999085263503373 169664962499656973813765)
                  ·
                    refine ⟨31812180468685682590081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169664962499656973813765 31812180468685682590081)
                    ·
                      rfl

theorem cell23_185862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_185862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185862 prefixEnd_185862 := by exact prefixLift 185862
  have htrace : WordTrace (prefixWord ++ tailWord_185862) baseStart_185862 baseEnd_185862 := by
    simpa [prefixWord, tailWord_185862, baseEnd_185862] using wordTrace_append hprefix tailTrace_185862
  have hstable : (prefixWord ++ tailWord_185862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185862).length < 2 ^ (prefixWord ++ tailWord_185862).sum := by decide
  have hdescent : baseEnd_185862 < baseStart_185862 := by decide
  rcases family_descends (prefixWord ++ tailWord_185862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185868 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_185868 : Nat := 118140960795 + 185868 * 2 ^ 59
def prefixEnd_185868 : Nat := 4983230072969 + 3 ^ 40 * 185868 * 2
def baseEnd_185868 : Nat := 95439622289984024295215

theorem tailTrace_185868 : CollatzResearch.WordTrace tailWord_185868 prefixEnd_185868 95439622289984024295215 := by
  unfold tailWord_185868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389581445319727286131129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4519441927092969714841505 3389581445319727286131129)
  ·
    refine ⟨2542186083989795464598347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3389581445319727286131129 2542186083989795464598347)
    ·
      refine ⟨3813279125984693196897521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2542186083989795464598347 3813279125984693196897521)
      ·
        refine ⟨2859959344488519897673141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3813279125984693196897521 2859959344488519897673141)
        ·
          refine ⟨268121188545798740406857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2859959344488519897673141 268121188545798740406857)
          ·
            refine ⟨201090891409349055305143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268121188545798740406857 201090891409349055305143)
            ·
              refine ⟨301636337114023582957715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201090891409349055305143 301636337114023582957715)
              ·
                refine ⟨452454505671035374436573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301636337114023582957715 452454505671035374436573)
                ·
                  refine ⟨169670439626638265413715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 452454505671035374436573 169670439626638265413715)
                  ·
                    refine ⟨254505659439957398120573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169670439626638265413715 254505659439957398120573)
                    ·
                      refine ⟨95439622289984024295215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254505659439957398120573 95439622289984024295215)
                      ·
                        rfl

theorem cell23_185868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_185868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185868 prefixEnd_185868 := by exact prefixLift 185868
  have htrace : WordTrace (prefixWord ++ tailWord_185868) baseStart_185868 baseEnd_185868 := by
    simpa [prefixWord, tailWord_185868, baseEnd_185868] using wordTrace_append hprefix tailTrace_185868
  have hstable : (prefixWord ++ tailWord_185868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185868).length < 2 ^ (prefixWord ++ tailWord_185868).sum := by decide
  have hdescent : baseEnd_185868 < baseStart_185868 := by decide
  rcases family_descends (prefixWord ++ tailWord_185868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185887 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_185887 : Nat := 118140960795 + 185887 * 2 ^ 59
def prefixEnd_185887 : Nat := 4983230072969 + 3 ^ 40 * 185887 * 2
def baseEnd_185887 : Nat := 95449378422419449957627

theorem tailTrace_185887 : CollatzResearch.WordTrace tailWord_185887 prefixEnd_185887 95449378422419449957627 := by
  unfold tailWord_185887
  simp only [CollatzResearch.WordTrace]
  refine ⟨6779855877570620817203915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4519903918380413878135943 6779855877570620817203915)
  ·
    refine ⟨10169783816355931225805873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6779855877570620817203915 10169783816355931225805873)
    ·
      refine ⟨7627337862266948419354405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10169783816355931225805873 7627337862266948419354405)
      ·
        refine ⟨1430125849175052828628951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7627337862266948419354405 1430125849175052828628951)
        ·
          refine ⟨2145188773762579242943427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1430125849175052828628951 2145188773762579242943427)
          ·
            refine ⟨3217783160643868864415141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145188773762579242943427 3217783160643868864415141)
            ·
              refine ⟨603334342620725412077839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3217783160643868864415141 603334342620725412077839)
              ·
                refine ⟨905001513931088118116759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603334342620725412077839 905001513931088118116759)
                ·
                  refine ⟨1357502270896632177175139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 905001513931088118116759 1357502270896632177175139)
                  ·
                    refine ⟨2036253406344948265762709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1357502270896632177175139 2036253406344948265762709)
                    ·
                      refine ⟨95449378422419449957627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2036253406344948265762709 95449378422419449957627)
                      ·
                        rfl

theorem cell23_185887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_185887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185887 prefixEnd_185887 := by exact prefixLift 185887
  have htrace : WordTrace (prefixWord ++ tailWord_185887) baseStart_185887 baseEnd_185887 := by
    simpa [prefixWord, tailWord_185887, baseEnd_185887] using wordTrace_append hprefix tailTrace_185887
  have hstable : (prefixWord ++ tailWord_185887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185887).length < 2 ^ (prefixWord ++ tailWord_185887).sum := by decide
  have hdescent : baseEnd_185887 < baseStart_185887 := by decide
  rcases family_descends (prefixWord ++ tailWord_185887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185967 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_185967 : Nat := 118140960795 + 185967 * 2 ^ 59
def prefixEnd_185967 : Nat := 4983230072969 + 3 ^ 40 * 185967 * 2
def baseEnd_185967 : Nat := 95490456874779136957259

theorem tailTrace_185967 : CollatzResearch.WordTrace tailWord_185967 prefixEnd_185967 95490456874779136957259 := by
  unfold tailWord_185967
  simp only [CollatzResearch.WordTrace]
  refine ⟨6782773717280794480116155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4521849144853862986744103 6782773717280794480116155)
  ·
    refine ⟨10174160575921191720174233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6782773717280794480116155 10174160575921191720174233)
    ·
      refine ⟨7630620431940893790130675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10174160575921191720174233 7630620431940893790130675)
      ·
        refine ⟨11445930647911340685196013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630620431940893790130675 11445930647911340685196013)
        ·
          refine ⟨4292223992966752756948505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11445930647911340685196013 4292223992966752756948505)
          ·
            refine ⟨3219167994725064567711379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4292223992966752756948505 3219167994725064567711379)
            ·
              refine ⟨4828751992087596851567069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3219167994725064567711379 4828751992087596851567069)
              ·
                refine ⟨1810781997032848819337651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4828751992087596851567069 1810781997032848819337651)
                ·
                  refine ⟨2716172995549273229006477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810781997032848819337651 2716172995549273229006477)
                  ·
                    refine ⟨1018564873330977460877429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2716172995549273229006477 1018564873330977460877429)
                    ·
                      refine ⟨95490456874779136957259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1018564873330977460877429 95490456874779136957259)
                      ·
                        rfl

theorem cell23_185967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_185967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185967 prefixEnd_185967 := by exact prefixLift 185967
  have htrace : WordTrace (prefixWord ++ tailWord_185967) baseStart_185967 baseEnd_185967 := by
    simpa [prefixWord, tailWord_185967, baseEnd_185967] using wordTrace_append hprefix tailTrace_185967
  have hstable : (prefixWord ++ tailWord_185967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185967).length < 2 ^ (prefixWord ++ tailWord_185967).sum := by decide
  have hdescent : baseEnd_185967 < baseStart_185967 := by decide
  rcases family_descends (prefixWord ++ tailWord_185967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185968 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2]
def baseStart_185968 : Nat := 118140960795 + 185968 * 2 ^ 59
def prefixEnd_185968 : Nat := 4983230072969 + 3 ^ 40 * 185968 * 2
def baseEnd_185968 : Nat := 95490970355433633044755

theorem tailTrace_185968 : CollatzResearch.WordTrace tailWord_185968 prefixEnd_185968 95490970355433633044755 := by
  unfold tailWord_185968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391405095138585825451279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4521873460184781100601705 3391405095138585825451279)
  ·
    refine ⟨5087107642707878738176919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391405095138585825451279 5087107642707878738176919)
    ·
      refine ⟨7630661464061818107265379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5087107642707878738176919 7630661464061818107265379)
      ·
        refine ⟨11445992196092727160898069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7630661464061818107265379 11445992196092727160898069)
        ·
          refine ⟨536530884191846585667097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11445992196092727160898069 536530884191846585667097)
          ·
            refine ⟨402398163143884939250323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536530884191846585667097 402398163143884939250323)
            ·
              refine ⟨603597244715827408875485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402398163143884939250323 603597244715827408875485)
              ·
                refine ⟨226348966768435278328307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 603597244715827408875485 226348966768435278328307)
                ·
                  refine ⟨339523450152652917492461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226348966768435278328307 339523450152652917492461)
                  ·
                    refine ⟨127321293807244844059673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 339523450152652917492461 127321293807244844059673)
                    ·
                      refine ⟨95490970355433633044755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127321293807244844059673 95490970355433633044755)
                      ·
                        rfl

theorem cell23_185968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 1, 3, 2].length) (baseStart_185968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185968 prefixEnd_185968 := by exact prefixLift 185968
  have htrace : WordTrace (prefixWord ++ tailWord_185968) baseStart_185968 baseEnd_185968 := by
    simpa [prefixWord, tailWord_185968, baseEnd_185968] using wordTrace_append hprefix tailTrace_185968
  have hstable : (prefixWord ++ tailWord_185968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185968).length < 2 ^ (prefixWord ++ tailWord_185968).sum := by decide
  have hdescent : baseEnd_185968 < baseStart_185968 := by decide
  rcases family_descends (prefixWord ++ tailWord_185968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185992 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_185992 : Nat := 118140960795 + 185992 * 2 ^ 59
def prefixEnd_185992 : Nat := 4983230072969 + 3 ^ 40 * 185992 * 2
def baseEnd_185992 : Nat := 95503293891141539144645

theorem tailTrace_185992 : CollatzResearch.WordTrace tailWord_185992 prefixEnd_185992 95503293891141539144645 := by
  unfold tailWord_185992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3391842771095111874888115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4522457028126815833184153 3391842771095111874888115)
  ·
    refine ⟨5087764156642667812332173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3391842771095111874888115 5087764156642667812332173)
    ·
      refine ⟨1907911558741000429624565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5087764156642667812332173 1907911558741000429624565)
      ·
        refine ⟨178866708631968790277303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1907911558741000429624565 178866708631968790277303)
        ·
          refine ⟨268300062947953185415955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178866708631968790277303 268300062947953185415955)
          ·
            refine ⟨402450094421929778123933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268300062947953185415955 402450094421929778123933)
            ·
              refine ⟨150918785408223666796475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 402450094421929778123933 150918785408223666796475)
              ·
                refine ⟨226378178112335500194713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150918785408223666796475 226378178112335500194713)
                ·
                  refine ⟨169783633584251625146035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226378178112335500194713 169783633584251625146035)
                  ·
                    refine ⟨254675450376377437719053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169783633584251625146035 254675450376377437719053)
                    ·
                      refine ⟨95503293891141539144645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254675450376377437719053 95503293891141539144645)
                      ·
                        rfl

theorem cell23_185992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_185992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185992 prefixEnd_185992 := by exact prefixLift 185992
  have htrace : WordTrace (prefixWord ++ tailWord_185992) baseStart_185992 baseEnd_185992 := by
    simpa [prefixWord, tailWord_185992, baseEnd_185992] using wordTrace_append hprefix tailTrace_185992
  have hstable : (prefixWord ++ tailWord_185992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185992).length < 2 ^ (prefixWord ++ tailWord_185992).sum := by decide
  have hdescent : baseEnd_185992 < baseStart_185992 := by decide
  rcases family_descends (prefixWord ++ tailWord_185992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_185998 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_185998 : Nat := 118140960795 + 185998 * 2 ^ 59
def prefixEnd_185998 : Nat := 4983230072969 + 3 ^ 40 * 185998 * 2
def baseEnd_185998 : Nat := 95506374775068515669617

theorem tailTrace_185998 : CollatzResearch.WordTrace tailWord_185998 prefixEnd_185998 95506374775068515669617 := by
  unfold tailWord_185998
  simp only [CollatzResearch.WordTrace]
  refine ⟨847988047521060846811831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4522602920112324516329765 847988047521060846811831)
  ·
    refine ⟨1271982071281591270217747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 847988047521060846811831 1271982071281591270217747)
    ·
      refine ⟨1907973106922386905326621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1271982071281591270217747 1907973106922386905326621)
      ·
        refine ⟨715489915095895089497483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1907973106922386905326621 715489915095895089497483)
        ·
          refine ⟨1073234872643842634246225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715489915095895089497483 1073234872643842634246225)
          ·
            refine ⟨804926154482881975684669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073234872643842634246225 804926154482881975684669)
            ·
              refine ⟨301847307931080740881751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 804926154482881975684669 301847307931080740881751)
              ·
                refine ⟨452770961896621111322627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301847307931080740881751 452770961896621111322627)
                ·
                  refine ⟨679156442844931666983941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 452770961896621111322627 679156442844931666983941)
                  ·
                    refine ⟨127341833033424687559489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 679156442844931666983941 127341833033424687559489)
                    ·
                      refine ⟨95506374775068515669617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127341833033424687559489 95506374775068515669617)
                      ·
                        rfl

theorem cell23_185998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_185998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_185998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_185998 prefixEnd_185998 := by exact prefixLift 185998
  have htrace : WordTrace (prefixWord ++ tailWord_185998) baseStart_185998 baseEnd_185998 := by
    simpa [prefixWord, tailWord_185998, baseEnd_185998] using wordTrace_append hprefix tailTrace_185998
  have hstable : (prefixWord ++ tailWord_185998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_185998).length < 2 ^ (prefixWord ++ tailWord_185998).sum := by decide
  have hdescent : baseEnd_185998 < baseStart_185998 := by decide
  rcases family_descends (prefixWord ++ tailWord_185998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186018 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 1, 5]
def baseStart_186018 : Nat := 118140960795 + 186018 * 2 ^ 59
def prefixEnd_186018 : Nat := 4983230072969 + 3 ^ 40 * 186018 * 2
def baseEnd_186018 : Nat := 95516644388158437419525

theorem tailTrace_186018 : CollatzResearch.WordTrace tailWord_186018 prefixEnd_186018 95516644388158437419525 := by
  unfold tailWord_186018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696158460024007547555677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4523089226730686793481805 1696158460024007547555677)
  ·
    refine ⟨636059422509002830333379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1696158460024007547555677 636059422509002830333379)
    ·
      refine ⟨954089133763504245500069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636059422509002830333379 954089133763504245500069)
      ·
        refine ⟨178891712580657046031263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 954089133763504245500069 178891712580657046031263)
        ·
          refine ⟨268337568870985569046895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 178891712580657046031263 268337568870985569046895)
          ·
            refine ⟨402506353306478353570343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268337568870985569046895 402506353306478353570343)
            ·
              refine ⟨603759529959717530355515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 402506353306478353570343 603759529959717530355515)
              ·
                refine ⟨905639294939576295533273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 603759529959717530355515 905639294939576295533273)
                ·
                  refine ⟨679229471204682221649955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 905639294939576295533273 679229471204682221649955)
                  ·
                    refine ⟨1018844206807023332474933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 679229471204682221649955 1018844206807023332474933)
                    ·
                      refine ⟨95516644388158437419525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1018844206807023332474933 95516644388158437419525)
                      ·
                        rfl

theorem cell23_186018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_186018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186018 prefixEnd_186018 := by exact prefixLift 186018
  have htrace : WordTrace (prefixWord ++ tailWord_186018) baseStart_186018 baseEnd_186018 := by
    simpa [prefixWord, tailWord_186018, baseEnd_186018] using wordTrace_append hprefix tailTrace_186018
  have hstable : (prefixWord ++ tailWord_186018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186018).length < 2 ^ (prefixWord ++ tailWord_186018).sum := by decide
  have hdescent : baseEnd_186018 < baseStart_186018 := by decide
  rcases family_descends (prefixWord ++ tailWord_186018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186021 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 5]
def baseStart_186021 : Nat := 118140960795 + 186021 * 2 ^ 59
def prefixEnd_186021 : Nat := 4983230072969 + 3 ^ 40 * 186021 * 2
def baseEnd_186021 : Nat := 10613131647791325075779

theorem tailTrace_186021 : CollatzResearch.WordTrace tailWord_186021 prefixEnd_186021 10613131647791325075779 := by
  unfold tailWord_186021
  simp only [CollatzResearch.WordTrace]
  refine ⟨6784743259085161702581917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4523162172723441135054611 6784743259085161702581917)
  ·
    refine ⟨2544278722156935638468219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6784743259085161702581917 2544278722156935638468219)
    ·
      refine ⟨3816418083235403457702329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2544278722156935638468219 3816418083235403457702329)
      ·
        refine ⟨2862313562426552593276747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3816418083235403457702329 2862313562426552593276747)
        ·
          refine ⟨4293470343639828889915121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862313562426552593276747 4293470343639828889915121)
          ·
            refine ⟨3220102757729871667436341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293470343639828889915121 3220102757729871667436341)
            ·
              refine ⟨301884633537175468822157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3220102757729871667436341 301884633537175468822157)
              ·
                refine ⟨113206737576440800808309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 301884633537175468822157 113206737576440800808309)
                ·
                  refine ⟨10613131647791325075779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113206737576440800808309 10613131647791325075779)
                  ·
                    rfl

theorem cell23_186021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_186021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186021 prefixEnd_186021 := by exact prefixLift 186021
  have htrace : WordTrace (prefixWord ++ tailWord_186021) baseStart_186021 baseEnd_186021 := by
    simpa [prefixWord, tailWord_186021, baseEnd_186021] using wordTrace_append hprefix tailTrace_186021
  have hstable : (prefixWord ++ tailWord_186021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186021).length < 2 ^ (prefixWord ++ tailWord_186021).sum := by decide
  have hdescent : baseEnd_186021 < baseStart_186021 := by decide
  rcases family_descends (prefixWord ++ tailWord_186021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186034 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_186034 : Nat := 118140960795 + 186034 * 2 ^ 59
def prefixEnd_186034 : Nat := 4983230072969 + 3 ^ 40 * 186034 * 2
def baseEnd_186034 : Nat := 31841620026210124939817

theorem tailTrace_186034 : CollatzResearch.WordTrace tailWord_186034 prefixEnd_186034 31841620026210124939817 := by
  unfold tailWord_186034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696304352009516230701289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4523478272025376615203437 1696304352009516230701289)
  ·
    refine ⟨1272228264007137173025967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1696304352009516230701289 1272228264007137173025967)
    ·
      refine ⟨1908342396010705759538951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272228264007137173025967 1908342396010705759538951)
      ·
        refine ⟨2862513594016058639308427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908342396010705759538951 2862513594016058639308427)
        ·
          refine ⟨4293770391024087958962641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2862513594016058639308427 4293770391024087958962641)
          ·
            refine ⟨3220327793268065969221981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4293770391024087958962641 3220327793268065969221981)
            ·
              refine ⟨1207622922475524738458243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3220327793268065969221981 1207622922475524738458243)
              ·
                refine ⟨1811434383713287107687365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207622922475524738458243 1811434383713287107687365)
                ·
                  refine ⟨339643946946241332691381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1811434383713287107687365 339643946946241332691381)
                  ·
                    refine ⟨31841620026210124939817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 339643946946241332691381 31841620026210124939817)
                    ·
                      rfl

theorem cell23_186034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_186034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186034 prefixEnd_186034 := by exact prefixLift 186034
  have htrace : WordTrace (prefixWord ++ tailWord_186034) baseStart_186034 baseEnd_186034 := by
    simpa [prefixWord, tailWord_186034, baseEnd_186034] using wordTrace_append hprefix tailTrace_186034
  have hstable : (prefixWord ++ tailWord_186034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186034).length < 2 ^ (prefixWord ++ tailWord_186034).sum := by decide
  have hdescent : baseEnd_186034 < baseStart_186034 := by decide
  rcases family_descends (prefixWord ++ tailWord_186034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186038 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_186038 : Nat := 118140960795 + 186038 * 2 ^ 59
def prefixEnd_186038 : Nat := 4983230072969 + 3 ^ 40 * 186038 * 2
def baseEnd_186038 : Nat := 10614101555694262129937

theorem tailTrace_186038 : CollatzResearch.WordTrace tailWord_186038 prefixEnd_186038 10614101555694262129937 := by
  unfold tailWord_186038
  simp only [CollatzResearch.WordTrace]
  refine ⟨424085206251473350371923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4523575533349049070633845 424085206251473350371923)
  ·
    refine ⟨636127809377210025557885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 424085206251473350371923 636127809377210025557885)
    ·
      refine ⟨238547928516453759584207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 636127809377210025557885 238547928516453759584207)
      ·
        refine ⟨357821892774680639376311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238547928516453759584207 357821892774680639376311)
        ·
          refine ⟨536732839162020959064467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357821892774680639376311 536732839162020959064467)
          ·
            refine ⟨805099258743031438596701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 536732839162020959064467 805099258743031438596701)
            ·
              refine ⟨301912222028636789473763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805099258743031438596701 301912222028636789473763)
              ·
                refine ⟨452868333042955184210645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301912222028636789473763 452868333042955184210645)
                ·
                  refine ⟨10614101555694262129937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 452868333042955184210645 10614101555694262129937)
                  ·
                    rfl

theorem cell23_186038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_186038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186038 prefixEnd_186038 := by exact prefixLift 186038
  have htrace : WordTrace (prefixWord ++ tailWord_186038) baseStart_186038 baseEnd_186038 := by
    simpa [prefixWord, tailWord_186038, baseEnd_186038] using wordTrace_append hprefix tailTrace_186038
  have hstable : (prefixWord ++ tailWord_186038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186038).length < 2 ^ (prefixWord ++ tailWord_186038).sum := by decide
  have hdescent : baseEnd_186038 < baseStart_186038 := by decide
  rcases family_descends (prefixWord ++ tailWord_186038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186044 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_186044 : Nat := 118140960795 + 186044 * 2 ^ 59
def prefixEnd_186044 : Nat := 4983230072969 + 3 ^ 40 * 186044 * 2
def baseEnd_186044 : Nat := 95529994885175335694405

theorem tailTrace_186044 : CollatzResearch.WordTrace tailWord_186044 prefixEnd_186044 95529994885175335694405 := by
  unfold tailWord_186044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392791069000918315334593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4523721425334557753779457 3392791069000918315334593)
  ·
    refine ⟨2544593301750688736500945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3392791069000918315334593 2544593301750688736500945)
    ·
      refine ⟨1908444976313016552375709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2544593301750688736500945 1908444976313016552375709)
      ·
        refine ⟨715666866117381207140891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1908444976313016552375709 715666866117381207140891)
        ·
          refine ⟨1073500299176071810711337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 715666866117381207140891 1073500299176071810711337)
          ·
            refine ⟨805125224382053858033503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1073500299176071810711337 805125224382053858033503)
            ·
              refine ⟨1207687836573080787050255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 805125224382053858033503 1207687836573080787050255)
              ·
                refine ⟨1811531754859621180575383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207687836573080787050255 1811531754859621180575383)
                ·
                  refine ⟨2717297632289431770863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1811531754859621180575383 2717297632289431770863075)
                  ·
                    refine ⟨4075946448434147656294613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2717297632289431770863075 4075946448434147656294613)
                    ·
                      refine ⟨95529994885175335694405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4075946448434147656294613 95529994885175335694405)
                      ·
                        rfl

theorem cell23_186044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_186044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186044 prefixEnd_186044 := by exact prefixLift 186044
  have htrace : WordTrace (prefixWord ++ tailWord_186044) baseStart_186044 baseEnd_186044 := by
    simpa [prefixWord, tailWord_186044, baseEnd_186044] using wordTrace_append hprefix tailTrace_186044
  have hstable : (prefixWord ++ tailWord_186044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186044).length < 2 ^ (prefixWord ++ tailWord_186044).sum := by decide
  have hdescent : baseEnd_186044 < baseStart_186044 := by decide
  rcases family_descends (prefixWord ++ tailWord_186044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186068 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_186068 : Nat := 118140960795 + 186068 * 2 ^ 59
def prefixEnd_186068 : Nat := 4983230072969 + 3 ^ 40 * 186068 * 2
def baseEnd_186068 : Nat := 31847439473627747264765

theorem tailTrace_186068 : CollatzResearch.WordTrace tailWord_186068 prefixEnd_186068 31847439473627747264765 := by
  unfold tailWord_186068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393228744957444364771429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4524304993276592486361905 3393228744957444364771429)
  ·
    refine ⟨636230389679520818394643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3393228744957444364771429 636230389679520818394643)
    ·
      refine ⟨954345584519281227591965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 636230389679520818394643 954345584519281227591965)
      ·
        refine ⟨357879594194730460346987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 954345584519281227591965 357879594194730460346987)
        ·
          refine ⟨536819391292095690520481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 357879594194730460346987 536819391292095690520481)
          ·
            refine ⟨402614543469071767890361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 536819391292095690520481 402614543469071767890361)
            ·
              refine ⟨301960907601803825917771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 402614543469071767890361 301960907601803825917771)
              ·
                refine ⟨452941361402705738876657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301960907601803825917771 452941361402705738876657)
                ·
                  refine ⟨339706021052029304157493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452941361402705738876657 339706021052029304157493)
                  ·
                    refine ⟨31847439473627747264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 339706021052029304157493 31847439473627747264765)
                    ·
                      rfl

theorem cell23_186068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_186068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186068 prefixEnd_186068 := by exact prefixLift 186068
  have htrace : WordTrace (prefixWord ++ tailWord_186068) baseStart_186068 baseEnd_186068 := by
    simpa [prefixWord, tailWord_186068, baseEnd_186068] using wordTrace_append hprefix tailTrace_186068
  have hstable : (prefixWord ++ tailWord_186068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186068).length < 2 ^ (prefixWord ++ tailWord_186068).sum := by decide
  have hdescent : baseEnd_186068 < baseStart_186068 := by decide
  rcases family_descends (prefixWord ++ tailWord_186068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186071 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4]
def baseStart_186071 : Nat := 118140960795 + 186071 * 2 ^ 59
def prefixEnd_186071 : Nat := 4983230072969 + 3 ^ 40 * 186071 * 2
def baseEnd_186071 : Nat := 95543858862846730056781

theorem tailTrace_186071 : CollatzResearch.WordTrace tailWord_186071 prefixEnd_186071 95543858862846730056781 := by
  unfold tailWord_186071
  simp only [CollatzResearch.WordTrace]
  refine ⟨6786566908904020241902067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524377939269346827934711 6786566908904020241902067)
  ·
    refine ⟨10179850363356030362853101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6786566908904020241902067 10179850363356030362853101)
    ·
      refine ⟨3817443886258511386069913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10179850363356030362853101 3817443886258511386069913)
      ·
        refine ⟨2863082914693883539552435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3817443886258511386069913 2863082914693883539552435)
        ·
          refine ⟨4294624372040825309328653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863082914693883539552435 4294624372040825309328653)
          ·
            refine ⟨1610484139515309490998245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4294624372040825309328653 1610484139515309490998245)
            ·
              refine ⟨301965776159120529562171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1610484139515309490998245 301965776159120529562171)
              ·
                refine ⟨452948664238680794343257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 301965776159120529562171 452948664238680794343257)
                ·
                  refine ⟨339711498179010595757443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452948664238680794343257 339711498179010595757443)
                  ·
                    refine ⟨509567247268515893636165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 339711498179010595757443 509567247268515893636165)
                    ·
                      refine ⟨95543858862846730056781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 509567247268515893636165 95543858862846730056781)
                      ·
                        rfl

theorem cell23_186071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_186071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186071 prefixEnd_186071 := by exact prefixLift 186071
  have htrace : WordTrace (prefixWord ++ tailWord_186071) baseStart_186071 baseEnd_186071 := by
    simpa [prefixWord, tailWord_186071, baseEnd_186071] using wordTrace_append hprefix tailTrace_186071
  have hstable : (prefixWord ++ tailWord_186071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186071).length < 2 ^ (prefixWord ++ tailWord_186071).sum := by decide
  have hdescent : baseEnd_186071 < baseStart_186071 := by decide
  rcases family_descends (prefixWord ++ tailWord_186071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186084 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_186084 : Nat := 118140960795 + 186084 * 2 ^ 59
def prefixEnd_186084 : Nat := 4983230072969 + 3 ^ 40 * 186084 * 2
def baseEnd_186084 : Nat := 95550534111355179194221

theorem tailTrace_186084 : CollatzResearch.WordTrace tailWord_186084 prefixEnd_186084 95550534111355179194221 := by
  unfold tailWord_186084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3393520528928461731062653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4524694038571282308083537 3393520528928461731062653)
  ·
    refine ⟨1272570198348173149148495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3393520528928461731062653 1272570198348173149148495)
    ·
      refine ⟨1908855297522259723722743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1272570198348173149148495 1908855297522259723722743)
      ·
        refine ⟨2863282946283389585584115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1908855297522259723722743 2863282946283389585584115)
        ·
          refine ⟨4294924419425084378376173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2863282946283389585584115 4294924419425084378376173)
          ·
            refine ⟨1610596657284406641891065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4294924419425084378376173 1610596657284406641891065)
            ·
              refine ⟨1207947492963304981418299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1610596657284406641891065 1207947492963304981418299)
              ·
                refine ⟨1811921239444957472127449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1207947492963304981418299 1811921239444957472127449)
                ·
                  refine ⟨1358940929583718104095587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1811921239444957472127449 1358940929583718104095587)
                  ·
                    refine ⟨2038411394375577156143381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1358940929583718104095587 2038411394375577156143381)
                    ·
                      refine ⟨95550534111355179194221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2038411394375577156143381 95550534111355179194221)
                      ·
                        rfl

theorem cell23_186084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_186084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186084 prefixEnd_186084 := by exact prefixLift 186084
  have htrace : WordTrace (prefixWord ++ tailWord_186084) baseStart_186084 baseEnd_186084 := by
    simpa [prefixWord, tailWord_186084, baseEnd_186084] using wordTrace_append hprefix tailTrace_186084
  have hstable : (prefixWord ++ tailWord_186084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186084).length < 2 ^ (prefixWord ++ tailWord_186084).sum := by decide
  have hdescent : baseEnd_186084 < baseStart_186084 := by decide
  rcases family_descends (prefixWord ++ tailWord_186084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186091 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3]
def baseStart_186091 : Nat := 118140960795 + 186091 * 2 ^ 59
def prefixEnd_186091 : Nat := 4983230072969 + 3 ^ 40 * 186091 * 2
def baseEnd_186091 : Nat := 95554128475936651806689

theorem tailTrace_186091 : CollatzResearch.WordTrace tailWord_186091 prefixEnd_186091 95554128475936651806689 := by
  unfold tailWord_186091
  simp only [CollatzResearch.WordTrace]
  refine ⟨6787296368831563657630127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4524864245887709105086751 6787296368831563657630127)
  ·
    refine ⟨10180944553247345486445191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6787296368831563657630127 10180944553247345486445191)
    ·
      refine ⟨15271416829871018229667787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10180944553247345486445191 15271416829871018229667787)
      ·
        refine ⟨22907125244806527344501681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15271416829871018229667787 22907125244806527344501681)
        ·
          refine ⟨17180343933604895508376261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22907125244806527344501681 17180343933604895508376261)
          ·
            refine ⟨3221314487550917907820549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17180343933604895508376261 3221314487550917907820549)
            ·
              refine ⟨603996466415797107716353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3221314487550917907820549 603996466415797107716353)
              ·
                refine ⟨452997349811847830787265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 603996466415797107716353 452997349811847830787265)
                ·
                  refine ⟨339748012358885873090449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 452997349811847830787265 339748012358885873090449)
                  ·
                    refine ⟨254811009269164404817837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 339748012358885873090449 254811009269164404817837)
                    ·
                      refine ⟨95554128475936651806689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254811009269164404817837 95554128475936651806689)
                      ·
                        rfl

theorem cell23_186091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 3].length) (baseStart_186091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186091 prefixEnd_186091 := by exact prefixLift 186091
  have htrace : WordTrace (prefixWord ++ tailWord_186091) baseStart_186091 baseEnd_186091 := by
    simpa [prefixWord, tailWord_186091, baseEnd_186091] using wordTrace_append hprefix tailTrace_186091
  have hstable : (prefixWord ++ tailWord_186091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186091).length < 2 ^ (prefixWord ++ tailWord_186091).sum := by decide
  have hdescent : baseEnd_186091 < baseStart_186091 := by decide
  rcases family_descends (prefixWord ++ tailWord_186091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186182 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_186182 : Nat := 118140960795 + 186182 * 2 ^ 59
def prefixEnd_186182 : Nat := 4983230072969 + 3 ^ 40 * 186182 * 2
def baseEnd_186182 : Nat := 95600855215495795768771

theorem tailTrace_186182 : CollatzResearch.WordTrace tailWord_186182 prefixEnd_186182 95600855215495795768771 := by
  unfold tailWord_186182
  simp only [CollatzResearch.WordTrace]
  refine ⟨212206731609433943724775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4527076941001257466128533 212206731609433943724775)
  ·
    refine ⟨318310097414150915587163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 212206731609433943724775 318310097414150915587163)
    ·
      refine ⟨477465146121226373380745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318310097414150915587163 477465146121226373380745)
      ·
        refine ⟨358098859590919780035559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477465146121226373380745 358098859590919780035559)
        ·
          refine ⟨537148289386379670053339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358098859590919780035559 537148289386379670053339)
          ·
            refine ⟨805722434079569505080009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537148289386379670053339 805722434079569505080009)
            ·
              refine ⟨604291825559677128810007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 805722434079569505080009 604291825559677128810007)
              ·
                refine ⟨906437738339515693215011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 604291825559677128810007 906437738339515693215011)
                ·
                  refine ⟨1359656607509273539822517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 906437738339515693215011 1359656607509273539822517)
                  ·
                    refine ⟨127467806953994394358361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1359656607509273539822517 127467806953994394358361)
                    ·
                      refine ⟨95600855215495795768771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127467806953994394358361 95600855215495795768771)
                      ·
                        rfl

theorem cell23_186182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_186182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186182 prefixEnd_186182 := by exact prefixLift 186182
  have htrace : WordTrace (prefixWord ++ tailWord_186182) baseStart_186182 baseEnd_186182 := by
    simpa [prefixWord, tailWord_186182, baseEnd_186182] using wordTrace_append hprefix tailTrace_186182
  have hstable : (prefixWord ++ tailWord_186182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186182).length < 2 ^ (prefixWord ++ tailWord_186182).sum := by decide
  have hdescent : baseEnd_186182 < baseStart_186182 := by decide
  rcases family_descends (prefixWord ++ tailWord_186182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186189 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_186189 : Nat := 118140960795 + 186189 * 2 ^ 59
def prefixEnd_186189 : Nat := 4983230072969 + 3 ^ 40 * 186189 * 2
def baseEnd_186189 : Nat := 95604449580077268381239

theorem tailTrace_186189 : CollatzResearch.WordTrace tailWord_186189 prefixEnd_186189 95604449580077268381239 := by
  unfold tailWord_186189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6790870722476526394697621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4527247148317684263131747 6790870722476526394697621)
  ·
    refine ⟨318322065116087174751451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6790870722476526394697621 318322065116087174751451)
    ·
      refine ⟨477483097674130762127177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318322065116087174751451 477483097674130762127177)
      ·
        refine ⟨358112323255598071595383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 477483097674130762127177 358112323255598071595383)
        ·
          refine ⟨537168484883397107393075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358112323255598071595383 537168484883397107393075)
          ·
            refine ⟨805752727325095661089613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537168484883397107393075 805752727325095661089613)
            ·
              refine ⟨302157272746910872908605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805752727325095661089613 302157272746910872908605)
              ·
                refine ⟨113308977280091577340727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302157272746910872908605 113308977280091577340727)
                ·
                  refine ⟨169963465920137366011091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113308977280091577340727 169963465920137366011091)
                  ·
                    refine ⟨254945198880206049016637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 169963465920137366011091 254945198880206049016637)
                    ·
                      refine ⟨95604449580077268381239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 254945198880206049016637 95604449580077268381239)
                      ·
                        rfl

theorem cell23_186189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_186189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186189 prefixEnd_186189 := by exact prefixLift 186189
  have htrace : WordTrace (prefixWord ++ tailWord_186189) baseStart_186189 baseEnd_186189 := by
    simpa [prefixWord, tailWord_186189, baseEnd_186189] using wordTrace_append hprefix tailTrace_186189
  have hstable : (prefixWord ++ tailWord_186189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186189).length < 2 ^ (prefixWord ++ tailWord_186189).sum := by decide
  have hdescent : baseEnd_186189 < baseStart_186189 := by decide
  rcases family_descends (prefixWord ++ tailWord_186189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186222 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_186222 : Nat := 118140960795 + 186222 * 2 ^ 59
def prefixEnd_186222 : Nat := 4983230072969 + 3 ^ 40 * 186222 * 2
def baseEnd_186222 : Nat := 31873798147225213089529

theorem tailTrace_186222 : CollatzResearch.WordTrace tailWord_186222 prefixEnd_186222 31873798147225213089529 := by
  unfold tailWord_186222
  simp only [CollatzResearch.WordTrace]
  refine ⟨849009291419621628831115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4528049554237982020432613 849009291419621628831115)
  ·
    refine ⟨1273513937129432443246673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849009291419621628831115 1273513937129432443246673)
    ·
      refine ⟨955135452847074332435005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1273513937129432443246673 955135452847074332435005)
      ·
        refine ⟨358175794817652874663127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 955135452847074332435005 358175794817652874663127)
        ·
          refine ⟨537263692226479311994691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358175794817652874663127 537263692226479311994691)
          ·
            refine ⟨805895538339718967992037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537263692226479311994691 805895538339718967992037)
            ·
              refine ⟨151105413438697306498507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 805895538339718967992037 151105413438697306498507)
              ·
                refine ⟨226658120158045959747761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151105413438697306498507 226658120158045959747761)
                ·
                  refine ⟨169993590118534469810821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226658120158045959747761 169993590118534469810821)
                  ·
                    refine ⟨31873798147225213089529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 169993590118534469810821 31873798147225213089529)
                    ·
                      rfl

theorem cell23_186222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_186222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186222 prefixEnd_186222 := by exact prefixLift 186222
  have htrace : WordTrace (prefixWord ++ tailWord_186222) baseStart_186222 baseEnd_186222 := by
    simpa [prefixWord, tailWord_186222, baseEnd_186222] using wordTrace_append hprefix tailTrace_186222
  have hstable : (prefixWord ++ tailWord_186222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186222).length < 2 ^ (prefixWord ++ tailWord_186222).sum := by decide
  have hdescent : baseEnd_186222 < baseStart_186222 := by decide
  rcases family_descends (prefixWord ++ tailWord_186222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186261 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_186261 : Nat := 118140960795 + 186261 * 2 ^ 59
def prefixEnd_186261 : Nat := 4983230072969 + 3 ^ 40 * 186261 * 2
def baseEnd_186261 : Nat := 31880473395733662226969

theorem tailTrace_186261 : CollatzResearch.WordTrace tailWord_186261 prefixEnd_186261 31880473395733662226969 := by
  unfold tailWord_186261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6793496778215682691318637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4528997852143788460879091 6793496778215682691318637)
  ·
    refine ⟨2547561291830881009244489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6793496778215682691318637 2547561291830881009244489)
    ·
      refine ⟨1910670968873160756933367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547561291830881009244489 1910670968873160756933367)
      ·
        refine ⟨2866006453309741135400051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1910670968873160756933367 2866006453309741135400051)
        ·
          refine ⟨4299009679964611703100077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2866006453309741135400051 4299009679964611703100077)
          ·
            refine ⟨1612128629986729388662529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4299009679964611703100077 1612128629986729388662529)
            ·
              refine ⟨1209096472490047041496897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1612128629986729388662529 1209096472490047041496897)
              ·
                refine ⟨906822354367535281122673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1209096472490047041496897 906822354367535281122673)
                ·
                  refine ⟨680116765775651460842005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 906822354367535281122673 680116765775651460842005)
                  ·
                    refine ⟨31880473395733662226969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 680116765775651460842005 31880473395733662226969)
                    ·
                      rfl

theorem cell23_186261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_186261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186261 prefixEnd_186261 := by exact prefixLift 186261
  have htrace : WordTrace (prefixWord ++ tailWord_186261) baseStart_186261 baseEnd_186261 := by
    simpa [prefixWord, tailWord_186261, baseEnd_186261] using wordTrace_append hprefix tailTrace_186261
  have hstable : (prefixWord ++ tailWord_186261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186261).length < 2 ^ (prefixWord ++ tailWord_186261).sum := by decide
  have hdescent : baseEnd_186261 < baseStart_186261 := by decide
  rcases family_descends (prefixWord ++ tailWord_186261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186268 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_186268 : Nat := 118140960795 + 186268 * 2 ^ 59
def prefixEnd_186268 : Nat := 4983230072969 + 3 ^ 40 * 186268 * 2
def baseEnd_186268 : Nat := 95645014551782459293375

theorem tailTrace_186268 : CollatzResearch.WordTrace tailWord_186268 prefixEnd_186268 95645014551782459293375 := by
  unfold tailWord_186268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3396876044595161443411729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4529168059460215257882305 3396876044595161443411729)
  ·
    refine ⟨2547657033446371082558797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3396876044595161443411729 2547657033446371082558797)
    ·
      refine ⟨955371387542389155959549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2547657033446371082558797 955371387542389155959549)
      ·
        refine ⟨358264270328395933484831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 955371387542389155959549 358264270328395933484831)
        ·
          refine ⟨537396405492593900227247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358264270328395933484831 537396405492593900227247)
          ·
            refine ⟨806094608238890850340871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537396405492593900227247 806094608238890850340871)
            ·
              refine ⟨1209141912358336275511307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 806094608238890850340871 1209141912358336275511307)
              ·
                refine ⟨1813712868537504413266961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1209141912358336275511307 1813712868537504413266961)
                ·
                  refine ⟨1360284651403128309950221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1813712868537504413266961 1360284651403128309950221)
                  ·
                    refine ⟨510106744276173116231333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1360284651403128309950221 510106744276173116231333)
                    ·
                      refine ⟨95645014551782459293375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 510106744276173116231333 95645014551782459293375)
                      ·
                        rfl

theorem cell23_186268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_186268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186268 prefixEnd_186268 := by exact prefixLift 186268
  have htrace : WordTrace (prefixWord ++ tailWord_186268) baseStart_186268 baseEnd_186268 := by
    simpa [prefixWord, tailWord_186268, baseEnd_186268] using wordTrace_append hprefix tailTrace_186268
  have hstable : (prefixWord ++ tailWord_186268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186268).length < 2 ^ (prefixWord ++ tailWord_186268).sum := by decide
  have hdescent : baseEnd_186268 < baseStart_186268 := by decide
  rcases family_descends (prefixWord ++ tailWord_186268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186291 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 7]
def baseStart_186291 : Nat := 118140960795 + 186291 * 2 ^ 59
def prefixEnd_186291 : Nat := 4983230072969 + 3 ^ 40 * 186291 * 2
def baseEnd_186291 : Nat := 10628536067426207700641

theorem tailTrace_186291 : CollatzResearch.WordTrace tailWord_186291 prefixEnd_186291 10628536067426207700641 := by
  unfold tailWord_186291
  simp only [CollatzResearch.WordTrace]
  refine ⟨6794590968106997814910727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4529727312071331876607151 6794590968106997814910727)
  ·
    refine ⟨10191886452160496722366091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6794590968106997814910727 10191886452160496722366091)
    ·
      refine ⟨15287829678240745083549137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10191886452160496722366091 15287829678240745083549137)
      ·
        refine ⟨11465872258680558812661853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15287829678240745083549137 11465872258680558812661853)
        ·
          refine ⟨4299702097005209554748195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11465872258680558812661853 4299702097005209554748195)
          ·
            refine ⟨6449553145507814332122293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4299702097005209554748195 6449553145507814332122293)
            ·
              refine ⟨604645607391357593636465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6449553145507814332122293 604645607391357593636465)
              ·
                refine ⟨453484205543518195227349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604645607391357593636465 453484205543518195227349)
                ·
                  refine ⟨10628536067426207700641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 453484205543518195227349 10628536067426207700641)
                  ·
                    rfl

theorem cell23_186291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 7].length) (baseStart_186291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186291 prefixEnd_186291 := by exact prefixLift 186291
  have htrace : WordTrace (prefixWord ++ tailWord_186291) baseStart_186291 baseEnd_186291 := by
    simpa [prefixWord, tailWord_186291, baseEnd_186291] using wordTrace_append hprefix tailTrace_186291
  have hstable : (prefixWord ++ tailWord_186291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186291).length < 2 ^ (prefixWord ++ tailWord_186291).sum := by decide
  have hdescent : baseEnd_186291 < baseStart_186291 := by decide
  rcases family_descends (prefixWord ++ tailWord_186291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186318 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_186318 : Nat := 118140960795 + 186318 * 2 ^ 59
def prefixEnd_186318 : Nat := 4983230072969 + 3 ^ 40 * 186318 * 2
def baseEnd_186318 : Nat := 95670688584507263668145

theorem tailTrace_186318 : CollatzResearch.WordTrace tailWord_186318 prefixEnd_186318 95670688584507263668145 := by
  unfold tailWord_186318
  simp only [CollatzResearch.WordTrace]
  refine ⟨849446967376147678267951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4530383826006120950762405 849446967376147678267951)
  ·
    refine ⟨1274170451064221517401927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 849446967376147678267951 1274170451064221517401927)
    ·
      refine ⟨1911255676596332276102891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1274170451064221517401927 1911255676596332276102891)
      ·
        refine ⟨2866883514894498414154337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1911255676596332276102891 2866883514894498414154337)
        ·
          refine ⟨2150162636170873810615753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2866883514894498414154337 2150162636170873810615753)
          ·
            refine ⟨1612621977128155357961815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150162636170873810615753 1612621977128155357961815)
            ·
              refine ⟨2418932965692233036942723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612621977128155357961815 2418932965692233036942723)
              ·
                refine ⟨3628399448538349555414085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2418932965692233036942723 3628399448538349555414085)
                ·
                  refine ⟨680324896600940541640141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3628399448538349555414085 680324896600940541640141)
                  ·
                    refine ⟨255121836225352703115053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 680324896600940541640141 255121836225352703115053)
                    ·
                      refine ⟨95670688584507263668145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255121836225352703115053 95670688584507263668145)
                      ·
                        rfl

theorem cell23_186318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_186318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186318 prefixEnd_186318 := by exact prefixLift 186318
  have htrace : WordTrace (prefixWord ++ tailWord_186318) baseStart_186318 baseEnd_186318 := by
    simpa [prefixWord, tailWord_186318, baseEnd_186318] using wordTrace_append hprefix tailTrace_186318
  have hstable : (prefixWord ++ tailWord_186318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186318).length < 2 ^ (prefixWord ++ tailWord_186318).sum := by decide
  have hdescent : baseEnd_186318 < baseStart_186318 := by decide
  rcases family_descends (prefixWord ++ tailWord_186318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186325 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 5]
def baseStart_186325 : Nat := 118140960795 + 186325 * 2 ^ 59
def prefixEnd_186325 : Nat := 4983230072969 + 3 ^ 40 * 186325 * 2
def baseEnd_186325 : Nat := 10630475883232081808957

theorem tailTrace_186325 : CollatzResearch.WordTrace tailWord_186325 prefixEnd_186325 10630475883232081808957 := by
  unfold tailWord_186325
  simp only [CollatzResearch.WordTrace]
  refine ⟨6795831049983821621648429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4530554033322547747765619 6795831049983821621648429)
  ·
    refine ⟨2548436643743933108118161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6795831049983821621648429 2548436643743933108118161)
    ·
      refine ⟨1911327482807949831088621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2548436643743933108118161 1911327482807949831088621)
      ·
        refine ⟨716747806052981186658233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1911327482807949831088621 716747806052981186658233)
        ·
          refine ⟨537560854539735889993675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 716747806052981186658233 537560854539735889993675)
          ·
            refine ⟨806341281809603834990513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 537560854539735889993675 806341281809603834990513)
            ·
              refine ⟨604755961357202876242885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 806341281809603834990513 604755961357202876242885)
              ·
                refine ⟨113391742754475539295541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 604755961357202876242885 113391742754475539295541)
                ·
                  refine ⟨10630475883232081808957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113391742754475539295541 10630475883232081808957)
                  ·
                    rfl

theorem cell23_186325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_186325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186325 prefixEnd_186325 := by exact prefixLift 186325
  have htrace : WordTrace (prefixWord ++ tailWord_186325) baseStart_186325 baseEnd_186325 := by
    simpa [prefixWord, tailWord_186325, baseEnd_186325] using wordTrace_append hprefix tailTrace_186325
  have hstable : (prefixWord ++ tailWord_186325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186325).length < 2 ^ (prefixWord ++ tailWord_186325).sum := by decide
  have hdescent : baseEnd_186325 < baseStart_186325 := by decide
  rcases family_descends (prefixWord ++ tailWord_186325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186351 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 8]
def baseStart_186351 : Nat := 118140960795 + 186351 * 2 ^ 59
def prefixEnd_186351 : Nat := 4983230072969 + 3 ^ 40 * 186351 * 2
def baseEnd_186351 : Nat := 31895877815368544851831

theorem tailTrace_186351 : CollatzResearch.WordTrace tailWord_186351 prefixEnd_186351 31895877815368544851831 := by
  unfold tailWord_186351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6796779347889628062094907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531186231926418708063271 6796779347889628062094907)
  ·
    refine ⟨10195169021834442093142361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6796779347889628062094907 10195169021834442093142361)
    ·
      refine ⟨7646376766375831569856771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10195169021834442093142361 7646376766375831569856771)
      ·
        refine ⟨11469565149563747354785157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7646376766375831569856771 11469565149563747354785157)
        ·
          refine ⟨2150543465543202629022217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11469565149563747354785157 2150543465543202629022217)
          ·
            refine ⟨1612907599157401971766663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2150543465543202629022217 1612907599157401971766663)
            ·
              refine ⟨2419361398736102957649995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1612907599157401971766663 2419361398736102957649995)
              ·
                refine ⟨3629042098104154436474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2419361398736102957649995 3629042098104154436474993)
                ·
                  refine ⟨2721781573578115827356245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3629042098104154436474993 2721781573578115827356245)
                  ·
                    refine ⟨31895877815368544851831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2721781573578115827356245 31895877815368544851831)
                    ·
                      rfl

theorem cell23_186351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_186351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186351 prefixEnd_186351 := by exact prefixLift 186351
  have htrace : WordTrace (prefixWord ++ tailWord_186351) baseStart_186351 baseEnd_186351 := by
    simpa [prefixWord, tailWord_186351, baseEnd_186351] using wordTrace_append hprefix tailTrace_186351
  have hstable : (prefixWord ++ tailWord_186351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186351).length < 2 ^ (prefixWord ++ tailWord_186351).sum := by decide
  have hdescent : baseEnd_186351 < baseStart_186351 := by decide
  rcases family_descends (prefixWord ++ tailWord_186351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186371 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6]
def baseStart_186371 : Nat := 118140960795 + 186371 * 2 ^ 59
def prefixEnd_186371 : Nat := 4983230072969 + 3 ^ 40 * 186371 * 2
def baseEnd_186371 : Nat := 95697903059195556305401

theorem tailTrace_186371 : CollatzResearch.WordTrace tailWord_186371 prefixEnd_186371 95697903059195556305401 := by
  unfold tailWord_186371
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797508807817171477822967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531672538544780985215311 6797508807817171477822967)
  ·
    refine ⟨10196263211725757216734451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797508807817171477822967 10196263211725757216734451)
    ·
      refine ⟨15294394817588635825101677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10196263211725757216734451 15294394817588635825101677)
      ·
        refine ⟨5735398056595738434413129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15294394817588635825101677 5735398056595738434413129)
        ·
          refine ⟨4301548542446803825809847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5735398056595738434413129 4301548542446803825809847)
          ·
            refine ⟨6452322813670205738714771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4301548542446803825809847 6452322813670205738714771)
            ·
              refine ⟨9678484220505308608072157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6452322813670205738714771 9678484220505308608072157)
              ·
                refine ⟨3629431582689490728027059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9678484220505308608072157 3629431582689490728027059)
                ·
                  refine ⟨5444147374034236092040589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3629431582689490728027059 5444147374034236092040589)
                  ·
                    refine ⟨2041555265262838534515221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5444147374034236092040589 2041555265262838534515221)
                    ·
                      refine ⟨95697903059195556305401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2041555265262838534515221 95697903059195556305401)
                      ·
                        rfl

theorem cell23_186371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_186371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186371 prefixEnd_186371 := by exact prefixLift 186371
  have htrace : WordTrace (prefixWord ++ tailWord_186371) baseStart_186371 baseEnd_186371 := by
    simpa [prefixWord, tailWord_186371, baseEnd_186371] using wordTrace_append hprefix tailTrace_186371
  have hstable : (prefixWord ++ tailWord_186371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186371).length < 2 ^ (prefixWord ++ tailWord_186371).sum := by decide
  have hdescent : baseEnd_186371 < baseStart_186371 := by decide
  rcases family_descends (prefixWord ++ tailWord_186371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186372 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_186372 : Nat := 118140960795 + 186372 * 2 ^ 59
def prefixEnd_186372 : Nat := 4983230072969 + 3 ^ 40 * 186372 * 2
def baseEnd_186372 : Nat := 31899472179950017464299

theorem tailTrace_186372 : CollatzResearch.WordTrace tailWord_186372 prefixEnd_186372 31899472179950017464299 := by
  unfold tailWord_186372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3398772640406774324304685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4531696853875699099072913 3398772640406774324304685)
  ·
    refine ⟨1274539740152540371614257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3398772640406774324304685 1274539740152540371614257)
    ·
      refine ⟨955904805114405278710693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1274539740152540371614257 955904805114405278710693)
      ·
        refine ⟨179232150958950989758255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 955904805114405278710693 179232150958950989758255)
        ·
          refine ⟨268848226438426484637383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179232150958950989758255 268848226438426484637383)
          ·
            refine ⟨403272339657639726956075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268848226438426484637383 403272339657639726956075)
            ·
              refine ⟨604908509486459590434113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403272339657639726956075 604908509486459590434113)
              ·
                refine ⟨453681382114844692825585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604908509486459590434113 453681382114844692825585)
                ·
                  refine ⟨340261036586133519619189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453681382114844692825585 340261036586133519619189)
                  ·
                    refine ⟨31899472179950017464299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340261036586133519619189 31899472179950017464299)
                    ·
                      rfl

theorem cell23_186372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_186372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186372 prefixEnd_186372 := by exact prefixLift 186372
  have htrace : WordTrace (prefixWord ++ tailWord_186372) baseStart_186372 baseEnd_186372 := by
    simpa [prefixWord, tailWord_186372, baseEnd_186372] using wordTrace_append hprefix tailTrace_186372
  have hstable : (prefixWord ++ tailWord_186372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186372).length < 2 ^ (prefixWord ++ tailWord_186372).sum := by decide
  have hdescent : baseEnd_186372 < baseStart_186372 := by decide
  rcases family_descends (prefixWord ++ tailWord_186372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186375 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_186375 : Nat := 118140960795 + 186375 * 2 ^ 59
def prefixEnd_186375 : Nat := 4983230072969 + 3 ^ 40 * 186375 * 2
def baseEnd_186375 : Nat := 95699956981813540655383

theorem tailTrace_186375 : CollatzResearch.WordTrace tailWord_186375 prefixEnd_186375 95699956981813540655383 := by
  unfold tailWord_186375
  simp only [CollatzResearch.WordTrace]
  refine ⟨6797654699802680160968579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4531769799868453440645719 6797654699802680160968579)
  ·
    refine ⟨10196482049704020241452869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6797654699802680160968579 10196482049704020241452869)
    ·
      refine ⟨1911840384319503795272413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10196482049704020241452869 1911840384319503795272413)
      ·
        refine ⟨716940144119813923227155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1911840384319503795272413 716940144119813923227155)
        ·
          refine ⟨1075410216179720884840733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 716940144119813923227155 1075410216179720884840733)
          ·
            refine ⟨403278831067395331815275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1075410216179720884840733 403278831067395331815275)
            ·
              refine ⟨604918246601092997722913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403278831067395331815275 604918246601092997722913)
              ·
                refine ⟨453688684950819748292185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 604918246601092997722913 453688684950819748292185)
                ·
                  refine ⟨340266513713114811219139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453688684950819748292185 340266513713114811219139)
                  ·
                    refine ⟨510399770569672216828709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340266513713114811219139 510399770569672216828709)
                    ·
                      refine ⟨95699956981813540655383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 510399770569672216828709 95699956981813540655383)
                      ·
                        rfl

theorem cell23_186375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_186375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186375 prefixEnd_186375 := by exact prefixLift 186375
  have htrace : WordTrace (prefixWord ++ tailWord_186375) baseStart_186375 baseEnd_186375 := by
    simpa [prefixWord, tailWord_186375, baseEnd_186375] using wordTrace_append hprefix tailTrace_186375
  have hstable : (prefixWord ++ tailWord_186375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186375).length < 2 ^ (prefixWord ++ tailWord_186375).sum := by decide
  have hdescent : baseEnd_186375 < baseStart_186375 := by decide
  rcases family_descends (prefixWord ++ tailWord_186375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186435 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 4, 3, 2]
def baseStart_186435 : Nat := 118140960795 + 186435 * 2 ^ 59
def prefixEnd_186435 : Nat := 4983230072969 + 3 ^ 40 * 186435 * 2
def baseEnd_186435 : Nat := 95730765821083305905107

theorem tailTrace_186435 : CollatzResearch.WordTrace tailWord_186435 prefixEnd_186435 95730765821083305905107 := by
  unfold tailWord_186435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6799843079585310408152759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533228719723540272101839 6799843079585310408152759)
  ·
    refine ⟨10199764619377965612229139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6799843079585310408152759 10199764619377965612229139)
    ·
      refine ⟨15299646929066948418343709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10199764619377965612229139 15299646929066948418343709)
      ·
        refine ⟨5737367598400105656878891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15299646929066948418343709 5737367598400105656878891)
        ·
          refine ⟨8606051397600158485318337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5737367598400105656878891 8606051397600158485318337)
          ·
            refine ⟨6454538548200118863988753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8606051397600158485318337 6454538548200118863988753)
            ·
              refine ⟨4840903911150089147991565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6454538548200118863988753 4840903911150089147991565)
              ·
                refine ⟨1815338966681283430496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4840903911150089147991565 1815338966681283430496837)
                ·
                  refine ⟨340376056252740643218157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1815338966681283430496837 340376056252740643218157)
                  ·
                    refine ⟨127641021094777741206809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340376056252740643218157 127641021094777741206809)
                    ·
                      refine ⟨95730765821083305905107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127641021094777741206809 95730765821083305905107)
                      ·
                        rfl

theorem cell23_186435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_186435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186435 prefixEnd_186435 := by exact prefixLift 186435
  have htrace : WordTrace (prefixWord ++ tailWord_186435) baseStart_186435 baseEnd_186435 := by
    simpa [prefixWord, tailWord_186435, baseEnd_186435] using wordTrace_append hprefix tailTrace_186435
  have hstable : (prefixWord ++ tailWord_186435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186435).length < 2 ^ (prefixWord ++ tailWord_186435).sum := by decide
  have hdescent : baseEnd_186435 < baseStart_186435 := by decide
  rcases family_descends (prefixWord ++ tailWord_186435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186445 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_186445 : Nat := 118140960795 + 186445 * 2 ^ 59
def prefixEnd_186445 : Nat := 4983230072969 + 3 ^ 40 * 186445 * 2
def baseEnd_186445 : Nat := 31911966875876088926687

theorem tailTrace_186445 : CollatzResearch.WordTrace tailWord_186445 prefixEnd_186445 31911966875876088926687 := by
  unfold tailWord_186445
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800207809549082116016789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533471873032721410677859 6800207809549082116016789)
  ·
    refine ⟨318759741072613224188287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6800207809549082116016789 318759741072613224188287)
    ·
      refine ⟨478139611608919836282431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 318759741072613224188287 478139611608919836282431)
      ·
        refine ⟨717209417413379754423647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 478139611608919836282431 717209417413379754423647)
        ·
          refine ⟨1075814126120069631635471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 717209417413379754423647 1075814126120069631635471)
          ·
            refine ⟨1613721189180104447453207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1075814126120069631635471 1613721189180104447453207)
            ·
              refine ⟨2420581783770156671179811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1613721189180104447453207 2420581783770156671179811)
              ·
                refine ⟨3630872675655235006769717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2420581783770156671179811 3630872675655235006769717)
                ·
                  refine ⟨340394313342678281884661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3630872675655235006769717 340394313342678281884661)
                  ·
                    refine ⟨31911966875876088926687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340394313342678281884661 31911966875876088926687)
                    ·
                      rfl

theorem cell23_186445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_186445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186445 prefixEnd_186445 := by exact prefixLift 186445
  have htrace : WordTrace (prefixWord ++ tailWord_186445) baseStart_186445 baseEnd_186445 := by
    simpa [prefixWord, tailWord_186445, baseEnd_186445] using wordTrace_append hprefix tailTrace_186445
  have hstable : (prefixWord ++ tailWord_186445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186445).length < 2 ^ (prefixWord ++ tailWord_186445).sum := by decide
  have hdescent : baseEnd_186445 < baseStart_186445 := by decide
  rcases family_descends (prefixWord ++ tailWord_186445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186465 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_186465 : Nat := 118140960795 + 186465 * 2 ^ 59
def prefixEnd_186465 : Nat := 4983230072969 + 3 ^ 40 * 186465 * 2
def baseEnd_186465 : Nat := 95746170240718188529969

theorem tailTrace_186465 : CollatzResearch.WordTrace tailWord_186465 prefixEnd_186465 95746170240718188529969 := by
  unfold tailWord_186465
  simp only [CollatzResearch.WordTrace]
  refine ⟨6800937269476625531744849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4533958179651083687829899 6800937269476625531744849)
  ·
    refine ⟨5100702952107469148808637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6800937269476625531744849 5100702952107469148808637)
    ·
      refine ⟨1912763607040300930803239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5100702952107469148808637 1912763607040300930803239)
      ·
        refine ⟨2869145410560451396204859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1912763607040300930803239 2869145410560451396204859)
        ·
          refine ⟨4303718115840677094307289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869145410560451396204859 4303718115840677094307289)
          ·
            refine ⟨3227788586880507820730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4303718115840677094307289 3227788586880507820730467)
            ·
              refine ⟨4841682880320761731095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3227788586880507820730467 4841682880320761731095701)
              ·
                refine ⟨226953885015035706145111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4841682880320761731095701 226953885015035706145111)
                ·
                  refine ⟨340430827522553559217667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226953885015035706145111 340430827522553559217667)
                  ·
                    refine ⟨510646241283830338826501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340430827522553559217667 510646241283830338826501)
                    ·
                      refine ⟨95746170240718188529969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 510646241283830338826501 95746170240718188529969)
                      ·
                        rfl

theorem cell23_186465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_186465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186465 prefixEnd_186465 := by exact prefixLift 186465
  have htrace : WordTrace (prefixWord ++ tailWord_186465) baseStart_186465 baseEnd_186465 := by
    simpa [prefixWord, tailWord_186465, baseEnd_186465] using wordTrace_append hprefix tailTrace_186465
  have hstable : (prefixWord ++ tailWord_186465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186465).length < 2 ^ (prefixWord ++ tailWord_186465).sum := by decide
  have hdescent : baseEnd_186465 < baseStart_186465 := by decide
  rcases family_descends (prefixWord ++ tailWord_186465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186469 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 2, 3, 2]
def baseStart_186469 : Nat := 118140960795 + 186469 * 2 ^ 59
def prefixEnd_186469 : Nat := 4983230072969 + 3 ^ 40 * 186469 * 2
def baseEnd_186469 : Nat := 95748224163336172879951

theorem tailTrace_186469 : CollatzResearch.WordTrace tailWord_186469 prefixEnd_186469 95748224163336172879951 := by
  unfold tailWord_186469
  simp only [CollatzResearch.WordTrace]
  refine ⟨6801083161462134214890461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4534055440974756143260307 6801083161462134214890461)
  ·
    refine ⟨2550406185548300330583923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6801083161462134214890461 2550406185548300330583923)
    ·
      refine ⟨3825609278322450495875885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2550406185548300330583923 3825609278322450495875885)
      ·
        refine ⟨1434603479370918935953457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3825609278322450495875885 1434603479370918935953457)
        ·
          refine ⟨1075952609528189201965093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434603479370918935953457 1075952609528189201965093)
          ·
            refine ⟨201741114286535475368455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1075952609528189201965093 201741114286535475368455)
            ·
              refine ⟨302611671429803213052683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201741114286535475368455 302611671429803213052683)
              ·
                refine ⟨453917507144704819579025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302611671429803213052683 453917507144704819579025)
                ·
                  refine ⟨340438130358528614684269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 453917507144704819579025 340438130358528614684269)
                  ·
                    refine ⟨127664298884448230506601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340438130358528614684269 127664298884448230506601)
                    ·
                      refine ⟨95748224163336172879951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127664298884448230506601 95748224163336172879951)
                      ·
                        rfl

theorem cell23_186469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_186469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186469 prefixEnd_186469 := by exact prefixLift 186469
  have htrace : WordTrace (prefixWord ++ tailWord_186469) baseStart_186469 baseEnd_186469 := by
    simpa [prefixWord, tailWord_186469, baseEnd_186469] using wordTrace_append hprefix tailTrace_186469
  have hstable : (prefixWord ++ tailWord_186469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186469).length < 2 ^ (prefixWord ++ tailWord_186469).sum := by decide
  have hdescent : baseEnd_186469 < baseStart_186469 := by decide
  rcases family_descends (prefixWord ++ tailWord_186469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186482 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_186482 : Nat := 118140960795 + 186482 * 2 ^ 59
def prefixEnd_186482 : Nat := 4983230072969 + 3 ^ 40 * 186482 * 2
def baseEnd_186482 : Nat := 95754899411844622017391

theorem tailTrace_186482 : CollatzResearch.WordTrace tailWord_186482 prefixEnd_186482 95754899411844622017391 := by
  unfold tailWord_186482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1700389327603759358778425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4534371540276691623409133 1700389327603759358778425)
  ·
    refine ⟨1275291995702819519083819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1700389327603759358778425 1275291995702819519083819)
    ·
      refine ⟨1912937993554229278625729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275291995702819519083819 1912937993554229278625729)
      ·
        refine ⟨1434703495165671958969297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1912937993554229278625729 1434703495165671958969297)
        ·
          refine ⟨1076027621374253969226973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1434703495165671958969297 1076027621374253969226973)
          ·
            refine ⟨403510358015345238460115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1076027621374253969226973 403510358015345238460115)
            ·
              refine ⟨605265537023017857690173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403510358015345238460115 605265537023017857690173)
              ·
                refine ⟨226974576383631696633815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605265537023017857690173 226974576383631696633815)
                ·
                  refine ⟨340461864575447544950723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 226974576383631696633815 340461864575447544950723)
                  ·
                    refine ⟨510692796863171317426085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340461864575447544950723 510692796863171317426085)
                    ·
                      refine ⟨95754899411844622017391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 510692796863171317426085 95754899411844622017391)
                      ·
                        rfl

theorem cell23_186482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_186482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186482 prefixEnd_186482 := by exact prefixLift 186482
  have htrace : WordTrace (prefixWord ++ tailWord_186482) baseStart_186482 baseEnd_186482 := by
    simpa [prefixWord, tailWord_186482, baseEnd_186482] using wordTrace_append hprefix tailTrace_186482
  have hstable : (prefixWord ++ tailWord_186482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186482).length < 2 ^ (prefixWord ++ tailWord_186482).sum := by decide
  have hdescent : baseEnd_186482 < baseStart_186482 := by decide
  rcases family_descends (prefixWord ++ tailWord_186482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186492 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_186492 : Nat := 118140960795 + 186492 * 2 ^ 59
def prefixEnd_186492 : Nat := 4983230072969 + 3 ^ 40 * 186492 * 2
def baseEnd_186492 : Nat := 31920011406129860964115

theorem tailTrace_186492 : CollatzResearch.WordTrace tailWord_186492 prefixEnd_186492 31920011406129860964115 := by
  unfold tailWord_186492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400961020189404571488865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4534614693585872761985153 3400961020189404571488865)
  ·
    refine ⟨2550720765142053428616649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3400961020189404571488865 2550720765142053428616649)
    ·
      refine ⟨1913040573856540071462487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2550720765142053428616649 1913040573856540071462487)
      ·
        refine ⟨2869560860784810107193731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913040573856540071462487 2869560860784810107193731)
        ·
          refine ⟨4304341291177215160790597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2869560860784810107193731 4304341291177215160790597)
          ·
            refine ⟨807063992095727842648237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4304341291177215160790597 807063992095727842648237)
            ·
              refine ⟨302648997035897940993089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807063992095727842648237 302648997035897940993089)
              ·
                refine ⟨226986747776923455744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302648997035897940993089 226986747776923455744817)
                ·
                  refine ⟨170240060832692591808613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226986747776923455744817 170240060832692591808613)
                  ·
                    refine ⟨31920011406129860964115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170240060832692591808613 31920011406129860964115)
                    ·
                      rfl

theorem cell23_186492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_186492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186492 prefixEnd_186492 := by exact prefixLift 186492
  have htrace : WordTrace (prefixWord ++ tailWord_186492) baseStart_186492 baseEnd_186492 := by
    simpa [prefixWord, tailWord_186492, baseEnd_186492] using wordTrace_append hprefix tailTrace_186492
  have hstable : (prefixWord ++ tailWord_186492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186492).length < 2 ^ (prefixWord ++ tailWord_186492).sum := by decide
  have hdescent : baseEnd_186492 < baseStart_186492 := by decide
  rcases family_descends (prefixWord ++ tailWord_186492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186499 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 3, 2, 2]
def baseStart_186499 : Nat := 118140960795 + 186499 * 2 ^ 59
def prefixEnd_186499 : Nat := 4983230072969 + 3 ^ 40 * 186499 * 2
def baseEnd_186499 : Nat := 95763628582971055504813

theorem tailTrace_186499 : CollatzResearch.WordTrace tailWord_186499 prefixEnd_186499 95763628582971055504813 := by
  unfold tailWord_186499
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802177351353449338482551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4534784900902299558988367 6802177351353449338482551)
  ·
    refine ⟨10203266027030174007723827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6802177351353449338482551 10203266027030174007723827)
    ·
      refine ⟨15304899040545261011585741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10203266027030174007723827 15304899040545261011585741)
      ·
        refine ⟨5739337140204472879344653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15304899040545261011585741 5739337140204472879344653)
        ·
          refine ⟨2152251427576677329754245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5739337140204472879344653 2152251427576677329754245)
          ·
            refine ⟨403547142670626999328921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2152251427576677329754245 403547142670626999328921)
            ·
              refine ⟨302660357002970249496691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403547142670626999328921 302660357002970249496691)
              ·
                refine ⟨453990535504455374245037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302660357002970249496691 453990535504455374245037)
                ·
                  refine ⟨170246450814170765341889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 453990535504455374245037 170246450814170765341889)
                  ·
                    refine ⟨127684838110628074006417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170246450814170765341889 127684838110628074006417)
                    ·
                      refine ⟨95763628582971055504813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127684838110628074006417 95763628582971055504813)
                      ·
                        rfl

theorem cell23_186499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_186499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186499 prefixEnd_186499 := by exact prefixLift 186499
  have htrace : WordTrace (prefixWord ++ tailWord_186499) baseStart_186499 baseEnd_186499 := by
    simpa [prefixWord, tailWord_186499, baseEnd_186499] using wordTrace_append hprefix tailTrace_186499
  have hstable : (prefixWord ++ tailWord_186499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186499).length < 2 ^ (prefixWord ++ tailWord_186499).sum := by decide
  have hdescent : baseEnd_186499 < baseStart_186499 := by decide
  rcases family_descends (prefixWord ++ tailWord_186499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186516 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_186516 : Nat := 118140960795 + 186516 * 2 ^ 59
def prefixEnd_186516 : Nat := 4983230072969 + 3 ^ 40 * 186516 * 2
def baseEnd_186516 : Nat := 95772357754097488992235

theorem tailTrace_186516 : CollatzResearch.WordTrace tailWord_186516 prefixEnd_186516 95772357754097488992235 := by
  unfold tailWord_186516
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401398696145930620925701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4535198261527907494567601 3401398696145930620925701)
  ·
    refine ⟨637762255527361991423569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3401398696145930620925701 637762255527361991423569)
    ·
      refine ⟨478321691645521493567677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 637762255527361991423569 478321691645521493567677)
      ·
        refine ⟨179370634367070560087879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 478321691645521493567677 179370634367070560087879)
        ·
          refine ⟨269055951550605840131819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179370634367070560087879 269055951550605840131819)
          ·
            refine ⟨403583927325908760197729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269055951550605840131819 403583927325908760197729)
            ·
              refine ⟨302687945494431570148297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403583927325908760197729 302687945494431570148297)
              ·
                refine ⟨227015959120823677611223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302687945494431570148297 227015959120823677611223)
                ·
                  refine ⟨340523938681235516416835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227015959120823677611223 340523938681235516416835)
                  ·
                    refine ⟨510785908021853274625253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 340523938681235516416835 510785908021853274625253)
                    ·
                      refine ⟨95772357754097488992235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 510785908021853274625253 95772357754097488992235)
                      ·
                        rfl

theorem cell23_186516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_186516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186516 prefixEnd_186516 := by exact prefixLift 186516
  have htrace : WordTrace (prefixWord ++ tailWord_186516) baseStart_186516 baseEnd_186516 := by
    simpa [prefixWord, tailWord_186516, baseEnd_186516] using wordTrace_append hprefix tailTrace_186516
  have hstable : (prefixWord ++ tailWord_186516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186516).length < 2 ^ (prefixWord ++ tailWord_186516).sum := by decide
  have hdescent : baseEnd_186516 < baseStart_186516 := by decide
  rcases family_descends (prefixWord ++ tailWord_186516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186519 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 3]
def baseStart_186519 : Nat := 118140960795 + 186519 * 2 ^ 59
def prefixEnd_186519 : Nat := 4983230072969 + 3 ^ 40 * 186519 * 2
def baseEnd_186519 : Nat := 95773898196060977254721

theorem tailTrace_186519 : CollatzResearch.WordTrace tailWord_186519 prefixEnd_186519 95773898196060977254721 := by
  unfold tailWord_186519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6802906811280992754210611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4535271207520661836140407 6802906811280992754210611)
  ·
    refine ⟨10204360216921489131315917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6802906811280992754210611 10204360216921489131315917)
    ·
      refine ⟨3826635081345558424243469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10204360216921489131315917 3826635081345558424243469)
      ·
        refine ⟨1434988155504584409091301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3826635081345558424243469 1434988155504584409091301)
        ·
          refine ⟨269060279157109576704619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1434988155504584409091301 269060279157109576704619)
          ·
            refine ⟨403590418735664365056929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269060279157109576704619 403590418735664365056929)
            ·
              refine ⟨302692814051748273792697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403590418735664365056929 302692814051748273792697)
              ·
                refine ⟨227019610538811205344523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302692814051748273792697 227019610538811205344523)
                ·
                  refine ⟨340529415808216808016785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227019610538811205344523 340529415808216808016785)
                  ·
                    refine ⟨255397061856162606012589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 340529415808216808016785 255397061856162606012589)
                    ·
                      refine ⟨95773898196060977254721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255397061856162606012589 95773898196060977254721)
                      ·
                        rfl

theorem cell23_186519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_186519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186519 prefixEnd_186519 := by exact prefixLift 186519
  have htrace : WordTrace (prefixWord ++ tailWord_186519) baseStart_186519 baseEnd_186519 := by
    simpa [prefixWord, tailWord_186519, baseEnd_186519] using wordTrace_append hprefix tailTrace_186519
  have hstable : (prefixWord ++ tailWord_186519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186519).length < 2 ^ (prefixWord ++ tailWord_186519).sum := by decide
  have hdescent : baseEnd_186519 < baseStart_186519 := by decide
  rcases family_descends (prefixWord ++ tailWord_186519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186589 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_186589 : Nat := 118140960795 + 186589 * 2 ^ 59
def prefixEnd_186589 : Nat := 4983230072969 + 3 ^ 40 * 186589 * 2
def baseEnd_186589 : Nat := 95809841841875703379399

theorem tailTrace_186589 : CollatzResearch.WordTrace tailWord_186589 prefixEnd_186589 95809841841875703379399 := by
  unfold tailWord_186589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6805459921027394709258821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4536973280684929806172547 6805459921027394709258821)
  ·
    refine ⟨1276023735192636507986029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6805459921027394709258821 1276023735192636507986029)
    ·
      refine ⟨478508900697238690494761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1276023735192636507986029 478508900697238690494761)
      ·
        refine ⟨358881675522929017871071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 478508900697238690494761 358881675522929017871071)
        ·
          refine ⟨538322513284393526806607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358881675522929017871071 538322513284393526806607)
          ·
            refine ⟨807483769926590290209911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538322513284393526806607 807483769926590290209911)
            ·
              refine ⟨1211225654889885435314867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807483769926590290209911 1211225654889885435314867)
              ·
                refine ⟨1816838482334828152972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1211225654889885435314867 1816838482334828152972301)
                ·
                  refine ⟨681314430875560557364613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1816838482334828152972301 681314430875560557364613)
                  ·
                    refine ⟨127746455789167604505865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 681314430875560557364613 127746455789167604505865)
                    ·
                      refine ⟨95809841841875703379399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127746455789167604505865 95809841841875703379399)
                      ·
                        rfl

theorem cell23_186589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_186589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186589 prefixEnd_186589 := by exact prefixLift 186589
  have htrace : WordTrace (prefixWord ++ tailWord_186589) baseStart_186589 baseEnd_186589 := by
    simpa [prefixWord, tailWord_186589, baseEnd_186589] using wordTrace_append hprefix tailTrace_186589
  have hstable : (prefixWord ++ tailWord_186589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186589).length < 2 ^ (prefixWord ++ tailWord_186589).sum := by decide
  have hdescent : baseEnd_186589 < baseStart_186589 := by decide
  rcases family_descends (prefixWord ++ tailWord_186589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186625 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 7]
def baseStart_186625 : Nat := 118140960795 + 186625 * 2 ^ 59
def prefixEnd_186625 : Nat := 4983230072969 + 3 ^ 40 * 186625 * 2
def baseEnd_186625 : Nat := 31942775715145854176411

theorem tailTrace_186625 : CollatzResearch.WordTrace tailWord_186625 prefixEnd_186625 31942775715145854176411 := by
  unfold tailWord_186625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6806772948896972857569329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4537848632597981905046219 6806772948896972857569329)
  ·
    refine ⟨5105079711672729643176997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6806772948896972857569329 5105079711672729643176997)
    ·
      refine ⟨957202445938636808095687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5105079711672729643176997 957202445938636808095687)
      ·
        refine ⟨1435803668907955212143531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957202445938636808095687 1435803668907955212143531)
        ·
          refine ⟨2153705503361932818215297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1435803668907955212143531 2153705503361932818215297)
          ·
            refine ⟨1615279127521449613661473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2153705503361932818215297 1615279127521449613661473)
            ·
              refine ⟨1211459345641087210246105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1615279127521449613661473 1211459345641087210246105)
              ·
                refine ⟨908594509230815407684579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211459345641087210246105 908594509230815407684579)
                ·
                  refine ⟨1362891763846223111526869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908594509230815407684579 1362891763846223111526869)
                  ·
                    refine ⟨31942775715145854176411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1362891763846223111526869 31942775715145854176411)
                    ·
                      rfl

theorem cell23_186625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_186625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186625 prefixEnd_186625 := by exact prefixLift 186625
  have htrace : WordTrace (prefixWord ++ tailWord_186625) baseStart_186625 baseEnd_186625 := by
    simpa [prefixWord, tailWord_186625, baseEnd_186625] using wordTrace_append hprefix tailTrace_186625
  have hstable : (prefixWord ++ tailWord_186625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186625).length < 2 ^ (prefixWord ++ tailWord_186625).sum := by decide
  have hdescent : baseEnd_186625 < baseStart_186625 := by decide
  rcases family_descends (prefixWord ++ tailWord_186625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186675 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6]
def baseStart_186675 : Nat := 118140960795 + 186675 * 2 ^ 59
def prefixEnd_186675 : Nat := 4983230072969 + 3 ^ 40 * 186675 * 2
def baseEnd_186675 : Nat := 95854001178162366904003

theorem tailTrace_186675 : CollatzResearch.WordTrace tailWord_186675 prefixEnd_186675 95854001178162366904003 := by
  unfold tailWord_186675
  simp only [CollatzResearch.WordTrace]
  refine ⟨6808596598715831396889479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4539064399143887597926319 6808596598715831396889479)
  ·
    refine ⟨10212894898073747095334219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6808596598715831396889479 10212894898073747095334219)
    ·
      refine ⟨15319342347110620643001329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10212894898073747095334219 15319342347110620643001329)
      ·
        refine ⟨11489506760332965482250997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15319342347110620643001329 11489506760332965482250997)
        ·
          refine ⟨1077141258781215513961031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11489506760332965482250997 1077141258781215513961031)
          ·
            refine ⟨1615711888171823270941547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1077141258781215513961031 1615711888171823270941547)
            ·
              refine ⟨2423567832257734906412321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1615711888171823270941547 2423567832257734906412321)
              ·
                refine ⟨1817675874193301179809241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2423567832257734906412321 1817675874193301179809241)
                ·
                  refine ⟨1363256905644975884856931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1817675874193301179809241 1363256905644975884856931)
                  ·
                    refine ⟨2044885358467463827285397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1363256905644975884856931 2044885358467463827285397)
                    ·
                      refine ⟨95854001178162366904003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2044885358467463827285397 95854001178162366904003)
                      ·
                        rfl

theorem cell23_186675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 6].length) (baseStart_186675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186675 prefixEnd_186675 := by exact prefixLift 186675
  have htrace : WordTrace (prefixWord ++ tailWord_186675) baseStart_186675 baseEnd_186675 := by
    simpa [prefixWord, tailWord_186675, baseEnd_186675] using wordTrace_append hprefix tailTrace_186675
  have hstable : (prefixWord ++ tailWord_186675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186675).length < 2 ^ (prefixWord ++ tailWord_186675).sum := by decide
  have hdescent : baseEnd_186675 < baseStart_186675 := by decide
  rcases family_descends (prefixWord ++ tailWord_186675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186682 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3]
def baseStart_186682 : Nat := 118140960795 + 186682 * 2 ^ 59
def prefixEnd_186682 : Nat := 4983230072969 + 3 ^ 40 * 186682 * 2
def baseEnd_186682 : Nat := 95857595542743839516471

theorem tailTrace_186682 : CollatzResearch.WordTrace tailWord_186682 prefixEnd_186682 95857595542743839516471 := by
  unfold tailWord_186682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702212977422617898098575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4539234606460314394929533 1702212977422617898098575)
  ·
    refine ⟨2553319466133926847147863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1702212977422617898098575 2553319466133926847147863)
    ·
      refine ⟨3829979199200890270721795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553319466133926847147863 3829979199200890270721795)
      ·
        refine ⟨5744968798801335406082693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3829979199200890270721795 5744968798801335406082693)
        ·
          refine ⟨1077181649775250388640505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5744968798801335406082693 1077181649775250388640505)
          ·
            refine ⟨807886237331437791480379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1077181649775250388640505 807886237331437791480379)
            ·
              refine ⟨1211829355997156687220569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 807886237331437791480379 1211829355997156687220569)
              ·
                refine ⟨908872016997867515415427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1211829355997156687220569 908872016997867515415427)
                ·
                  refine ⟨1363308025496801273123141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 908872016997867515415427 1363308025496801273123141)
                  ·
                    refine ⟨255620254780650238710589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1363308025496801273123141 255620254780650238710589)
                    ·
                      refine ⟨95857595542743839516471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255620254780650238710589 95857595542743839516471)
                      ·
                        rfl

theorem cell23_186682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_186682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186682 prefixEnd_186682 := by exact prefixLift 186682
  have htrace : WordTrace (prefixWord ++ tailWord_186682) baseStart_186682 baseEnd_186682 := by
    simpa [prefixWord, tailWord_186682, baseEnd_186682] using wordTrace_append hprefix tailTrace_186682
  have hstable : (prefixWord ++ tailWord_186682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186682).length < 2 ^ (prefixWord ++ tailWord_186682).sum := by decide
  have hdescent : baseEnd_186682 < baseStart_186682 := by decide
  rcases family_descends (prefixWord ++ tailWord_186682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186706 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_186706 : Nat := 118140960795 + 186706 * 2 ^ 59
def prefixEnd_186706 : Nat := 4983230072969 + 3 ^ 40 * 186706 * 2
def baseEnd_186706 : Nat := 31956639692817248538787

theorem tailTrace_186706 : CollatzResearch.WordTrace tailWord_186706 prefixEnd_186706 31956639692817248538787 := by
  unfold tailWord_186706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702431815400880922816993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4539818174402349127511981 1702431815400880922816993)
  ·
    refine ⟨1276823861550660692112745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1702431815400880922816993 1276823861550660692112745)
    ·
      refine ⟨957617896162995519084559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1276823861550660692112745 957617896162995519084559)
      ·
        refine ⟨1436426844244493278626839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957617896162995519084559 1436426844244493278626839)
        ·
          refine ⟨2154640266366739917940259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436426844244493278626839 2154640266366739917940259)
          ·
            refine ⟨3231960399550109876910389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2154640266366739917940259 3231960399550109876910389)
            ·
              refine ⟨302996287457822800960349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3231960399550109876910389 302996287457822800960349)
              ·
                refine ⟨113623607796683550360131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302996287457822800960349 113623607796683550360131)
                ·
                  refine ⟨170435411695025325540197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113623607796683550360131 170435411695025325540197)
                  ·
                    refine ⟨31956639692817248538787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170435411695025325540197 31956639692817248538787)
                    ·
                      rfl

theorem cell23_186706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_186706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186706 prefixEnd_186706 := by exact prefixLift 186706
  have htrace : WordTrace (prefixWord ++ tailWord_186706) baseStart_186706 baseEnd_186706 := by
    simpa [prefixWord, tailWord_186706, baseEnd_186706] using wordTrace_append hprefix tailTrace_186706
  have hstable : (prefixWord ++ tailWord_186706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186706).length < 2 ^ (prefixWord ++ tailWord_186706).sum := by decide
  have hdescent : baseEnd_186706 < baseStart_186706 := by decide
  rcases family_descends (prefixWord ++ tailWord_186706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186749 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_186749 : Nat := 118140960795 + 186749 * 2 ^ 59
def prefixEnd_186749 : Nat := 4983230072969 + 3 ^ 40 * 186749 * 2
def baseEnd_186749 : Nat := 31963999582198359126221

theorem tailTrace_186749 : CollatzResearch.WordTrace tailWord_186749 prefixEnd_186749 31963999582198359126221 := by
  unfold tailWord_186749
  simp only [CollatzResearch.WordTrace]
  refine ⟨6811295600447742035083301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4540863733631828023388867 6811295600447742035083301)
  ·
    refine ⟨1277117925083951631578119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6811295600447742035083301 1277117925083951631578119)
    ·
      refine ⟨1915676887625927447367179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1277117925083951631578119 1915676887625927447367179)
      ·
        refine ⟨2873515331438891171050769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1915676887625927447367179 2873515331438891171050769)
        ·
          refine ⟨2155136498579168378288077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2873515331438891171050769 2155136498579168378288077)
          ·
            refine ⟨808176186967188141858029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2155136498579168378288077 808176186967188141858029)
            ·
              refine ⟨303066070112695553196761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 808176186967188141858029 303066070112695553196761)
              ·
                refine ⟨227299552584521664897571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 303066070112695553196761 227299552584521664897571)
                ·
                  refine ⟨340949328876782497346357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227299552584521664897571 340949328876782497346357)
                  ·
                    refine ⟨31963999582198359126221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 340949328876782497346357 31963999582198359126221)
                    ·
                      rfl

theorem cell23_186749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_186749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186749 prefixEnd_186749 := by exact prefixLift 186749
  have htrace : WordTrace (prefixWord ++ tailWord_186749) baseStart_186749 baseEnd_186749 := by
    simpa [prefixWord, tailWord_186749, baseEnd_186749] using wordTrace_append hprefix tailTrace_186749
  have hstable : (prefixWord ++ tailWord_186749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186749).length < 2 ^ (prefixWord ++ tailWord_186749).sum := by decide
  have hdescent : baseEnd_186749 < baseStart_186749 := by decide
  rcases family_descends (prefixWord ++ tailWord_186749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186756 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_186756 : Nat := 118140960795 + 186756 * 2 ^ 59
def prefixEnd_186756 : Nat := 4983230072969 + 3 ^ 40 * 186756 * 2
def baseEnd_186756 : Nat := 95895593111176549991131

theorem tailTrace_186756 : CollatzResearch.WordTrace tailWord_186756 prefixEnd_186756 95895593111176549991131 := by
  unfold tailWord_186756
  simp only [CollatzResearch.WordTrace]
  refine ⟨3405775455711191115294061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4541033940948254820392081 3405775455711191115294061)
  ·
    refine ⟨1277165795891696668235273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3405775455711191115294061 1277165795891696668235273)
    ·
      refine ⟨957874346918772501176455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1277165795891696668235273 957874346918772501176455)
      ·
        refine ⟨1436811520378158751764683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 957874346918772501176455 1436811520378158751764683)
        ·
          refine ⟨2155217280567238127647025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1436811520378158751764683 2155217280567238127647025)
          ·
            refine ⟨1616412960425428595735269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2155217280567238127647025 1616412960425428595735269)
            ·
              refine ⟨303077430079767861700363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1616412960425428595735269 303077430079767861700363)
              ·
                refine ⟨454616145119651792550545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303077430079767861700363 454616145119651792550545)
                ·
                  refine ⟨340962108839738844412909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 454616145119651792550545 340962108839738844412909)
                  ·
                    refine ⟨127860790814902066654841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 340962108839738844412909 127860790814902066654841)
                    ·
                      refine ⟨95895593111176549991131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 127860790814902066654841 95895593111176549991131)
                      ·
                        rfl

theorem cell23_186756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_186756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186756 prefixEnd_186756 := by exact prefixLift 186756
  have htrace : WordTrace (prefixWord ++ tailWord_186756) baseStart_186756 baseEnd_186756 := by
    simpa [prefixWord, tailWord_186756, baseEnd_186756] using wordTrace_append hprefix tailTrace_186756
  have hstable : (prefixWord ++ tailWord_186756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186756).length < 2 ^ (prefixWord ++ tailWord_186756).sum := by decide
  have hdescent : baseEnd_186756 < baseStart_186756 := by decide
  rcases family_descends (prefixWord ++ tailWord_186756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186809 : List Nat := [1, 2, 1, 4, 3, 2, 3, 7]
def baseStart_186809 : Nat := 118140960795 + 186809 * 2 ^ 59
def prefixEnd_186809 : Nat := 4983230072969 + 3 ^ 40 * 186809 * 2
def baseEnd_186809 : Nat := 3552696577254253430681

theorem tailTrace_186809 : CollatzResearch.WordTrace tailWord_186809 prefixEnd_186809 3552696577254253430681 := by
  unfold tailWord_186809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813483980230372282267481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4542322653486914854844987 6813483980230372282267481)
  ·
    refine ⟨5110112985172779211700611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6813483980230372282267481 5110112985172779211700611)
    ·
      refine ⟨7665169477759168817550917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5110112985172779211700611 7665169477759168817550917)
      ·
        refine ⟨1437219277079844153290797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7665169477759168817550917 1437219277079844153290797)
        ·
          refine ⟨538957228904941557484049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1437219277079844153290797 538957228904941557484049)
          ·
            refine ⟨404217921678706168113037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 538957228904941557484049 404217921678706168113037)
            ·
              refine ⟨151581720629514813042389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 404217921678706168113037 151581720629514813042389)
              ·
                refine ⟨3552696577254253430681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151581720629514813042389 3552696577254253430681)
                ·
                  rfl

theorem cell23_186809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 7].length) (baseStart_186809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186809 prefixEnd_186809 := by exact prefixLift 186809
  have htrace : WordTrace (prefixWord ++ tailWord_186809) baseStart_186809 baseEnd_186809 := by
    simpa [prefixWord, tailWord_186809, baseEnd_186809] using wordTrace_append hprefix tailTrace_186809
  have hstable : (prefixWord ++ tailWord_186809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186809).length < 2 ^ (prefixWord ++ tailWord_186809).sum := by decide
  have hdescent : baseEnd_186809 < baseStart_186809 := by decide
  rcases family_descends (prefixWord ++ tailWord_186809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186817 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 1, 5]
def baseStart_186817 : Nat := 118140960795 + 186817 * 2 ^ 59
def prefixEnd_186817 : Nat := 4983230072969 + 3 ^ 40 * 186817 * 2
def baseEnd_186817 : Nat := 31975638477033603776117

theorem tailTrace_186817 : CollatzResearch.WordTrace tailWord_186817 prefixEnd_186817 31975638477033603776117 := by
  unfold tailWord_186817
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813775764201389648558705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4542517176134259765705803 6813775764201389648558705)
  ·
    refine ⟨5110331823151042236419029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6813775764201389648558705 5110331823151042236419029)
    ·
      refine ⟨119773402105102552416071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5110331823151042236419029 119773402105102552416071)
      ·
        refine ⟨179660103157653828624107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119773402105102552416071 179660103157653828624107)
        ·
          refine ⟨269490154736480742936161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179660103157653828624107 269490154736480742936161)
          ·
            refine ⟨202117616052360557202121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269490154736480742936161 202117616052360557202121)
            ·
              refine ⟨151588212039270417901591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202117616052360557202121 151588212039270417901591)
              ·
                refine ⟨227382318058905626852387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151588212039270417901591 227382318058905626852387)
                ·
                  refine ⟨341073477088358440278581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227382318058905626852387 341073477088358440278581)
                  ·
                    refine ⟨31975638477033603776117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341073477088358440278581 31975638477033603776117)
                    ·
                      rfl

theorem cell23_186817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_186817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186817 prefixEnd_186817 := by exact prefixLift 186817
  have htrace : WordTrace (prefixWord ++ tailWord_186817) baseStart_186817 baseEnd_186817 := by
    simpa [prefixWord, tailWord_186817, baseEnd_186817] using wordTrace_append hprefix tailTrace_186817
  have hstable : (prefixWord ++ tailWord_186817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186817).length < 2 ^ (prefixWord ++ tailWord_186817).sum := by decide
  have hdescent : baseEnd_186817 < baseStart_186817 := by decide
  rcases family_descends (prefixWord ++ tailWord_186817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186819 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 3]
def baseStart_186819 : Nat := 118140960795 + 186819 * 2 ^ 59
def prefixEnd_186819 : Nat := 4983230072969 + 3 ^ 40 * 186819 * 2
def baseEnd_186819 : Nat := 95927942392409803503341

theorem tailTrace_186819 : CollatzResearch.WordTrace tailWord_186819 prefixEnd_186819 95927942392409803503341 := by
  unfold tailWord_186819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813848710194143990131511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4542565806796095993421007 6813848710194143990131511)
  ·
    refine ⟨10220773065291215985197267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6813848710194143990131511 10220773065291215985197267)
    ·
      refine ⟨15331159597936823977795901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10220773065291215985197267 15331159597936823977795901)
      ·
        refine ⟨5749184849226308991673463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15331159597936823977795901 5749184849226308991673463)
        ·
          refine ⟨8623777273839463487510195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5749184849226308991673463 8623777273839463487510195)
          ·
            refine ⟨12935665910759195231265293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8623777273839463487510195 12935665910759195231265293)
            ·
              refine ⟨4850874716534698211724485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12935665910759195231265293 4850874716534698211724485)
              ·
                refine ⟨909539009350255914698341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4850874716534698211724485 909539009350255914698341)
                ·
                  refine ⟨170538564253172984005939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 909539009350255914698341 170538564253172984005939)
                  ·
                    refine ⟨255807846379759476008909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170538564253172984005939 255807846379759476008909)
                    ·
                      refine ⟨95927942392409803503341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255807846379759476008909 95927942392409803503341)
                      ·
                        rfl

theorem cell23_186819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_186819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186819 prefixEnd_186819 := by exact prefixLift 186819
  have htrace : WordTrace (prefixWord ++ tailWord_186819) baseStart_186819 baseEnd_186819 := by
    simpa [prefixWord, tailWord_186819, baseEnd_186819] using wordTrace_append hprefix tailTrace_186819
  have hstable : (prefixWord ++ tailWord_186819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186819).length < 2 ^ (prefixWord ++ tailWord_186819).sum := by decide
  have hdescent : baseEnd_186819 < baseStart_186819 := by decide
  rcases family_descends (prefixWord ++ tailWord_186819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186820 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_186820 : Nat := 118140960795 + 186820 * 2 ^ 59
def prefixEnd_186820 : Nat := 4983230072969 + 3 ^ 40 * 186820 * 2
def baseEnd_186820 : Nat := 95928455873064299590837

theorem tailTrace_186820 : CollatzResearch.WordTrace tailWord_186820 prefixEnd_186820 95928455873064299590837 := by
  unfold tailWord_186820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3406942591595260580458957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4542590122127014107278609 3406942591595260580458957)
  ·
    refine ⟨1277603471848222717672109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3406942591595260580458957 1277603471848222717672109)
    ·
      refine ⟨479101301943083519127041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1277603471848222717672109 479101301943083519127041)
      ·
        refine ⟨359325976457312639345281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 479101301943083519127041 359325976457312639345281)
        ·
          refine ⟨269494482342984479508961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359325976457312639345281 269494482342984479508961)
          ·
            refine ⟨202120861757238359631721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269494482342984479508961 202120861757238359631721)
            ·
              refine ⟨151590646317928769723791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202120861757238359631721 151590646317928769723791)
              ·
                refine ⟨227385969476893154585687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151590646317928769723791 227385969476893154585687)
                ·
                  refine ⟨341078954215339731878531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227385969476893154585687 341078954215339731878531)
                  ·
                    refine ⟨511618431323009597817797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 341078954215339731878531 511618431323009597817797)
                    ·
                      refine ⟨95928455873064299590837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 511618431323009597817797 95928455873064299590837)
                      ·
                        rfl

theorem cell23_186820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_186820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186820 prefixEnd_186820 := by exact prefixLift 186820
  have htrace : WordTrace (prefixWord ++ tailWord_186820) baseStart_186820 baseEnd_186820 := by
    simpa [prefixWord, tailWord_186820, baseEnd_186820] using wordTrace_append hprefix tailTrace_186820
  have hstable : (prefixWord ++ tailWord_186820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186820).length < 2 ^ (prefixWord ++ tailWord_186820).sum := by decide
  have hdescent : baseEnd_186820 < baseStart_186820 := by decide
  rcases family_descends (prefixWord ++ tailWord_186820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186823 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_186823 : Nat := 118140960795 + 186823 * 2 ^ 59
def prefixEnd_186823 : Nat := 4983230072969 + 3 ^ 40 * 186823 * 2
def baseEnd_186823 : Nat := 95929996315027787853323

theorem tailTrace_186823 : CollatzResearch.WordTrace tailWord_186823 prefixEnd_186823 95929996315027787853323 := by
  unfold tailWord_186823
  simp only [CollatzResearch.WordTrace]
  refine ⟨6813994602179652673277123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4542663068119768448851415 6813994602179652673277123)
  ·
    refine ⟨10220991903269479009915685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6813994602179652673277123 10220991903269479009915685)
    ·
      refine ⟨1916435981863027314359191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10220991903269479009915685 1916435981863027314359191)
      ·
        refine ⟨2874653972794540971538787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916435981863027314359191 2874653972794540971538787)
        ·
          refine ⟨4311980959191811457308181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2874653972794540971538787 4311980959191811457308181)
          ·
            refine ⟨202124107462116162061321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4311980959191811457308181 202124107462116162061321)
            ·
              refine ⟨151593080596587121545991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202124107462116162061321 151593080596587121545991)
              ·
                refine ⟨227389620894880682318987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151593080596587121545991 227389620894880682318987)
                ·
                  refine ⟨341084431342321023478481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227389620894880682318987 341084431342321023478481)
                  ·
                    refine ⟨255813323506740767608861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 341084431342321023478481 255813323506740767608861)
                    ·
                      refine ⟨95929996315027787853323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255813323506740767608861 95929996315027787853323)
                      ·
                        rfl

theorem cell23_186823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_186823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186823 prefixEnd_186823 := by exact prefixLift 186823
  have htrace : WordTrace (prefixWord ++ tailWord_186823) baseStart_186823 baseEnd_186823 := by
    simpa [prefixWord, tailWord_186823, baseEnd_186823] using wordTrace_append hprefix tailTrace_186823
  have hstable : (prefixWord ++ tailWord_186823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186823).length < 2 ^ (prefixWord ++ tailWord_186823).sum := by decide
  have hdescent : baseEnd_186823 < baseStart_186823 := by decide
  rcases family_descends (prefixWord ++ tailWord_186823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186850 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_186850 : Nat := 118140960795 + 186850 * 2 ^ 59
def prefixEnd_186850 : Nat := 4983230072969 + 3 ^ 40 * 186850 * 2
def baseEnd_186850 : Nat := 95943860292699182215699

theorem tailTrace_186850 : CollatzResearch.WordTrace tailWord_186850 prefixEnd_186850 95943860292699182215699 := by
  unfold tailWord_186850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1703744843270459071127501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4543319582054557523006669 1703744843270459071127501)
  ·
    refine ⟨638904316226422151672813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1703744843270459071127501 638904316226422151672813)
    ·
      refine ⟨239589118584908306877305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 638904316226422151672813 239589118584908306877305)
      ·
        refine ⟨179691838938681230157979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239589118584908306877305 179691838938681230157979)
        ·
          refine ⟨269537758408021845236969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179691838938681230157979 269537758408021845236969)
          ·
            refine ⟨202153318806016383927727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269537758408021845236969 202153318806016383927727)
            ·
              refine ⟨303229978209024575891591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202153318806016383927727 303229978209024575891591)
              ·
                refine ⟨454844967313536863837387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303229978209024575891591 454844967313536863837387)
                ·
                  refine ⟨682267450970305295756081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454844967313536863837387 682267450970305295756081)
                  ·
                    refine ⟨511700588227728971817061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 682267450970305295756081 511700588227728971817061)
                    ·
                      refine ⟨95943860292699182215699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 511700588227728971817061 95943860292699182215699)
                      ·
                        rfl

theorem cell23_186850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_186850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186850 prefixEnd_186850 := by exact prefixLift 186850
  have htrace : WordTrace (prefixWord ++ tailWord_186850) baseStart_186850 baseEnd_186850 := by
    simpa [prefixWord, tailWord_186850, baseEnd_186850] using wordTrace_append hprefix tailTrace_186850
  have hstable : (prefixWord ++ tailWord_186850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186850).length < 2 ^ (prefixWord ++ tailWord_186850).sum := by decide
  have hdescent : baseEnd_186850 < baseStart_186850 := by decide
  rcases family_descends (prefixWord ++ tailWord_186850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186853 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_186853 : Nat := 118140960795 + 186853 * 2 ^ 59
def prefixEnd_186853 : Nat := 4983230072969 + 3 ^ 40 * 186853 * 2
def baseEnd_186853 : Nat := 95945400734662670478185

theorem tailTrace_186853 : CollatzResearch.WordTrace tailWord_186853 prefixEnd_186853 95945400734662670478185 := by
  unfold tailWord_186853
  simp only [CollatzResearch.WordTrace]
  refine ⟨6815088792070967796869213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4543392528047311864579475 6815088792070967796869213)
  ·
    refine ⟨2555658297026612923825955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6815088792070967796869213 2555658297026612923825955)
    ·
      refine ⟨3833487445539919385738933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2555658297026612923825955 3833487445539919385738933)
      ·
        refine ⟨359389448019367442413025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3833487445539919385738933 359389448019367442413025)
        ·
          refine ⟨269542086014525581809769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359389448019367442413025 269542086014525581809769)
          ·
            refine ⟨202156564510894186357327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269542086014525581809769 202156564510894186357327)
            ·
              refine ⟨303234846766341279535991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202156564510894186357327 303234846766341279535991)
              ·
                refine ⟨454852270149511919303987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303234846766341279535991 454852270149511919303987)
                ·
                  refine ⟨682278405224267878955981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 454852270149511919303987 682278405224267878955981)
                  ·
                    refine ⟨255854401959100454608493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 682278405224267878955981 255854401959100454608493)
                    ·
                      refine ⟨95945400734662670478185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 255854401959100454608493 95945400734662670478185)
                      ·
                        rfl

theorem cell23_186853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_186853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186853 prefixEnd_186853 := by exact prefixLift 186853
  have htrace : WordTrace (prefixWord ++ tailWord_186853) baseStart_186853 baseEnd_186853 := by
    simpa [prefixWord, tailWord_186853, baseEnd_186853] using wordTrace_append hprefix tailTrace_186853
  have hstable : (prefixWord ++ tailWord_186853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186853).length < 2 ^ (prefixWord ++ tailWord_186853).sum := by decide
  have hdescent : baseEnd_186853 < baseStart_186853 := by decide
  rcases family_descends (prefixWord ++ tailWord_186853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186929 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_186929 : Nat := 118140960795 + 186929 * 2 ^ 59
def prefixEnd_186929 : Nat := 4983230072969 + 3 ^ 40 * 186929 * 2
def baseEnd_186929 : Nat := 31994808421468124375945

theorem tailTrace_186929 : CollatzResearch.WordTrace tailWord_186929 prefixEnd_186929 31994808421468124375945 := by
  unfold tailWord_186929
  simp only [CollatzResearch.WordTrace]
  refine ⟨6817860739795632776635841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4545240493197088517757227 6817860739795632776635841)
  ·
    refine ⟨5113395554846724582476881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6817860739795632776635841 5113395554846724582476881)
    ·
      refine ⟨3835046666135043436857661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5113395554846724582476881 3835046666135043436857661)
      ·
        refine ⟨1438142499800641288821623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3835046666135043436857661 1438142499800641288821623)
        ·
          refine ⟨2157213749700961933232435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1438142499800641288821623 2157213749700961933232435)
          ·
            refine ⟨3235820624551442899848653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2157213749700961933232435 3235820624551442899848653)
            ·
              refine ⟨1213432734206791087443245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3235820624551442899848653 1213432734206791087443245)
              ·
                refine ⟨455037275327546657791217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1213432734206791087443245 455037275327546657791217)
                ·
                  refine ⟨341277956495659993343413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455037275327546657791217 341277956495659993343413)
                  ·
                    refine ⟨31994808421468124375945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341277956495659993343413 31994808421468124375945)
                    ·
                      rfl

theorem cell23_186929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_186929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186929 prefixEnd_186929 := by exact prefixLift 186929
  have htrace : WordTrace (prefixWord ++ tailWord_186929) baseStart_186929 baseEnd_186929 := by
    simpa [prefixWord, tailWord_186929, baseEnd_186929] using wordTrace_append hprefix tailTrace_186929
  have hstable : (prefixWord ++ tailWord_186929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186929).length < 2 ^ (prefixWord ++ tailWord_186929).sum := by decide
  have hdescent : baseEnd_186929 < baseStart_186929 := by decide
  rcases family_descends (prefixWord ++ tailWord_186929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186950 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_186950 : Nat := 118140960795 + 186950 * 2 ^ 59
def prefixEnd_186950 : Nat := 4983230072969 + 3 ^ 40 * 186950 * 2
def baseEnd_186950 : Nat := 10666134262016532329471

theorem tailTrace_186950 : CollatzResearch.WordTrace tailWord_186950 prefixEnd_186950 10666134262016532329471 := by
  unfold tailWord_186950
  simp only [CollatzResearch.WordTrace]
  refine ⟨213082083522486042598447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4545751115146368908766869 213082083522486042598447)
  ·
    refine ⟨319623125283729063897671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213082083522486042598447 319623125283729063897671)
    ·
      refine ⟨479434687925593595846507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 319623125283729063897671 479434687925593595846507)
      ·
        refine ⟨719152031888390393769761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479434687925593595846507 719152031888390393769761)
        ·
          refine ⟨539364023916292795327321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 719152031888390393769761 539364023916292795327321)
          ·
            refine ⟨404523017937219596495491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 539364023916292795327321 404523017937219596495491)
            ·
              refine ⟨606784526905829394743237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 404523017937219596495491 606784526905829394743237)
              ·
                refine ⟨113772098794843011514357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 606784526905829394743237 113772098794843011514357)
                ·
                  refine ⟨10666134262016532329471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113772098794843011514357 10666134262016532329471)
                  ·
                    rfl

theorem cell23_186950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_186950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186950 prefixEnd_186950 := by exact prefixLift 186950
  have htrace : WordTrace (prefixWord ++ tailWord_186950) baseStart_186950 baseEnd_186950 := by
    simpa [prefixWord, tailWord_186950, baseEnd_186950] using wordTrace_append hprefix tailTrace_186950
  have hstable : (prefixWord ++ tailWord_186950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186950).length < 2 ^ (prefixWord ++ tailWord_186950).sum := by decide
  have hdescent : baseEnd_186950 < baseStart_186950 := by decide
  rcases family_descends (prefixWord ++ tailWord_186950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_186986 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_186986 : Nat := 118140960795 + 186986 * 2 ^ 59
def prefixEnd_186986 : Nat := 4983230072969 + 3 ^ 40 * 186986 * 2
def baseEnd_186986 : Nat := 96013693661710650115073

theorem tailTrace_186986 : CollatzResearch.WordTrace tailWord_186986 prefixEnd_186986 96013693661710650115073 := by
  unfold tailWord_186986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1704984925147282877865203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4546626467059421007640541 1704984925147282877865203)
  ·
    refine ⟨2557477387720924316797805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1704984925147282877865203 2557477387720924316797805)
    ·
      refine ⟨959054020395346618799177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2557477387720924316797805 959054020395346618799177)
      ·
        refine ⟨719290515296509964099383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959054020395346618799177 719290515296509964099383)
        ·
          refine ⟨1078935772944764946149075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719290515296509964099383 1078935772944764946149075)
          ·
            refine ⟨1618403659417147419223613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1078935772944764946149075 1618403659417147419223613)
            ·
              refine ⟨606901372281430282208855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1618403659417147419223613 606901372281430282208855)
              ·
                refine ⟨910352058422145423313283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 606901372281430282208855 910352058422145423313283)
                ·
                  refine ⟨1365528087633218134969925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910352058422145423313283 1365528087633218134969925)
                  ·
                    refine ⟨256036516431228400306861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1365528087633218134969925 256036516431228400306861)
                    ·
                      refine ⟨96013693661710650115073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256036516431228400306861 96013693661710650115073)
                      ·
                        rfl

theorem cell23_186986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_186986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_186986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_186986 prefixEnd_186986 := by exact prefixLift 186986
  have htrace : WordTrace (prefixWord ++ tailWord_186986) baseStart_186986 baseEnd_186986 := by
    simpa [prefixWord, tailWord_186986, baseEnd_186986] using wordTrace_append hprefix tailTrace_186986
  have hstable : (prefixWord ++ tailWord_186986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_186986).length < 2 ^ (prefixWord ++ tailWord_186986).sum := by decide
  have hdescent : baseEnd_186986 < baseStart_186986 := by decide
  rcases family_descends (prefixWord ++ tailWord_186986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187009 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_187009 : Nat := 118140960795 + 187009 * 2 ^ 59
def prefixEnd_187009 : Nat := 4983230072969 + 3 ^ 40 * 187009 * 2
def baseEnd_187009 : Nat := 96025503716764060127467

theorem tailTrace_187009 : CollatzResearch.WordTrace tailWord_187009 prefixEnd_187009 96025503716764060127467 := by
  unfold tailWord_187009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6820778579505806439548081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4547185719670537626365387 6820778579505806439548081)
  ·
    refine ⟨5115583934629354829661061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6820778579505806439548081 5115583934629354829661061)
    ·
      refine ⟨959171987743004030561449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5115583934629354829661061 959171987743004030561449)
      ·
        refine ⟨719378990807253022921087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959171987743004030561449 719378990807253022921087)
        ·
          refine ⟨1079068486210879534381631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719378990807253022921087 1079068486210879534381631)
          ·
            refine ⟨1618602729316319301572447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079068486210879534381631 1618602729316319301572447)
            ·
              refine ⟨2427904093974478952358671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1618602729316319301572447 2427904093974478952358671)
              ·
                refine ⟨3641856140961718428538007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2427904093974478952358671 3641856140961718428538007)
                ·
                  refine ⟨5462784211442577642807011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3641856140961718428538007 5462784211442577642807011)
                  ·
                    refine ⟨8194176317163866464210517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5462784211442577642807011 8194176317163866464210517)
                    ·
                      refine ⟨96025503716764060127467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8194176317163866464210517 96025503716764060127467)
                      ·
                        rfl

theorem cell23_187009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_187009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187009 prefixEnd_187009 := by exact prefixLift 187009
  have htrace : WordTrace (prefixWord ++ tailWord_187009) baseStart_187009 baseEnd_187009 := by
    simpa [prefixWord, tailWord_187009, baseEnd_187009] using wordTrace_append hprefix tailTrace_187009
  have hstable : (prefixWord ++ tailWord_187009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187009).length < 2 ^ (prefixWord ++ tailWord_187009).sum := by decide
  have hdescent : baseEnd_187009 < baseStart_187009 := by decide
  rcases family_descends (prefixWord ++ tailWord_187009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187019 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 3, 5]
def baseStart_187019 : Nat := 118140960795 + 187019 * 2 ^ 59
def prefixEnd_187019 : Nat := 4983230072969 + 3 ^ 40 * 187019 * 2
def baseEnd_187019 : Nat := 32010212841103007000807

theorem tailTrace_187019 : CollatzResearch.WordTrace tailWord_187019 prefixEnd_187019 32010212841103007000807 := by
  unfold tailWord_187019
  simp only [CollatzResearch.WordTrace]
  refine ⟨6821143309469578147412111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4547428872979718764941407 6821143309469578147412111)
  ·
    refine ⟨10231714964204367221118167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6821143309469578147412111 10231714964204367221118167)
    ·
      refine ⟨15347572446306550831677251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10231714964204367221118167 15347572446306550831677251)
      ·
        refine ⟨23021358669459826247515877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15347572446306550831677251 23021358669459826247515877)
        ·
          refine ⟨4316504750523717421409227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23021358669459826247515877 4316504750523717421409227)
          ·
            refine ⟨6474757125785576132113841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4316504750523717421409227 6474757125785576132113841)
            ·
              refine ⟨4856067844339182099085381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6474757125785576132113841 4856067844339182099085381)
              ·
                refine ⟨910512720813596643578509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4856067844339182099085381 910512720813596643578509)
                ·
                  refine ⟨341442270305098741341941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 910512720813596643578509 341442270305098741341941)
                  ·
                    refine ⟨32010212841103007000807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341442270305098741341941 32010212841103007000807)
                    ·
                      rfl

theorem cell23_187019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 5].length) (baseStart_187019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187019 prefixEnd_187019 := by exact prefixLift 187019
  have htrace : WordTrace (prefixWord ++ tailWord_187019) baseStart_187019 baseEnd_187019 := by
    simpa [prefixWord, tailWord_187019, baseEnd_187019] using wordTrace_append hprefix tailTrace_187019
  have hstable : (prefixWord ++ tailWord_187019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187019).length < 2 ^ (prefixWord ++ tailWord_187019).sum := by decide
  have hdescent : baseEnd_187019 < baseStart_187019 := by decide
  rcases family_descends (prefixWord ++ tailWord_187019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187053 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_187053 : Nat := 118140960795 + 187053 * 2 ^ 59
def prefixEnd_187053 : Nat := 4983230072969 + 3 ^ 40 * 187053 * 2
def baseEnd_187053 : Nat := 32016032288520629325755

theorem tailTrace_187053 : CollatzResearch.WordTrace tailWord_187053 prefixEnd_187053 32016032288520629325755 := by
  unfold tailWord_187053
  simp only [CollatzResearch.WordTrace]
  refine ⟨6822383391346401954149813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4548255594230934636099875 6822383391346401954149813)
  ·
    refine ⟨639598442938725183201545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6822383391346401954149813 639598442938725183201545)
    ·
      refine ⟨479698832204043887401159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 639598442938725183201545 479698832204043887401159)
      ·
        refine ⟨719548248306065831101739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479698832204043887401159 719548248306065831101739)
        ·
          refine ⟨1079322372459098746652609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719548248306065831101739 1079322372459098746652609)
          ·
            refine ⟨809491779344324059989457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079322372459098746652609 809491779344324059989457)
            ·
              refine ⟨607118834508243044992093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809491779344324059989457 607118834508243044992093)
              ·
                refine ⟨227669562940591141872035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 607118834508243044992093 227669562940591141872035)
                ·
                  refine ⟨341504344410886712808053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227669562940591141872035 341504344410886712808053)
                  ·
                    refine ⟨32016032288520629325755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341504344410886712808053 32016032288520629325755)
                    ·
                      rfl

theorem cell23_187053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_187053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187053 prefixEnd_187053 := by exact prefixLift 187053
  have htrace : WordTrace (prefixWord ++ tailWord_187053) baseStart_187053 baseEnd_187053 := by
    simpa [prefixWord, tailWord_187053, baseEnd_187053] using wordTrace_append hprefix tailTrace_187053
  have hstable : (prefixWord ++ tailWord_187053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187053).length < 2 ^ (prefixWord ++ tailWord_187053).sum := by decide
  have hdescent : baseEnd_187053 < baseStart_187053 := by decide
  rcases family_descends (prefixWord ++ tailWord_187053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187066 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_187066 : Nat := 118140960795 + 187066 * 2 ^ 59
def prefixEnd_187066 : Nat := 4983230072969 + 3 ^ 40 * 187066 * 2
def baseEnd_187066 : Nat := 32018257371356779038235

theorem tailTrace_187066 : CollatzResearch.WordTrace tailWord_187066 prefixEnd_187066 32018257371356779038235 := by
  unfold tailWord_187066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1705714385074826293593263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4548571693532870116248701 1705714385074826293593263)
  ·
    refine ⟨2558571577612239440389895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1705714385074826293593263 2558571577612239440389895)
    ·
      refine ⟨3837857366418359160584843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2558571577612239440389895 3837857366418359160584843)
      ·
        refine ⟨5756786049627538740877265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3837857366418359160584843 5756786049627538740877265)
        ·
          refine ⟨4317589537220654055657949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5756786049627538740877265 4317589537220654055657949)
          ·
            refine ⟨1619096076457745270871731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4317589537220654055657949 1619096076457745270871731)
            ·
              refine ⟨2428644114686617906307597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619096076457745270871731 2428644114686617906307597)
              ·
                refine ⟨910741543007481714865349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2428644114686617906307597 910741543007481714865349)
                ·
                  refine ⟨170764039313902821537253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 910741543007481714865349 170764039313902821537253)
                  ·
                    refine ⟨32018257371356779038235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170764039313902821537253 32018257371356779038235)
                    ·
                      rfl

theorem cell23_187066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_187066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187066 prefixEnd_187066 := by exact prefixLift 187066
  have htrace : WordTrace (prefixWord ++ tailWord_187066) baseStart_187066 baseEnd_187066 := by
    simpa [prefixWord, tailWord_187066, baseEnd_187066] using wordTrace_append hprefix tailTrace_187066
  have hstable : (prefixWord ++ tailWord_187066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187066).length < 2 ^ (prefixWord ++ tailWord_187066).sum := by decide
  have hdescent : baseEnd_187066 < baseStart_187066 := by decide
  rcases family_descends (prefixWord ++ tailWord_187066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187086 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_187086 : Nat := 118140960795 + 187086 * 2 ^ 59
def prefixEnd_187086 : Nat := 4983230072969 + 3 ^ 40 * 187086 * 2
def baseEnd_187086 : Nat := 96065041727160258864613

theorem tailTrace_187086 : CollatzResearch.WordTrace tailWord_187086 prefixEnd_187086 96065041727160258864613 := by
  unfold tailWord_187086
  simp only [CollatzResearch.WordTrace]
  refine ⟨852948375028356073762639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4549058000151232393400741 852948375028356073762639)
  ·
    refine ⟨1279422562542534110643959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 852948375028356073762639 1279422562542534110643959)
    ·
      refine ⟨1919133843813801165965939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279422562542534110643959 1919133843813801165965939)
      ·
        refine ⟨2878700765720701748948909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919133843813801165965939 2878700765720701748948909)
        ·
          refine ⟨1079512787145263155855841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2878700765720701748948909 1079512787145263155855841)
          ·
            refine ⟨809634590358947366891881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079512787145263155855841 809634590358947366891881)
            ·
              refine ⟨607225942769210525168911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 809634590358947366891881 607225942769210525168911)
              ·
                refine ⟨910838914153815787753367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607225942769210525168911 910838914153815787753367)
                ·
                  refine ⟨1366258371230723681630051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 910838914153815787753367 1366258371230723681630051)
                  ·
                    refine ⟨2049387556846085522445077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1366258371230723681630051 2049387556846085522445077)
                    ·
                      refine ⟨96065041727160258864613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2049387556846085522445077 96065041727160258864613)
                      ·
                        rfl

theorem cell23_187086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_187086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187086 prefixEnd_187086 := by exact prefixLift 187086
  have htrace : WordTrace (prefixWord ++ tailWord_187086) baseStart_187086 baseEnd_187086 := by
    simpa [prefixWord, tailWord_187086, baseEnd_187086] using wordTrace_append hprefix tailTrace_187086
  have hstable : (prefixWord ++ tailWord_187086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187086).length < 2 ^ (prefixWord ++ tailWord_187086).sum := by decide
  have hdescent : baseEnd_187086 < baseStart_187086 := by decide
  rcases family_descends (prefixWord ++ tailWord_187086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187126 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_187126 : Nat := 118140960795 + 187126 * 2 ^ 59
def prefixEnd_187126 : Nat := 4983230072969 + 3 ^ 40 * 187126 * 2
def baseEnd_187126 : Nat := 32028526984446700788143

theorem tailTrace_187126 : CollatzResearch.WordTrace tailWord_187126 prefixEnd_187126 32028526984446700788143 := by
  unfold tailWord_187126
  simp only [CollatzResearch.WordTrace]
  refine ⟨426565370005120963847327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4550030613387956947704821 426565370005120963847327)
  ·
    refine ⟨639848055007681445770991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 426565370005120963847327 639848055007681445770991)
    ·
      refine ⟨959772082511522168656487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 639848055007681445770991 959772082511522168656487)
      ·
        refine ⟨1439658123767283252984731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 959772082511522168656487 1439658123767283252984731)
        ·
          refine ⟨2159487185650924879477097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439658123767283252984731 2159487185650924879477097)
          ·
            refine ⟨1619615389238193659607823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159487185650924879477097 1619615389238193659607823)
            ·
              refine ⟨2429423083857290489411735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619615389238193659607823 2429423083857290489411735)
              ·
                refine ⟨3644134625785935734117603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429423083857290489411735 3644134625785935734117603)
                ·
                  refine ⟨5466201938678903601176405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3644134625785935734117603 5466201938678903601176405)
                  ·
                    refine ⟨32028526984446700788143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5466201938678903601176405 32028526984446700788143)
                    ·
                      rfl

theorem cell23_187126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_187126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187126 prefixEnd_187126 := by exact prefixLift 187126
  have htrace : WordTrace (prefixWord ++ tailWord_187126) baseStart_187126 baseEnd_187126 := by
    simpa [prefixWord, tailWord_187126, baseEnd_187126] using wordTrace_append hprefix tailTrace_187126
  have hstable : (prefixWord ++ tailWord_187126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187126).length < 2 ^ (prefixWord ++ tailWord_187126).sum := by decide
  have hdescent : baseEnd_187126 < baseStart_187126 := by decide
  rcases family_descends (prefixWord ++ tailWord_187126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187133 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_187133 : Nat := 118140960795 + 187133 * 2 ^ 59
def prefixEnd_187133 : Nat := 4983230072969 + 3 ^ 40 * 187133 * 2
def baseEnd_187133 : Nat := 96089175317921574976897

theorem tailTrace_187133 : CollatzResearch.WordTrace tailWord_187133 prefixEnd_187133 96089175317921574976897 := by
  unfold tailWord_187133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6825301231056575617062053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4550200820704383744708035 6825301231056575617062053)
  ·
    refine ⟨1279743980823107928199135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6825301231056575617062053 1279743980823107928199135)
    ·
      refine ⟨1919615971234661892298703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279743980823107928199135 1919615971234661892298703)
      ·
        refine ⟨2879423956851992838448055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1919615971234661892298703 2879423956851992838448055)
        ·
          refine ⟨4319135935277989257672083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2879423956851992838448055 4319135935277989257672083)
          ·
            refine ⟨6478703902916983886508125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4319135935277989257672083 6478703902916983886508125)
            ·
              refine ⟨2429513963593868957440547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6478703902916983886508125 2429513963593868957440547)
              ·
                refine ⟨3644270945390803436160821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2429513963593868957440547 3644270945390803436160821)
                ·
                  refine ⟨341650401130387822140077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3644270945390803436160821 341650401130387822140077)
                  ·
                    refine ⟨128118900423895433302529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341650401130387822140077 128118900423895433302529)
                    ·
                      refine ⟨96089175317921574976897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128118900423895433302529 96089175317921574976897)
                      ·
                        rfl

theorem cell23_187133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_187133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187133 prefixEnd_187133 := by exact prefixLift 187133
  have htrace : WordTrace (prefixWord ++ tailWord_187133) baseStart_187133 baseEnd_187133 := by
    simpa [prefixWord, tailWord_187133, baseEnd_187133] using wordTrace_append hprefix tailTrace_187133
  have hstable : (prefixWord ++ tailWord_187133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187133).length < 2 ^ (prefixWord ++ tailWord_187133).sum := by decide
  have hdescent : baseEnd_187133 < baseStart_187133 := by decide
  rcases family_descends (prefixWord ++ tailWord_187133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187140 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_187140 : Nat := 118140960795 + 187140 * 2 ^ 59
def prefixEnd_187140 : Nat := 4983230072969 + 3 ^ 40 * 187140 * 2
def baseEnd_187140 : Nat := 96092769682503047589365

theorem tailTrace_187140 : CollatzResearch.WordTrace tailWord_187140 prefixEnd_187140 96092769682503047589365 := by
  unfold tailWord_187140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3412778271015607906283437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4550371028020810541711249 3412778271015607906283437)
  ·
    refine ⟨1279791851630852964856289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3412778271015607906283437 1279791851630852964856289)
    ·
      refine ⟨959843888723139723642217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1279791851630852964856289 959843888723139723642217)
      ·
        refine ⟨719882916542354792731663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 959843888723139723642217 719882916542354792731663)
        ·
          refine ⟨1079824374813532189097495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719882916542354792731663 1079824374813532189097495)
          ·
            refine ⟨1619736562220298283646243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1079824374813532189097495 1619736562220298283646243)
            ·
              refine ⟨2429604843330447425469365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619736562220298283646243 2429604843330447425469365)
              ·
                refine ⟨227775454062229446137753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2429604843330447425469365 227775454062229446137753)
                ·
                  refine ⟨170831590546672084603315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 227775454062229446137753 170831590546672084603315)
                  ·
                    refine ⟨256247385820008126904973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170831590546672084603315 256247385820008126904973)
                    ·
                      refine ⟨96092769682503047589365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256247385820008126904973 96092769682503047589365)
                      ·
                        rfl

theorem cell23_187140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_187140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187140 prefixEnd_187140 := by exact prefixLift 187140
  have htrace : WordTrace (prefixWord ++ tailWord_187140) baseStart_187140 baseEnd_187140 := by
    simpa [prefixWord, tailWord_187140, baseEnd_187140] using wordTrace_append hprefix tailTrace_187140
  have hstable : (prefixWord ++ tailWord_187140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187140).length < 2 ^ (prefixWord ++ tailWord_187140).sum := by decide
  have hdescent : baseEnd_187140 < baseStart_187140 := by decide
  rcases family_descends (prefixWord ++ tailWord_187140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187146 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_187146 : Nat := 118140960795 + 187146 * 2 ^ 59
def prefixEnd_187146 : Nat := 4983230072969 + 3 ^ 40 * 187146 * 2
def baseEnd_187146 : Nat := 96095850566430024114337

theorem tailTrace_187146 : CollatzResearch.WordTrace tailWord_187146 prefixEnd_187146 96095850566430024114337 := by
  unfold tailWord_187146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706443845002369709321323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4550516920006319224856861 1706443845002369709321323)
  ·
    refine ⟨2559665767503554563981985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1706443845002369709321323 2559665767503554563981985)
    ·
      refine ⟨1919749325627665922986489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2559665767503554563981985 1919749325627665922986489)
      ·
        refine ⟨1439811994220749442239867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919749325627665922986489 1439811994220749442239867)
        ·
          refine ⟨2159717991331124163359801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439811994220749442239867 2159717991331124163359801)
          ·
            refine ⟨1619788493498343122519851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2159717991331124163359801 1619788493498343122519851)
            ·
              refine ⟨2429682740247514683779777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1619788493498343122519851 2429682740247514683779777)
              ·
                refine ⟨1822262055185636012834833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2429682740247514683779777 1822262055185636012834833)
                ·
                  refine ⟨1366696541389227009626125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1822262055185636012834833 1366696541389227009626125)
                  ·
                    refine ⟨512511203020960128609797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1366696541389227009626125 512511203020960128609797)
                    ·
                      refine ⟨96095850566430024114337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 512511203020960128609797 96095850566430024114337)
                      ·
                        rfl

theorem cell23_187146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_187146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187146 prefixEnd_187146 := by exact prefixLift 187146
  have htrace : WordTrace (prefixWord ++ tailWord_187146) baseStart_187146 baseEnd_187146 := by
    simpa [prefixWord, tailWord_187146, baseEnd_187146] using wordTrace_append hprefix tailTrace_187146
  have hstable : (prefixWord ++ tailWord_187146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187146).length < 2 ^ (prefixWord ++ tailWord_187146).sum := by decide
  have hdescent : baseEnd_187146 < baseStart_187146 := by decide
  rcases family_descends (prefixWord ++ tailWord_187146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187150 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_187150 : Nat := 118140960795 + 187150 * 2 ^ 59
def prefixEnd_187150 : Nat := 4983230072969 + 3 ^ 40 * 187150 * 2
def baseEnd_187150 : Nat := 96097904489048008464319

theorem tailTrace_187150 : CollatzResearch.WordTrace tailWord_187150 prefixEnd_187150 96097904489048008464319 := by
  unfold tailWord_187150
  simp only [CollatzResearch.WordTrace]
  refine ⟨853240158999373440053863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4550614181329991680287269 853240158999373440053863)
  ·
    refine ⟨1279860238499060160080795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 853240158999373440053863 1279860238499060160080795)
    ·
      refine ⟨1919790357748590240121193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1279860238499060160080795 1919790357748590240121193)
      ·
        refine ⟨1439842768311442680090895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1919790357748590240121193 1439842768311442680090895)
        ·
          refine ⟨2159764152467164020136343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1439842768311442680090895 2159764152467164020136343)
          ·
            refine ⟨3239646228700746030204515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2159764152467164020136343 3239646228700746030204515)
            ·
              refine ⟨4859469343051119045306773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3239646228700746030204515 4859469343051119045306773)
              ·
                refine ⟨227787625455521205248755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4859469343051119045306773 227787625455521205248755)
                ·
                  refine ⟨341681438183281807873133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227787625455521205248755 341681438183281807873133)
                  ·
                    refine ⟨128130539318730677952425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341681438183281807873133 128130539318730677952425)
                    ·
                      refine ⟨96097904489048008464319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128130539318730677952425 96097904489048008464319)
                      ·
                        rfl

theorem cell23_187150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_187150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187150 prefixEnd_187150 := by exact prefixLift 187150
  have htrace : WordTrace (prefixWord ++ tailWord_187150) baseStart_187150 baseEnd_187150 := by
    simpa [prefixWord, tailWord_187150, baseEnd_187150] using wordTrace_append hprefix tailTrace_187150
  have hstable : (prefixWord ++ tailWord_187150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187150).length < 2 ^ (prefixWord ++ tailWord_187150).sum := by decide
  have hdescent : baseEnd_187150 < baseStart_187150 := by decide
  rcases family_descends (prefixWord ++ tailWord_187150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187167 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 1, 3, 2]
def baseStart_187167 : Nat := 118140960795 + 187167 * 2 ^ 59
def prefixEnd_187167 : Nat := 4983230072969 + 3 ^ 40 * 187167 * 2
def baseEnd_187167 : Nat := 96106633660174441951741

theorem tailTrace_187167 : CollatzResearch.WordTrace tailWord_187167 prefixEnd_187167 96106633660174441951741 := by
  unfold tailWord_187167
  simp only [CollatzResearch.WordTrace]
  refine ⟨6826541312933399423799755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4551027541955599615866503 6826541312933399423799755)
  ·
    refine ⟨10239811969400099135699633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6826541312933399423799755 10239811969400099135699633)
    ·
      refine ⟨7679858977050074351774725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10239811969400099135699633 7679858977050074351774725)
      ·
        refine ⟨1439973558196888940957761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7679858977050074351774725 1439973558196888940957761)
        ·
          refine ⟨1079980168647666705718321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1439973558196888940957761 1079980168647666705718321)
          ·
            refine ⟨809985126485750029288741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1079980168647666705718321 809985126485750029288741)
            ·
              refine ⟨151872211216078130491639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 809985126485750029288741 151872211216078130491639)
              ·
                refine ⟨227808316824117195737459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151872211216078130491639 227808316824117195737459)
                ·
                  refine ⟨341712475236175793606189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 227808316824117195737459 341712475236175793606189)
                  ·
                    refine ⟨128142178213565922602321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 341712475236175793606189 128142178213565922602321)
                    ·
                      refine ⟨96106633660174441951741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128142178213565922602321 96106633660174441951741)
                      ·
                        rfl

theorem cell23_187167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_187167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187167 prefixEnd_187167 := by exact prefixLift 187167
  have htrace : WordTrace (prefixWord ++ tailWord_187167) baseStart_187167 baseEnd_187167 := by
    simpa [prefixWord, tailWord_187167, baseEnd_187167] using wordTrace_append hprefix tailTrace_187167
  have hstable : (prefixWord ++ tailWord_187167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187167).length < 2 ^ (prefixWord ++ tailWord_187167).sum := by decide
  have hdescent : baseEnd_187167 < baseStart_187167 := by decide
  rcases family_descends (prefixWord ++ tailWord_187167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187180 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_187180 : Nat := 118140960795 + 187180 * 2 ^ 59
def prefixEnd_187180 : Nat := 4983230072969 + 3 ^ 40 * 187180 * 2
def baseEnd_187180 : Nat := 96113308908682891089181

theorem tailTrace_187180 : CollatzResearch.WordTrace tailWord_187180 prefixEnd_187180 96113308908682891089181 := by
  unfold tailWord_187180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3413507730943151322011497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4551343641257535096015329 3413507730943151322011497)
  ·
    refine ⟨2560130798207363491508623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3413507730943151322011497 2560130798207363491508623)
    ·
      refine ⟨3840196197311045237262935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2560130798207363491508623 3840196197311045237262935)
      ·
        refine ⟨5760294295966567855894403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3840196197311045237262935 5760294295966567855894403)
        ·
          refine ⟨8640441443949851783841605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5760294295966567855894403 8640441443949851783841605)
          ·
            refine ⟨1620082770740597209470301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8640441443949851783841605 1620082770740597209470301)
            ·
              refine ⟨607531039027723953551363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1620082770740597209470301 607531039027723953551363)
              ·
                refine ⟨911296558541585930327045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607531039027723953551363 911296558541585930327045)
                ·
                  refine ⟨170868104726547361936321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 911296558541585930327045 170868104726547361936321)
                  ·
                    refine ⟨128151078544910521452241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 170868104726547361936321 128151078544910521452241)
                    ·
                      refine ⟨96113308908682891089181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128151078544910521452241 96113308908682891089181)
                      ·
                        rfl

theorem cell23_187180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_187180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187180 prefixEnd_187180 := by exact prefixLift 187180
  have htrace : WordTrace (prefixWord ++ tailWord_187180) baseStart_187180 baseEnd_187180 := by
    simpa [prefixWord, tailWord_187180, baseEnd_187180] using wordTrace_append hprefix tailTrace_187180
  have hstable : (prefixWord ++ tailWord_187180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187180).length < 2 ^ (prefixWord ++ tailWord_187180).sum := by decide
  have hdescent : baseEnd_187180 < baseStart_187180 := by decide
  rcases family_descends (prefixWord ++ tailWord_187180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187216 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 7]
def baseStart_187216 : Nat := 118140960795 + 187216 * 2 ^ 59
def prefixEnd_187216 : Nat := 4983230072969 + 3 ^ 40 * 187216 * 2
def baseEnd_187216 : Nat := 32043931404081583413005

theorem tailTrace_187216 : CollatzResearch.WordTrace tailWord_187216 prefixEnd_187216 32043931404081583413005 := by
  unfold tailWord_187216
  simp only [CollatzResearch.WordTrace]
  refine ⟨3414164244877940396166751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4552218993170587194889001 3414164244877940396166751)
  ·
    refine ⟨5121246367316910594250127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3414164244877940396166751 5121246367316910594250127)
    ·
      refine ⟨7681869550975365891375191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5121246367316910594250127 7681869550975365891375191)
      ·
        refine ⟨11522804326463048837062787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7681869550975365891375191 11522804326463048837062787)
        ·
          refine ⟨17284206489694573255594181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11522804326463048837062787 17284206489694573255594181)
          ·
            refine ⟨3240788716817732485423909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17284206489694573255594181 3240788716817732485423909)
            ·
              refine ⟨607647884403324841016983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3240788716817732485423909 607647884403324841016983)
              ·
                refine ⟨911471826604987261525475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 607647884403324841016983 911471826604987261525475)
                ·
                  refine ⟨1367207739907480892288213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 911471826604987261525475 1367207739907480892288213)
                  ·
                    refine ⟨32043931404081583413005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1367207739907480892288213 32043931404081583413005)
                    ·
                      rfl

theorem cell23_187216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_187216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187216 prefixEnd_187216 := by exact prefixLift 187216
  have htrace : WordTrace (prefixWord ++ tailWord_187216) baseStart_187216 baseEnd_187216 := by
    simpa [prefixWord, tailWord_187216, baseEnd_187216] using wordTrace_append hprefix tailTrace_187216
  have hstable : (prefixWord ++ tailWord_187216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187216).length < 2 ^ (prefixWord ++ tailWord_187216).sum := by decide
  have hdescent : baseEnd_187216 < baseStart_187216 := by decide
  rcases family_descends (prefixWord ++ tailWord_187216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187263 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 3, 4]
def baseStart_187263 : Nat := 118140960795 + 187263 * 2 ^ 59
def prefixEnd_187263 : Nat := 4983230072969 + 3 ^ 40 * 187263 * 2
def baseEnd_187263 : Nat := 32051975934335355450433

theorem tailTrace_187263 : CollatzResearch.WordTrace tailWord_187263 prefixEnd_187263 32051975934335355450433 := by
  unfold tailWord_187263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6830042720585607819294443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4553361813723738546196295 6830042720585607819294443)
  ·
    refine ⟨10245064080878411728941665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6830042720585607819294443 10245064080878411728941665)
    ·
      refine ⟨7683798060658808796706249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10245064080878411728941665 7683798060658808796706249)
      ·
        refine ⟨5762848545494106597529687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7683798060658808796706249 5762848545494106597529687)
        ·
          refine ⟨8644272818241159896294531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5762848545494106597529687 8644272818241159896294531)
          ·
            refine ⟨12966409227361739844441797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8644272818241159896294531 12966409227361739844441797)
            ·
              refine ⟨2431201730130326220832837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12966409227361739844441797 2431201730130326220832837)
              ·
                refine ⟨455850324399436166406157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2431201730130326220832837 455850324399436166406157)
                ·
                  refine ⟨170943871649788562402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 455850324399436166406157 170943871649788562402309)
                  ·
                    refine ⟨32051975934335355450433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170943871649788562402309 32051975934335355450433)
                    ·
                      rfl

theorem cell23_187263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 4].length) (baseStart_187263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187263 prefixEnd_187263 := by exact prefixLift 187263
  have htrace : WordTrace (prefixWord ++ tailWord_187263) baseStart_187263 baseEnd_187263 := by
    simpa [prefixWord, tailWord_187263, baseEnd_187263] using wordTrace_append hprefix tailTrace_187263
  have hstable : (prefixWord ++ tailWord_187263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187263).length < 2 ^ (prefixWord ++ tailWord_187263).sum := by decide
  have hdescent : baseEnd_187263 < baseStart_187263 := by decide
  rcases family_descends (prefixWord ++ tailWord_187263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187276 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 10]
def baseStart_187276 : Nat := 118140960795 + 187276 * 2 ^ 59
def prefixEnd_187276 : Nat := 4983230072969 + 3 ^ 40 * 187276 * 2
def baseEnd_187276 : Nat := 10684733672390501720971

theorem tailTrace_187276 : CollatzResearch.WordTrace tailWord_187276 prefixEnd_187276 10684733672390501720971 := by
  unfold tailWord_187276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415258434769255519758841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4553677913025674026345121 3415258434769255519758841)
  ·
    refine ⟨2561443826076941639819131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3415258434769255519758841 2561443826076941639819131)
    ·
      refine ⟨3842165739115412459728697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2561443826076941639819131 3842165739115412459728697)
      ·
        refine ⟨2881624304336559344796523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3842165739115412459728697 2881624304336559344796523)
        ·
          refine ⟨4322436456504839017194785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2881624304336559344796523 4322436456504839017194785)
          ·
            refine ⟨3241827342378629262896089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4322436456504839017194785 3241827342378629262896089)
            ·
              refine ⟨2431370506783971947172067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3241827342378629262896089 2431370506783971947172067)
              ·
                refine ⟨3647055760175957920758101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2431370506783971947172067 3647055760175957920758101)
                ·
                  refine ⟨10684733672390501720971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3647055760175957920758101 10684733672390501720971)
                  ·
                    rfl

theorem cell23_187276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_187276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187276 prefixEnd_187276 := by exact prefixLift 187276
  have htrace : WordTrace (prefixWord ++ tailWord_187276) baseStart_187276 baseEnd_187276 := by
    simpa [prefixWord, tailWord_187276, baseEnd_187276] using wordTrace_append hprefix tailTrace_187276
  have hstable : (prefixWord ++ tailWord_187276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187276).length < 2 ^ (prefixWord ++ tailWord_187276).sum := by decide
  have hdescent : baseEnd_187276 < baseStart_187276 := by decide
  rcases family_descends (prefixWord ++ tailWord_187276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187318 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_187318 : Nat := 118140960795 + 187318 * 2 ^ 59
def prefixEnd_187318 : Nat := 4983230072969 + 3 ^ 40 * 187318 * 2
def baseEnd_187318 : Nat := 32061389746334450387849

theorem tailTrace_187318 : CollatzResearch.WordTrace tailWord_187318 prefixEnd_187318 32061389746334450387849 := by
  unfold tailWord_187318
  simp only [CollatzResearch.WordTrace]
  refine ⟨427003045961647013284163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4554699156924234808364405 427003045961647013284163)
  ·
    refine ⟨640504568942470519926245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 427003045961647013284163 640504568942470519926245)
    ·
      refine ⟨120094606676713222486171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 640504568942470519926245 120094606676713222486171)
      ·
        refine ⟨180141910015069833729257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120094606676713222486171 180141910015069833729257)
        ·
          refine ⟨135106432511302375296943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180141910015069833729257 135106432511302375296943)
          ·
            refine ⟨202659648766953562945415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135106432511302375296943 202659648766953562945415)
            ·
              refine ⟨303989473150430344418123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202659648766953562945415 303989473150430344418123)
              ·
                refine ⟨455984209725645516627185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 303989473150430344418123 455984209725645516627185)
                ·
                  refine ⟨341988157294234137470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 455984209725645516627185 341988157294234137470389)
                  ·
                    refine ⟨32061389746334450387849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 341988157294234137470389 32061389746334450387849)
                    ·
                      rfl

theorem cell23_187318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_187318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187318 prefixEnd_187318 := by exact prefixLift 187318
  have htrace : WordTrace (prefixWord ++ tailWord_187318) baseStart_187318 baseEnd_187318 := by
    simpa [prefixWord, tailWord_187318, baseEnd_187318] using wordTrace_append hprefix tailTrace_187318
  have hstable : (prefixWord ++ tailWord_187318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187318).length < 2 ^ (prefixWord ++ tailWord_187318).sum := by decide
  have hdescent : baseEnd_187318 < baseStart_187318 := by decide
  rcases family_descends (prefixWord ++ tailWord_187318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187320 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_187320 : Nat := 118140960795 + 187320 * 2 ^ 59
def prefixEnd_187320 : Nat := 4983230072969 + 3 ^ 40 * 187320 * 2
def baseEnd_187320 : Nat := 96185196200312343338537

theorem tailTrace_187320 : CollatzResearch.WordTrace tailWord_187320 prefixEnd_187320 96185196200312343338537 := by
  unfold tailWord_187320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416060840689553277059707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4554747787586071036079609 3416060840689553277059707)
  ·
    refine ⟨5124091261034329915589561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3416060840689553277059707 5124091261034329915589561)
    ·
      refine ⟨3843068445775747436692171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5124091261034329915589561 3843068445775747436692171)
      ·
        refine ⟨5764602668663621155038257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3843068445775747436692171 5764602668663621155038257)
        ·
          refine ⟨4323452001497715866278693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5764602668663621155038257 4323452001497715866278693)
          ·
            refine ⟨810647250280821724927255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4323452001497715866278693 810647250280821724927255)
            ·
              refine ⟨1215970875421232587390883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 810647250280821724927255 1215970875421232587390883)
              ·
                refine ⟨1823956313131848881086325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1215970875421232587390883 1823956313131848881086325)
                ·
                  refine ⟨170995904356110832601843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1823956313131848881086325 170995904356110832601843)
                  ·
                    refine ⟨256493856534166248902765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 170995904356110832601843 256493856534166248902765)
                    ·
                      refine ⟨96185196200312343338537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256493856534166248902765 96185196200312343338537)
                      ·
                        rfl

theorem cell23_187320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_187320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187320 prefixEnd_187320 := by exact prefixLift 187320
  have htrace : WordTrace (prefixWord ++ tailWord_187320) baseStart_187320 baseEnd_187320 := by
    simpa [prefixWord, tailWord_187320, baseEnd_187320] using wordTrace_append hprefix tailTrace_187320
  have hstable : (prefixWord ++ tailWord_187320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187320).length < 2 ^ (prefixWord ++ tailWord_187320).sum := by decide
  have hdescent : baseEnd_187320 < baseStart_187320 := by decide
  rcases family_descends (prefixWord ++ tailWord_187320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187340 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_187340 : Nat := 118140960795 + 187340 * 2 ^ 59
def prefixEnd_187340 : Nat := 4983230072969 + 3 ^ 40 * 187340 * 2
def baseEnd_187340 : Nat := 32065155271134088362815

theorem tailTrace_187340 : CollatzResearch.WordTrace tailWord_187340 prefixEnd_187340 32065155271134088362815 := by
  unfold tailWord_187340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3416425570653324984923737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4555234094204433313231649 3416425570653324984923737)
  ·
    refine ⟨2562319177989993738692803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3416425570653324984923737 2562319177989993738692803)
    ·
      refine ⟨3843478766984990608039205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562319177989993738692803 3843478766984990608039205)
      ·
        refine ⟨720652268809685739007351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3843478766984990608039205 720652268809685739007351)
        ·
          refine ⟨1080978403214528608511027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 720652268809685739007351 1080978403214528608511027)
          ·
            refine ⟨1621467604821792912766541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1080978403214528608511027 1621467604821792912766541)
            ·
              refine ⟨608050351808172342287453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1621467604821792912766541 608050351808172342287453)
              ·
                refine ⟨228018881928064628357795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608050351808172342287453 228018881928064628357795)
                ·
                  refine ⟨342028322892096942536693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228018881928064628357795 342028322892096942536693)
                  ·
                    refine ⟨32065155271134088362815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342028322892096942536693 32065155271134088362815)
                    ·
                      rfl

theorem cell23_187340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_187340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187340 prefixEnd_187340 := by exact prefixLift 187340
  have htrace : WordTrace (prefixWord ++ tailWord_187340) baseStart_187340 baseEnd_187340 := by
    simpa [prefixWord, tailWord_187340, baseEnd_187340] using wordTrace_append hprefix tailTrace_187340
  have hstable : (prefixWord ++ tailWord_187340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187340).length < 2 ^ (prefixWord ++ tailWord_187340).sum := by decide
  have hdescent : baseEnd_187340 < baseStart_187340 := by decide
  rcases family_descends (prefixWord ++ tailWord_187340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187354 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3]
def baseStart_187354 : Nat := 118140960795 + 187354 * 2 ^ 59
def prefixEnd_187354 : Nat := 4983230072969 + 3 ^ 40 * 187354 * 2
def baseEnd_187354 : Nat := 96202654542565210313381

theorem tailTrace_187354 : CollatzResearch.WordTrace tailWord_187354 prefixEnd_187354 96202654542565210313381 := by
  unfold tailWord_187354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708340440813982590214279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4555574508837286907238077 1708340440813982590214279)
  ·
    refine ⟨2562510661220973885321419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708340440813982590214279 2562510661220973885321419)
    ·
      refine ⟨3843765991831460827982129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2562510661220973885321419 3843765991831460827982129)
      ·
        refine ⟨2882824493873595620986597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3843765991831460827982129 2882824493873595620986597)
        ·
          refine ⟨540529592601299178934987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2882824493873595620986597 540529592601299178934987)
          ·
            refine ⟨810794388901948768402481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540529592601299178934987 810794388901948768402481)
            ·
              refine ⟨608095791676461576301861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 810794388901948768402481 608095791676461576301861)
              ·
                refine ⟨114017960939336545556599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 608095791676461576301861 114017960939336545556599)
                ·
                  refine ⟨171026941409004818334899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114017960939336545556599 171026941409004818334899)
                  ·
                    refine ⟨256540412113507227502349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171026941409004818334899 256540412113507227502349)
                    ·
                      refine ⟨96202654542565210313381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256540412113507227502349 96202654542565210313381)
                      ·
                        rfl

theorem cell23_187354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_187354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187354 prefixEnd_187354 := by exact prefixLift 187354
  have htrace : WordTrace (prefixWord ++ tailWord_187354) baseStart_187354 baseEnd_187354 := by
    simpa [prefixWord, tailWord_187354, baseEnd_187354] using wordTrace_append hprefix tailTrace_187354
  have hstable : (prefixWord ++ tailWord_187354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187354).length < 2 ^ (prefixWord ++ tailWord_187354).sum := by decide
  have hdescent : baseEnd_187354 < baseStart_187354 := by decide
  rcases family_descends (prefixWord ++ tailWord_187354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187370 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 6]
def baseStart_187370 : Nat := 118140960795 + 187370 * 2 ^ 59
def prefixEnd_187370 : Nat := 4983230072969 + 3 ^ 40 * 187370 * 2
def baseEnd_187370 : Nat := 32070290077679049237769

theorem tailTrace_187370 : CollatzResearch.WordTrace tailWord_187370 prefixEnd_187370 32070290077679049237769 := by
  unfold tailWord_187370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1708486332799491273359891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4555963554131976728959709 1708486332799491273359891)
  ·
    refine ⟨2562729499199236910039837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1708486332799491273359891 2562729499199236910039837)
    ·
      refine ⟨961023562199713841264939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2562729499199236910039837 961023562199713841264939)
      ·
        refine ⟨1441535343299570761897409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 961023562199713841264939 1441535343299570761897409)
        ·
          refine ⟨1081151507474678071423057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1441535343299570761897409 1081151507474678071423057)
          ·
            refine ⟨810863630606008553567293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1081151507474678071423057 810863630606008553567293)
            ·
              refine ⟨304073861477253207587735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 810863630606008553567293 304073861477253207587735)
              ·
                refine ⟨456110792215879811381603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304073861477253207587735 456110792215879811381603)
                ·
                  refine ⟨684166188323819717072405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456110792215879811381603 684166188323819717072405)
                  ·
                    refine ⟨32070290077679049237769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 684166188323819717072405 32070290077679049237769)
                    ·
                      rfl

theorem cell23_187370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_187370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187370 prefixEnd_187370 := by exact prefixLift 187370
  have htrace : WordTrace (prefixWord ++ tailWord_187370) baseStart_187370 baseEnd_187370 := by
    simpa [prefixWord, tailWord_187370, baseEnd_187370] using wordTrace_append hprefix tailTrace_187370
  have hstable : (prefixWord ++ tailWord_187370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187370).length < 2 ^ (prefixWord ++ tailWord_187370).sum := by decide
  have hdescent : baseEnd_187370 < baseStart_187370 := by decide
  rcases family_descends (prefixWord ++ tailWord_187370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187377 : List Nat := [1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_187377 : Nat := 118140960795 + 187377 * 2 ^ 59
def prefixEnd_187377 : Nat := 4983230072969 + 3 ^ 40 * 187377 * 2
def baseEnd_187377 : Nat := 96214464597618620325775

theorem tailTrace_187377 : CollatzResearch.WordTrace tailWord_187377 prefixEnd_187377 96214464597618620325775 := by
  unfold tailWord_187377
  simp only [CollatzResearch.WordTrace]
  refine ⟨6834200642172605288944385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4556133761448403525962923 6834200642172605288944385)
  ·
    refine ⟨5125650481629453966708289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6834200642172605288944385 5125650481629453966708289)
    ·
      refine ⟨3844237861222090475031217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5125650481629453966708289 3844237861222090475031217)
      ·
        refine ⟨2883178395916567856273413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3844237861222090475031217 2883178395916567856273413)
        ·
          refine ⟨540595949234356473051265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2883178395916567856273413 540595949234356473051265)
          ·
            refine ⟨405446961925767354788449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540595949234356473051265 405446961925767354788449)
            ·
              refine ⟨304085221444325516091337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405446961925767354788449 304085221444325516091337)
              ·
                refine ⟨228063916083244137068503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304085221444325516091337 228063916083244137068503)
                ·
                  refine ⟨342095874124866205602755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228063916083244137068503 342095874124866205602755)
                  ·
                    refine ⟨513143811187299308404133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342095874124866205602755 513143811187299308404133)
                    ·
                      refine ⟨96214464597618620325775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 513143811187299308404133 96214464597618620325775)
                      ·
                        rfl

theorem cell23_187377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_187377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187377 prefixEnd_187377 := by exact prefixLift 187377
  have htrace : WordTrace (prefixWord ++ tailWord_187377) baseStart_187377 baseEnd_187377 := by
    simpa [prefixWord, tailWord_187377, baseEnd_187377] using wordTrace_append hprefix tailTrace_187377
  have hstable : (prefixWord ++ tailWord_187377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187377).length < 2 ^ (prefixWord ++ tailWord_187377).sum := by decide
  have hdescent : baseEnd_187377 < baseStart_187377 := by decide
  rcases family_descends (prefixWord ++ tailWord_187377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187421 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_187421 : Nat := 118140960795 + 187421 * 2 ^ 59
def prefixEnd_187421 : Nat := 4983230072969 + 3 ^ 40 * 187421 * 2
def baseEnd_187421 : Nat := 32079019248805482725191

theorem tailTrace_187421 : CollatzResearch.WordTrace tailWord_187421 prefixEnd_187421 32079019248805482725191 := by
  unfold tailWord_187421
  simp only [CollatzResearch.WordTrace]
  refine ⟨6835805454013200803546117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557203636008800535697411 6835805454013200803546117)
  ·
    refine ⟨1281713522627475150664897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6835805454013200803546117 1281713522627475150664897)
    ·
      refine ⟨961285141970606362998673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1281713522627475150664897 961285141970606362998673)
      ·
        refine ⟨720963856477954772249005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 961285141970606362998673 720963856477954772249005)
        ·
          refine ⟨270361446179233039593377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 720963856477954772249005 270361446179233039593377)
          ·
            refine ⟨202771084634424779695033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270361446179233039593377 202771084634424779695033)
            ·
              refine ⟨152078313475818584771275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202771084634424779695033 152078313475818584771275)
              ·
                refine ⟨228117470213727877156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152078313475818584771275 228117470213727877156913)
                ·
                  refine ⟨171088102660295907867685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228117470213727877156913 171088102660295907867685)
                  ·
                    refine ⟨32079019248805482725191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171088102660295907867685 32079019248805482725191)
                    ·
                      rfl

theorem cell23_187421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_187421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187421 prefixEnd_187421 := by exact prefixLift 187421
  have htrace : WordTrace (prefixWord ++ tailWord_187421) baseStart_187421 baseEnd_187421 := by
    simpa [prefixWord, tailWord_187421, baseEnd_187421] using wordTrace_append hprefix tailTrace_187421
  have hstable : (prefixWord ++ tailWord_187421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187421).length < 2 ^ (prefixWord ++ tailWord_187421).sum := by decide
  have hdescent : baseEnd_187421 < baseStart_187421 := by decide
  rcases family_descends (prefixWord ++ tailWord_187421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187431 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_187431 : Nat := 118140960795 + 187431 * 2 ^ 59
def prefixEnd_187431 : Nat := 4983230072969 + 3 ^ 40 * 187431 * 2
def baseEnd_187431 : Nat := 96242192552961409050527

theorem tailTrace_187431 : CollatzResearch.WordTrace tailWord_187431 prefixEnd_187431 96242192552961409050527 := by
  unfold tailWord_187431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836170183976972511410147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557446789317981674273431 6836170183976972511410147)
  ·
    refine ⟨10254255275965458767115221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836170183976972511410147 10254255275965458767115221)
    ·
      refine ⟨240334108030440439854263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10254255275965458767115221 240334108030440439854263)
      ·
        refine ⟨360501162045660659781395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240334108030440439854263 360501162045660659781395)
        ·
          refine ⟨540751743068490989672093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360501162045660659781395 540751743068490989672093)
          ·
            refine ⟨202781903650684121127035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 540751743068490989672093 202781903650684121127035)
            ·
              refine ⟨304172855476026181690553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202781903650684121127035 304172855476026181690553)
              ·
                refine ⟨228129641607019636267915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304172855476026181690553 228129641607019636267915)
                ·
                  refine ⟨342194462410529454401873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228129641607019636267915 342194462410529454401873)
                  ·
                    refine ⟨256645846807897090801405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342194462410529454401873 256645846807897090801405)
                    ·
                      refine ⟨96242192552961409050527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256645846807897090801405 96242192552961409050527)
                      ·
                        rfl

theorem cell23_187431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_187431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187431 prefixEnd_187431 := by exact prefixLift 187431
  have htrace : WordTrace (prefixWord ++ tailWord_187431) baseStart_187431 baseEnd_187431 := by
    simpa [prefixWord, tailWord_187431, baseEnd_187431] using wordTrace_append hprefix tailTrace_187431
  have hstable : (prefixWord ++ tailWord_187431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187431).length < 2 ^ (prefixWord ++ tailWord_187431).sum := by decide
  have hdescent : baseEnd_187431 < baseStart_187431 := by decide
  rcases family_descends (prefixWord ++ tailWord_187431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187443 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 6]
def baseStart_187443 : Nat := 118140960795 + 187443 * 2 ^ 59
def prefixEnd_187443 : Nat := 4983230072969 + 3 ^ 40 * 187443 * 2
def baseEnd_187443 : Nat := 32082784773605120700157

theorem tailTrace_187443 : CollatzResearch.WordTrace tailWord_187443 prefixEnd_187443 32082784773605120700157 := by
  unfold tailWord_187443
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836607859933498560846983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4557738573288999040564655 6836607859933498560846983)
  ·
    refine ⟨10254911789900247841270475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836607859933498560846983 10254911789900247841270475)
    ·
      refine ⟨15382367684850371761905713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10254911789900247841270475 15382367684850371761905713)
      ·
        refine ⟨11536775763637778821429285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15382367684850371761905713 11536775763637778821429285)
        ·
          refine ⟨2163145455682083529017991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11536775763637778821429285 2163145455682083529017991)
          ·
            refine ⟨3244718183523125293526987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163145455682083529017991 3244718183523125293526987)
            ·
              refine ⟨4867077275284687940290481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244718183523125293526987 4867077275284687940290481)
              ·
                refine ⟨3650307956463515955217861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4867077275284687940290481 3650307956463515955217861)
                ·
                  refine ⟨684432741836909241603349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3650307956463515955217861 684432741836909241603349)
                  ·
                    refine ⟨32082784773605120700157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 684432741836909241603349 32082784773605120700157)
                    ·
                      rfl

theorem cell23_187443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_187443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187443 prefixEnd_187443 := by exact prefixLift 187443
  have htrace : WordTrace (prefixWord ++ tailWord_187443) baseStart_187443 baseEnd_187443 := by
    simpa [prefixWord, tailWord_187443, baseEnd_187443] using wordTrace_append hprefix tailTrace_187443
  have hstable : (prefixWord ++ tailWord_187443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187443).length < 2 ^ (prefixWord ++ tailWord_187443).sum := by decide
  have hdescent : baseEnd_187443 < baseStart_187443 := by decide
  rcases family_descends (prefixWord ++ tailWord_187443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187444 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_187444 : Nat := 118140960795 + 187444 * 2 ^ 59
def prefixEnd_187444 : Nat := 4983230072969 + 3 ^ 40 * 187444 * 2
def baseEnd_187444 : Nat := 96248867801469858187967

theorem tailTrace_187444 : CollatzResearch.WordTrace tailWord_187444 prefixEnd_187444 96248867801469858187967 := by
  unfold tailWord_187444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418322166464937865816693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4557762888619917154422257 3418322166464937865816693)
  ·
    refine ⟨320467703106087924920315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3418322166464937865816693 320467703106087924920315)
    ·
      refine ⟨480701554659131887380473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320467703106087924920315 480701554659131887380473)
      ·
        refine ⟨360526165994348915535355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 480701554659131887380473 360526165994348915535355)
        ·
          refine ⟨540789248991523373303033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360526165994348915535355 540789248991523373303033)
          ·
            refine ⟨405591936743642529977275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 540789248991523373303033 405591936743642529977275)
            ·
              refine ⟨608387905115463794965913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 405591936743642529977275 608387905115463794965913)
              ·
                refine ⟨456290928836597846224435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 608387905115463794965913 456290928836597846224435)
                ·
                  refine ⟨684436393254896769336653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456290928836597846224435 684436393254896769336653)
                  ·
                    refine ⟨256663647470586288501245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 684436393254896769336653 256663647470586288501245)
                    ·
                      refine ⟨96248867801469858187967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256663647470586288501245 96248867801469858187967)
                      ·
                        rfl

theorem cell23_187444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_187444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187444 prefixEnd_187444 := by exact prefixLift 187444
  have htrace : WordTrace (prefixWord ++ tailWord_187444) baseStart_187444 baseEnd_187444 := by
    simpa [prefixWord, tailWord_187444, baseEnd_187444] using wordTrace_append hprefix tailTrace_187444
  have hstable : (prefixWord ++ tailWord_187444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187444).length < 2 ^ (prefixWord ++ tailWord_187444).sum := by decide
  have hdescent : baseEnd_187444 < baseStart_187444 := by decide
  rcases family_descends (prefixWord ++ tailWord_187444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187462 : List Nat := [6, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_187462 : Nat := 118140960795 + 187462 * 2 ^ 59
def prefixEnd_187462 : Nat := 4983230072969 + 3 ^ 40 * 187462 * 2
def baseEnd_187462 : Nat := 96258110453250787762885

theorem tailTrace_187462 : CollatzResearch.WordTrace tailWord_187462 prefixEnd_187462 96258110453250787762885 := by
  unfold tailWord_187462
  simp only [CollatzResearch.WordTrace]
  refine ⟨213665651464520775180895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4558200564576443203859093 213665651464520775180895)
  ·
    refine ⟨320498477196781162771343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213665651464520775180895 320498477196781162771343)
    ·
      refine ⟨480747715795171744157015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320498477196781162771343 480747715795171744157015)
      ·
        refine ⟨721121573692757616235523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480747715795171744157015 721121573692757616235523)
        ·
          refine ⟨1081682360539136424353285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721121573692757616235523 1081682360539136424353285)
          ·
            refine ⟨202815442601088079566241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1081682360539136424353285 202815442601088079566241)
            ·
              refine ⟨152111581950816059674681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202815442601088079566241 152111581950816059674681)
              ·
                refine ⟨114083686463112044756011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152111581950816059674681 114083686463112044756011)
                ·
                  refine ⟨171125529694668067134017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114083686463112044756011 171125529694668067134017)
                  ·
                    refine ⟨128344147271001050350513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171125529694668067134017 128344147271001050350513)
                    ·
                      refine ⟨96258110453250787762885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128344147271001050350513 96258110453250787762885)
                      ·
                        rfl

theorem cell23_187462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_187462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187462 prefixEnd_187462 := by exact prefixLift 187462
  have htrace : WordTrace (prefixWord ++ tailWord_187462) baseStart_187462 baseEnd_187462 := by
    simpa [prefixWord, tailWord_187462, baseEnd_187462] using wordTrace_append hprefix tailTrace_187462
  have hstable : (prefixWord ++ tailWord_187462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187462).length < 2 ^ (prefixWord ++ tailWord_187462).sum := by decide
  have hdescent : baseEnd_187462 < baseStart_187462 := by decide
  rcases family_descends (prefixWord ++ tailWord_187462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187470 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_187470 : Nat := 118140960795 + 187470 * 2 ^ 59
def prefixEnd_187470 : Nat := 4983230072969 + 3 ^ 40 * 187470 * 2
def baseEnd_187470 : Nat := 96262218298486756462847

theorem tailTrace_187470 : CollatzResearch.WordTrace tailWord_187470 prefixEnd_187470 96262218298486756462847 := by
  unfold tailWord_187470
  simp only [CollatzResearch.WordTrace]
  refine ⟨854699078854460271509983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4558395087223788114719909 854699078854460271509983)
  ·
    refine ⟨1282048618281690407264975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854699078854460271509983 1282048618281690407264975)
    ·
      refine ⟨1923072927422535610897463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282048618281690407264975 1923072927422535610897463)
      ·
        refine ⟨2884609391133803416346195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1923072927422535610897463 2884609391133803416346195)
        ·
          refine ⟨4326914086700705124519293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884609391133803416346195 4326914086700705124519293)
          ·
            refine ⟨1622592782512764421694735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4326914086700705124519293 1622592782512764421694735)
            ·
              refine ⟨2433889173769146632542103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622592782512764421694735 2433889173769146632542103)
              ·
                refine ⟨3650833760653719948813155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433889173769146632542103 3650833760653719948813155)
                ·
                  refine ⟨5476250640980579923219733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3650833760653719948813155 5476250640980579923219733)
                  ·
                    refine ⟨256699248795964683900925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5476250640980579923219733 256699248795964683900925)
                    ·
                      refine ⟨96262218298486756462847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256699248795964683900925 96262218298486756462847)
                      ·
                        rfl

theorem cell23_187470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_187470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187470 prefixEnd_187470 := by exact prefixLift 187470
  have htrace : WordTrace (prefixWord ++ tailWord_187470) baseStart_187470 baseEnd_187470 := by
    simpa [prefixWord, tailWord_187470, baseEnd_187470] using wordTrace_append hprefix tailTrace_187470
  have hstable : (prefixWord ++ tailWord_187470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187470).length < 2 ^ (prefixWord ++ tailWord_187470).sum := by decide
  have hdescent : baseEnd_187470 < baseStart_187470 := by decide
  rcases family_descends (prefixWord ++ tailWord_187470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187480 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_187480 : Nat := 118140960795 + 187480 * 2 ^ 59
def prefixEnd_187480 : Nat := 4983230072969 + 3 ^ 40 * 187480 * 2
def baseEnd_187480 : Nat := 96267353105031717337801

theorem tailTrace_187480 : CollatzResearch.WordTrace tailWord_187480 prefixEnd_187480 96267353105031717337801 := by
  unfold tailWord_187480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418978680399726939971947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4558638240532969253295929 3418978680399726939971947)
  ·
    refine ⟨5128468020599590409957921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418978680399726939971947 5128468020599590409957921)
    ·
      refine ⟨3846351015449692807468441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5128468020599590409957921 3846351015449692807468441)
      ·
        refine ⟨2884763261587269605601331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3846351015449692807468441 2884763261587269605601331)
        ·
          refine ⟨4327144892380904408401997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884763261587269605601331 4327144892380904408401997)
          ·
            refine ⟨1622679334642839153150749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4327144892380904408401997 1622679334642839153150749)
            ·
              refine ⟨608504750491064682431531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1622679334642839153150749 608504750491064682431531)
              ·
                refine ⟨912757125736597023647297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 608504750491064682431531 912757125736597023647297)
                ·
                  refine ⟨684567844302447767735473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 912757125736597023647297 684567844302447767735473)
                  ·
                    refine ⟨513425883226835825801605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 684567844302447767735473 513425883226835825801605)
                    ·
                      refine ⟨96267353105031717337801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 513425883226835825801605 96267353105031717337801)
                      ·
                        rfl

theorem cell23_187480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_187480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187480 prefixEnd_187480 := by exact prefixLift 187480
  have htrace : WordTrace (prefixWord ++ tailWord_187480) baseStart_187480 baseEnd_187480 := by
    simpa [prefixWord, tailWord_187480, baseEnd_187480] using wordTrace_append hprefix tailTrace_187480
  have hstable : (prefixWord ++ tailWord_187480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187480).length < 2 ^ (prefixWord ++ tailWord_187480).sum := by decide
  have hdescent : baseEnd_187480 < baseStart_187480 := by decide
  rcases family_descends (prefixWord ++ tailWord_187480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187484 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_187484 : Nat := 118140960795 + 187484 * 2 ^ 59
def prefixEnd_187484 : Nat := 4983230072969 + 3 ^ 40 * 187484 * 2
def baseEnd_187484 : Nat := 96269407027649701687783

theorem tailTrace_187484 : CollatzResearch.WordTrace tailWord_187484 prefixEnd_187484 96269407027649701687783 := by
  unfold tailWord_187484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419051626392481281544753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4558735501856641708726337 3419051626392481281544753)
  ·
    refine ⟨2564288719794360961158565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3419051626392481281544753 2564288719794360961158565)
    ·
      refine ⟨480804134961442680217231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2564288719794360961158565 480804134961442680217231)
      ·
        refine ⟨721206202442164020325847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480804134961442680217231 721206202442164020325847)
        ·
          refine ⟨1081809303663246030488771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721206202442164020325847 1081809303663246030488771)
          ·
            refine ⟨1622713955494869045733157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1081809303663246030488771 1622713955494869045733157)
            ·
              refine ⟨304258866655287946074967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1622713955494869045733157 304258866655287946074967)
              ·
                refine ⟨456388299982931919112451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304258866655287946074967 456388299982931919112451)
                ·
                  refine ⟨684582449974397878668677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456388299982931919112451 684582449974397878668677)
                  ·
                    refine ⟨128359209370199602250377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 684582449974397878668677 128359209370199602250377)
                    ·
                      refine ⟨96269407027649701687783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128359209370199602250377 96269407027649701687783)
                      ·
                        rfl

theorem cell23_187484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_187484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187484 prefixEnd_187484 := by exact prefixLift 187484
  have htrace : WordTrace (prefixWord ++ tailWord_187484) baseStart_187484 baseEnd_187484 := by
    simpa [prefixWord, tailWord_187484, baseEnd_187484] using wordTrace_append hprefix tailTrace_187484
  have hstable : (prefixWord ++ tailWord_187484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187484).length < 2 ^ (prefixWord ++ tailWord_187484).sum := by decide
  have hdescent : baseEnd_187484 < baseStart_187484 := by decide
  rcases family_descends (prefixWord ++ tailWord_187484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187500 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_187500 : Nat := 118140960795 + 187500 * 2 ^ 59
def prefixEnd_187500 : Nat := 4983230072969 + 3 ^ 40 * 187500 * 2
def baseEnd_187500 : Nat := 96277622718121639087709

theorem tailTrace_187500 : CollatzResearch.WordTrace tailWord_187500 prefixEnd_187500 96277622718121639087709 := by
  unfold tailWord_187500
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419343410363498647835977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4559124547151331530447969 3419343410363498647835977)
  ·
    refine ⟨2564507557772623985876983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3419343410363498647835977 2564507557772623985876983)
    ·
      refine ⟨3846761336658935978815475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2564507557772623985876983 3846761336658935978815475)
      ·
        refine ⟨5770142004988403968223213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3846761336658935978815475 5770142004988403968223213)
        ·
          refine ⟨2163803251870651488083705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5770142004988403968223213 2163803251870651488083705)
          ·
            refine ⟨1622852438902988616062779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2163803251870651488083705 1622852438902988616062779)
            ·
              refine ⟨2434278658354482924094169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1622852438902988616062779 2434278658354482924094169)
              ·
                refine ⟨1825708993765862193070627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434278658354482924094169 1825708993765862193070627)
                ·
                  refine ⟨2738563490648793289605941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825708993765862193070627 2738563490648793289605941)
                  ·
                    refine ⟨256740327248324370900557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2738563490648793289605941 256740327248324370900557)
                    ·
                      refine ⟨96277622718121639087709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256740327248324370900557 96277622718121639087709)
                      ·
                        rfl

theorem cell23_187500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_187500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187500 prefixEnd_187500 := by exact prefixLift 187500
  have htrace : WordTrace (prefixWord ++ tailWord_187500) baseStart_187500 baseEnd_187500 := by
    simpa [prefixWord, tailWord_187500, baseEnd_187500] using wordTrace_append hprefix tailTrace_187500
  have hstable : (prefixWord ++ tailWord_187500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187500).length < 2 ^ (prefixWord ++ tailWord_187500).sum := by decide
  have hdescent : baseEnd_187500 < baseStart_187500 := by decide
  rcases family_descends (prefixWord ++ tailWord_187500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187520 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 2, 5]
def baseStart_187520 : Nat := 118140960795 + 187520 * 2 ^ 59
def prefixEnd_187520 : Nat := 4983230072969 + 3 ^ 40 * 187520 * 2
def baseEnd_187520 : Nat := 32095964110403853612539

theorem tailTrace_187520 : CollatzResearch.WordTrace tailWord_187520 prefixEnd_187520 32095964110403853612539 := by
  unfold tailWord_187520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3419708140327270355700007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4559610853769693807600009 3419708140327270355700007)
  ·
    refine ⟨5129562210490905533550011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3419708140327270355700007 5129562210490905533550011)
    ·
      refine ⟨7694343315736358300325017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5129562210490905533550011 7694343315736358300325017)
      ·
        refine ⟨5770757486802268725243763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694343315736358300325017 5770757486802268725243763)
        ·
          refine ⟨8656136230203403087865645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770757486802268725243763 8656136230203403087865645)
          ·
            refine ⟨3246051086326276157949617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8656136230203403087865645 3246051086326276157949617)
            ·
              refine ⟨2434538314744707118462213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246051086326276157949617 2434538314744707118462213)
              ·
                refine ⟨456475934014632584711665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2434538314744707118462213 456475934014632584711665)
                ·
                  refine ⟨342356950510974438533749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 456475934014632584711665 342356950510974438533749)
                  ·
                    refine ⟨32095964110403853612539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342356950510974438533749 32095964110403853612539)
                    ·
                      rfl

theorem cell23_187520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_187520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187520 prefixEnd_187520 := by exact prefixLift 187520
  have htrace : WordTrace (prefixWord ++ tailWord_187520) baseStart_187520 baseEnd_187520 := by
    simpa [prefixWord, tailWord_187520, baseEnd_187520] using wordTrace_append hprefix tailTrace_187520
  have hstable : (prefixWord ++ tailWord_187520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187520).length < 2 ^ (prefixWord ++ tailWord_187520).sum := by decide
  have hdescent : baseEnd_187520 < baseStart_187520 := by decide
  rcases family_descends (prefixWord ++ tailWord_187520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187530 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_187530 : Nat := 118140960795 + 187530 * 2 ^ 59
def prefixEnd_187530 : Nat := 4983230072969 + 3 ^ 40 * 187530 * 2
def baseEnd_187530 : Nat := 96293027137756521712571

theorem tailTrace_187530 : CollatzResearch.WordTrace tailWord_187530 prefixEnd_187530 96293027137756521712571 := by
  unfold tailWord_187530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709945252654578104816011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4559854007078874946176029 1709945252654578104816011)
  ·
    refine ⟨2564917878981867157224017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1709945252654578104816011 2564917878981867157224017)
    ·
      refine ⟨1923688409236400367918013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2564917878981867157224017 1923688409236400367918013)
      ·
        refine ⟨721383153463650137969255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1923688409236400367918013 721383153463650137969255)
        ·
          refine ⟨1082074730195475206953883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 721383153463650137969255 1082074730195475206953883)
          ·
            refine ⟨1623112095293212810430825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1082074730195475206953883 1623112095293212810430825)
            ·
              refine ⟨1217334071469909607823119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1623112095293212810430825 1217334071469909607823119)
              ·
                refine ⟨1826001107204864411734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217334071469909607823119 1826001107204864411734679)
                ·
                  refine ⟨2739001660807296617602019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826001107204864411734679 2739001660807296617602019)
                  ·
                    refine ⟨4108502491210944926403029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2739001660807296617602019 4108502491210944926403029)
                    ·
                      refine ⟨96293027137756521712571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4108502491210944926403029 96293027137756521712571)
                      ·
                        rfl

theorem cell23_187530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_187530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187530 prefixEnd_187530 := by exact prefixLift 187530
  have htrace : WordTrace (prefixWord ++ tailWord_187530) baseStart_187530 baseEnd_187530 := by
    simpa [prefixWord, tailWord_187530, baseEnd_187530] using wordTrace_append hprefix tailTrace_187530
  have hstable : (prefixWord ++ tailWord_187530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187530).length < 2 ^ (prefixWord ++ tailWord_187530).sum := by decide
  have hdescent : baseEnd_187530 < baseStart_187530 := by decide
  rcases family_descends (prefixWord ++ tailWord_187530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187577 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_187577 : Nat := 118140960795 + 187577 * 2 ^ 59
def prefixEnd_187577 : Nat := 4983230072969 + 3 ^ 40 * 187577 * 2
def baseEnd_187577 : Nat := 96317160728517837824855

theorem tailTrace_187577 : CollatzResearch.WordTrace tailWord_187577 prefixEnd_187577 96317160728517837824855 := by
  unfold tailWord_187577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6841495241448039446224985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4560996827632026297483323 6841495241448039446224985)
  ·
    refine ⟨5131121431086029584668739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6841495241448039446224985 5131121431086029584668739)
    ·
      refine ⟨7696682146629044377003109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5131121431086029584668739 7696682146629044377003109)
      ·
        refine ⟨1443127902492945820688083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7696682146629044377003109 1443127902492945820688083)
        ·
          refine ⟨2164691853739418731032125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1443127902492945820688083 2164691853739418731032125)
          ·
            refine ⟨811759445152282024137047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2164691853739418731032125 811759445152282024137047)
            ·
              refine ⟨1217639167728423036205571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811759445152282024137047 1217639167728423036205571)
              ·
                refine ⟨1826458751592634554308357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217639167728423036205571 1826458751592634554308357)
                ·
                  refine ⟨342461015923618978932817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826458751592634554308357 342461015923618978932817)
                  ·
                    refine ⟨256845761942714234199613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 342461015923618978932817 256845761942714234199613)
                    ·
                      refine ⟨96317160728517837824855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256845761942714234199613 96317160728517837824855)
                      ·
                        rfl

theorem cell23_187577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_187577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187577 prefixEnd_187577 := by exact prefixLift 187577
  have htrace : WordTrace (prefixWord ++ tailWord_187577) baseStart_187577 baseEnd_187577 := by
    simpa [prefixWord, tailWord_187577, baseEnd_187577] using wordTrace_append hprefix tailTrace_187577
  have hstable : (prefixWord ++ tailWord_187577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187577).length < 2 ^ (prefixWord ++ tailWord_187577).sum := by decide
  have hdescent : baseEnd_187577 < baseStart_187577 := by decide
  rcases family_descends (prefixWord ++ tailWord_187577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187641 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 1, 1, 3]
def baseStart_187641 : Nat := 118140960795 + 187641 * 2 ^ 59
def prefixEnd_187641 : Nat := 4983230072969 + 3 ^ 40 * 187641 * 2
def baseEnd_187641 : Nat := 96350023490405587424561

theorem tailTrace_187641 : CollatzResearch.WordTrace tailWord_187641 prefixEnd_187641 96350023490405587424561 := by
  unfold tailWord_187641
  simp only [CollatzResearch.WordTrace]
  refine ⟨6843829513216178376554777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562553008810785584369851 6843829513216178376554777)
  ·
    refine ⟨5132872134912133782416083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6843829513216178376554777 5132872134912133782416083)
    ·
      refine ⟨7699308202368200673624125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132872134912133782416083 7699308202368200673624125)
      ·
        refine ⟨2887240575888075252609047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7699308202368200673624125 2887240575888075252609047)
        ·
          refine ⟨4330860863832112878913571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887240575888075252609047 4330860863832112878913571)
          ·
            refine ⟨6496291295748169318370357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4330860863832112878913571 6496291295748169318370357)
            ·
              refine ⟨609027308976390873597221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6496291295748169318370357 609027308976390873597221)
              ·
                refine ⟨114192620433073288799479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609027308976390873597221 114192620433073288799479)
                ·
                  refine ⟨171288930649609933199219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114192620433073288799479 171288930649609933199219)
                  ·
                    refine ⟨256933395974414899798829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171288930649609933199219 256933395974414899798829)
                    ·
                      refine ⟨96350023490405587424561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 256933395974414899798829 96350023490405587424561)
                      ·
                        rfl

theorem cell23_187641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_187641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187641 prefixEnd_187641 := by exact prefixLift 187641
  have htrace : WordTrace (prefixWord ++ tailWord_187641) baseStart_187641 baseEnd_187641 := by
    simpa [prefixWord, tailWord_187641, baseEnd_187641] using wordTrace_append hprefix tailTrace_187641
  have hstable : (prefixWord ++ tailWord_187641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187641).length < 2 ^ (prefixWord ++ tailWord_187641).sum := by decide
  have hdescent : baseEnd_187641 < baseStart_187641 := by decide
  rcases family_descends (prefixWord ++ tailWord_187641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187647 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_187647 : Nat := 118140960795 + 187647 * 2 ^ 59
def prefixEnd_187647 : Nat := 4983230072969 + 3 ^ 40 * 187647 * 2
def baseEnd_187647 : Nat := 96353104374332563949533

theorem tailTrace_187647 : CollatzResearch.WordTrace tailWord_187647 prefixEnd_187647 96353104374332563949533 := by
  unfold tailWord_187647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844048351194441401273195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562698900796294267515463 6844048351194441401273195)
  ·
    refine ⟨10266072526791662101909793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6844048351194441401273195 10266072526791662101909793)
    ·
      refine ⟨7699554395093746576432345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266072526791662101909793 7699554395093746576432345)
      ·
        refine ⟨5774665796320309932324259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7699554395093746576432345 5774665796320309932324259)
        ·
          refine ⟨8661998694480464898486389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774665796320309932324259 8661998694480464898486389)
          ·
            refine ⟨812062377607543584233099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8661998694480464898486389 812062377607543584233099)
            ·
              refine ⟨1218093566411315376349649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812062377607543584233099 1218093566411315376349649)
              ·
                refine ⟨913570174808486532262237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1218093566411315376349649 913570174808486532262237)
                ·
                  refine ⟨342588815553182449598339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 913570174808486532262237 342588815553182449598339)
                  ·
                    refine ⟨513883223329773674397509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 342588815553182449598339 513883223329773674397509)
                    ·
                      refine ⟨96353104374332563949533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 513883223329773674397509 96353104374332563949533)
                      ·
                        rfl

theorem cell23_187647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_187647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187647 prefixEnd_187647 := by exact prefixLift 187647
  have htrace : WordTrace (prefixWord ++ tailWord_187647) baseStart_187647 baseEnd_187647 := by
    simpa [prefixWord, tailWord_187647, baseEnd_187647] using wordTrace_append hprefix tailTrace_187647
  have hstable : (prefixWord ++ tailWord_187647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187647).length < 2 ^ (prefixWord ++ tailWord_187647).sum := by decide
  have hdescent : baseEnd_187647 < baseStart_187647 := by decide
  rcases family_descends (prefixWord ++ tailWord_187647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187657 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_187657 : Nat := 118140960795 + 187657 * 2 ^ 59
def prefixEnd_187657 : Nat := 4983230072969 + 3 ^ 40 * 187657 * 2
def baseEnd_187657 : Nat := 32119413060292508274829

theorem tailTrace_187657 : CollatzResearch.WordTrace tailWord_187657 prefixEnd_187657 32119413060292508274829 := by
  unfold tailWord_187657
  simp only [CollatzResearch.WordTrace]
  refine ⟨6844413081158213109137225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4562942054105475406091483 6844413081158213109137225)
  ·
    refine ⟨5133309810868659831852919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6844413081158213109137225 5133309810868659831852919)
    ·
      refine ⟨7699964716302989747779379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5133309810868659831852919 7699964716302989747779379)
      ·
        refine ⟨11549947074454484621669069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7699964716302989747779379 11549947074454484621669069)
        ·
          refine ⟨4331230152920431733125901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11549947074454484621669069 4331230152920431733125901)
          ·
            refine ⟨1624211307345161899922213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4331230152920431733125901 1624211307345161899922213)
            ·
              refine ⟨304539620127217856235415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1624211307345161899922213 304539620127217856235415)
              ·
                refine ⟨456809430190826784353123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304539620127217856235415 456809430190826784353123)
                ·
                  refine ⟨685214145286240176529685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456809430190826784353123 685214145286240176529685)
                  ·
                    refine ⟨32119413060292508274829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 685214145286240176529685 32119413060292508274829)
                    ·
                      rfl

theorem cell23_187657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_187657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187657 prefixEnd_187657 := by exact prefixLift 187657
  have htrace : WordTrace (prefixWord ++ tailWord_187657) baseStart_187657 baseEnd_187657 := by
    simpa [prefixWord, tailWord_187657, baseEnd_187657] using wordTrace_append hprefix tailTrace_187657
  have hstable : (prefixWord ++ tailWord_187657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187657).length < 2 ^ (prefixWord ++ tailWord_187657).sum := by decide
  have hdescent : baseEnd_187657 < baseStart_187657 := by decide
  rcases family_descends (prefixWord ++ tailWord_187657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187678 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_187678 : Nat := 118140960795 + 187678 * 2 ^ 59
def prefixEnd_187678 : Nat := 4983230072969 + 3 ^ 40 * 187678 * 2
def baseEnd_187678 : Nat := 32123007424873980887297

theorem tailTrace_187678 : CollatzResearch.WordTrace tailWord_187678 prefixEnd_187678 32123007424873980887297 := by
  unfold tailWord_187678
  simp only [CollatzResearch.WordTrace]
  refine ⟨855647376760266711956461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4563452676054755797101125 855647376760266711956461)
  ·
    refine ⟨320867766285100016983673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 855647376760266711956461 320867766285100016983673)
    ·
      refine ⟨240650824713825012737755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320867766285100016983673 240650824713825012737755)
      ·
        refine ⟨360976237070737519106633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240650824713825012737755 360976237070737519106633)
        ·
          refine ⟨270732177803053139329975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360976237070737519106633 270732177803053139329975)
          ·
            refine ⟨406098266704579708994963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270732177803053139329975 406098266704579708994963)
            ·
              refine ⟨609147400056869563492445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406098266704579708994963 609147400056869563492445)
              ·
                refine ⟨228430275021326086309667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 609147400056869563492445 228430275021326086309667)
                ·
                  refine ⟨342645412531989129464501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228430275021326086309667 342645412531989129464501)
                  ·
                    refine ⟨32123007424873980887297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 342645412531989129464501 32123007424873980887297)
                    ·
                      rfl

theorem cell23_187678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_187678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187678 prefixEnd_187678 := by exact prefixLift 187678
  have htrace : WordTrace (prefixWord ++ tailWord_187678) baseStart_187678 baseEnd_187678 := by
    simpa [prefixWord, tailWord_187678, baseEnd_187678] using wordTrace_append hprefix tailTrace_187678
  have hstable : (prefixWord ++ tailWord_187678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187678).length < 2 ^ (prefixWord ++ tailWord_187678).sum := by decide
  have hdescent : baseEnd_187678 < baseStart_187678 := by decide
  rcases family_descends (prefixWord ++ tailWord_187678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187698 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_187698 : Nat := 118140960795 + 187698 * 2 ^ 59
def prefixEnd_187698 : Nat := 4983230072969 + 3 ^ 40 * 187698 * 2
def baseEnd_187698 : Nat := 96379291887711864411799

theorem tailTrace_187698 : CollatzResearch.WordTrace tailWord_187698 prefixEnd_187698 96379291887711864411799 := by
  unfold tailWord_187698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1711477118502419277844937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4563938982673118074253165 1711477118502419277844937)
  ·
    refine ⟨1283607838876814458383703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1711477118502419277844937 1283607838876814458383703)
    ·
      refine ⟨1925411758315221687575555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1283607838876814458383703 1925411758315221687575555)
      ·
        refine ⟨2888117637472832531363333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925411758315221687575555 2888117637472832531363333)
        ·
          refine ⟨541522057026156099630625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2888117637472832531363333 541522057026156099630625)
          ·
            refine ⟨406141542769617074722969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541522057026156099630625 406141542769617074722969)
            ·
              refine ⟨304606157077212806042227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406141542769617074722969 304606157077212806042227)
              ·
                refine ⟨456909235615819209063341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304606157077212806042227 456909235615819209063341)
                ·
                  refine ⟨171340963355932203398753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 456909235615819209063341 171340963355932203398753)
                  ·
                    refine ⟨128505722516949152549065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171340963355932203398753 128505722516949152549065)
                    ·
                      refine ⟨96379291887711864411799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128505722516949152549065 96379291887711864411799)
                      ·
                        rfl

theorem cell23_187698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_187698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187698 prefixEnd_187698 := by exact prefixLift 187698
  have htrace : WordTrace (prefixWord ++ tailWord_187698) baseStart_187698 baseEnd_187698 := by
    simpa [prefixWord, tailWord_187698, baseEnd_187698] using wordTrace_append hprefix tailTrace_187698
  have hstable : (prefixWord ++ tailWord_187698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187698).length < 2 ^ (prefixWord ++ tailWord_187698).sum := by decide
  have hdescent : baseEnd_187698 < baseStart_187698 := by decide
  rcases family_descends (prefixWord ++ tailWord_187698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187767 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_187767 : Nat := 118140960795 + 187767 * 2 ^ 59
def prefixEnd_187767 : Nat := 4983230072969 + 3 ^ 40 * 187767 * 2
def baseEnd_187767 : Nat := 96414722052872094448981

theorem tailTrace_187767 : CollatzResearch.WordTrace tailWord_187767 prefixEnd_187767 96414722052872094448981 := by
  unfold tailWord_187767
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848425110759701895641555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4565616740506467930427703 6848425110759701895641555)
  ·
    refine ⟨10272637666139552843462333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6848425110759701895641555 10272637666139552843462333)
    ·
      refine ⟨3852239124802332316298375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10272637666139552843462333 3852239124802332316298375)
      ·
        refine ⟨5778358687203498474447563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3852239124802332316298375 5778358687203498474447563)
        ·
          refine ⟨8667538030805247711671345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5778358687203498474447563 8667538030805247711671345)
          ·
            refine ⟨6500653523103935783753509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8667538030805247711671345 6500653523103935783753509)
            ·
              refine ⟨1218872535581987959453783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6500653523103935783753509 1218872535581987959453783)
              ·
                refine ⟨1828308803372981939180675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218872535581987959453783 1828308803372981939180675)
                ·
                  refine ⟨2742463205059472908771013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828308803372981939180675 2742463205059472908771013)
                  ·
                    refine ⟨514211850948651170394565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2742463205059472908771013 514211850948651170394565)
                    ·
                      refine ⟨96414722052872094448981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 514211850948651170394565 96414722052872094448981)
                      ·
                        rfl

theorem cell23_187767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_187767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187767 prefixEnd_187767 := by exact prefixLift 187767
  have htrace : WordTrace (prefixWord ++ tailWord_187767) baseStart_187767 baseEnd_187767 := by
    simpa [prefixWord, tailWord_187767, baseEnd_187767] using wordTrace_append hprefix tailTrace_187767
  have hstable : (prefixWord ++ tailWord_187767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187767).length < 2 ^ (prefixWord ++ tailWord_187767).sum := by decide
  have hdescent : baseEnd_187767 < baseStart_187767 := by decide
  rcases family_descends (prefixWord ++ tailWord_187767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187805 : List Nat := [1, 4, 2, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_187805 : Nat := 118140960795 + 187805 * 2 ^ 59
def prefixEnd_187805 : Nat := 4983230072969 + 3 ^ 40 * 187805 * 2
def baseEnd_187805 : Nat := 96434234317742945773807

theorem tailTrace_187805 : CollatzResearch.WordTrace tailWord_187805 prefixEnd_187805 96434234317742945773807 := by
  unfold tailWord_187805
  simp only [CollatzResearch.WordTrace]
  refine ⟨6849811084622034385524869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4566540723081356257016579 6849811084622034385524869)
  ·
    refine ⟨1284339578366631447285913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6849811084622034385524869 1284339578366631447285913)
    ·
      refine ⟨963254683774973585464435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1284339578366631447285913 963254683774973585464435)
      ·
        refine ⟨1444882025662460378196653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 963254683774973585464435 1444882025662460378196653)
        ·
          refine ⟨541830759623422641823745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1444882025662460378196653 541830759623422641823745)
          ·
            refine ⟨406373069717566981367809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541830759623422641823745 406373069717566981367809)
            ·
              refine ⟨304779802288175236025857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406373069717566981367809 304779802288175236025857)
              ·
                refine ⟨228584851716131427019393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304779802288175236025857 228584851716131427019393)
                ·
                  refine ⟨171438638787098570264545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228584851716131427019393 171438638787098570264545)
                  ·
                    refine ⟨128578979090323927698409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171438638787098570264545 128578979090323927698409)
                    ·
                      refine ⟨96434234317742945773807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128578979090323927698409 96434234317742945773807)
                      ·
                        rfl

theorem cell23_187805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_187805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187805 prefixEnd_187805 := by exact prefixLift 187805
  have htrace : WordTrace (prefixWord ++ tailWord_187805) baseStart_187805 baseEnd_187805 := by
    simpa [prefixWord, tailWord_187805, baseEnd_187805] using wordTrace_append hprefix tailTrace_187805
  have hstable : (prefixWord ++ tailWord_187805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187805).length < 2 ^ (prefixWord ++ tailWord_187805).sum := by decide
  have hdescent : baseEnd_187805 < baseStart_187805 := by decide
  rcases family_descends (prefixWord ++ tailWord_187805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187821 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_187821 : Nat := 118140960795 + 187821 * 2 ^ 59
def prefixEnd_187821 : Nat := 4983230072969 + 3 ^ 40 * 187821 * 2
def baseEnd_187821 : Nat := 96442450008214883173733

theorem tailTrace_187821 : CollatzResearch.WordTrace tailWord_187821 prefixEnd_187821 96442450008214883173733 := by
  unfold tailWord_187821
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850394652564069118107317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4566929768376046078738211 6850394652564069118107317)
  ·
    refine ⟨642224498677881479822561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6850394652564069118107317 642224498677881479822561)
    ·
      refine ⟨481668374008411109866921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 642224498677881479822561 481668374008411109866921)
      ·
        refine ⟨361251280506308332400191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481668374008411109866921 361251280506308332400191)
        ·
          refine ⟨541876920759462498600287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361251280506308332400191 541876920759462498600287)
          ·
            refine ⟨812815381139193747900431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541876920759462498600287 812815381139193747900431)
            ·
              refine ⟨1219223071708790621850647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812815381139193747900431 1219223071708790621850647)
              ·
                refine ⟨1828834607563185932775971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1219223071708790621850647 1828834607563185932775971)
                ·
                  refine ⟨2743251911344778899163957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828834607563185932775971 2743251911344778899163957)
                  ·
                    refine ⟨257179866688573021796621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2743251911344778899163957 257179866688573021796621)
                    ·
                      refine ⟨96442450008214883173733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257179866688573021796621 96442450008214883173733)
                      ·
                        rfl

theorem cell23_187821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_187821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187821 prefixEnd_187821 := by exact prefixLift 187821
  have htrace : WordTrace (prefixWord ++ tailWord_187821) baseStart_187821 baseEnd_187821 := by
    simpa [prefixWord, tailWord_187821, baseEnd_187821] using wordTrace_append hprefix tailTrace_187821
  have hstable : (prefixWord ++ tailWord_187821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187821).length < 2 ^ (prefixWord ++ tailWord_187821).sum := by decide
  have hdescent : baseEnd_187821 < baseStart_187821 := by decide
  rcases family_descends (prefixWord ++ tailWord_187821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187861 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_187861 : Nat := 118140960795 + 187861 * 2 ^ 59
def prefixEnd_187861 : Nat := 4983230072969 + 3 ^ 40 * 187861 * 2
def baseEnd_187861 : Nat := 96462989234394726673549

theorem tailTrace_187861 : CollatzResearch.WordTrace tailWord_187861 prefixEnd_187861 96462989234394726673549 := by
  unfold tailWord_187861
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851853572419155949563437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4567902381612770633042291 6851853572419155949563437)
  ·
    refine ⟨2569445089657183481086289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6851853572419155949563437 2569445089657183481086289)
    ·
      refine ⟨1927083817242887610814717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2569445089657183481086289 1927083817242887610814717)
      ·
        refine ⟨722656431466082854055519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1927083817242887610814717 722656431466082854055519)
        ·
          refine ⟨1083984647199124281083279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722656431466082854055519 1083984647199124281083279)
          ·
            refine ⟨1625976970798686421624919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1083984647199124281083279 1625976970798686421624919)
            ·
              refine ⟨2438965456198029632437379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1625976970798686421624919 2438965456198029632437379)
              ·
                refine ⟨3658448184297044448656069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438965456198029632437379 3658448184297044448656069)
                ·
                  refine ⟨685959034555695834123013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3658448184297044448656069 685959034555695834123013)
                  ·
                    refine ⟨128617318979192968898065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 685959034555695834123013 128617318979192968898065)
                    ·
                      refine ⟨96462989234394726673549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128617318979192968898065 96462989234394726673549)
                      ·
                        rfl

theorem cell23_187861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_187861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187861 prefixEnd_187861 := by exact prefixLift 187861
  have htrace : WordTrace (prefixWord ++ tailWord_187861) baseStart_187861 baseEnd_187861 := by
    simpa [prefixWord, tailWord_187861, baseEnd_187861] using wordTrace_append hprefix tailTrace_187861
  have hstable : (prefixWord ++ tailWord_187861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187861).length < 2 ^ (prefixWord ++ tailWord_187861).sum := by decide
  have hdescent : baseEnd_187861 < baseStart_187861 := by decide
  rcases family_descends (prefixWord ++ tailWord_187861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187871 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 3, 4]
def baseStart_187871 : Nat := 118140960795 + 187871 * 2 ^ 59
def prefixEnd_187871 : Nat := 4983230072969 + 3 ^ 40 * 187871 * 2
def baseEnd_187871 : Nat := 32156041346979895849501

theorem tailTrace_187871 : CollatzResearch.WordTrace tailWord_187871 prefixEnd_187871 32156041346979895849501 := by
  unfold tailWord_187871
  simp only [CollatzResearch.WordTrace]
  refine ⟨6852218302382927657427467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4568145534921951771618311 6852218302382927657427467)
  ·
    refine ⟨10278327453574391486141201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6852218302382927657427467 10278327453574391486141201)
    ·
      refine ⟨7708745590180793614605901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10278327453574391486141201 7708745590180793614605901)
      ·
        refine ⟨2890779596317797605477213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7708745590180793614605901 2890779596317797605477213)
        ·
          refine ⟨1084042348619174102053955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2890779596317797605477213 1084042348619174102053955)
          ·
            refine ⟨1626063522928761153080933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1084042348619174102053955 1626063522928761153080933)
            ·
              refine ⟨304886910549142716202675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1626063522928761153080933 304886910549142716202675)
              ·
                refine ⟨457330365823714074304013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304886910549142716202675 457330365823714074304013)
                ·
                  refine ⟨171498887183892777864005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457330365823714074304013 171498887183892777864005)
                  ·
                    refine ⟨32156041346979895849501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171498887183892777864005 32156041346979895849501)
                    ·
                      rfl

theorem cell23_187871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 4].length) (baseStart_187871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187871 prefixEnd_187871 := by exact prefixLift 187871
  have htrace : WordTrace (prefixWord ++ tailWord_187871) baseStart_187871 baseEnd_187871 := by
    simpa [prefixWord, tailWord_187871, baseEnd_187871] using wordTrace_append hprefix tailTrace_187871
  have hstable : (prefixWord ++ tailWord_187871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187871).length < 2 ^ (prefixWord ++ tailWord_187871).sum := by decide
  have hdescent : baseEnd_187871 < baseStart_187871 := by decide
  rcases family_descends (prefixWord ++ tailWord_187871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187961 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_187961 : Nat := 118140960795 + 187961 * 2 ^ 59
def prefixEnd_187961 : Nat := 4983230072969 + 3 ^ 40 * 187961 * 2
def baseEnd_187961 : Nat := 32171445766614778474363

theorem tailTrace_187961 : CollatzResearch.WordTrace tailWord_187961 prefixEnd_187961 32171445766614778474363 := by
  unfold tailWord_187961
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855500872056873028203737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4570333914704582018802491 6855500872056873028203737)
  ·
    refine ⟨5141625654042654771152803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6855500872056873028203737 5141625654042654771152803)
    ·
      refine ⟨7712438481063982156729205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5141625654042654771152803 7712438481063982156729205)
      ·
        refine ⟨723041107599748327193363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7712438481063982156729205 723041107599748327193363)
        ·
          refine ⟨1084561661399622490790045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723041107599748327193363 1084561661399622490790045)
          ·
            refine ⟨406710623024858434046267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1084561661399622490790045 406710623024858434046267)
            ·
              refine ⟨610065934537287651069401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406710623024858434046267 610065934537287651069401)
              ·
                refine ⟨457549450902965738302051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610065934537287651069401 457549450902965738302051)
                ·
                  refine ⟨686324176354448607453077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457549450902965738302051 686324176354448607453077)
                  ·
                    refine ⟨32171445766614778474363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 686324176354448607453077 32171445766614778474363)
                    ·
                      rfl

theorem cell23_187961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_187961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187961 prefixEnd_187961 := by exact prefixLift 187961
  have htrace : WordTrace (prefixWord ++ tailWord_187961) baseStart_187961 baseEnd_187961 := by
    simpa [prefixWord, tailWord_187961, baseEnd_187961] using wordTrace_append hprefix tailTrace_187961
  have hstable : (prefixWord ++ tailWord_187961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187961).length < 2 ^ (prefixWord ++ tailWord_187961).sum := by decide
  have hdescent : baseEnd_187961 < baseStart_187961 := by decide
  rcases family_descends (prefixWord ++ tailWord_187961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187965 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_187965 : Nat := 118140960795 + 187965 * 2 ^ 59
def prefixEnd_187965 : Nat := 4983230072969 + 3 ^ 40 * 187965 * 2
def baseEnd_187965 : Nat := 32172130407487439924357

theorem tailTrace_187965 : CollatzResearch.WordTrace tailWord_187965 prefixEnd_187965 32172130407487439924357 := by
  unfold tailWord_187965
  simp only [CollatzResearch.WordTrace]
  refine ⟨6855646764042381711349349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4570431176028254474232899 6855646764042381711349349)
  ·
    refine ⟨1285433768257946570878003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6855646764042381711349349 1285433768257946570878003)
    ·
      refine ⟨1928150652386919856317005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285433768257946570878003 1928150652386919856317005)
      ·
        refine ⟨723056494645094946118877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1928150652386919856317005 723056494645094946118877)
        ·
          refine ⟨271146185491910604794579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 723056494645094946118877 271146185491910604794579)
          ·
            refine ⟨406719278237865907191869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271146185491910604794579 406719278237865907191869)
            ·
              refine ⟨152519729339199715196951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406719278237865907191869 152519729339199715196951)
              ·
                refine ⟨228779594008799572795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152519729339199715196951 228779594008799572795427)
                ·
                  refine ⟨343169391013199359193141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228779594008799572795427 343169391013199359193141)
                  ·
                    refine ⟨32172130407487439924357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 343169391013199359193141 32172130407487439924357)
                    ·
                      rfl

theorem cell23_187965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_187965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187965 prefixEnd_187965 := by exact prefixLift 187965
  have htrace : WordTrace (prefixWord ++ tailWord_187965) baseStart_187965 baseEnd_187965 := by
    simpa [prefixWord, tailWord_187965, baseEnd_187965] using wordTrace_append hprefix tailTrace_187965
  have hstable : (prefixWord ++ tailWord_187965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187965).length < 2 ^ (prefixWord ++ tailWord_187965).sum := by decide
  have hdescent : baseEnd_187965 < baseStart_187965 := by decide
  rcases family_descends (prefixWord ++ tailWord_187965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187978 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_187978 : Nat := 118140960795 + 187978 * 2 ^ 59
def prefixEnd_187978 : Nat := 4983230072969 + 3 ^ 40 * 187978 * 2
def baseEnd_187978 : Nat := 32174355490323589636837

theorem tailTrace_187978 : CollatzResearch.WordTrace tailWord_187978 prefixEnd_187978 32174355490323589636837 := by
  unfold tailWord_187978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714030228248821232893147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4570747275330189954381725 1714030228248821232893147)
  ·
    refine ⟨2571045342373231849339721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1714030228248821232893147 2571045342373231849339721)
    ·
      refine ⟨1928284006779923887004791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2571045342373231849339721 1928284006779923887004791)
      ·
        refine ⟨2892426010169885830507187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1928284006779923887004791 2892426010169885830507187)
        ·
          refine ⟨4338639015254828745760781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892426010169885830507187 4338639015254828745760781)
          ·
            refine ⟨1626989630720560779660293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4338639015254828745760781 1626989630720560779660293)
            ·
              refine ⟨305060555760105146186305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1626989630720560779660293 305060555760105146186305)
              ·
                refine ⟨228795416820078859639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305060555760105146186305 228795416820078859639729)
                ·
                  refine ⟨171596562615059144729797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228795416820078859639729 171596562615059144729797)
                  ·
                    refine ⟨32174355490323589636837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171596562615059144729797 32174355490323589636837)
                    ·
                      rfl

theorem cell23_187978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_187978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187978 prefixEnd_187978 := by exact prefixLift 187978
  have htrace : WordTrace (prefixWord ++ tailWord_187978) baseStart_187978 baseEnd_187978 := by
    simpa [prefixWord, tailWord_187978, baseEnd_187978] using wordTrace_append hprefix tailTrace_187978
  have hstable : (prefixWord ++ tailWord_187978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187978).length < 2 ^ (prefixWord ++ tailWord_187978).sum := by decide
  have hdescent : baseEnd_187978 < baseStart_187978 := by decide
  rcases family_descends (prefixWord ++ tailWord_187978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187991 : List Nat := [1, 1, 3, 2, 2, 5, 1, 8]
def baseStart_187991 : Nat := 118140960795 + 187991 * 2 ^ 59
def prefixEnd_187991 : Nat := 4983230072969 + 3 ^ 40 * 187991 * 2
def baseEnd_187991 : Nat := 3575175619239971038813

theorem tailTrace_187991 : CollatzResearch.WordTrace tailWord_187991 prefixEnd_187991 3575175619239971038813 := by
  unfold tailWord_187991
  simp only [CollatzResearch.WordTrace]
  refine ⟨6856595061948188151795827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4571063374632125434530551 6856595061948188151795827)
  ·
    refine ⟨10284892592922282227693741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6856595061948188151795827 10284892592922282227693741)
    ·
      refine ⟨3856834722345855835385153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10284892592922282227693741 3856834722345855835385153)
      ·
        refine ⟨2892626041759391876538865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856834722345855835385153 2892626041759391876538865)
        ·
          refine ⟨2169469531319543907404149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2892626041759391876538865 2169469531319543907404149)
          ·
            refine ⟨203387768561207241319139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2169469531319543907404149 203387768561207241319139)
            ·
              refine ⟨305081652841810861978709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203387768561207241319139 305081652841810861978709)
              ·
                refine ⟨3575175619239971038813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 305081652841810861978709 3575175619239971038813)
                ·
                  rfl

theorem cell23_187991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 8].length) (baseStart_187991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187991 prefixEnd_187991 := by exact prefixLift 187991
  have htrace : WordTrace (prefixWord ++ tailWord_187991) baseStart_187991 baseEnd_187991 := by
    simpa [prefixWord, tailWord_187991, baseEnd_187991] using wordTrace_append hprefix tailTrace_187991
  have hstable : (prefixWord ++ tailWord_187991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187991).length < 2 ^ (prefixWord ++ tailWord_187991).sum := by decide
  have hdescent : baseEnd_187991 < baseStart_187991 := by decide
  rcases family_descends (prefixWord ++ tailWord_187991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_187994 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_187994 : Nat := 118140960795 + 187994 * 2 ^ 59
def prefixEnd_187994 : Nat := 4983230072969 + 3 ^ 40 * 187994 * 2
def baseEnd_187994 : Nat := 96531282161442706310437

theorem tailTrace_187994 : CollatzResearch.WordTrace tailWord_187994 prefixEnd_187994 96531282161442706310437 := by
  unfold tailWord_187994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714176120234329916038759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4571136320624879776103357 1714176120234329916038759)
  ·
    refine ⟨2571264180351494874058139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1714176120234329916038759 2571264180351494874058139)
    ·
      refine ⟨3856896270527242311087209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2571264180351494874058139 3856896270527242311087209)
      ·
        refine ⟨2892672202895431733315407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3856896270527242311087209 2892672202895431733315407)
        ·
          refine ⟨4339008304343147599973111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2892672202895431733315407 4339008304343147599973111)
          ·
            refine ⟨6508512456514721399959667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4339008304343147599973111 6508512456514721399959667)
            ·
              refine ⟨9762768684772082099939501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6508512456514721399959667 9762768684772082099939501)
              ·
                refine ⟨3661038256789530787477313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9762768684772082099939501 3661038256789530787477313)
                ·
                  refine ⟨2745778692592148090607985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3661038256789530787477313 2745778692592148090607985)
                  ·
                    refine ⟨2059334019444111067955989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2745778692592148090607985 2059334019444111067955989)
                    ·
                      refine ⟨96531282161442706310437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2059334019444111067955989 96531282161442706310437)
                      ·
                        rfl

theorem cell23_187994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_187994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_187994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_187994 prefixEnd_187994 := by exact prefixLift 187994
  have htrace : WordTrace (prefixWord ++ tailWord_187994) baseStart_187994 baseEnd_187994 := by
    simpa [prefixWord, tailWord_187994, baseEnd_187994] using wordTrace_append hprefix tailTrace_187994
  have hstable : (prefixWord ++ tailWord_187994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_187994).length < 2 ^ (prefixWord ++ tailWord_187994).sum := by decide
  have hdescent : baseEnd_187994 < baseStart_187994 := by decide
  rcases family_descends (prefixWord ++ tailWord_187994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188008 : List Nat := [2, 1, 4, 3, 1, 2, 3, 7]
def baseStart_188008 : Nat := 118140960795 + 188008 * 2 ^ 59
def prefixEnd_188008 : Nat := 4983230072969 + 3 ^ 40 * 188008 * 2
def baseEnd_188008 : Nat := 3575498921874283390199

theorem tailTrace_188008 : CollatzResearch.WordTrace tailWord_188008 prefixEnd_188008 3575498921874283390199 := by
  unfold tailWord_188008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3428607551443300027582339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4571476735257733370109785 3428607551443300027582339)
  ·
    refine ⟨5142911327164950041373509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3428607551443300027582339 5142911327164950041373509)
    ·
      refine ⟨964295873843428132757533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5142911327164950041373509 964295873843428132757533)
      ·
        refine ⟨361610952691285549784075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 964295873843428132757533 361610952691285549784075)
        ·
          refine ⟨542416429036928324676113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361610952691285549784075 542416429036928324676113)
          ·
            refine ⟨406812321777696243507085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 542416429036928324676113 406812321777696243507085)
            ·
              refine ⟨152554620666636091315157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406812321777696243507085 152554620666636091315157)
              ·
                refine ⟨3575498921874283390199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 152554620666636091315157 3575498921874283390199)
                ·
                  rfl

theorem cell23_188008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 7].length) (baseStart_188008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188008 prefixEnd_188008 := by exact prefixLift 188008
  have htrace : WordTrace (prefixWord ++ tailWord_188008) baseStart_188008 baseEnd_188008 := by
    simpa [prefixWord, tailWord_188008, baseEnd_188008] using wordTrace_append hprefix tailTrace_188008
  have hstable : (prefixWord ++ tailWord_188008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188008).length < 2 ^ (prefixWord ++ tailWord_188008).sum := by decide
  have hdescent : baseEnd_188008 < baseStart_188008 := by decide
  rcases family_descends (prefixWord ++ tailWord_188008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188018 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_188018 : Nat := 118140960795 + 188018 * 2 ^ 59
def prefixEnd_188018 : Nat := 4983230072969 + 3 ^ 40 * 188018 * 2
def baseEnd_188018 : Nat := 96543605697150612410327

theorem tailTrace_188018 : CollatzResearch.WordTrace tailWord_188018 prefixEnd_188018 96543605697150612410327 := by
  unfold tailWord_188018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714394958212592940757177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4571719888566914508685805 1714394958212592940757177)
  ·
    refine ⟨1285796218659444705567883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1714394958212592940757177 1285796218659444705567883)
    ·
      refine ⟨1928694327989167058351825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1285796218659444705567883 1928694327989167058351825)
      ·
        refine ⟨1446520745991875293763869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1928694327989167058351825 1446520745991875293763869)
        ·
          refine ⟨542445279746953235161451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1446520745991875293763869 542445279746953235161451)
          ·
            refine ⟨813667919620429852742177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542445279746953235161451 813667919620429852742177)
            ·
              refine ⟨610250939715322389556633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 813667919620429852742177 610250939715322389556633)
              ·
                refine ⟨457688204786491792167475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610250939715322389556633 457688204786491792167475)
                ·
                  refine ⟨686532307179737688251213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457688204786491792167475 686532307179737688251213)
                  ·
                    refine ⟨257449615192401633094205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686532307179737688251213 257449615192401633094205)
                    ·
                      refine ⟨96543605697150612410327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257449615192401633094205 96543605697150612410327)
                      ·
                        rfl

theorem cell23_188018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_188018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188018 prefixEnd_188018 := by exact prefixLift 188018
  have htrace : WordTrace (prefixWord ++ tailWord_188018) baseStart_188018 baseEnd_188018 := by
    simpa [prefixWord, tailWord_188018, baseEnd_188018] using wordTrace_append hprefix tailTrace_188018
  have hstable : (prefixWord ++ tailWord_188018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188018).length < 2 ^ (prefixWord ++ tailWord_188018).sum := by decide
  have hdescent : baseEnd_188018 < baseStart_188018 := by decide
  rcases family_descends (prefixWord ++ tailWord_188018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188022 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3]
def baseStart_188022 : Nat := 118140960795 + 188022 * 2 ^ 59
def prefixEnd_188022 : Nat := 4983230072969 + 3 ^ 40 * 188022 * 2
def baseEnd_188022 : Nat := 96545659619768596760309

theorem tailTrace_188022 : CollatzResearch.WordTrace tailWord_188022 prefixEnd_188022 96545659619768596760309 := by
  unfold tailWord_188022
  simp only [CollatzResearch.WordTrace]
  refine ⟨428607857802242527885895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4571817149890586964116213 428607857802242527885895)
  ·
    refine ⟨642911786703363791828843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 428607857802242527885895 642911786703363791828843)
    ·
      refine ⟨964367680055045687743265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 642911786703363791828843 964367680055045687743265)
      ·
        refine ⟨723275760041284265807449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 964367680055045687743265 723275760041284265807449)
        ·
          refine ⟨542456820030963199355587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 723275760041284265807449 542456820030963199355587)
          ·
            refine ⟨813685230046444799033381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542456820030963199355587 813685230046444799033381)
            ·
              refine ⟨152565980633708399818759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 813685230046444799033381 152565980633708399818759)
              ·
                refine ⟨228848970950562599728139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152565980633708399818759 228848970950562599728139)
                ·
                  refine ⟨343273456425843899592209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228848970950562599728139 343273456425843899592209)
                  ·
                    refine ⟨257455092319382924694157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343273456425843899592209 257455092319382924694157)
                    ·
                      refine ⟨96545659619768596760309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257455092319382924694157 96545659619768596760309)
                      ·
                        rfl

theorem cell23_188022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_188022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188022 prefixEnd_188022 := by exact prefixLift 188022
  have htrace : WordTrace (prefixWord ++ tailWord_188022) baseStart_188022 baseEnd_188022 := by
    simpa [prefixWord, tailWord_188022, baseEnd_188022] using wordTrace_append hprefix tailTrace_188022
  have hstable : (prefixWord ++ tailWord_188022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188022).length < 2 ^ (prefixWord ++ tailWord_188022).sum := by decide
  have hdescent : baseEnd_188022 < baseStart_188022 := by decide
  rcases family_descends (prefixWord ++ tailWord_188022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188052 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_188052 : Nat := 118140960795 + 188052 * 2 ^ 59
def prefixEnd_188052 : Nat := 4983230072969 + 3 ^ 40 * 188052 * 2
def baseEnd_188052 : Nat := 96561064039403479385171

theorem tailTrace_188052 : CollatzResearch.WordTrace tailWord_188052 prefixEnd_188052 96561064039403479385171 := by
  unfold tailWord_188052
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429409957363597784883205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4572546609818130379844273 3429409957363597784883205)
  ·
    refine ⟨643014367005674584665601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3429409957363597784883205 643014367005674584665601)
    ·
      refine ⟨482260775254255938499201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 643014367005674584665601 482260775254255938499201)
      ·
        refine ⟨361695581440691953874401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482260775254255938499201 361695581440691953874401)
        ·
          refine ⟨271271686080518965405801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361695581440691953874401 271271686080518965405801)
          ·
            refine ⟨203453764560389224054351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271271686080518965405801 203453764560389224054351)
            ·
              refine ⟨305180646840583836081527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203453764560389224054351 305180646840583836081527)
              ·
                refine ⟨457770970260875754122291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305180646840583836081527 457770970260875754122291)
                ·
                  refine ⟨686656455391313631183437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457770970260875754122291 686656455391313631183437)
                  ·
                    refine ⟨257496170771742611693789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686656455391313631183437 257496170771742611693789)
                    ·
                      refine ⟨96561064039403479385171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257496170771742611693789 96561064039403479385171)
                      ·
                        rfl

theorem cell23_188052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_188052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188052 prefixEnd_188052 := by exact prefixLift 188052
  have htrace : WordTrace (prefixWord ++ tailWord_188052) baseStart_188052 baseEnd_188052 := by
    simpa [prefixWord, tailWord_188052, baseEnd_188052] using wordTrace_append hprefix tailTrace_188052
  have hstable : (prefixWord ++ tailWord_188052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188052).length < 2 ^ (prefixWord ++ tailWord_188052).sum := by decide
  have hdescent : baseEnd_188052 < baseStart_188052 := by decide
  rcases family_descends (prefixWord ++ tailWord_188052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188061 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_188061 : Nat := 118140960795 + 188061 * 2 ^ 59
def prefixEnd_188061 : Nat := 4983230072969 + 3 ^ 40 * 188061 * 2
def baseEnd_188061 : Nat := 96565685365293944172629

theorem tailTrace_188061 : CollatzResearch.WordTrace tailWord_188061 prefixEnd_188061 96565685365293944172629 := by
  unfold tailWord_188061
  simp only [CollatzResearch.WordTrace]
  refine ⟨6859148171694590106844037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4572765447796393404562691 6859148171694590106844037)
  ·
    refine ⟨1286090282192735645033257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6859148171694590106844037 1286090282192735645033257)
    ·
      refine ⟨964567711644551733774943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1286090282192735645033257 964567711644551733774943)
      ·
        refine ⟨1446851567466827600662415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 964567711644551733774943 1446851567466827600662415)
        ·
          refine ⟨2170277351200241400993623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1446851567466827600662415 2170277351200241400993623)
          ·
            refine ⟨3255416026800362101490435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2170277351200241400993623 3255416026800362101490435)
            ·
              refine ⟨4883124040200543152235653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3255416026800362101490435 4883124040200543152235653)
              ·
                refine ⟨915585757537601841044185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4883124040200543152235653 915585757537601841044185)
                ·
                  refine ⟨686689318153201380783139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 915585757537601841044185 686689318153201380783139)
                  ·
                    refine ⟨1030033977229802071174709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 686689318153201380783139 1030033977229802071174709)
                    ·
                      refine ⟨96565685365293944172629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1030033977229802071174709 96565685365293944172629)
                      ·
                        rfl

theorem cell23_188061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_188061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188061 prefixEnd_188061 := by exact prefixLift 188061
  have htrace : WordTrace (prefixWord ++ tailWord_188061) baseStart_188061 baseEnd_188061 := by
    simpa [prefixWord, tailWord_188061, baseEnd_188061] using wordTrace_append hprefix tailTrace_188061
  have hstable : (prefixWord ++ tailWord_188061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188061).length < 2 ^ (prefixWord ++ tailWord_188061).sum := by decide
  have hdescent : baseEnd_188061 < baseStart_188061 := by decide
  rcases family_descends (prefixWord ++ tailWord_188061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188062 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_188062 : Nat := 118140960795 + 188062 * 2 ^ 59
def prefixEnd_188062 : Nat := 4983230072969 + 3 ^ 40 * 188062 * 2
def baseEnd_188062 : Nat := 96566198845948440260125

theorem tailTrace_188062 : CollatzResearch.WordTrace tailWord_188062 prefixEnd_188062 96566198845948440260125 := by
  unfold tailWord_188062
  simp only [CollatzResearch.WordTrace]
  refine ⟨857398080586370909703805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4572789763127311518420293 857398080586370909703805)
  ·
    refine ⟨321524280219889091138927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 857398080586370909703805 321524280219889091138927)
    ·
      refine ⟨482286420329833636708391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 321524280219889091138927 482286420329833636708391)
      ·
        refine ⟨723429630494750455062587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 482286420329833636708391 723429630494750455062587)
        ·
          refine ⟨1085144445742125682593881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723429630494750455062587 1085144445742125682593881)
          ·
            refine ⟨813858334306594261945411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1085144445742125682593881 813858334306594261945411)
            ·
              refine ⟨1220787501459891392918117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 813858334306594261945411 1220787501459891392918117)
              ·
                refine ⟨228897656523729636172147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1220787501459891392918117 228897656523729636172147)
                ·
                  refine ⟨343346484785594454258221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 228897656523729636172147 343346484785594454258221)
                  ·
                    refine ⟨128754931794597920346833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 343346484785594454258221 128754931794597920346833)
                    ·
                      refine ⟨96566198845948440260125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128754931794597920346833 96566198845948440260125)
                      ·
                        rfl

theorem cell23_188062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_188062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188062 prefixEnd_188062 := by exact prefixLift 188062
  have htrace : WordTrace (prefixWord ++ tailWord_188062) baseStart_188062 baseEnd_188062 := by
    simpa [prefixWord, tailWord_188062, baseEnd_188062] using wordTrace_append hprefix tailTrace_188062
  have hstable : (prefixWord ++ tailWord_188062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188062).length < 2 ^ (prefixWord ++ tailWord_188062).sum := by decide
  have hdescent : baseEnd_188062 < baseStart_188062 := by decide
  rcases family_descends (prefixWord ++ tailWord_188062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3]
def baseStart_188091 : Nat := 118140960795 + 188091 * 2 ^ 59
def prefixEnd_188091 : Nat := 4983230072969 + 3 ^ 40 * 188091 * 2
def baseEnd_188091 : Nat := 96581089784928826797491

theorem tailTrace_188091 : CollatzResearch.WordTrace tailWord_188091 prefixEnd_188091 96581089784928826797491 := by
  unfold tailWord_188091
  simp only [CollatzResearch.WordTrace]
  refine ⟨6860242361585905230436127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4573494907723936820290751 6860242361585905230436127)
  ·
    refine ⟨10290363542378857845654191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6860242361585905230436127 10290363542378857845654191)
    ·
      refine ⟨15435545313568286768481287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10290363542378857845654191 15435545313568286768481287)
      ·
        refine ⟨23153317970352430152721931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15435545313568286768481287 23153317970352430152721931)
        ·
          refine ⟨34729976955528645229082897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23153317970352430152721931 34729976955528645229082897)
          ·
            refine ⟨26047482716646483921812173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34729976955528645229082897 26047482716646483921812173)
            ·
              refine ⟨9767806018742431470679565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26047482716646483921812173 9767806018742431470679565)
              ·
                refine ⟨3662927257028411801504837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9767806018742431470679565 3662927257028411801504837)
                ·
                  refine ⟨686798860692827212782157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3662927257028411801504837 686798860692827212782157)
                  ·
                    refine ⟨257549572759810204793309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 686798860692827212782157 257549572759810204793309)
                    ·
                      refine ⟨96581089784928826797491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257549572759810204793309 96581089784928826797491)
                      ·
                        rfl

theorem cell23_188091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 3, 3].length) (baseStart_188091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188091 prefixEnd_188091 := by exact prefixLift 188091
  have htrace : WordTrace (prefixWord ++ tailWord_188091) baseStart_188091 baseEnd_188091 := by
    simpa [prefixWord, tailWord_188091, baseEnd_188091] using wordTrace_append hprefix tailTrace_188091
  have hstable : (prefixWord ++ tailWord_188091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188091).length < 2 ^ (prefixWord ++ tailWord_188091).sum := by decide
  have hdescent : baseEnd_188091 < baseStart_188091 := by decide
  rcases family_descends (prefixWord ++ tailWord_188091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188166 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_188166 : Nat := 118140960795 + 188166 * 2 ^ 59
def prefixEnd_188166 : Nat := 4983230072969 + 3 ^ 40 * 188166 * 2
def baseEnd_188166 : Nat := 10735511203779559262183

theorem tailTrace_188166 : CollatzResearch.WordTrace tailWord_188166 prefixEnd_188166 10735511203779559262183 := by
  unfold tailWord_188166
  simp only [CollatzResearch.WordTrace]
  refine ⟨214468057384818532481761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4575318557542795359610901 214468057384818532481761)
  ·
    refine ⟨160851043038613899361321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 214468057384818532481761 160851043038613899361321)
    ·
      refine ⟨120638282278960424520991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160851043038613899361321 120638282278960424520991)
      ·
        refine ⟨180957423418440636781487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120638282278960424520991 180957423418440636781487)
        ·
          refine ⟨271436135127660955172231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180957423418440636781487 271436135127660955172231)
          ·
            refine ⟨407154202691491432758347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271436135127660955172231 407154202691491432758347)
            ·
              refine ⟨610731304037237149137521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407154202691491432758347 610731304037237149137521)
              ·
                refine ⟨458048478027927861853141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 610731304037237149137521 458048478027927861853141)
                ·
                  refine ⟨10735511203779559262183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 458048478027927861853141 10735511203779559262183)
                  ·
                    rfl

theorem cell23_188166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_188166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188166 prefixEnd_188166 := by exact prefixLift 188166
  have htrace : WordTrace (prefixWord ++ tailWord_188166) baseStart_188166 baseEnd_188166 := by
    simpa [prefixWord, tailWord_188166, baseEnd_188166] using wordTrace_append hprefix tailTrace_188166
  have hstable : (prefixWord ++ tailWord_188166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188166).length < 2 ^ (prefixWord ++ tailWord_188166).sum := by decide
  have hdescent : baseEnd_188166 < baseStart_188166 := by decide
  rcases family_descends (prefixWord ++ tailWord_188166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188168 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_188168 : Nat := 118140960795 + 188168 * 2 ^ 59
def prefixEnd_188168 : Nat := 4983230072969 + 3 ^ 40 * 188168 * 2
def baseEnd_188168 : Nat := 96620627795325025534637

theorem tailTrace_188168 : CollatzResearch.WordTrace tailWord_188168 prefixEnd_188168 96620627795325025534637 := by
  unfold tailWord_188168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431525391153473690494579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4575367188204631587326105 3431525391153473690494579)
  ·
    refine ⟨5147288086730210535741869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431525391153473690494579 5147288086730210535741869)
    ·
      refine ⟨1930233032523828950903201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5147288086730210535741869 1930233032523828950903201)
      ·
        refine ⟨1447674774392871713177401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1930233032523828950903201 1447674774392871713177401)
        ·
          refine ⟨1085756080794653784883051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1447674774392871713177401 1085756080794653784883051)
          ·
            refine ⟨1628634121191980677324577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085756080794653784883051 1628634121191980677324577)
            ·
              refine ⟨1221475590893985507993433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1628634121191980677324577 1221475590893985507993433)
              ·
                refine ⟨916106693170489130995075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1221475590893985507993433 916106693170489130995075)
                ·
                  refine ⟨1374160039755733696492613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916106693170489130995075 1374160039755733696492613)
                  ·
                    refine ⟨257655007454200068092365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1374160039755733696492613 257655007454200068092365)
                    ·
                      refine ⟨96620627795325025534637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257655007454200068092365 96620627795325025534637)
                      ·
                        rfl

theorem cell23_188168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_188168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188168 prefixEnd_188168 := by exact prefixLift 188168
  have htrace : WordTrace (prefixWord ++ tailWord_188168) baseStart_188168 baseEnd_188168 := by
    simpa [prefixWord, tailWord_188168, baseEnd_188168] using wordTrace_append hprefix tailTrace_188168
  have hstable : (prefixWord ++ tailWord_188168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188168).length < 2 ^ (prefixWord ++ tailWord_188168).sum := by decide
  have hdescent : baseEnd_188168 < baseStart_188168 := by decide
  rcases family_descends (prefixWord ++ tailWord_188168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188192 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 1, 4]
def baseStart_188192 : Nat := 118140960795 + 188192 * 2 ^ 59
def prefixEnd_188192 : Nat := 4983230072969 + 3 ^ 40 * 188192 * 2
def baseEnd_188192 : Nat := 32210983777010977211509

theorem tailTrace_188192 : CollatzResearch.WordTrace tailWord_188192 prefixEnd_188192 32210983777010977211509 := by
  unfold tailWord_188192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431963067109999739931415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4575950756146666319908553 3431963067109999739931415)
  ·
    refine ⟨5147944600664999609897123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431963067109999739931415 5147944600664999609897123)
    ·
      refine ⟨7721916900997499414845685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5147944600664999609897123 7721916900997499414845685)
      ·
        refine ⟨723929709468515570141783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7721916900997499414845685 723929709468515570141783)
        ·
          refine ⟨1085894564202773355212675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 723929709468515570141783 1085894564202773355212675)
          ·
            refine ⟨1628841846304160032819013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1085894564202773355212675 1628841846304160032819013)
            ·
              refine ⟨305407846182030006153565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1628841846304160032819013 305407846182030006153565)
              ·
                refine ⟨114527942318261252307587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 305407846182030006153565 114527942318261252307587)
                ·
                  refine ⟨171791913477391878461381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114527942318261252307587 171791913477391878461381)
                  ·
                    refine ⟨32210983777010977211509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171791913477391878461381 32210983777010977211509)
                    ·
                      rfl

theorem cell23_188192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 4].length) (baseStart_188192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188192 prefixEnd_188192 := by exact prefixLift 188192
  have htrace : WordTrace (prefixWord ++ tailWord_188192) baseStart_188192 baseEnd_188192 := by
    simpa [prefixWord, tailWord_188192, baseEnd_188192] using wordTrace_append hprefix tailTrace_188192
  have hstable : (prefixWord ++ tailWord_188192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188192).length < 2 ^ (prefixWord ++ tailWord_188192).sum := by decide
  have hdescent : baseEnd_188192 < baseStart_188192 := by decide
  rcases family_descends (prefixWord ++ tailWord_188192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188222 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 6]
def baseStart_188222 : Nat := 118140960795 + 188222 * 2 ^ 59
def prefixEnd_188222 : Nat := 4983230072969 + 3 ^ 40 * 188222 * 2
def baseEnd_188222 : Nat := 10738706194518646028821

theorem tailTrace_188222 : CollatzResearch.WordTrace tailWord_188222 prefixEnd_188222 10738706194518646028821 := by
  unfold tailWord_188222
  simp only [CollatzResearch.WordTrace]
  refine ⟨858127540513914325431865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4576680216074209735636613 858127540513914325431865)
  ·
    refine ⟨643595655385435744073899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 858127540513914325431865 643595655385435744073899)
    ·
      refine ⟨965393483078153616110849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 643595655385435744073899 965393483078153616110849)
      ·
        refine ⟨724045112308615212083137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965393483078153616110849 724045112308615212083137)
        ·
          refine ⟨543033834231461409062353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724045112308615212083137 543033834231461409062353)
          ·
            refine ⟨407275375673596056796765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 543033834231461409062353 407275375673596056796765)
            ·
              refine ⟨152728265877598521298787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 407275375673596056796765 152728265877598521298787)
              ·
                refine ⟨229092398816397781948181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152728265877598521298787 229092398816397781948181)
                ·
                  refine ⟨10738706194518646028821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229092398816397781948181 10738706194518646028821)
                  ·
                    rfl

theorem cell23_188222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_188222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188222 prefixEnd_188222 := by exact prefixLift 188222
  have htrace : WordTrace (prefixWord ++ tailWord_188222) baseStart_188222 baseEnd_188222 := by
    simpa [prefixWord, tailWord_188222, baseEnd_188222] using wordTrace_append hprefix tailTrace_188222
  have hstable : (prefixWord ++ tailWord_188222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188222).length < 2 ^ (prefixWord ++ tailWord_188222).sum := by decide
  have hdescent : baseEnd_188222 < baseStart_188222 := by decide
  rcases family_descends (prefixWord ++ tailWord_188222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188255 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 4]
def baseStart_188255 : Nat := 118140960795 + 188255 * 2 ^ 59
def prefixEnd_188255 : Nat := 4983230072969 + 3 ^ 40 * 188255 * 2
def baseEnd_188255 : Nat := 96665300612266185146737

theorem tailTrace_188255 : CollatzResearch.WordTrace tailWord_188255 prefixEnd_188255 96665300612266185146737 := by
  unfold tailWord_188255
  simp only [CollatzResearch.WordTrace]
  refine ⟨6866223932991761239406219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4577482621994507492937479 6866223932991761239406219)
  ·
    refine ⟨10299335899487641859109329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6866223932991761239406219 10299335899487641859109329)
    ·
      refine ⟨7724501924615731394331997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10299335899487641859109329 7724501924615731394331997)
      ·
        refine ⟨2896688221730899272874499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7724501924615731394331997 2896688221730899272874499)
        ·
          refine ⟨4345032332596348909311749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2896688221730899272874499 4345032332596348909311749)
          ·
            refine ⟨814693562361815420495953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4345032332596348909311749 814693562361815420495953)
            ·
              refine ⟨611020171771361565371965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 814693562361815420495953 611020171771361565371965)
              ·
                refine ⟨229132564414260587014487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611020171771361565371965 229132564414260587014487)
                ·
                  refine ⟨343698846621390880521731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229132564414260587014487 343698846621390880521731)
                  ·
                    refine ⟨515548269932086320782597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 343698846621390880521731 515548269932086320782597)
                    ·
                      refine ⟨96665300612266185146737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 515548269932086320782597 96665300612266185146737)
                      ·
                        rfl

theorem cell23_188255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_188255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188255 prefixEnd_188255 := by exact prefixLift 188255
  have htrace : WordTrace (prefixWord ++ tailWord_188255) baseStart_188255 baseEnd_188255 := by
    simpa [prefixWord, tailWord_188255, baseEnd_188255] using wordTrace_append hprefix tailTrace_188255
  have hstable : (prefixWord ++ tailWord_188255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188255).length < 2 ^ (prefixWord ++ tailWord_188255).sum := by decide
  have hdescent : baseEnd_188255 < baseStart_188255 := by decide
  rcases family_descends (prefixWord ++ tailWord_188255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188266 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_188266 : Nat := 118140960795 + 188266 * 2 ^ 59
def prefixEnd_188266 : Nat := 4983230072969 + 3 ^ 40 * 188266 * 2
def baseEnd_188266 : Nat := 96670948899465642109187

theorem tailTrace_188266 : CollatzResearch.WordTrace tailWord_188266 prefixEnd_188266 96670948899465642109187 := by
  unfold tailWord_188266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716656283987977529514163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4577750090634606745371101 1716656283987977529514163)
  ·
    refine ⟨2574984425981966294271245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716656283987977529514163 2574984425981966294271245)
    ·
      refine ⟨965619159743237360351717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2574984425981966294271245 965619159743237360351717)
      ·
        refine ⟨181053592451857005065947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 965619159743237360351717 181053592451857005065947)
        ·
          refine ⟨271580388677785507598921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181053592451857005065947 271580388677785507598921)
          ·
            refine ⟨203685291508339130699191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271580388677785507598921 203685291508339130699191)
            ·
              refine ⟨305527937262508696048787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203685291508339130699191 305527937262508696048787)
              ·
                refine ⟨458291905893763044073181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305527937262508696048787 458291905893763044073181)
                ·
                  refine ⟨171859464710161141527443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458291905893763044073181 171859464710161141527443)
                  ·
                    refine ⟨257789197065241712291165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171859464710161141527443 257789197065241712291165)
                    ·
                      refine ⟨96670948899465642109187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257789197065241712291165 96670948899465642109187)
                      ·
                        rfl

theorem cell23_188266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_188266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188266 prefixEnd_188266 := by exact prefixLift 188266
  have htrace : WordTrace (prefixWord ++ tailWord_188266) baseStart_188266 baseEnd_188266 := by
    simpa [prefixWord, tailWord_188266, baseEnd_188266] using wordTrace_append hprefix tailTrace_188266
  have hstable : (prefixWord ++ tailWord_188266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188266).length < 2 ^ (prefixWord ++ tailWord_188266).sum := by decide
  have hdescent : baseEnd_188266 < baseStart_188266 := by decide
  rcases family_descends (prefixWord ++ tailWord_188266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188268 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_188268 : Nat := 118140960795 + 188268 * 2 ^ 59
def prefixEnd_188268 : Nat := 4983230072969 + 3 ^ 40 * 188268 * 2
def baseEnd_188268 : Nat := 96671975860774634284177

theorem tailTrace_188268 : CollatzResearch.WordTrace tailWord_188268 prefixEnd_188268 96671975860774634284177 := by
  unfold tailWord_188268
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433349040972332229814729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4577798721296442973086305 3433349040972332229814729)
  ·
    refine ⟨2575011780729249172361047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3433349040972332229814729 2575011780729249172361047)
    ·
      refine ⟨3862517671093873758541571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575011780729249172361047 3862517671093873758541571)
      ·
        refine ⟨5793776506640810637812357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862517671093873758541571 5793776506640810637812357)
        ·
          refine ⟨1086333094995151994589817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5793776506640810637812357 1086333094995151994589817)
          ·
            refine ⟨814749821246363995942363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1086333094995151994589817 814749821246363995942363)
            ·
              refine ⟨1222124731869545993913545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 814749821246363995942363 1222124731869545993913545)
              ·
                refine ⟨916593548902159495435159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1222124731869545993913545 916593548902159495435159)
                ·
                  refine ⟨1374890323353239243152739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 916593548902159495435159 1374890323353239243152739)
                  ·
                    refine ⟨2062335485029858864729109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1374890323353239243152739 2062335485029858864729109)
                    ·
                      refine ⟨96671975860774634284177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2062335485029858864729109 96671975860774634284177)
                      ·
                        rfl

theorem cell23_188268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_188268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188268 prefixEnd_188268 := by exact prefixLift 188268
  have htrace : WordTrace (prefixWord ++ tailWord_188268) baseStart_188268 baseEnd_188268 := by
    simpa [prefixWord, tailWord_188268, baseEnd_188268] using wordTrace_append hprefix tailTrace_188268
  have hstable : (prefixWord ++ tailWord_188268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188268).length < 2 ^ (prefixWord ++ tailWord_188268).sum := by decide
  have hdescent : baseEnd_188268 < baseStart_188268 := by decide
  rcases family_descends (prefixWord ++ tailWord_188268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188282 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 2, 4]
def baseStart_188282 : Nat := 118140960795 + 188282 * 2 ^ 59
def prefixEnd_188282 : Nat := 4983230072969 + 3 ^ 40 * 188282 * 2
def baseEnd_188282 : Nat := 32226388196645859836371

theorem tailTrace_188282 : CollatzResearch.WordTrace tailWord_188282 prefixEnd_188282 32226388196645859836371 := by
  unfold tailWord_188282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1716802175973486212659775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4578139135929296567092733 1716802175973486212659775)
  ·
    refine ⟨2575203263960229318989663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1716802175973486212659775 2575203263960229318989663)
    ·
      refine ⟨3862804895940343978484495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2575203263960229318989663 3862804895940343978484495)
      ·
        refine ⟨5794207343910515967726743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3862804895940343978484495 5794207343910515967726743)
        ·
          refine ⟨8691311015865773951590115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794207343910515967726743 8691311015865773951590115)
          ·
            refine ⟨13036966523798660927385173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8691311015865773951590115 13036966523798660927385173)
            ·
              refine ⟨152776951450765557742795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 13036966523798660927385173 152776951450765557742795)
              ·
                refine ⟨229165427176148336614193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152776951450765557742795 229165427176148336614193)
                ·
                  refine ⟨171874070382111252460645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229165427176148336614193 171874070382111252460645)
                  ·
                    refine ⟨32226388196645859836371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171874070382111252460645 32226388196645859836371)
                    ·
                      rfl

theorem cell23_188282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_188282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188282 prefixEnd_188282 := by exact prefixLift 188282
  have htrace : WordTrace (prefixWord ++ tailWord_188282) baseStart_188282 baseEnd_188282 := by
    simpa [prefixWord, tailWord_188282, baseEnd_188282] using wordTrace_append hprefix tailTrace_188282
  have hstable : (prefixWord ++ tailWord_188282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188282).length < 2 ^ (prefixWord ++ tailWord_188282).sum := by decide
  have hdescent : baseEnd_188282 < baseStart_188282 := by decide
  rcases family_descends (prefixWord ++ tailWord_188282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188292 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_188292 : Nat := 118140960795 + 188292 * 2 ^ 59
def prefixEnd_188292 : Nat := 4983230072969 + 3 ^ 40 * 188292 * 2
def baseEnd_188292 : Nat := 96684299396482540384067

theorem tailTrace_188292 : CollatzResearch.WordTrace tailWord_188292 prefixEnd_188292 96684299396482540384067 := by
  unfold tailWord_188292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3433786716928858279251565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4578382289238477705668753 3433786716928858279251565)
  ·
    refine ⟨1287670018848321854719337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3433786716928858279251565 1287670018848321854719337)
    ·
      refine ⟨965752514136241391039503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1287670018848321854719337 965752514136241391039503)
      ·
        refine ⟨1448628771204362086559255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 965752514136241391039503 1448628771204362086559255)
        ·
          refine ⟨2172943156806543129838883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1448628771204362086559255 2172943156806543129838883)
          ·
            refine ⟨3259414735209814694758325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2172943156806543129838883 3259414735209814694758325)
            ·
              refine ⟨305570131425920127633593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3259414735209814694758325 305570131425920127633593)
              ·
                refine ⟨229177598569440095725195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305570131425920127633593 229177598569440095725195)
                ·
                  refine ⟨343766397854160143587793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229177598569440095725195 343766397854160143587793)
                  ·
                    refine ⟨257824798390620107690845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 343766397854160143587793 257824798390620107690845)
                    ·
                      refine ⟨96684299396482540384067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257824798390620107690845 96684299396482540384067)
                      ·
                        rfl

theorem cell23_188292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_188292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188292 prefixEnd_188292 := by exact prefixLift 188292
  have htrace : WordTrace (prefixWord ++ tailWord_188292) baseStart_188292 baseEnd_188292 := by
    simpa [prefixWord, tailWord_188292, baseEnd_188292] using wordTrace_append hprefix tailTrace_188292
  have hstable : (prefixWord ++ tailWord_188292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188292).length < 2 ^ (prefixWord ++ tailWord_188292).sum := by decide
  have hdescent : baseEnd_188292 < baseStart_188292 := by decide
  rcases family_descends (prefixWord ++ tailWord_188292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188305 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_188305 : Nat := 118140960795 + 188305 * 2 ^ 59
def prefixEnd_188305 : Nat := 4983230072969 + 3 ^ 40 * 188305 * 2
def baseEnd_188305 : Nat := 96690974644990989521507

theorem tailTrace_188305 : CollatzResearch.WordTrace tailWord_188305 prefixEnd_188305 96690974644990989521507 := by
  unfold tailWord_188305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6868047582810619778726369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4578698388540413185817579 6868047582810619778726369)
  ·
    refine ⟨5151035687107964834044777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6868047582810619778726369 5151035687107964834044777)
    ·
      refine ⟨3863276765330973625533583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5151035687107964834044777 3863276765330973625533583)
      ·
        refine ⟨5794915147996460438300375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3863276765330973625533583 5794915147996460438300375)
        ·
          refine ⟨8692372721994690657450563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5794915147996460438300375 8692372721994690657450563)
          ·
            refine ⟨13038559082992035986175845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8692372721994690657450563 13038559082992035986175845)
            ·
              refine ⟨2444729828061006747407971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13038559082992035986175845 2444729828061006747407971)
              ·
                refine ⟨3667094742091510121111957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2444729828061006747407971 3667094742091510121111957)
                ·
                  refine ⟨171895066035539536927123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3667094742091510121111957 171895066035539536927123)
                  ·
                    refine ⟨257842599053309305390685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171895066035539536927123 257842599053309305390685)
                    ·
                      refine ⟨96690974644990989521507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 257842599053309305390685 96690974644990989521507)
                      ·
                        rfl

theorem cell23_188305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_188305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188305 prefixEnd_188305 := by exact prefixLift 188305
  have htrace : WordTrace (prefixWord ++ tailWord_188305) baseStart_188305 baseEnd_188305 := by
    simpa [prefixWord, tailWord_188305, baseEnd_188305] using wordTrace_append hprefix tailTrace_188305
  have hstable : (prefixWord ++ tailWord_188305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188305).length < 2 ^ (prefixWord ++ tailWord_188305).sum := by decide
  have hdescent : baseEnd_188305 < baseStart_188305 := by decide
  rcases family_descends (prefixWord ++ tailWord_188305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188362 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_188362 : Nat := 118140960795 + 188362 * 2 ^ 59
def prefixEnd_188362 : Nat := 4983230072969 + 3 ^ 40 * 188362 * 2
def baseEnd_188362 : Nat := 96720243042297266508745

theorem tailTrace_188362 : CollatzResearch.WordTrace tailWord_188362 prefixEnd_188362 96720243042297266508745 := by
  unfold tailWord_188362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1717531635901029628387835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4580084362402745675700893 1717531635901029628387835)
  ·
    refine ⟨2576297453851544442581753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1717531635901029628387835 2576297453851544442581753)
    ·
      refine ⟨1932223090388658331936315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2576297453851544442581753 1932223090388658331936315)
      ·
        refine ⟨2898334635582987497904473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1932223090388658331936315 2898334635582987497904473)
        ·
          refine ⟨2173750976687240623428355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2898334635582987497904473 2173750976687240623428355)
          ·
            refine ⟨3260626465030860935142533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2173750976687240623428355 3260626465030860935142533)
            ·
              refine ⟨611367462193286425339225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3260626465030860935142533 611367462193286425339225)
              ·
                refine ⟨458525596644964819004419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611367462193286425339225 458525596644964819004419)
                ·
                  refine ⟨687788394967447228506629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 458525596644964819004419 687788394967447228506629)
                  ·
                    refine ⟨128960324056396355344993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 687788394967447228506629 128960324056396355344993)
                    ·
                      refine ⟨96720243042297266508745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 128960324056396355344993 96720243042297266508745)
                      ·
                        rfl

theorem cell23_188362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_188362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188362 prefixEnd_188362 := by exact prefixLift 188362
  have htrace : WordTrace (prefixWord ++ tailWord_188362) baseStart_188362 baseEnd_188362 := by
    simpa [prefixWord, tailWord_188362, baseEnd_188362] using wordTrace_append hprefix tailTrace_188362
  have hstable : (prefixWord ++ tailWord_188362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188362).length < 2 ^ (prefixWord ++ tailWord_188362).sum := by decide
  have hdescent : baseEnd_188362 < baseStart_188362 := by decide
  rcases family_descends (prefixWord ++ tailWord_188362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188435 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4]
def baseStart_188435 : Nat := 118140960795 + 188435 * 2 ^ 59
def prefixEnd_188435 : Nat := 4983230072969 + 3 ^ 40 * 188435 * 2
def baseEnd_188435 : Nat := 96757727130075480895909

theorem tailTrace_188435 : CollatzResearch.WordTrace tailWord_188435 prefixEnd_188435 96757727130075480895909 := by
  unfold tailWord_188435
  simp only [CollatzResearch.WordTrace]
  refine ⟨6872789072339651980958759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4581859381559767987305839 6872789072339651980958759)
  ·
    refine ⟨10309183608509477971438139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6872789072339651980958759 10309183608509477971438139)
    ·
      refine ⟨15463775412764216957157209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10309183608509477971438139 15463775412764216957157209)
      ·
        refine ⟨11597831559573162717867907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15463775412764216957157209 11597831559573162717867907)
        ·
          refine ⟨17396747339359744076801861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11597831559573162717867907 17396747339359744076801861)
          ·
            refine ⟨3261890126129952014400349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17396747339359744076801861 3261890126129952014400349)
            ·
              refine ⟨1223208797298732005400131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3261890126129952014400349 1223208797298732005400131)
              ·
                refine ⟨1834813195948098008100197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223208797298732005400131 1834813195948098008100197)
                ·
                  refine ⟨344027474240268376518787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1834813195948098008100197 344027474240268376518787)
                  ·
                    refine ⟨516041211360402564778181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 344027474240268376518787 516041211360402564778181)
                    ·
                      refine ⟨96757727130075480895909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 516041211360402564778181 96757727130075480895909)
                      ·
                        rfl

theorem cell23_188435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_188435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188435 prefixEnd_188435 := by exact prefixLift 188435
  have htrace : WordTrace (prefixWord ++ tailWord_188435) baseStart_188435 baseEnd_188435 := by
    simpa [prefixWord, tailWord_188435, baseEnd_188435] using wordTrace_append hprefix tailTrace_188435
  have hstable : (prefixWord ++ tailWord_188435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188435).length < 2 ^ (prefixWord ++ tailWord_188435).sum := by decide
  have hdescent : baseEnd_188435 < baseStart_188435 := by decide
  rcases family_descends (prefixWord ++ tailWord_188435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188436 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 7]
def baseStart_188436 : Nat := 118140960795 + 188436 * 2 ^ 59
def prefixEnd_188436 : Nat := 4983230072969 + 3 ^ 40 * 188436 * 2
def baseEnd_188436 : Nat := 10750915623414441887045

theorem tailTrace_188436 : CollatzResearch.WordTrace tailWord_188436 prefixEnd_188436 10750915623414441887045 := by
  unfold tailWord_188436
  simp only [CollatzResearch.WordTrace]
  refine ⟨3436412772668014575872581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4581883696890686101163441 3436412772668014575872581)
  ·
    refine ⟨644327394875252732976109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3436412772668014575872581 644327394875252732976109)
    ·
      refine ⟨241622773078219774866041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 644327394875252732976109 241622773078219774866041)
      ·
        refine ⟨181217079808664831149531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241622773078219774866041 181217079808664831149531)
        ·
          refine ⟨271825619712997246724297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181217079808664831149531 271825619712997246724297)
          ·
            refine ⟨203869214784747935043223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271825619712997246724297 203869214784747935043223)
            ·
              refine ⟨305803822177121902564835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203869214784747935043223 305803822177121902564835)
              ·
                refine ⟨458705733265682853847253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305803822177121902564835 458705733265682853847253)
                ·
                  refine ⟨10750915623414441887045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 458705733265682853847253 10750915623414441887045)
                  ·
                    rfl

theorem cell23_188436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_188436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188436 prefixEnd_188436 := by exact prefixLift 188436
  have htrace : WordTrace (prefixWord ++ tailWord_188436) baseStart_188436 baseEnd_188436 := by
    simpa [prefixWord, tailWord_188436, baseEnd_188436] using wordTrace_append hprefix tailTrace_188436
  have hstable : (prefixWord ++ tailWord_188436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188436).length < 2 ^ (prefixWord ++ tailWord_188436).sum := by decide
  have hdescent : baseEnd_188436 < baseStart_188436 := by decide
  rcases family_descends (prefixWord ++ tailWord_188436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188486 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_188486 : Nat := 118140960795 + 188486 * 2 ^ 59
def prefixEnd_188486 : Nat := 4983230072969 + 3 ^ 40 * 188486 * 2
def baseEnd_188486 : Nat := 96783914643454781358175

theorem tailTrace_188486 : CollatzResearch.WordTrace tailWord_188486 prefixEnd_188486 96783914643454781358175 := by
  unfold tailWord_188486
  simp only [CollatzResearch.WordTrace]
  refine ⟨214832787348590240345791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4583099463436591794043541 214832787348590240345791)
  ·
    refine ⟨322249181022885360518687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 214832787348590240345791 322249181022885360518687)
    ·
      refine ⟨483373771534328040778031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322249181022885360518687 483373771534328040778031)
      ·
        refine ⟨725060657301492061167047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 483373771534328040778031 725060657301492061167047)
        ·
          refine ⟨1087590985952238091750571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725060657301492061167047 1087590985952238091750571)
          ·
            refine ⟨1631386478928357137625857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087590985952238091750571 1631386478928357137625857)
            ·
              refine ⟨1223539859196267853219393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631386478928357137625857 1223539859196267853219393)
              ·
                refine ⟨917654894397200889914545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223539859196267853219393 917654894397200889914545)
                ·
                  refine ⟨688241170797900667435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 917654894397200889914545 688241170797900667435909)
                  ·
                    refine ⟨129045219524606375144233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688241170797900667435909 129045219524606375144233)
                    ·
                      refine ⟨96783914643454781358175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129045219524606375144233 96783914643454781358175)
                      ·
                        rfl

theorem cell23_188486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_188486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188486 prefixEnd_188486 := by exact prefixLift 188486
  have htrace : WordTrace (prefixWord ++ tailWord_188486) baseStart_188486 baseEnd_188486 := by
    simpa [prefixWord, tailWord_188486, baseEnd_188486] using wordTrace_append hprefix tailTrace_188486
  have hstable : (prefixWord ++ tailWord_188486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188486).length < 2 ^ (prefixWord ++ tailWord_188486).sum := by decide
  have hdescent : baseEnd_188486 < baseStart_188486 := by decide
  rcases family_descends (prefixWord ++ tailWord_188486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188505 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_188505 : Nat := 118140960795 + 188505 * 2 ^ 59
def prefixEnd_188505 : Nat := 4983230072969 + 3 ^ 40 * 188505 * 2
def baseEnd_188505 : Nat := 32264556925296735673529

theorem tailTrace_188505 : CollatzResearch.WordTrace tailWord_188505 prefixEnd_188505 32264556925296735673529 := by
  unfold tailWord_188505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875342182086053936006969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4583561454724035957337979 6875342182086053936006969)
  ·
    refine ⟨5156506636564540452005227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6875342182086053936006969 5156506636564540452005227)
    ·
      refine ⟨7734759954846810678007841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156506636564540452005227 7734759954846810678007841)
      ·
        refine ⟨5801069966135108008505881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7734759954846810678007841 5801069966135108008505881)
        ·
          refine ⟨4350802474601331006379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5801069966135108008505881 4350802474601331006379411)
          ·
            refine ⟨6526203711901996509569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350802474601331006379411 6526203711901996509569117)
            ·
              refine ⟨2447326391963248691088419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6526203711901996509569117 2447326391963248691088419)
              ·
                refine ⟨3670989587944873036632629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447326391963248691088419 3670989587944873036632629)
                ·
                  refine ⟨344155273869831847184309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3670989587944873036632629 344155273869831847184309)
                  ·
                    refine ⟨32264556925296735673529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 344155273869831847184309 32264556925296735673529)
                    ·
                      rfl

theorem cell23_188505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_188505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188505 prefixEnd_188505 := by exact prefixLift 188505
  have htrace : WordTrace (prefixWord ++ tailWord_188505) baseStart_188505 baseEnd_188505 := by
    simpa [prefixWord, tailWord_188505, baseEnd_188505] using wordTrace_append hprefix tailTrace_188505
  have hstable : (prefixWord ++ tailWord_188505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188505).length < 2 ^ (prefixWord ++ tailWord_188505).sum := by decide
  have hdescent : baseEnd_188505 < baseStart_188505 := by decide
  rcases family_descends (prefixWord ++ tailWord_188505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188509 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 6]
def baseStart_188509 : Nat := 118140960795 + 188509 * 2 ^ 59
def prefixEnd_188509 : Nat := 4983230072969 + 3 ^ 40 * 188509 * 2
def baseEnd_188509 : Nat := 10755080522056465707841

theorem tailTrace_188509 : CollatzResearch.WordTrace tailWord_188509 prefixEnd_188509 10755080522056465707841 := by
  unfold tailWord_188509
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875488074071562619152581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4583658716047708412768387 6875488074071562619152581)
  ·
    refine ⟨1289154013888417991091109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6875488074071562619152581 1289154013888417991091109)
    ·
      refine ⟨241716377604078373329583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1289154013888417991091109 241716377604078373329583)
      ·
        refine ⟨362574566406117559994375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241716377604078373329583 362574566406117559994375)
        ·
          refine ⟨543861849609176339991563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362574566406117559994375 543861849609176339991563)
          ·
            refine ⟨815792774413764509987345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543861849609176339991563 815792774413764509987345)
            ·
              refine ⟨611844580810323382490509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 815792774413764509987345 611844580810323382490509)
              ·
                refine ⟨229441717803871268433941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 611844580810323382490509 229441717803871268433941)
                ·
                  refine ⟨10755080522056465707841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 229441717803871268433941 10755080522056465707841)
                  ·
                    rfl

theorem cell23_188509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_188509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188509 prefixEnd_188509 := by exact prefixLift 188509
  have htrace : WordTrace (prefixWord ++ tailWord_188509) baseStart_188509 baseEnd_188509 := by
    simpa [prefixWord, tailWord_188509, baseEnd_188509] using wordTrace_append hprefix tailTrace_188509
  have hstable : (prefixWord ++ tailWord_188509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188509).length < 2 ^ (prefixWord ++ tailWord_188509).sum := by decide
  have hdescent : baseEnd_188509 < baseStart_188509 := by decide
  rcases family_descends (prefixWord ++ tailWord_188509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188519 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_188519 : Nat := 118140960795 + 188519 * 2 ^ 59
def prefixEnd_188519 : Nat := 4983230072969 + 3 ^ 40 * 188519 * 2
def baseEnd_188519 : Nat := 96800859505053152245523

theorem tailTrace_188519 : CollatzResearch.WordTrace tailWord_188519 prefixEnd_188519 96800859505053152245523 := by
  unfold tailWord_188519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875852804035334327016611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4583901869356889551344407 6875852804035334327016611)
  ·
    refine ⟨10313779206053001490524917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875852804035334327016611 10313779206053001490524917)
    ·
      refine ⟨966916800567468889736711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10313779206053001490524917 966916800567468889736711)
      ·
        refine ⟨1450375200851203334605067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 966916800567468889736711 1450375200851203334605067)
        ·
          refine ⟨2175562801276805001907601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450375200851203334605067 2175562801276805001907601)
          ·
            refine ⟨1631672100957603751430701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175562801276805001907601 1631672100957603751430701)
            ·
              refine ⟨611877037859101406786513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1631672100957603751430701 611877037859101406786513)
              ·
                refine ⟨458907778394326055089885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 611877037859101406786513 458907778394326055089885)
                ·
                  refine ⟨172090416897872270658707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 458907778394326055089885 172090416897872270658707)
                  ·
                    refine ⟨258135625346808405988061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172090416897872270658707 258135625346808405988061)
                    ·
                      refine ⟨96800859505053152245523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258135625346808405988061 96800859505053152245523)
                      ·
                        rfl

theorem cell23_188519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_188519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188519 prefixEnd_188519 := by exact prefixLift 188519
  have htrace : WordTrace (prefixWord ++ tailWord_188519) baseStart_188519 baseEnd_188519 := by
    simpa [prefixWord, tailWord_188519, baseEnd_188519] using wordTrace_append hprefix tailTrace_188519
  have hstable : (prefixWord ++ tailWord_188519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188519).length < 2 ^ (prefixWord ++ tailWord_188519).sum := by decide
  have hdescent : baseEnd_188519 < baseStart_188519 := by decide
  rcases family_descends (prefixWord ++ tailWord_188519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188555 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_188555 : Nat := 118140960795 + 188555 * 2 ^ 59
def prefixEnd_188555 : Nat := 4983230072969 + 3 ^ 40 * 188555 * 2
def baseEnd_188555 : Nat := 96819344808615011395357

theorem tailTrace_188555 : CollatzResearch.WordTrace tailWord_188555 prefixEnd_188555 96819344808615011395357 := by
  unfold tailWord_188555
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877165831904912475327119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4584777221269941650218079 6877165831904912475327119)
  ·
    refine ⟨10315748747857368712990679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6877165831904912475327119 10315748747857368712990679)
    ·
      refine ⟨15473623121786053069486019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10315748747857368712990679 15473623121786053069486019)
      ·
        refine ⟨23210434682679079604229029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15473623121786053069486019 23210434682679079604229029)
        ·
          refine ⟨4351956503002327425792943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23210434682679079604229029 4351956503002327425792943)
          ·
            refine ⟨6527934754503491138689415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4351956503002327425792943 6527934754503491138689415)
            ·
              refine ⟨9791902131755236708034123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527934754503491138689415 9791902131755236708034123)
              ·
                refine ⟨14687853197632855062051185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791902131755236708034123 14687853197632855062051185)
                ·
                  refine ⟨11015889898224641296538389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14687853197632855062051185 11015889898224641296538389)
                  ·
                    refine ⟨516369838979280060775237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11015889898224641296538389 516369838979280060775237)
                    ·
                      refine ⟨96819344808615011395357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 516369838979280060775237 96819344808615011395357)
                      ·
                        rfl

theorem cell23_188555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_188555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188555 prefixEnd_188555 := by exact prefixLift 188555
  have htrace : WordTrace (prefixWord ++ tailWord_188555) baseStart_188555 baseEnd_188555 := by
    simpa [prefixWord, tailWord_188555, baseEnd_188555] using wordTrace_append hprefix tailTrace_188555
  have hstable : (prefixWord ++ tailWord_188555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188555).length < 2 ^ (prefixWord ++ tailWord_188555).sum := by decide
  have hdescent : baseEnd_188555 < baseStart_188555 := by decide
  rcases family_descends (prefixWord ++ tailWord_188555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188565 : List Nat := [1, 3, 2, 1, 1, 1, 4, 10]
def baseStart_188565 : Nat := 118140960795 + 188565 * 2 ^ 59
def prefixEnd_188565 : Nat := 4983230072969 + 3 ^ 40 * 188565 * 2
def baseEnd_188565 : Nat := 3586091837598517491493

theorem tailTrace_188565 : CollatzResearch.WordTrace tailWord_188565 prefixEnd_188565 3586091837598517491493 := by
  unfold tailWord_188565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6877530561868684183191149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4585020374579122788794099 6877530561868684183191149)
  ·
    refine ⟨2579073960700756568696681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6877530561868684183191149 2579073960700756568696681)
    ·
      refine ⟨1934305470525567426522511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2579073960700756568696681 1934305470525567426522511)
      ·
        refine ⟨2901458205788351139783767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934305470525567426522511 2901458205788351139783767)
        ·
          refine ⟨4352187308682526709675651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901458205788351139783767 4352187308682526709675651)
          ·
            refine ⟨6528280963023790064513477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352187308682526709675651 6528280963023790064513477)
            ·
              refine ⟨1224052680566960637096277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6528280963023790064513477 1224052680566960637096277)
              ·
                refine ⟨3586091837598517491493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1224052680566960637096277 3586091837598517491493)
                ·
                  rfl

theorem cell23_188565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 10].length) (baseStart_188565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188565 prefixEnd_188565 := by exact prefixLift 188565
  have htrace : WordTrace (prefixWord ++ tailWord_188565) baseStart_188565 baseEnd_188565 := by
    simpa [prefixWord, tailWord_188565, baseEnd_188565] using wordTrace_append hprefix tailTrace_188565
  have hstable : (prefixWord ++ tailWord_188565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188565).length < 2 ^ (prefixWord ++ tailWord_188565).sum := by decide
  have hdescent : baseEnd_188565 < baseStart_188565 := by decide
  rcases family_descends (prefixWord ++ tailWord_188565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188572 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_188572 : Nat := 118140960795 + 188572 * 2 ^ 59
def prefixEnd_188572 : Nat := 4983230072969 + 3 ^ 40 * 188572 * 2
def baseEnd_188572 : Nat := 96828073979741444882779

theorem tailTrace_188572 : CollatzResearch.WordTrace tailWord_188572 prefixEnd_188572 96828073979741444882779 := by
  unfold tailWord_188572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438892936421662189347985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4585190581895549585797313 3438892936421662189347985)
  ·
    refine ⟨2579169702316246642010989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3438892936421662189347985 2579169702316246642010989)
    ·
      refine ⟨967188638368592490754121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2579169702316246642010989 967188638368592490754121)
      ·
        refine ⟨725391478776444368065591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 967188638368592490754121 725391478776444368065591)
        ·
          refine ⟨1088087218164666552098387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725391478776444368065591 1088087218164666552098387)
          ·
            refine ⟨1632130827246999828147581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088087218164666552098387 1632130827246999828147581)
            ·
              refine ⟨612049060217624935555343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1632130827246999828147581 612049060217624935555343)
              ·
                refine ⟨918073590326437403333015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 612049060217624935555343 918073590326437403333015)
                ·
                  refine ⟨1377110385489656104999523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918073590326437403333015 1377110385489656104999523)
                  ·
                    refine ⟨2065665578234484157499285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1377110385489656104999523 2065665578234484157499285)
                    ·
                      refine ⟨96828073979741444882779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2065665578234484157499285 96828073979741444882779)
                      ·
                        rfl

theorem cell23_188572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_188572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188572 prefixEnd_188572 := by exact prefixLift 188572
  have htrace : WordTrace (prefixWord ++ tailWord_188572) baseStart_188572 baseEnd_188572 := by
    simpa [prefixWord, tailWord_188572, baseEnd_188572] using wordTrace_append hprefix tailTrace_188572
  have hstable : (prefixWord ++ tailWord_188572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188572).length < 2 ^ (prefixWord ++ tailWord_188572).sum := by decide
  have hdescent : baseEnd_188572 < baseStart_188572 := by decide
  rcases family_descends (prefixWord ++ tailWord_188572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188576 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2]
def baseStart_188576 : Nat := 118140960795 + 188576 * 2 ^ 59
def prefixEnd_188576 : Nat := 4983230072969 + 3 ^ 40 * 188576 * 2
def baseEnd_188576 : Nat := 96830127902359429232761

theorem tailTrace_188576 : CollatzResearch.WordTrace tailWord_188576 prefixEnd_188576 96830127902359429232761 := by
  unfold tailWord_188576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438965882414416530920791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4585287843219222041227721 3438965882414416530920791)
  ·
    refine ⟨5158448823621624796381187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3438965882414416530920791 5158448823621624796381187)
    ·
      refine ⟨7737673235432437194571781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5158448823621624796381187 7737673235432437194571781)
      ·
        refine ⟨1450813731643581973982209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7737673235432437194571781 1450813731643581973982209)
        ·
          refine ⟨1088110298732686480486657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450813731643581973982209 1088110298732686480486657)
          ·
            refine ⟨816082724049514860364993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1088110298732686480486657 816082724049514860364993)
            ·
              refine ⟨612062043037136145273745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 816082724049514860364993 612062043037136145273745)
              ·
                refine ⟨459046532277852108955309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 612062043037136145273745 459046532277852108955309)
                ·
                  refine ⟨172142449604194540858241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 459046532277852108955309 172142449604194540858241)
                  ·
                    refine ⟨129106837203145905643681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172142449604194540858241 129106837203145905643681)
                    ·
                      refine ⟨96830127902359429232761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129106837203145905643681 96830127902359429232761)
                      ·
                        rfl

theorem cell23_188576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_188576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188576 prefixEnd_188576 := by exact prefixLift 188576
  have htrace : WordTrace (prefixWord ++ tailWord_188576) baseStart_188576 baseEnd_188576 := by
    simpa [prefixWord, tailWord_188576, baseEnd_188576] using wordTrace_append hprefix tailTrace_188576
  have hstable : (prefixWord ++ tailWord_188576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188576).length < 2 ^ (prefixWord ++ tailWord_188576).sum := by decide
  have hdescent : baseEnd_188576 < baseStart_188576 := by decide
  rcases family_descends (prefixWord ++ tailWord_188576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188595 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 9]
def baseStart_188595 : Nat := 118140960795 + 188595 * 2 ^ 59
def prefixEnd_188595 : Nat := 4983230072969 + 3 ^ 40 * 188595 * 2
def baseEnd_188595 : Nat := 32279961344931618298391

theorem tailTrace_188595 : CollatzResearch.WordTrace tailWord_188595 prefixEnd_188595 32279961344931618298391 := by
  unfold tailWord_188595
  simp only [CollatzResearch.WordTrace]
  refine ⟨6878624751759999306783239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4585749834506666204522159 6878624751759999306783239)
  ·
    refine ⟨10317937127639998960174859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6878624751759999306783239 10317937127639998960174859)
    ·
      refine ⟨15476905691459998440262289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10317937127639998960174859 15476905691459998440262289)
      ·
        refine ⟨11607679268594998830196717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15476905691459998440262289 11607679268594998830196717)
        ·
          refine ⟨4352879725723124561323769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11607679268594998830196717 4352879725723124561323769)
          ·
            refine ⟨3264659794292343420992827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352879725723124561323769 3264659794292343420992827)
            ·
              refine ⟨4896989691438515131489241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3264659794292343420992827 4896989691438515131489241)
              ·
                refine ⟨3672742268578886348616931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4896989691438515131489241 3672742268578886348616931)
                ·
                  refine ⟨5509113402868329522925397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3672742268578886348616931 5509113402868329522925397)
                  ·
                    refine ⟨32279961344931618298391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5509113402868329522925397 32279961344931618298391)
                    ·
                      rfl

theorem cell23_188595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_188595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188595 prefixEnd_188595 := by exact prefixLift 188595
  have htrace : WordTrace (prefixWord ++ tailWord_188595) baseStart_188595 baseEnd_188595 := by
    simpa [prefixWord, tailWord_188595, baseEnd_188595] using wordTrace_append hprefix tailTrace_188595
  have hstable : (prefixWord ++ tailWord_188595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188595).length < 2 ^ (prefixWord ++ tailWord_188595).sum := by decide
  have hdescent : baseEnd_188595 < baseStart_188595 := by decide
  rcases family_descends (prefixWord ++ tailWord_188595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188619 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 3, 3, 2]
def baseStart_188619 : Nat := 118140960795 + 188619 * 2 ^ 59
def prefixEnd_188619 : Nat := 4983230072969 + 3 ^ 40 * 188619 * 2
def baseEnd_188619 : Nat := 96852207570502760995063

theorem tailTrace_188619 : CollatzResearch.WordTrace tailWord_188619 prefixEnd_188619 96852207570502760995063 := by
  unfold tailWord_188619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6879500103673051405656911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4586333402448700937104607 6879500103673051405656911)
  ·
    refine ⟨10319250155509577108485367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6879500103673051405656911 10319250155509577108485367)
    ·
      refine ⟨15478875233264365662728051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10319250155509577108485367 15478875233264365662728051)
      ·
        refine ⟨23218312849896548494092077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15478875233264365662728051 23218312849896548494092077)
        ·
          refine ⟨8706867318711205685284529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23218312849896548494092077 8706867318711205685284529)
          ·
            refine ⟨6530150489033404263963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8706867318711205685284529 6530150489033404263963397)
            ·
              refine ⟨1224403216693763299493137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6530150489033404263963397 1224403216693763299493137)
              ·
                refine ⟨918302412520322474619853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1224403216693763299493137 918302412520322474619853)
                ·
                  refine ⟨344363404695120927982445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 918302412520322474619853 344363404695120927982445)
                  ·
                    refine ⟨129136276760670347993417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344363404695120927982445 129136276760670347993417)
                    ·
                      refine ⟨96852207570502760995063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129136276760670347993417 96852207570502760995063)
                      ·
                        rfl

theorem cell23_188619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3, 2].length) (baseStart_188619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188619 prefixEnd_188619 := by exact prefixLift 188619
  have htrace : WordTrace (prefixWord ++ tailWord_188619) baseStart_188619 baseEnd_188619 := by
    simpa [prefixWord, tailWord_188619, baseEnd_188619] using wordTrace_append hprefix tailTrace_188619
  have hstable : (prefixWord ++ tailWord_188619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188619).length < 2 ^ (prefixWord ++ tailWord_188619).sum := by decide
  have hdescent : baseEnd_188619 < baseStart_188619 := by decide
  rcases family_descends (prefixWord ++ tailWord_188619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188620 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_188620 : Nat := 118140960795 + 188620 * 2 ^ 59
def prefixEnd_188620 : Nat := 4983230072969 + 3 ^ 40 * 188620 * 2
def baseEnd_188620 : Nat := 32284240350385752360853

theorem tailTrace_188620 : CollatzResearch.WordTrace tailWord_188620 prefixEnd_188620 32284240350385752360853 := by
  unfold tailWord_188620
  simp only [CollatzResearch.WordTrace]
  refine ⟨3439768288334714288221657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4586357717779619050962209 3439768288334714288221657)
  ·
    refine ⟨2579826216251035716166243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3439768288334714288221657 2579826216251035716166243)
    ·
      refine ⟨3869739324376553574249365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579826216251035716166243 3869739324376553574249365)
      ·
        refine ⟨181394030830150948792939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3869739324376553574249365 181394030830150948792939)
        ·
          refine ⟨272091046245226423189409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181394030830150948792939 272091046245226423189409)
          ·
            refine ⟨204068284683919817392057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272091046245226423189409 204068284683919817392057)
            ·
              refine ⟨153051213512939863044043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204068284683919817392057 153051213512939863044043)
              ·
                refine ⟨229576820269409794566065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153051213512939863044043 229576820269409794566065)
                ·
                  refine ⟨172182615202057345924549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 229576820269409794566065 172182615202057345924549)
                  ·
                    refine ⟨32284240350385752360853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172182615202057345924549 32284240350385752360853)
                    ·
                      rfl

theorem cell23_188620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_188620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188620 prefixEnd_188620 := by exact prefixLift 188620
  have htrace : WordTrace (prefixWord ++ tailWord_188620) baseStart_188620 baseEnd_188620 := by
    simpa [prefixWord, tailWord_188620, baseEnd_188620] using wordTrace_append hprefix tailTrace_188620
  have hstable : (prefixWord ++ tailWord_188620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188620).length < 2 ^ (prefixWord ++ tailWord_188620).sum := by decide
  have hdescent : baseEnd_188620 < baseStart_188620 := by decide
  rcases family_descends (prefixWord ++ tailWord_188620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188630 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_188630 : Nat := 118140960795 + 188630 * 2 ^ 59
def prefixEnd_188630 : Nat := 4983230072969 + 3 ^ 40 * 188630 * 2
def baseEnd_188630 : Nat := 96857855857702217957513

theorem tailTrace_188630 : CollatzResearch.WordTrace tailWord_188630 prefixEnd_188630 96857855857702217957513 := by
  unfold tailWord_188630
  simp only [CollatzResearch.WordTrace]
  refine ⟨429993831664575017769209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4586600871088800189538229 429993831664575017769209)
  ·
    refine ⟨322495373748431263326907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 429993831664575017769209 322495373748431263326907)
    ·
      refine ⟨483743060622646894990361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322495373748431263326907 483743060622646894990361)
      ·
        refine ⟨362807295466985171242771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 483743060622646894990361 362807295466985171242771)
        ·
          refine ⟨544210943200477756864157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 362807295466985171242771 544210943200477756864157)
          ·
            refine ⟨204079103700179158824059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 544210943200477756864157 204079103700179158824059)
            ·
              refine ⟨306118655550268738236089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204079103700179158824059 306118655550268738236089)
              ·
                refine ⟨229588991662701553677067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306118655550268738236089 229588991662701553677067)
                ·
                  refine ⟨344383487494052330515601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229588991662701553677067 344383487494052330515601)
                  ·
                    refine ⟨258287615620539247886701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344383487494052330515601 258287615620539247886701)
                    ·
                      refine ⟨96857855857702217957513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258287615620539247886701 96857855857702217957513)
                      ·
                        rfl

theorem cell23_188630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_188630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188630 prefixEnd_188630 := by exact prefixLift 188630
  have htrace : WordTrace (prefixWord ++ tailWord_188630) baseStart_188630 baseEnd_188630 := by
    simpa [prefixWord, tailWord_188630, baseEnd_188630] using wordTrace_append hprefix tailTrace_188630
  have hstable : (prefixWord ++ tailWord_188630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188630).length < 2 ^ (prefixWord ++ tailWord_188630).sum := by decide
  have hdescent : baseEnd_188630 < baseStart_188630 := by decide
  rcases family_descends (prefixWord ++ tailWord_188630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188649 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 1, 4, 2]
def baseStart_188649 : Nat := 118140960795 + 188649 * 2 ^ 59
def prefixEnd_188649 : Nat := 4983230072969 + 3 ^ 40 * 188649 * 2
def baseEnd_188649 : Nat := 96867611990137643619925

theorem tailTrace_188649 : CollatzResearch.WordTrace tailWord_188649 prefixEnd_188649 96867611990137643619925 := by
  unfold tailWord_188649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880594293564366529249001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4587062862376244352832667 6880594293564366529249001)
  ·
    refine ⟨5160445720173274896936751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6880594293564366529249001 5160445720173274896936751)
    ·
      refine ⟨7740668580259912345405127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5160445720173274896936751 7740668580259912345405127)
      ·
        refine ⟨11611002870389868518107691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7740668580259912345405127 11611002870389868518107691)
        ·
          refine ⟨17416504305584802777161537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11611002870389868518107691 17416504305584802777161537)
          ·
            refine ⟨13062378229188602082871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17416504305584802777161537 13062378229188602082871153)
            ·
              refine ⟨9796783671891451562153365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13062378229188602082871153 9796783671891451562153365)
              ·
                refine ⟨459224234619911791975939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9796783671891451562153365 459224234619911791975939)
                ·
                  refine ⟨688836351929867687963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 459224234619911791975939 688836351929867687963909)
                  ·
                    refine ⟨129156815986850191493233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 688836351929867687963909 129156815986850191493233)
                    ·
                      refine ⟨96867611990137643619925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129156815986850191493233 96867611990137643619925)
                      ·
                        rfl

theorem cell23_188649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 4, 2].length) (baseStart_188649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188649 prefixEnd_188649 := by exact prefixLift 188649
  have htrace : WordTrace (prefixWord ++ tailWord_188649) baseStart_188649 baseEnd_188649 := by
    simpa [prefixWord, tailWord_188649, baseEnd_188649] using wordTrace_append hprefix tailTrace_188649
  have hstable : (prefixWord ++ tailWord_188649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188649).length < 2 ^ (prefixWord ++ tailWord_188649).sum := by decide
  have hdescent : baseEnd_188649 < baseStart_188649 := by decide
  rcases family_descends (prefixWord ++ tailWord_188649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188652 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_188652 : Nat := 118140960795 + 188652 * 2 ^ 59
def prefixEnd_188652 : Nat := 4983230072969 + 3 ^ 40 * 188652 * 2
def baseEnd_188652 : Nat := 96869152432101131882411

theorem tailTrace_188652 : CollatzResearch.WordTrace tailWord_188652 prefixEnd_188652 96869152432101131882411 := by
  unfold tailWord_188652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440351856276749020804105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4587135808368998694405473 3440351856276749020804105)
  ·
    refine ⟨2580263892207561765603079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440351856276749020804105 2580263892207561765603079)
    ·
      refine ⟨3870395838311342648404619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580263892207561765603079 3870395838311342648404619)
      ·
        refine ⟨5805593757467013972606929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3870395838311342648404619 5805593757467013972606929)
        ·
          refine ⟨4354195318100260479455197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5805593757467013972606929 4354195318100260479455197)
          ·
            refine ⟨1632823244287597679795699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4354195318100260479455197 1632823244287597679795699)
            ·
              refine ⟨2449234866431396519693549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632823244287597679795699 2449234866431396519693549)
              ·
                refine ⟨918463074911773694885081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2449234866431396519693549 918463074911773694885081)
                ·
                  refine ⟨688847306183830271163811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 918463074911773694885081 688847306183830271163811)
                  ·
                    refine ⟨1033270959275745406745717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 688847306183830271163811 1033270959275745406745717)
                    ·
                      refine ⟨96869152432101131882411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1033270959275745406745717 96869152432101131882411)
                      ·
                        rfl

theorem cell23_188652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_188652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188652 prefixEnd_188652 := by exact prefixLift 188652
  have htrace : WordTrace (prefixWord ++ tailWord_188652) baseStart_188652 baseEnd_188652 := by
    simpa [prefixWord, tailWord_188652, baseEnd_188652] using wordTrace_append hprefix tailTrace_188652
  have hstable : (prefixWord ++ tailWord_188652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188652).length < 2 ^ (prefixWord ++ tailWord_188652).sum := by decide
  have hdescent : baseEnd_188652 < baseStart_188652 := by decide
  rcases family_descends (prefixWord ++ tailWord_188652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188706 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_188706 : Nat := 118140960795 + 188706 * 2 ^ 59
def prefixEnd_188706 : Nat := 4983230072969 + 3 ^ 40 * 188706 * 2
def baseEnd_188706 : Nat := 10766320043049324511907

theorem tailTrace_188706 : CollatzResearch.WordTrace tailWord_188706 prefixEnd_188706 10766320043049324511907 := by
  unfold tailWord_188706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1720668313589466316018493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4588448836238576842715981 1720668313589466316018493)
  ·
    refine ⟨645250617596049868506935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1720668313589466316018493 645250617596049868506935)
    ·
      refine ⟨967875926394074802760403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645250617596049868506935 967875926394074802760403)
      ·
        refine ⟨1451813889591112204140605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 967875926394074802760403 1451813889591112204140605)
        ·
          refine ⟨544430208596667076552727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1451813889591112204140605 544430208596667076552727)
          ·
            refine ⟨816645312895000614829091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544430208596667076552727 816645312895000614829091)
            ·
              refine ⟨1224967969342500922243637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816645312895000614829091 1224967969342500922243637)
              ·
                refine ⟨114840747125859461460341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1224967969342500922243637 114840747125859461460341)
                ·
                  refine ⟨10766320043049324511907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114840747125859461460341 10766320043049324511907)
                  ·
                    rfl

theorem cell23_188706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_188706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188706 prefixEnd_188706 := by exact prefixLift 188706
  have htrace : WordTrace (prefixWord ++ tailWord_188706) baseStart_188706 baseEnd_188706 := by
    simpa [prefixWord, tailWord_188706, baseEnd_188706] using wordTrace_append hprefix tailTrace_188706
  have hstable : (prefixWord ++ tailWord_188706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188706).length < 2 ^ (prefixWord ++ tailWord_188706).sum := by decide
  have hdescent : baseEnd_188706 < baseStart_188706 := by decide
  rcases family_descends (prefixWord ++ tailWord_188706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188759 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_188759 : Nat := 118140960795 + 188759 * 2 ^ 59
def prefixEnd_188759 : Nat := 4983230072969 + 3 ^ 40 * 188759 * 2
def baseEnd_188759 : Nat := 96924094862132213244419

theorem tailTrace_188759 : CollatzResearch.WordTrace tailWord_188759 prefixEnd_188759 96924094862132213244419 := by
  unfold tailWord_188759
  simp only [CollatzResearch.WordTrace]
  refine ⟨6884606323165855315753331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4589737548777236877168887 6884606323165855315753331)
  ·
    refine ⟨10326909484748782973629997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6884606323165855315753331 10326909484748782973629997)
    ·
      refine ⟨3872591056780793615111249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10326909484748782973629997 3872591056780793615111249)
      ·
        refine ⟨2904443292585595211333437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3872591056780793615111249 2904443292585595211333437)
        ·
          refine ⟨1089166234719598204250039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2904443292585595211333437 1089166234719598204250039)
          ·
            refine ⟨1633749352079397306375059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089166234719598204250039 1633749352079397306375059)
            ·
              refine ⟨2450624028119095959562589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633749352079397306375059 2450624028119095959562589)
              ·
                refine ⟨918984010544660984835971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2450624028119095959562589 918984010544660984835971)
                ·
                  refine ⟨1378476015816991477253957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918984010544660984835971 1378476015816991477253957)
                  ·
                    refine ⟨258464252965685901985117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1378476015816991477253957 258464252965685901985117)
                    ·
                      refine ⟨96924094862132213244419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258464252965685901985117 96924094862132213244419)
                      ·
                        rfl

theorem cell23_188759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_188759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188759 prefixEnd_188759 := by exact prefixLift 188759
  have htrace : WordTrace (prefixWord ++ tailWord_188759) baseStart_188759 baseEnd_188759 := by
    simpa [prefixWord, tailWord_188759, baseEnd_188759] using wordTrace_append hprefix tailTrace_188759
  have hstable : (prefixWord ++ tailWord_188759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188759).length < 2 ^ (prefixWord ++ tailWord_188759).sum := by decide
  have hdescent : baseEnd_188759 < baseStart_188759 := by decide
  rcases family_descends (prefixWord ++ tailWord_188759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188776 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_188776 : Nat := 118140960795 + 188776 * 2 ^ 59
def prefixEnd_188776 : Nat := 4983230072969 + 3 ^ 40 * 188776 * 2
def baseEnd_188776 : Nat := 96932824033258646731841

theorem tailTrace_188776 : CollatzResearch.WordTrace tailWord_188776 prefixEnd_188776 96932824033258646731841 := by
  unfold tailWord_188776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442613182052133609561091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4590150909402844812748121 3442613182052133609561091)
  ·
    refine ⟨5163919773078200414341637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3442613182052133609561091 5163919773078200414341637)
    ·
      refine ⟨968234957452162577689057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5163919773078200414341637 968234957452162577689057)
      ·
        refine ⟨726176218089121933266793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 968234957452162577689057 726176218089121933266793)
        ·
          refine ⟨544632163566841449950095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 726176218089121933266793 544632163566841449950095)
          ·
            refine ⟨816948245350262174925143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 544632163566841449950095 816948245350262174925143)
            ·
              refine ⟨1225422368025393262387715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 816948245350262174925143 1225422368025393262387715)
              ·
                refine ⟨1838133552038089893581573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225422368025393262387715 1838133552038089893581573)
                ·
                  refine ⟨344650041007141855046545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1838133552038089893581573 344650041007141855046545)
                  ·
                    refine ⟨258487530755356391284909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344650041007141855046545 258487530755356391284909)
                    ·
                      refine ⟨96932824033258646731841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258487530755356391284909 96932824033258646731841)
                      ·
                        rfl

theorem cell23_188776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_188776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188776 prefixEnd_188776 := by exact prefixLift 188776
  have htrace : WordTrace (prefixWord ++ tailWord_188776) baseStart_188776 baseEnd_188776 := by
    simpa [prefixWord, tailWord_188776, baseEnd_188776] using wordTrace_append hprefix tailTrace_188776
  have hstable : (prefixWord ++ tailWord_188776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188776).length < 2 ^ (prefixWord ++ tailWord_188776).sum := by decide
  have hdescent : baseEnd_188776 < baseStart_188776 := by decide
  rcases family_descends (prefixWord ++ tailWord_188776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188810 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_188810 : Nat := 118140960795 + 188810 * 2 ^ 59
def prefixEnd_188810 : Nat := 4983230072969 + 3 ^ 40 * 188810 * 2
def baseEnd_188810 : Nat := 96950282375511513706685

theorem tailTrace_188810 : CollatzResearch.WordTrace tailWord_188810 prefixEnd_188810 96950282375511513706685 := by
  unfold tailWord_188810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1721616611495272756464971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4590977630654060683906589 1721616611495272756464971)
  ·
    refine ⟨2582424917242909134697457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1721616611495272756464971 2582424917242909134697457)
    ·
      refine ⟨1936818687932181851023093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2582424917242909134697457 1936818687932181851023093)
      ·
        refine ⟨181576751993642048533415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1936818687932181851023093 181576751993642048533415)
        ·
          refine ⟨272365127990463072800123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181576751993642048533415 272365127990463072800123)
          ·
            refine ⟨408547691985694609200185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272365127990463072800123 408547691985694609200185)
            ·
              refine ⟨306410768989270956900139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408547691985694609200185 306410768989270956900139)
              ·
                refine ⟨459616153483906435350209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306410768989270956900139 459616153483906435350209)
                ·
                  refine ⟨344712115112929826512657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 459616153483906435350209 344712115112929826512657)
                  ·
                    refine ⟨258534086334697369884493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344712115112929826512657 258534086334697369884493)
                    ·
                      refine ⟨96950282375511513706685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258534086334697369884493 96950282375511513706685)
                      ·
                        rfl

theorem cell23_188810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_188810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188810 prefixEnd_188810 := by exact prefixLift 188810
  have htrace : WordTrace (prefixWord ++ tailWord_188810) baseStart_188810 baseEnd_188810 := by
    simpa [prefixWord, tailWord_188810, baseEnd_188810] using wordTrace_append hprefix tailTrace_188810
  have hstable : (prefixWord ++ tailWord_188810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188810).length < 2 ^ (prefixWord ++ tailWord_188810).sum := by decide
  have hdescent : baseEnd_188810 < baseStart_188810 := by decide
  rcases family_descends (prefixWord ++ tailWord_188810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188886 : List Nat := [5, 2, 1, 1, 1, 1, 12]
def baseStart_188886 : Nat := 118140960795 + 188886 * 2 ^ 59
def prefixEnd_188886 : Nat := 4983230072969 + 3 ^ 40 * 188886 * 2
def baseEnd_188886 : Nat := 1197398850682138473535

theorem tailTrace_188886 : CollatzResearch.WordTrace tailWord_188886 prefixEnd_188886 1197398850682138473535 := by
  unfold tailWord_188886
  simp only [CollatzResearch.WordTrace]
  refine ⟨430577399606609750351657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4592825595803837337084341 430577399606609750351657)
  ·
    refine ⟨322933049704957312763743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 430577399606609750351657 322933049704957312763743)
    ·
      refine ⟨484399574557435969145615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 322933049704957312763743 484399574557435969145615)
      ·
        refine ⟨726599361836153953718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484399574557435969145615 726599361836153953718423)
        ·
          refine ⟨1089899042754230930577635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 726599361836153953718423 1089899042754230930577635)
          ·
            refine ⟨1634848564131346395866453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089899042754230930577635 1634848564131346395866453)
            ·
              refine ⟨1197398850682138473535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 1634848564131346395866453 1197398850682138473535)
              ·
                rfl

theorem cell23_188886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 12].length) (baseStart_188886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188886 prefixEnd_188886 := by exact prefixLift 188886
  have htrace : WordTrace (prefixWord ++ tailWord_188886) baseStart_188886 baseEnd_188886 := by
    simpa [prefixWord, tailWord_188886, baseEnd_188886] using wordTrace_append hprefix tailTrace_188886
  have hstable : (prefixWord ++ tailWord_188886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188886).length < 2 ^ (prefixWord ++ tailWord_188886).sum := by decide
  have hdescent : baseEnd_188886 < baseStart_188886 := by decide
  rcases family_descends (prefixWord ++ tailWord_188886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188917 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_188917 : Nat := 118140960795 + 188917 * 2 ^ 59
def prefixEnd_188917 : Nat := 4983230072969 + 3 ^ 40 * 188917 * 2
def baseEnd_188917 : Nat := 97005224805542595068693

theorem tailTrace_188917 : CollatzResearch.WordTrace tailWord_188917 prefixEnd_188917 97005224805542595068693 := by
  unfold tailWord_188917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890369056593448300005005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4593579371062298866670003 6890369056593448300005005)
  ·
    refine ⟨2583888396222543112501877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6890369056593448300005005 2583888396222543112501877)
    ·
      refine ⟨242239537145863416797051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2583888396222543112501877 242239537145863416797051)
      ·
        refine ⟨363359305718795125195577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242239537145863416797051 363359305718795125195577)
        ·
          refine ⟨272519479289096343896683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363359305718795125195577 272519479289096343896683)
          ·
            refine ⟨408779218933644515845025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272519479289096343896683 408779218933644515845025)
            ·
              refine ⟨306584414200233386883769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408779218933644515845025 306584414200233386883769)
              ·
                refine ⟨229938310650175040162827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306584414200233386883769 229938310650175040162827)
                ·
                  refine ⟨344907465975262560244241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229938310650175040162827 344907465975262560244241)
                  ·
                    refine ⟨258680599481446920183181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344907465975262560244241 258680599481446920183181)
                    ·
                      refine ⟨97005224805542595068693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258680599481446920183181 97005224805542595068693)
                      ·
                        rfl

theorem cell23_188917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_188917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188917 prefixEnd_188917 := by exact prefixLift 188917
  have htrace : WordTrace (prefixWord ++ tailWord_188917) baseStart_188917 baseEnd_188917 := by
    simpa [prefixWord, tailWord_188917, baseEnd_188917] using wordTrace_append hprefix tailTrace_188917
  have hstable : (prefixWord ++ tailWord_188917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188917).length < 2 ^ (prefixWord ++ tailWord_188917).sum := by decide
  have hdescent : baseEnd_188917 < baseStart_188917 := by decide
  rcases family_descends (prefixWord ++ tailWord_188917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188919 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_188919 : Nat := 118140960795 + 188919 * 2 ^ 59
def prefixEnd_188919 : Nat := 4983230072969 + 3 ^ 40 * 188919 * 2
def baseEnd_188919 : Nat := 97006251766851587243683

theorem tailTrace_188919 : CollatzResearch.WordTrace tailWord_188919 prefixEnd_188919 97006251766851587243683 := by
  unfold tailWord_188919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890442002586202641577811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4593628001724135094385207 6890442002586202641577811)
  ·
    refine ⟨10335663003879303962366717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6890442002586202641577811 10335663003879303962366717)
    ·
      refine ⟨3875873626454738985887519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10335663003879303962366717 3875873626454738985887519)
      ·
        refine ⟨5813810439682108478831279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3875873626454738985887519 5813810439682108478831279)
        ·
          refine ⟨8720715659523162718246919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5813810439682108478831279 8720715659523162718246919)
          ·
            refine ⟨13081073489284744077370379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720715659523162718246919 13081073489284744077370379)
            ·
              refine ⟨19621610233927116116055569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13081073489284744077370379 19621610233927116116055569)
              ·
                refine ⟨14716207675445337087041677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19621610233927116116055569 14716207675445337087041677)
                ·
                  refine ⟨5518577878292001407640629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14716207675445337087041677 5518577878292001407640629)
                  ·
                    refine ⟨517366676089875131966309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5518577878292001407640629 517366676089875131966309)
                    ·
                      refine ⟨97006251766851587243683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 517366676089875131966309 97006251766851587243683)
                      ·
                        rfl

theorem cell23_188919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_188919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188919 prefixEnd_188919 := by exact prefixLift 188919
  have htrace : WordTrace (prefixWord ++ tailWord_188919) baseStart_188919 baseEnd_188919 := by
    simpa [prefixWord, tailWord_188919, baseEnd_188919] using wordTrace_append hprefix tailTrace_188919
  have hstable : (prefixWord ++ tailWord_188919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188919).length < 2 ^ (prefixWord ++ tailWord_188919).sum := by decide
  have hdescent : baseEnd_188919 < baseStart_188919 := by decide
  rcases family_descends (prefixWord ++ tailWord_188919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188934 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_188934 : Nat := 118140960795 + 188934 * 2 ^ 59
def prefixEnd_188934 : Nat := 4983230072969 + 3 ^ 40 * 188934 * 2
def baseEnd_188934 : Nat := 97013953976669028556115

theorem tailTrace_188934 : CollatzResearch.WordTrace tailWord_188934 prefixEnd_188934 97013953976669028556115 := by
  unfold tailWord_188934
  simp only [CollatzResearch.WordTrace]
  refine ⟨215343409297870631355433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4593992731687906802249237 215343409297870631355433)
  ·
    refine ⟨161507556973402973516575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215343409297870631355433 161507556973402973516575)
    ·
      refine ⟨242261335460104460274863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161507556973402973516575 242261335460104460274863)
      ·
        refine ⟨363392003190156690412295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242261335460104460274863 363392003190156690412295)
        ·
          refine ⟨545088004785235035618443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 363392003190156690412295 545088004785235035618443)
          ·
            refine ⟨817632007177852553427665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545088004785235035618443 817632007177852553427665)
            ·
              refine ⟨613224005383389415070749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817632007177852553427665 613224005383389415070749)
              ·
                refine ⟨229959002018771030651531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613224005383389415070749 229959002018771030651531)
                ·
                  refine ⟨344938503028156545977297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229959002018771030651531 344938503028156545977297)
                  ·
                    refine ⟨258703877271117409482973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 344938503028156545977297 258703877271117409482973)
                    ·
                      refine ⟨97013953976669028556115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258703877271117409482973 97013953976669028556115)
                      ·
                        rfl

theorem cell23_188934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_188934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188934 prefixEnd_188934 := by exact prefixLift 188934
  have htrace : WordTrace (prefixWord ++ tailWord_188934) baseStart_188934 baseEnd_188934 := by
    simpa [prefixWord, tailWord_188934, baseEnd_188934] using wordTrace_append hprefix tailTrace_188934
  have hstable : (prefixWord ++ tailWord_188934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188934).length < 2 ^ (prefixWord ++ tailWord_188934).sum := by decide
  have hdescent : baseEnd_188934 < baseStart_188934 := by decide
  rcases family_descends (prefixWord ++ tailWord_188934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188940 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_188940 : Nat := 118140960795 + 188940 * 2 ^ 59
def prefixEnd_188940 : Nat := 4983230072969 + 3 ^ 40 * 188940 * 2
def baseEnd_188940 : Nat := 97017034860596005081087

theorem tailTrace_188940 : CollatzResearch.WordTrace tailWord_188940 prefixEnd_188940 97017034860596005081087 := by
  unfold tailWord_188940
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445603967755061614046137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4594138623673415485394849 3445603967755061614046137)
  ·
    refine ⟨2584202975816296210534603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3445603967755061614046137 2584202975816296210534603)
    ·
      refine ⟨3876304463724444315801905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2584202975816296210534603 3876304463724444315801905)
      ·
        refine ⟨2907228347793333236851429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3876304463724444315801905 2907228347793333236851429)
        ·
          refine ⟨545105315211249981909643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2907228347793333236851429 545105315211249981909643)
          ·
            refine ⟨817657972816874972864465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545105315211249981909643 817657972816874972864465)
            ·
              refine ⟨613243479612656229648349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 817657972816874972864465 613243479612656229648349)
              ·
                refine ⟨229966304854746086118131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 613243479612656229648349 229966304854746086118131)
                ·
                  refine ⟨344949457282119129177197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229966304854746086118131 344949457282119129177197)
                  ·
                    refine ⟨129356046480794673441449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 344949457282119129177197 129356046480794673441449)
                    ·
                      refine ⟨97017034860596005081087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129356046480794673441449 97017034860596005081087)
                      ·
                        rfl

theorem cell23_188940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_188940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188940 prefixEnd_188940 := by exact prefixLift 188940
  have htrace : WordTrace (prefixWord ++ tailWord_188940) baseStart_188940 baseEnd_188940 := by
    simpa [prefixWord, tailWord_188940, baseEnd_188940] using wordTrace_append hprefix tailTrace_188940
  have hstable : (prefixWord ++ tailWord_188940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188940).length < 2 ^ (prefixWord ++ tailWord_188940).sum := by decide
  have hdescent : baseEnd_188940 < baseStart_188940 := by decide
  rcases family_descends (prefixWord ++ tailWord_188940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_188974 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_188974 : Nat := 118140960795 + 188974 * 2 ^ 59
def prefixEnd_188974 : Nat := 4983230072969 + 3 ^ 40 * 188974 * 2
def baseEnd_188974 : Nat := 97034493202848872055931

theorem tailTrace_188974 : CollatzResearch.WordTrace tailWord_188974 prefixEnd_188974 97034493202848872055931 := by
  unfold tailWord_188974
  simp only [CollatzResearch.WordTrace]
  refine ⟨861556002173368379353747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4594965344924631356553317 861556002173368379353747)
  ·
    refine ⟨1292334003260052569030621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861556002173368379353747 1292334003260052569030621)
    ·
      refine ⟨484625251222519713386483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1292334003260052569030621 484625251222519713386483)
      ·
        refine ⟨726937876833779570079725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484625251222519713386483 726937876833779570079725)
        ·
          refine ⟨272601703812667338779897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726937876833779570079725 272601703812667338779897)
          ·
            refine ⟨204451277859500504084923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272601703812667338779897 204451277859500504084923)
            ·
              refine ⟨306676916789250756127385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204451277859500504084923 306676916789250756127385)
              ·
                refine ⟨230007687591938067095539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306676916789250756127385 230007687591938067095539)
                ·
                  refine ⟨345011531387907100643309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230007687591938067095539 345011531387907100643309)
                  ·
                    refine ⟨129379324270465162741241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345011531387907100643309 129379324270465162741241)
                    ·
                      refine ⟨97034493202848872055931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129379324270465162741241 97034493202848872055931)
                      ·
                        rfl

theorem cell23_188974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_188974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_188974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_188974 prefixEnd_188974 := by exact prefixLift 188974
  have htrace : WordTrace (prefixWord ++ tailWord_188974) baseStart_188974 baseEnd_188974 := by
    simpa [prefixWord, tailWord_188974, baseEnd_188974] using wordTrace_append hprefix tailTrace_188974
  have hstable : (prefixWord ++ tailWord_188974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_188974).length < 2 ^ (prefixWord ++ tailWord_188974).sum := by decide
  have hdescent : baseEnd_188974 < baseStart_188974 := by decide
  rcases family_descends (prefixWord ++ tailWord_188974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189013 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_189013 : Nat := 118140960795 + 189013 * 2 ^ 59
def prefixEnd_189013 : Nat := 4983230072969 + 3 ^ 40 * 189013 * 2
def baseEnd_189013 : Nat := 97054518948374219468251

theorem tailTrace_189013 : CollatzResearch.WordTrace tailWord_189013 prefixEnd_189013 97054518948374219468251 := by
  unfold tailWord_189013
  simp only [CollatzResearch.WordTrace]
  refine ⟨6893870464245656695499693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4595913642830437796999795 6893870464245656695499693)
  ·
    refine ⟨2585201424092121260812385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6893870464245656695499693 2585201424092121260812385)
    ·
      refine ⟨1938901068069090945609289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2585201424092121260812385 1938901068069090945609289)
      ·
        refine ⟨1454175801051818209206967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1938901068069090945609289 1454175801051818209206967)
        ·
          refine ⟨2181263701577727313810451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454175801051818209206967 2181263701577727313810451)
          ·
            refine ⟨3271895552366590970715677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181263701577727313810451 3271895552366590970715677)
            ·
              refine ⟨1226960832137471614018379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3271895552366590970715677 1226960832137471614018379)
              ·
                refine ⟨1840441248206207421027569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226960832137471614018379 1840441248206207421027569)
                ·
                  refine ⟨1380330936154655565770677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840441248206207421027569 1380330936154655565770677)
                  ·
                    refine ⟨129406025264498959291001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1380330936154655565770677 129406025264498959291001)
                    ·
                      refine ⟨97054518948374219468251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129406025264498959291001 97054518948374219468251)
                      ·
                        rfl

theorem cell23_189013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_189013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189013 prefixEnd_189013 := by exact prefixLift 189013
  have htrace : WordTrace (prefixWord ++ tailWord_189013) baseStart_189013 baseEnd_189013 := by
    simpa [prefixWord, tailWord_189013, baseEnd_189013] using wordTrace_append hprefix tailTrace_189013
  have hstable : (prefixWord ++ tailWord_189013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189013).length < 2 ^ (prefixWord ++ tailWord_189013).sum := by decide
  have hdescent : baseEnd_189013 < baseStart_189013 := by decide
  rcases family_descends (prefixWord ++ tailWord_189013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189016 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_189016 : Nat := 118140960795 + 189016 * 2 ^ 59
def prefixEnd_189016 : Nat := 4983230072969 + 3 ^ 40 * 189016 * 2
def baseEnd_189016 : Nat := 97056059390337707730737

theorem tailTrace_189016 : CollatzResearch.WordTrace tailWord_189016 prefixEnd_189016 97056059390337707730737 := by
  unfold tailWord_189016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446989941617394103929451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4595986588823192138572601 3446989941617394103929451)
  ·
    refine ⟨5170484912426091155894177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3446989941617394103929451 5170484912426091155894177)
    ·
      refine ⟨3877863684319568366920633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5170484912426091155894177 3877863684319568366920633)
      ·
        refine ⟨2908397763239676275190475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3877863684319568366920633 2908397763239676275190475)
        ·
          refine ⟨4362596644859514412785713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2908397763239676275190475 4362596644859514412785713)
          ·
            refine ⟨3271947483644635809589285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4362596644859514412785713 3271947483644635809589285)
            ·
              refine ⟨613490153183369214297991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3271947483644635809589285 613490153183369214297991)
              ·
                refine ⟨920235229775053821446987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613490153183369214297991 920235229775053821446987)
                ·
                  refine ⟨1380352844662580732170481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920235229775053821446987 1380352844662580732170481)
                  ·
                    refine ⟨1035264633496935549127861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1380352844662580732170481 1035264633496935549127861)
                    ·
                      refine ⟨97056059390337707730737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1035264633496935549127861 97056059390337707730737)
                      ·
                        rfl

theorem cell23_189016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_189016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189016 prefixEnd_189016 := by exact prefixLift 189016
  have htrace : WordTrace (prefixWord ++ tailWord_189016) baseStart_189016 baseEnd_189016 := by
    simpa [prefixWord, tailWord_189016, baseEnd_189016] using wordTrace_append hprefix tailTrace_189016
  have hstable : (prefixWord ++ tailWord_189016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189016).length < 2 ^ (prefixWord ++ tailWord_189016).sum := by decide
  have hdescent : baseEnd_189016 < baseStart_189016 := by decide
  rcases family_descends (prefixWord ++ tailWord_189016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189020 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_189020 : Nat := 118140960795 + 189020 * 2 ^ 59
def prefixEnd_189020 : Nat := 4983230072969 + 3 ^ 40 * 189020 * 2
def baseEnd_189020 : Nat := 97058113312955692080719

theorem tailTrace_189020 : CollatzResearch.WordTrace tailWord_189020 prefixEnd_189020 97058113312955692080719 := by
  unfold tailWord_189020
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447062887610148445502257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4596083850146864594003009 3447062887610148445502257)
  ·
    refine ⟨2585297165707611334126693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3447062887610148445502257 2585297165707611334126693)
    ·
      refine ⟨484743218570177125148755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2585297165707611334126693 484743218570177125148755)
      ·
        refine ⟨727114827855265687723133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484743218570177125148755 727114827855265687723133)
        ·
          refine ⟨272668060445724632896175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727114827855265687723133 272668060445724632896175)
          ·
            refine ⟨409002090668586949344263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272668060445724632896175 409002090668586949344263)
            ·
              refine ⟨613503136002880424016395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409002090668586949344263 613503136002880424016395)
              ·
                refine ⟨920254704004320636024593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 613503136002880424016395 920254704004320636024593)
                ·
                  refine ⟨690191028003240477018445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920254704004320636024593 690191028003240477018445)
                  ·
                    refine ⟨258821635501215178881917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690191028003240477018445 258821635501215178881917)
                    ·
                      refine ⟨97058113312955692080719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258821635501215178881917 97058113312955692080719)
                      ·
                        rfl

theorem cell23_189020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_189020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189020 prefixEnd_189020 := by exact prefixLift 189020
  have htrace : WordTrace (prefixWord ++ tailWord_189020) baseStart_189020 baseEnd_189020 := by
    simpa [prefixWord, tailWord_189020, baseEnd_189020] using wordTrace_append hprefix tailTrace_189020
  have hstable : (prefixWord ++ tailWord_189020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189020).length < 2 ^ (prefixWord ++ tailWord_189020).sum := by decide
  have hdescent : baseEnd_189020 < baseStart_189020 := by decide
  rcases family_descends (prefixWord ++ tailWord_189020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189040 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 2, 5]
def baseStart_189040 : Nat := 118140960795 + 189040 * 2 ^ 59
def prefixEnd_189040 : Nat := 4983230072969 + 3 ^ 40 * 189040 * 2
def baseEnd_189040 : Nat := 32356127642015204610209

theorem tailTrace_189040 : CollatzResearch.WordTrace tailWord_189040 prefixEnd_189040 32356127642015204610209 := by
  unfold tailWord_189040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447427617573920153366287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4596570156765226871155049 3447427617573920153366287)
  ·
    refine ⟨5171141426360880230049431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447427617573920153366287 5171141426360880230049431)
    ·
      refine ⟨7756712139541320345074147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171141426360880230049431 7756712139541320345074147)
      ·
        refine ⟨11635068209311980517611221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7756712139541320345074147 11635068209311980517611221)
        ·
          refine ⟨272696911155749543381513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11635068209311980517611221 272696911155749543381513)
          ·
            refine ⟨204522683366812157536135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272696911155749543381513 204522683366812157536135)
            ·
              refine ⟨306784025050218236304203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204522683366812157536135 306784025050218236304203)
              ·
                refine ⟨460176037575327354456305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306784025050218236304203 460176037575327354456305)
                ·
                  refine ⟨345132028181495515842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460176037575327354456305 345132028181495515842229)
                  ·
                    refine ⟨32356127642015204610209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 345132028181495515842229 32356127642015204610209)
                    ·
                      rfl

theorem cell23_189040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 5].length) (baseStart_189040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189040 prefixEnd_189040 := by exact prefixLift 189040
  have htrace : WordTrace (prefixWord ++ tailWord_189040) baseStart_189040 baseEnd_189040 := by
    simpa [prefixWord, tailWord_189040, baseEnd_189040] using wordTrace_append hprefix tailTrace_189040
  have hstable : (prefixWord ++ tailWord_189040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189040).length < 2 ^ (prefixWord ++ tailWord_189040).sum := by decide
  have hdescent : baseEnd_189040 < baseStart_189040 := by decide
  rcases family_descends (prefixWord ++ tailWord_189040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189056 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_189056 : Nat := 118140960795 + 189056 * 2 ^ 59
def prefixEnd_189056 : Nat := 4983230072969 + 3 ^ 40 * 189056 * 2
def baseEnd_189056 : Nat := 97076598616517551230553

theorem tailTrace_189056 : CollatzResearch.WordTrace tailWord_189056 prefixEnd_189056 97076598616517551230553 := by
  unfold tailWord_189056
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447719401544937519657511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4596959202059916692876681 3447719401544937519657511)
  ·
    refine ⟨5171579102317406279486267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3447719401544937519657511 5171579102317406279486267)
    ·
      refine ⟨7757368653476109419229401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171579102317406279486267 7757368653476109419229401)
      ·
        refine ⟨5818026490107082064422051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7757368653476109419229401 5818026490107082064422051)
        ·
          refine ⟨8727039735160623096633077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5818026490107082064422051 8727039735160623096633077)
          ·
            refine ⟨818159975171308415309351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8727039735160623096633077 818159975171308415309351)
            ·
              refine ⟨1227239962756962622964027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818159975171308415309351 1227239962756962622964027)
              ·
                refine ⟨1840859944135443934446041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227239962756962622964027 1840859944135443934446041)
                ·
                  refine ⟨1380644958101582950834531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840859944135443934446041 1380644958101582950834531)
                  ·
                    refine ⟨2070967437152374426251797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1380644958101582950834531 2070967437152374426251797)
                    ·
                      refine ⟨97076598616517551230553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2070967437152374426251797 97076598616517551230553)
                      ·
                        rfl

theorem cell23_189056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_189056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189056 prefixEnd_189056 := by exact prefixLift 189056
  have htrace : WordTrace (prefixWord ++ tailWord_189056) baseStart_189056 baseEnd_189056 := by
    simpa [prefixWord, tailWord_189056, baseEnd_189056] using wordTrace_append hprefix tailTrace_189056
  have hstable : (prefixWord ++ tailWord_189056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189056).length < 2 ^ (prefixWord ++ tailWord_189056).sum := by decide
  have hdescent : baseEnd_189056 < baseStart_189056 := by decide
  rcases family_descends (prefixWord ++ tailWord_189056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189060 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_189060 : Nat := 118140960795 + 189060 * 2 ^ 59
def prefixEnd_189060 : Nat := 4983230072969 + 3 ^ 40 * 189060 * 2
def baseEnd_189060 : Nat := 97078652539135535580535

theorem tailTrace_189060 : CollatzResearch.WordTrace tailWord_189060 prefixEnd_189060 97078652539135535580535 := by
  unfold tailWord_189060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3447792347537691861230317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4597056463383589148307089 3447792347537691861230317)
  ·
    refine ⟨1292922130326634447961369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3447792347537691861230317 1292922130326634447961369)
    ·
      refine ⟨969691597744975835971027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292922130326634447961369 969691597744975835971027)
      ·
        refine ⟨1454537396617463753956541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969691597744975835971027 1454537396617463753956541)
        ·
          refine ⟨545451523731548907733703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1454537396617463753956541 545451523731548907733703)
          ·
            refine ⟨818177285597323361600555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 545451523731548907733703 818177285597323361600555)
            ·
              refine ⟨1227265928395985042400833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818177285597323361600555 1227265928395985042400833)
              ·
                refine ⟨920449446296988781800625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227265928395985042400833 920449446296988781800625)
                ·
                  refine ⟨690337084722741586350469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 920449446296988781800625 690337084722741586350469)
                  ·
                    refine ⟨129438203385514047440713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 690337084722741586350469 129438203385514047440713)
                    ·
                      refine ⟨97078652539135535580535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129438203385514047440713 97078652539135535580535)
                      ·
                        rfl

theorem cell23_189060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_189060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189060 prefixEnd_189060 := by exact prefixLift 189060
  have htrace : WordTrace (prefixWord ++ tailWord_189060) baseStart_189060 baseEnd_189060 := by
    simpa [prefixWord, tailWord_189060, baseEnd_189060] using wordTrace_append hprefix tailTrace_189060
  have hstable : (prefixWord ++ tailWord_189060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189060).length < 2 ^ (prefixWord ++ tailWord_189060).sum := by decide
  have hdescent : baseEnd_189060 < baseStart_189060 := by decide
  rcases family_descends (prefixWord ++ tailWord_189060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189063 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_189063 : Nat := 118140960795 + 189063 * 2 ^ 59
def prefixEnd_189063 : Nat := 4983230072969 + 3 ^ 40 * 189063 * 2
def baseEnd_189063 : Nat := 97080192981099023843021

theorem tailTrace_189063 : CollatzResearch.WordTrace tailWord_189063 prefixEnd_189063 97080192981099023843021 := by
  unfold tailWord_189063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895694114064515234819843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4597129409376343489879895 6895694114064515234819843)
  ·
    refine ⟨10343541171096772852229765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6895694114064515234819843 10343541171096772852229765)
    ·
      refine ⟨1939413969580644909793081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10343541171096772852229765 1939413969580644909793081)
      ·
        refine ⟨1454560477185483682344811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1939413969580644909793081 1454560477185483682344811)
        ·
          refine ⟨2181840715778225523517217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454560477185483682344811 2181840715778225523517217)
          ·
            refine ⟨1636380536833669142637913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181840715778225523517217 1636380536833669142637913)
            ·
              refine ⟨1227285402625251856978435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636380536833669142637913 1227285402625251856978435)
              ·
                refine ⟨1840928103937877785467653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227285402625251856978435 1840928103937877785467653)
                ·
                  refine ⟨345174019488352084775185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1840928103937877785467653 345174019488352084775185)
                  ·
                    refine ⟨258880514616264063581389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 345174019488352084775185 258880514616264063581389)
                    ·
                      refine ⟨97080192981099023843021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 258880514616264063581389 97080192981099023843021)
                      ·
                        rfl

theorem cell23_189063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_189063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189063 prefixEnd_189063 := by exact prefixLift 189063
  have htrace : WordTrace (prefixWord ++ tailWord_189063) baseStart_189063 baseEnd_189063 := by
    simpa [prefixWord, tailWord_189063, baseEnd_189063] using wordTrace_append hprefix tailTrace_189063
  have hstable : (prefixWord ++ tailWord_189063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189063).length < 2 ^ (prefixWord ++ tailWord_189063).sum := by decide
  have hdescent : baseEnd_189063 < baseStart_189063 := by decide
  rcases family_descends (prefixWord ++ tailWord_189063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189070 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_189070 : Nat := 118140960795 + 189070 * 2 ^ 59
def prefixEnd_189070 : Nat := 4983230072969 + 3 ^ 40 * 189070 * 2
def baseEnd_189070 : Nat := 32361262448560165485163

theorem tailTrace_189070 : CollatzResearch.WordTrace tailWord_189070 prefixEnd_189070 32361262448560165485163 := by
  unfold tailWord_189070
  simp only [CollatzResearch.WordTrace]
  refine ⟨861993678129894428790583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4597299616692770286883109 861993678129894428790583)
  ·
    refine ⟨1292990517194841643185875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 861993678129894428790583 1292990517194841643185875)
    ·
      refine ⟨1939485775792262464778813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292990517194841643185875 1939485775792262464778813)
      ·
        refine ⟨727307165922098424292055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1939485775792262464778813 727307165922098424292055)
        ·
          refine ⟨1090960748883147636438083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727307165922098424292055 1090960748883147636438083)
          ·
            refine ⟨1636441123324721454657125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090960748883147636438083 1636441123324721454657125)
            ·
              refine ⟨306832710623385272748211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1636441123324721454657125 306832710623385272748211)
              ·
                refine ⟨460249065935077909122317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306832710623385272748211 460249065935077909122317)
                ·
                  refine ⟨172593399725654215920869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460249065935077909122317 172593399725654215920869)
                  ·
                    refine ⟨32361262448560165485163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172593399725654215920869 32361262448560165485163)
                    ·
                      rfl

theorem cell23_189070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_189070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189070 prefixEnd_189070 := by exact prefixLift 189070
  have htrace : WordTrace (prefixWord ++ tailWord_189070) baseStart_189070 baseEnd_189070 := by
    simpa [prefixWord, tailWord_189070, baseEnd_189070] using wordTrace_append hprefix tailTrace_189070
  have hstable : (prefixWord ++ tailWord_189070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189070).length < 2 ^ (prefixWord ++ tailWord_189070).sum := by decide
  have hdescent : baseEnd_189070 < baseStart_189070 := by decide
  rcases family_descends (prefixWord ++ tailWord_189070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189120 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2]
def baseStart_189120 : Nat := 118140960795 + 189120 * 2 ^ 59
def prefixEnd_189120 : Nat := 4983230072969 + 3 ^ 40 * 189120 * 2
def baseEnd_189120 : Nat := 97109461378405300830259

theorem tailTrace_189120 : CollatzResearch.WordTrace tailWord_189120 prefixEnd_189120 97109461378405300830259 := by
  unfold tailWord_189120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3448886537429006984822407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4598515383238675979763209 3448886537429006984822407)
  ·
    refine ⟨5173329806143510477233611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3448886537429006984822407 5173329806143510477233611)
    ·
      refine ⟨7759994709215265715850417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5173329806143510477233611 7759994709215265715850417)
      ·
        refine ⟨5819996031911449286887813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7759994709215265715850417 5819996031911449286887813)
        ·
          refine ⟨1091249255983396741291465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5819996031911449286887813 1091249255983396741291465)
          ·
            refine ⟨818436941987547555968599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091249255983396741291465 818436941987547555968599)
            ·
              refine ⟨1227655412981321333952899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 818436941987547555968599 1227655412981321333952899)
              ·
                refine ⟨1841483119471982000929349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227655412981321333952899 1841483119471982000929349)
                ·
                  refine ⟨345278084900996625174253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1841483119471982000929349 345278084900996625174253)
                  ·
                    refine ⟨129479281837873734440345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 345278084900996625174253 129479281837873734440345)
                    ·
                      refine ⟨97109461378405300830259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129479281837873734440345 97109461378405300830259)
                      ·
                        rfl

theorem cell23_189120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_189120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189120 prefixEnd_189120 := by exact prefixLift 189120
  have htrace : WordTrace (prefixWord ++ tailWord_189120) baseStart_189120 baseEnd_189120 := by
    simpa [prefixWord, tailWord_189120, baseEnd_189120] using wordTrace_append hprefix tailTrace_189120
  have hstable : (prefixWord ++ tailWord_189120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189120).length < 2 ^ (prefixWord ++ tailWord_189120).sum := by decide
  have hdescent : baseEnd_189120 < baseStart_189120 := by decide
  rcases family_descends (prefixWord ++ tailWord_189120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189121 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_189121 : Nat := 118140960795 + 189121 * 2 ^ 59
def prefixEnd_189121 : Nat := 4983230072969 + 3 ^ 40 * 189121 * 2
def baseEnd_189121 : Nat := 32369991619686598972585

theorem tailTrace_189121 : CollatzResearch.WordTrace tailWord_189121 prefixEnd_189121 32369991619686598972585 := by
  unfold tailWord_189121
  simp only [CollatzResearch.WordTrace]
  refine ⟨6897809547854391140431217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4598539698569594093620811 6897809547854391140431217)
  ·
    refine ⟨5173357160890793355323413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6897809547854391140431217 5173357160890793355323413)
    ·
      refine ⟨242501116916755938530785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5173357160890793355323413 242501116916755938530785)
      ·
        refine ⟨181875837687566953898089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242501116916755938530785 181875837687566953898089)
        ·
          refine ⟨136406878265675215423567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181875837687566953898089 136406878265675215423567)
          ·
            refine ⟨204610317398512823135351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136406878265675215423567 204610317398512823135351)
            ·
              refine ⟨306915476097769234703027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204610317398512823135351 306915476097769234703027)
              ·
                refine ⟨460373214146653852054541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306915476097769234703027 460373214146653852054541)
                ·
                  refine ⟨172639955304995194520453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 460373214146653852054541 172639955304995194520453)
                  ·
                    refine ⟨32369991619686598972585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172639955304995194520453 32369991619686598972585)
                    ·
                      rfl

theorem cell23_189121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_189121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189121 prefixEnd_189121 := by exact prefixLift 189121
  have htrace : WordTrace (prefixWord ++ tailWord_189121) baseStart_189121 baseEnd_189121 := by
    simpa [prefixWord, tailWord_189121, baseEnd_189121] using wordTrace_append hprefix tailTrace_189121
  have hstable : (prefixWord ++ tailWord_189121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189121).length < 2 ^ (prefixWord ++ tailWord_189121).sum := by decide
  have hdescent : baseEnd_189121 < baseStart_189121 := by decide
  rcases family_descends (prefixWord ++ tailWord_189121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189136 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_189136 : Nat := 118140960795 + 189136 * 2 ^ 59
def prefixEnd_189136 : Nat := 4983230072969 + 3 ^ 40 * 189136 * 2
def baseEnd_189136 : Nat := 97117677068877238230185

theorem tailTrace_189136 : CollatzResearch.WordTrace tailWord_189136 prefixEnd_189136 97117677068877238230185 := by
  unfold tailWord_189136
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449178321400024351113631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4598904428533365801484841 3449178321400024351113631)
  ·
    refine ⟨5173767482100036526670447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3449178321400024351113631 5173767482100036526670447)
    ·
      refine ⟨7760651223150054790005671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5173767482100036526670447 7760651223150054790005671)
      ·
        refine ⟨11640976834725082185008507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7760651223150054790005671 11640976834725082185008507)
        ·
          refine ⟨17461465252087623277512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11640976834725082185008507 17461465252087623277512761)
          ·
            refine ⟨13096098939065717458134571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17461465252087623277512761 13096098939065717458134571)
            ·
              refine ⟨19644148408598576187201857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13096098939065717458134571 19644148408598576187201857)
              ·
                refine ⟨14733111306448932140401393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19644148408598576187201857 14733111306448932140401393)
                ·
                  refine ⟨11049833479836699105301045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14733111306448932140401393 11049833479836699105301045)
                  ·
                    refine ⟨1035921888734690541121973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11049833479836699105301045 1035921888734690541121973)
                    ·
                      refine ⟨97117677068877238230185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1035921888734690541121973 97117677068877238230185)
                      ·
                        rfl

theorem cell23_189136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_189136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189136 prefixEnd_189136 := by exact prefixLift 189136
  have htrace : WordTrace (prefixWord ++ tailWord_189136) baseStart_189136 baseEnd_189136 := by
    simpa [prefixWord, tailWord_189136, baseEnd_189136] using wordTrace_append hprefix tailTrace_189136
  have hstable : (prefixWord ++ tailWord_189136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189136).length < 2 ^ (prefixWord ++ tailWord_189136).sum := by decide
  have hdescent : baseEnd_189136 < baseStart_189136 := by decide
  rcases family_descends (prefixWord ++ tailWord_189136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189160 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 6]
def baseStart_189160 : Nat := 118140960795 + 189160 * 2 ^ 59
def prefixEnd_189160 : Nat := 4983230072969 + 3 ^ 40 * 189160 * 2
def baseEnd_189160 : Nat := 32376666868195048110025

theorem tailTrace_189160 : CollatzResearch.WordTrace tailWord_189160 prefixEnd_189160 32376666868195048110025 := by
  unfold tailWord_189160
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449615997356550400550467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4599487996475400534067289 3449615997356550400550467)
  ·
    refine ⟨5174423996034825600825701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3449615997356550400550467 5174423996034825600825701)
    ·
      refine ⟨970204499256529800154819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5174423996034825600825701 970204499256529800154819)
      ·
        refine ⟨1455306748884794700232229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970204499256529800154819 1455306748884794700232229)
        ·
          refine ⟨272870015415899006293543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1455306748884794700232229 272870015415899006293543)
          ·
            refine ⟨409305023123848509440315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272870015415899006293543 409305023123848509440315)
            ·
              refine ⟨613957534685772764160473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409305023123848509440315 613957534685772764160473)
              ·
                refine ⟨460468151014329573120355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 613957534685772764160473 460468151014329573120355)
                ·
                  refine ⟨690702226521494359680533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460468151014329573120355 690702226521494359680533)
                  ·
                    refine ⟨32376666868195048110025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 690702226521494359680533 32376666868195048110025)
                    ·
                      rfl

theorem cell23_189160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_189160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189160 prefixEnd_189160 := by exact prefixLift 189160
  have htrace : WordTrace (prefixWord ++ tailWord_189160) baseStart_189160 baseEnd_189160 := by
    simpa [prefixWord, tailWord_189160, baseEnd_189160] using wordTrace_append hprefix tailTrace_189160
  have hstable : (prefixWord ++ tailWord_189160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189160).length < 2 ^ (prefixWord ++ tailWord_189160).sum := by decide
  have hdescent : baseEnd_189160 < baseStart_189160 := by decide
  rcases family_descends (prefixWord ++ tailWord_189160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189167 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 1, 1, 4]
def baseStart_189167 : Nat := 118140960795 + 189167 * 2 ^ 59
def prefixEnd_189167 : Nat := 4983230072969 + 3 ^ 40 * 189167 * 2
def baseEnd_189167 : Nat := 97133594969166616942543

theorem tailTrace_189167 : CollatzResearch.WordTrace tailWord_189167 prefixEnd_189167 97133594969166616942543 := by
  unfold tailWord_189167
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899487305687740996605755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4599658203791827331070503 6899487305687740996605755)
  ·
    refine ⟨10349230958531611494908633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899487305687740996605755 10349230958531611494908633)
    ·
      refine ⟨7761923218898708621181475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10349230958531611494908633 7761923218898708621181475)
      ·
        refine ⟨11642884828348062931772213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7761923218898708621181475 11642884828348062931772213)
        ·
          refine ⟨1091520452657630899853645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11642884828348062931772213 1091520452657630899853645)
          ·
            refine ⟨409320169746611587445117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1091520452657630899853645 409320169746611587445117)
            ·
              refine ⟨153495063654979345291919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409320169746611587445117 153495063654979345291919)
              ·
                refine ⟨230242595482469017937879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153495063654979345291919 230242595482469017937879)
                ·
                  refine ⟨345363893223703526906819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230242595482469017937879 345363893223703526906819)
                  ·
                    refine ⟨518045839835555290360229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345363893223703526906819 518045839835555290360229)
                    ·
                      refine ⟨97133594969166616942543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 518045839835555290360229 97133594969166616942543)
                      ·
                        rfl

theorem cell23_189167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 1, 1, 4].length) (baseStart_189167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189167 prefixEnd_189167 := by exact prefixLift 189167
  have htrace : WordTrace (prefixWord ++ tailWord_189167) baseStart_189167 baseEnd_189167 := by
    simpa [prefixWord, tailWord_189167, baseEnd_189167] using wordTrace_append hprefix tailTrace_189167
  have hstable : (prefixWord ++ tailWord_189167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189167).length < 2 ^ (prefixWord ++ tailWord_189167).sum := by decide
  have hdescent : baseEnd_189167 < baseStart_189167 := by decide
  rcases family_descends (prefixWord ++ tailWord_189167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189170 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_189170 : Nat := 118140960795 + 189170 * 2 ^ 59
def prefixEnd_189170 : Nat := 4983230072969 + 3 ^ 40 * 189170 * 2
def baseEnd_189170 : Nat := 97135135411130105205029

theorem tailTrace_189170 : CollatzResearch.WordTrace tailWord_189170 prefixEnd_189170 97135135411130105205029 := by
  unfold tailWord_189170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1724899181169218127241241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4599731149784581672643309 1724899181169218127241241)
  ·
    refine ⟨1293674385876913595430931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1724899181169218127241241 1293674385876913595430931)
    ·
      refine ⟨1940511578815370393146397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1293674385876913595430931 1940511578815370393146397)
      ·
        refine ⟨727691842055763897429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1940511578815370393146397 727691842055763897429899)
        ·
          refine ⟨1091537763083645846144849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 727691842055763897429899 1091537763083645846144849)
          ·
            refine ⟨818653322312734384608637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1091537763083645846144849 818653322312734384608637)
            ·
              refine ⟨306994995867275394228239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 818653322312734384608637 306994995867275394228239)
              ·
                refine ⟨460492493800913091342359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306994995867275394228239 460492493800913091342359)
                ·
                  refine ⟨690738740701369637013539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460492493800913091342359 690738740701369637013539)
                  ·
                    refine ⟨1036108111052054455520309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 690738740701369637013539 1036108111052054455520309)
                    ·
                      refine ⟨97135135411130105205029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1036108111052054455520309 97135135411130105205029)
                      ·
                        rfl

theorem cell23_189170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_189170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189170 prefixEnd_189170 := by exact prefixLift 189170
  have htrace : WordTrace (prefixWord ++ tailWord_189170) baseStart_189170 baseEnd_189170 := by
    simpa [prefixWord, tailWord_189170, baseEnd_189170] using wordTrace_append hprefix tailTrace_189170
  have hstable : (prefixWord ++ tailWord_189170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189170).length < 2 ^ (prefixWord ++ tailWord_189170).sum := by decide
  have hdescent : baseEnd_189170 < baseStart_189170 := by decide
  rcases family_descends (prefixWord ++ tailWord_189170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189183 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3]
def baseStart_189183 : Nat := 118140960795 + 189183 * 2 ^ 59
def prefixEnd_189183 : Nat := 4983230072969 + 3 ^ 40 * 189183 * 2
def baseEnd_189183 : Nat := 97141810659638554342469

theorem tailTrace_189183 : CollatzResearch.WordTrace tailWord_189183 prefixEnd_189183 97141810659638554342469 := by
  unfold tailWord_189183
  simp only [CollatzResearch.WordTrace]
  refine ⟨6900070873629775729188203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4600047249086517152792135 6900070873629775729188203)
  ·
    refine ⟨10350106310444663593782305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6900070873629775729188203 10350106310444663593782305)
    ·
      refine ⟨7762579732833497695336729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10350106310444663593782305 7762579732833497695336729)
      ·
        refine ⟨5821934799625123271502547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7762579732833497695336729 5821934799625123271502547)
        ·
          refine ⟨8732902199437684907253821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5821934799625123271502547 8732902199437684907253821)
          ·
            refine ⟨3274838324789131840220183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8732902199437684907253821 3274838324789131840220183)
            ·
              refine ⟨4912257487183697760330275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3274838324789131840220183 4912257487183697760330275)
              ·
                refine ⟨7368386230775546640495413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4912257487183697760330275 7368386230775546640495413)
                ·
                  refine ⟨690786209135207497546445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7368386230775546640495413 690786209135207497546445)
                  ·
                    refine ⟨259044828425702811579917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 690786209135207497546445 259044828425702811579917)
                    ·
                      refine ⟨97141810659638554342469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 259044828425702811579917 97141810659638554342469)
                      ·
                        rfl

theorem cell23_189183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 3].length) (baseStart_189183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189183 prefixEnd_189183 := by exact prefixLift 189183
  have htrace : WordTrace (prefixWord ++ tailWord_189183) baseStart_189183 baseEnd_189183 := by
    simpa [prefixWord, tailWord_189183, baseEnd_189183] using wordTrace_append hprefix tailTrace_189183
  have hstable : (prefixWord ++ tailWord_189183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189183).length < 2 ^ (prefixWord ++ tailWord_189183).sum := by decide
  have hdescent : baseEnd_189183 < baseStart_189183 := by decide
  rcases family_descends (prefixWord ++ tailWord_189183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189233 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_189233 : Nat := 118140960795 + 189233 * 2 ^ 59
def prefixEnd_189233 : Nat := 4983230072969 + 3 ^ 40 * 189233 * 2
def baseEnd_189233 : Nat := 32389161564121119572413

theorem tailTrace_189233 : CollatzResearch.WordTrace tailWord_189233 prefixEnd_189233 32389161564121119572413 := by
  unfold tailWord_189233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6901894523448634268508353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601263015632422845672235 6901894523448634268508353)
  ·
    refine ⟨5176420892586475701381265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6901894523448634268508353 5176420892586475701381265)
    ·
      refine ⟨3882315669439856776035949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5176420892586475701381265 3882315669439856776035949)
      ·
        refine ⟨1455868376039946291013481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3882315669439856776035949 1455868376039946291013481)
        ·
          refine ⟨1091901282029959718260111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1455868376039946291013481 1091901282029959718260111)
          ·
            refine ⟨1637851923044939577390167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091901282029959718260111 1637851923044939577390167)
            ·
              refine ⟨2456777884567409366085251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637851923044939577390167 2456777884567409366085251)
              ·
                refine ⟨3685166826851114049127877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456777884567409366085251 3685166826851114049127877)
                ·
                  refine ⟨690968780034583884211477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3685166826851114049127877 690968780034583884211477)
                  ·
                    refine ⟨32389161564121119572413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 690968780034583884211477 32389161564121119572413)
                    ·
                      rfl

theorem cell23_189233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_189233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189233 prefixEnd_189233 := by exact prefixLift 189233
  have htrace : WordTrace (prefixWord ++ tailWord_189233) baseStart_189233 baseEnd_189233 := by
    simpa [prefixWord, tailWord_189233, baseEnd_189233] using wordTrace_append hprefix tailTrace_189233
  have hstable : (prefixWord ++ tailWord_189233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189233).length < 2 ^ (prefixWord ++ tailWord_189233).sum := by decide
  have hdescent : baseEnd_189233 < baseStart_189233 := by decide
  rcases family_descends (prefixWord ++ tailWord_189233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189253 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_189253 : Nat := 118140960795 + 189253 * 2 ^ 59
def prefixEnd_189253 : Nat := 4983230072969 + 3 ^ 40 * 189253 * 2
def baseEnd_189253 : Nat := 97177754305453280467147

theorem tailTrace_189253 : CollatzResearch.WordTrace tailWord_189253 prefixEnd_189253 97177754305453280467147 := by
  unfold tailWord_189253
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902623983376177684236413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601749322250785122824275 6902623983376177684236413)
  ·
    refine ⟨2588483993766066631588655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6902623983376177684236413 2588483993766066631588655)
    ·
      refine ⟨3882725990649099947382983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2588483993766066631588655 3882725990649099947382983)
      ·
        refine ⟨5824088985973649921074475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3882725990649099947382983 5824088985973649921074475)
        ·
          refine ⟨8736133478960474881611713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5824088985973649921074475 8736133478960474881611713)
          ·
            refine ⟨6552100109220356161208785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8736133478960474881611713 6552100109220356161208785)
            ·
              refine ⟨4914075081915267120906589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6552100109220356161208785 4914075081915267120906589)
              ·
                refine ⟨1842778155718225170339971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914075081915267120906589 1842778155718225170339971)
                ·
                  refine ⟨2764167233577337755509957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842778155718225170339971 2764167233577337755509957)
                  ·
                    refine ⟨518281356295750829158117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764167233577337755509957 518281356295750829158117)
                    ·
                      refine ⟨97177754305453280467147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 518281356295750829158117 97177754305453280467147)
                      ·
                        rfl

theorem cell23_189253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_189253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189253 prefixEnd_189253 := by exact prefixLift 189253
  have htrace : WordTrace (prefixWord ++ tailWord_189253) baseStart_189253 baseEnd_189253 := by
    simpa [prefixWord, tailWord_189253, baseEnd_189253] using wordTrace_append hprefix tailTrace_189253
  have hstable : (prefixWord ++ tailWord_189253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189253).length < 2 ^ (prefixWord ++ tailWord_189253).sum := by decide
  have hdescent : baseEnd_189253 < baseStart_189253 := by decide
  rcases family_descends (prefixWord ++ tailWord_189253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189257 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 1, 4, 2]
def baseStart_189257 : Nat := 118140960795 + 189257 * 2 ^ 59
def prefixEnd_189257 : Nat := 4983230072969 + 3 ^ 40 * 189257 * 2
def baseEnd_189257 : Nat := 97179808228071264817129

theorem tailTrace_189257 : CollatzResearch.WordTrace tailWord_189257 prefixEnd_189257 97179808228071264817129 := by
  unfold tailWord_189257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902769875361686367382025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4601846583574457578254683 6902769875361686367382025)
  ·
    refine ⟨5177077406521264775536519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6902769875361686367382025 5177077406521264775536519)
    ·
      refine ⟨7765616109781897163304779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177077406521264775536519 7765616109781897163304779)
      ·
        refine ⟨11648424164672845744957169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765616109781897163304779 11648424164672845744957169)
        ·
          refine ⟨8736318123504634308717877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11648424164672845744957169 8736318123504634308717877)
          ·
            refine ⟨819029824078559466442301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8736318123504634308717877 819029824078559466442301)
            ·
              refine ⟨307136184029459799915863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819029824078559466442301 307136184029459799915863)
              ·
                refine ⟨460704276044189699873795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307136184029459799915863 460704276044189699873795)
                ·
                  refine ⟨691056414066284549810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460704276044189699873795 691056414066284549810693)
                  ·
                    refine ⟨129573077637428353089505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 691056414066284549810693 129573077637428353089505)
                    ·
                      refine ⟨97179808228071264817129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129573077637428353089505 97179808228071264817129)
                      ·
                        rfl

theorem cell23_189257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 1, 4, 2].length) (baseStart_189257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189257 prefixEnd_189257 := by exact prefixLift 189257
  have htrace : WordTrace (prefixWord ++ tailWord_189257) baseStart_189257 baseEnd_189257 := by
    simpa [prefixWord, tailWord_189257, baseEnd_189257] using wordTrace_append hprefix tailTrace_189257
  have hstable : (prefixWord ++ tailWord_189257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189257).length < 2 ^ (prefixWord ++ tailWord_189257).sum := by decide
  have hdescent : baseEnd_189257 < baseStart_189257 := by decide
  rcases family_descends (prefixWord ++ tailWord_189257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189323 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 8]
def baseStart_189323 : Nat := 118140960795 + 189323 * 2 ^ 59
def prefixEnd_189323 : Nat := 4983230072969 + 3 ^ 40 * 189323 * 2
def baseEnd_189323 : Nat := 32404565983756002197275

theorem tailTrace_189323 : CollatzResearch.WordTrace tailWord_189323 prefixEnd_189323 32404565983756002197275 := by
  unfold tailWord_189323
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905177093122579639284623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4603451395415053092856415 6905177093122579639284623)
  ·
    refine ⟨10357765639683869458926935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6905177093122579639284623 10357765639683869458926935)
    ·
      refine ⟨15536648459525804188390403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10357765639683869458926935 15536648459525804188390403)
      ·
        refine ⟨23304972689288706282585605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15536648459525804188390403 23304972689288706282585605)
        ·
          refine ⟨4369682379241632427984801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23304972689288706282585605 4369682379241632427984801)
          ·
            refine ⟨3277261784431224320988601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369682379241632427984801 3277261784431224320988601)
            ·
              refine ⟨2457946338323418240741451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277261784431224320988601 2457946338323418240741451)
              ·
                refine ⟨3686919507485127361112177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457946338323418240741451 3686919507485127361112177)
                ·
                  refine ⟨2765189630613845520834133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686919507485127361112177 2765189630613845520834133)
                  ·
                    refine ⟨32404565983756002197275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2765189630613845520834133 32404565983756002197275)
                    ·
                      rfl

theorem cell23_189323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 8].length) (baseStart_189323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189323 prefixEnd_189323 := by exact prefixLift 189323
  have htrace : WordTrace (prefixWord ++ tailWord_189323) baseStart_189323 baseEnd_189323 := by
    simpa [prefixWord, tailWord_189323, baseEnd_189323] using wordTrace_append hprefix tailTrace_189323
  have hstable : (prefixWord ++ tailWord_189323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189323).length < 2 ^ (prefixWord ++ tailWord_189323).sum := by decide
  have hdescent : baseEnd_189323 < baseStart_189323 := by decide
  rcases family_descends (prefixWord ++ tailWord_189323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189370 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_189370 : Nat := 118140960795 + 189370 * 2 ^ 59
def prefixEnd_189370 : Nat := 4983230072969 + 3 ^ 40 * 189370 * 2
def baseEnd_189370 : Nat := 10804203504669924744901

theorem tailTrace_189370 : CollatzResearch.WordTrace tailWord_189370 prefixEnd_189370 10804203504669924744901 := by
  unfold tailWord_189370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726722830988076666561391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4604594215968204444163709 1726722830988076666561391)
  ·
    refine ⟨2590084246482114999842087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726722830988076666561391 2590084246482114999842087)
    ·
      refine ⟨3885126369723172499763131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590084246482114999842087 3885126369723172499763131)
      ·
        refine ⟨5827689554584758749644697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885126369723172499763131 5827689554584758749644697)
        ·
          refine ⟨4370767165938569062233523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827689554584758749644697 4370767165938569062233523)
          ·
            refine ⟨6556150748907853593350285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370767165938569062233523 6556150748907853593350285)
            ·
              refine ⟨2458556530840445097506357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6556150748907853593350285 2458556530840445097506357)
              ·
                refine ⟨230489674766291727891221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2458556530840445097506357 230489674766291727891221)
                ·
                  refine ⟨10804203504669924744901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230489674766291727891221 10804203504669924744901)
                  ·
                    rfl

theorem cell23_189370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_189370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189370 prefixEnd_189370 := by exact prefixLift 189370
  have htrace : WordTrace (prefixWord ++ tailWord_189370) baseStart_189370 baseEnd_189370 := by
    simpa [prefixWord, tailWord_189370, baseEnd_189370] using wordTrace_append hprefix tailTrace_189370
  have hstable : (prefixWord ++ tailWord_189370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189370).length < 2 ^ (prefixWord ++ tailWord_189370).sum := by decide
  have hdescent : baseEnd_189370 < baseStart_189370 := by decide
  rcases family_descends (prefixWord ++ tailWord_189370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189437 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_189437 : Nat := 118140960795 + 189437 * 2 ^ 59
def prefixEnd_189437 : Nat := 4983230072969 + 3 ^ 40 * 189437 * 2
def baseEnd_189437 : Nat := 97272234745880560566301

theorem tailTrace_189437 : CollatzResearch.WordTrace tailWord_189437 prefixEnd_189437 97272234745880560566301 := by
  unfold tailWord_189437
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909335014709577108934565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4606223343139718072623043 6909335014709577108934565)
  ·
    refine ⟨1295500315258045707925231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6909335014709577108934565 1295500315258045707925231)
    ·
      refine ⟨1943250472887068561887847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295500315258045707925231 1943250472887068561887847)
      ·
        refine ⟨2914875709330602842831771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943250472887068561887847 2914875709330602842831771)
        ·
          refine ⟨4372313563995904264247657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914875709330602842831771 4372313563995904264247657)
          ·
            refine ⟨3279235172996928198185743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4372313563995904264247657 3279235172996928198185743)
            ·
              refine ⟨4918852759495392297278615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279235172996928198185743 4918852759495392297278615)
              ·
                refine ⟨7378279139243088445917923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4918852759495392297278615 7378279139243088445917923)
                ·
                  refine ⟨11067418708864632668876885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7378279139243088445917923 11067418708864632668876885)
                  ·
                    refine ⟨129696312994507414088401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11067418708864632668876885 129696312994507414088401)
                    ·
                      refine ⟨97272234745880560566301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129696312994507414088401 97272234745880560566301)
                      ·
                        rfl

theorem cell23_189437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_189437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189437 prefixEnd_189437 := by exact prefixLift 189437
  have htrace : WordTrace (prefixWord ++ tailWord_189437) baseStart_189437 baseEnd_189437 := by
    simpa [prefixWord, tailWord_189437, baseEnd_189437] using wordTrace_append hprefix tailTrace_189437
  have hstable : (prefixWord ++ tailWord_189437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189437).length < 2 ^ (prefixWord ++ tailWord_189437).sum := by decide
  have hdescent : baseEnd_189437 < baseStart_189437 := by decide
  rcases family_descends (prefixWord ++ tailWord_189437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189442 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_189442 : Nat := 118140960795 + 189442 * 2 ^ 59
def prefixEnd_189442 : Nat := 4983230072969 + 3 ^ 40 * 189442 * 2
def baseEnd_189442 : Nat := 32424934049717680334593

theorem tailTrace_189442 : CollatzResearch.WordTrace tailWord_189442 prefixEnd_189442 32424934049717680334593 := by
  unfold tailWord_189442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727379344922865740716645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4606344919794308641911053 1727379344922865740716645)
  ·
    refine ⟨323883627173037326384371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1727379344922865740716645 323883627173037326384371)
    ·
      refine ⟨485825440759555989576557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323883627173037326384371 485825440759555989576557)
      ·
        refine ⟨182184540284833496091209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 485825440759555989576557 182184540284833496091209)
        ·
          refine ⟨136638405213625122068407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182184540284833496091209 136638405213625122068407)
          ·
            refine ⟨204957607820437683102611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136638405213625122068407 204957607820437683102611)
            ·
              refine ⟨307436411730656524653917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204957607820437683102611 307436411730656524653917)
              ·
                refine ⟨115288654398996196745219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307436411730656524653917 115288654398996196745219)
                ·
                  refine ⟨172932981598494295117829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115288654398996196745219 172932981598494295117829)
                  ·
                    refine ⟨32424934049717680334593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172932981598494295117829 32424934049717680334593)
                    ·
                      rfl

theorem cell23_189442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_189442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189442 prefixEnd_189442 := by exact prefixLift 189442
  have htrace : WordTrace (prefixWord ++ tailWord_189442) baseStart_189442 baseEnd_189442 := by
    simpa [prefixWord, tailWord_189442, baseEnd_189442] using wordTrace_append hprefix tailTrace_189442
  have hstable : (prefixWord ++ tailWord_189442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189442).length < 2 ^ (prefixWord ++ tailWord_189442).sum := by decide
  have hdescent : baseEnd_189442 < baseStart_189442 := by decide
  rcases family_descends (prefixWord ++ tailWord_189442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189447 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 6, 4]
def baseStart_189447 : Nat := 118140960795 + 189447 * 2 ^ 59
def prefixEnd_189447 : Nat := 4983230072969 + 3 ^ 40 * 189447 * 2
def baseEnd_189447 : Nat := 32425789850808507147085

theorem tailTrace_189447 : CollatzResearch.WordTrace tailWord_189447 prefixEnd_189447 32425789850808507147085 := by
  unfold tailWord_189447
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909699744673348816798595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4606466496448899211199063 6909699744673348816798595)
  ·
    refine ⟨10364549617010023225197893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6909699744673348816798595 10364549617010023225197893)
    ·
      refine ⟨1943353053189379354724605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10364549617010023225197893 1943353053189379354724605)
      ·
        refine ⟨728757394946017258021727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1943353053189379354724605 728757394946017258021727)
        ·
          refine ⟨1093136092419025887032591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728757394946017258021727 1093136092419025887032591)
          ·
            refine ⟨1639704138628538830548887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093136092419025887032591 1639704138628538830548887)
            ·
              refine ⟨2459556207942808245823331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639704138628538830548887 2459556207942808245823331)
              ·
                refine ⟨3689334311914212368734997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2459556207942808245823331 3689334311914212368734997)
                ·
                  refine ⟨172937545870978704784453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3689334311914212368734997 172937545870978704784453)
                  ·
                    refine ⟨32425789850808507147085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 172937545870978704784453 32425789850808507147085)
                    ·
                      rfl

theorem cell23_189447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_189447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189447 prefixEnd_189447 := by exact prefixLift 189447
  have htrace : WordTrace (prefixWord ++ tailWord_189447) baseStart_189447 baseEnd_189447 := by
    simpa [prefixWord, tailWord_189447, baseEnd_189447] using wordTrace_append hprefix tailTrace_189447
  have hstable : (prefixWord ++ tailWord_189447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189447).length < 2 ^ (prefixWord ++ tailWord_189447).sum := by decide
  have hdescent : baseEnd_189447 < baseStart_189447 := by decide
  rcases family_descends (prefixWord ++ tailWord_189447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189448 : List Nat := [2, 1, 3, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_189448 : Nat := 118140960795 + 189448 * 2 ^ 59
def prefixEnd_189448 : Nat := 4983230072969 + 3 ^ 40 * 189448 * 2
def baseEnd_189448 : Nat := 97277883033080017528751

theorem tailTrace_189448 : CollatzResearch.WordTrace tailWord_189448 prefixEnd_189448 97277883033080017528751 := by
  unfold tailWord_189448
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454868108834862993792499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4606490811779817325056665 3454868108834862993792499)
  ·
    refine ⟨5182302163252294490688749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3454868108834862993792499 5182302163252294490688749)
    ·
      refine ⟨1943363311219610434008281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5182302163252294490688749 1943363311219610434008281)
      ·
        refine ⟨1457522483414707825506211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1943363311219610434008281 1457522483414707825506211)
        ·
          refine ⟨2186283725122061738259317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457522483414707825506211 2186283725122061738259317)
          ·
            refine ⟨204964099230193287961811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2186283725122061738259317 204964099230193287961811)
            ·
              refine ⟨307446148845289931942717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204964099230193287961811 307446148845289931942717)
              ·
                refine ⟨115292305816983724478519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307446148845289931942717 115292305816983724478519)
                ·
                  refine ⟨172938458725475586717779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115292305816983724478519 172938458725475586717779)
                  ·
                    refine ⟨259407688088213380076669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 172938458725475586717779 259407688088213380076669)
                    ·
                      refine ⟨97277883033080017528751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 259407688088213380076669 97277883033080017528751)
                      ·
                        rfl

theorem cell23_189448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_189448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189448 prefixEnd_189448 := by exact prefixLift 189448
  have htrace : WordTrace (prefixWord ++ tailWord_189448) baseStart_189448 baseEnd_189448 := by
    simpa [prefixWord, tailWord_189448, baseEnd_189448] using wordTrace_append hprefix tailTrace_189448
  have hstable : (prefixWord ++ tailWord_189448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189448).length < 2 ^ (prefixWord ++ tailWord_189448).sum := by decide
  have hdescent : baseEnd_189448 < baseStart_189448 := by decide
  rcases family_descends (prefixWord ++ tailWord_189448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189454 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_189454 : Nat := 118140960795 + 189454 * 2 ^ 59
def prefixEnd_189454 : Nat := 4983230072969 + 3 ^ 40 * 189454 * 2
def baseEnd_189454 : Nat := 97280963917006994053723

theorem tailTrace_189454 : CollatzResearch.WordTrace tailWord_189454 prefixEnd_189454 97280963917006994053723 := by
  unfold tailWord_189454
  simp only [CollatzResearch.WordTrace]
  refine ⟨863744381955998626537927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4606636703765326008202277 863744381955998626537927)
  ·
    refine ⟨1295616572933997939806891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 863744381955998626537927 1295616572933997939806891)
    ·
      refine ⟨1943424859400996909710337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1295616572933997939806891 1943424859400996909710337)
      ·
        refine ⟨1457568644550747682282753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1943424859400996909710337 1457568644550747682282753)
        ·
          refine ⟨1093176483413060761712065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1457568644550747682282753 1093176483413060761712065)
          ·
            refine ⟨819882362559795571284049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1093176483413060761712065 819882362559795571284049)
            ·
              refine ⟨614911771919846678463037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819882362559795571284049 614911771919846678463037)
              ·
                refine ⟨230591914469942504423639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 614911771919846678463037 230591914469942504423639)
                ·
                  refine ⟨345887871704913756635459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230591914469942504423639 345887871704913756635459)
                  ·
                    refine ⟨518831807557370634953189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345887871704913756635459 518831807557370634953189)
                    ·
                      refine ⟨97280963917006994053723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 518831807557370634953189 97280963917006994053723)
                      ·
                        rfl

theorem cell23_189454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_189454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189454 prefixEnd_189454 := by exact prefixLift 189454
  have htrace : WordTrace (prefixWord ++ tailWord_189454) baseStart_189454 baseEnd_189454 := by
    simpa [prefixWord, tailWord_189454, baseEnd_189454] using wordTrace_append hprefix tailTrace_189454
  have hstable : (prefixWord ++ tailWord_189454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189454).length < 2 ^ (prefixWord ++ tailWord_189454).sum := by decide
  have hdescent : baseEnd_189454 < baseStart_189454 := by decide
  rcases family_descends (prefixWord ++ tailWord_189454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189471 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 3, 2, 2]
def baseStart_189471 : Nat := 118140960795 + 189471 * 2 ^ 59
def prefixEnd_189471 : Nat := 4983230072969 + 3 ^ 40 * 189471 * 2
def baseEnd_189471 : Nat := 97289693088133427541145

theorem tailTrace_189471 : CollatzResearch.WordTrace tailWord_189471 prefixEnd_189471 97289693088133427541145 := by
  unfold tailWord_189471
  simp only [CollatzResearch.WordTrace]
  refine ⟨6910575096586400915672267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4607050064390933943781511 6910575096586400915672267)
  ·
    refine ⟨10365862644879601373508401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6910575096586400915672267 10365862644879601373508401)
    ·
      refine ⟨7774396983659701030131301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10365862644879601373508401 7774396983659701030131301)
      ·
        refine ⟨1457699434436193943149619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7774396983659701030131301 1457699434436193943149619)
        ·
          refine ⟨2186549151654290914724429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457699434436193943149619 2186549151654290914724429)
          ·
            refine ⟨819955931870359093021661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2186549151654290914724429 819955931870359093021661)
            ·
              refine ⟨307483474451384659883123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819955931870359093021661 307483474451384659883123)
              ·
                refine ⟨461225211677076989824685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307483474451384659883123 461225211677076989824685)
                ·
                  refine ⟨172959454378903871184257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461225211677076989824685 172959454378903871184257)
                  ·
                    refine ⟨129719590784177903388193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 172959454378903871184257 129719590784177903388193)
                    ·
                      refine ⟨97289693088133427541145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129719590784177903388193 97289693088133427541145)
                      ·
                        rfl

theorem cell23_189471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_189471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189471 prefixEnd_189471 := by exact prefixLift 189471
  have htrace : WordTrace (prefixWord ++ tailWord_189471) baseStart_189471 baseEnd_189471 := by
    simpa [prefixWord, tailWord_189471, baseEnd_189471] using wordTrace_append hprefix tailTrace_189471
  have hstable : (prefixWord ++ tailWord_189471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189471).length < 2 ^ (prefixWord ++ tailWord_189471).sum := by decide
  have hdescent : baseEnd_189471 < baseStart_189471 := by decide
  rcases family_descends (prefixWord ++ tailWord_189471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189520 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_189520 : Nat := 118140960795 + 189520 * 2 ^ 59
def prefixEnd_189520 : Nat := 4983230072969 + 3 ^ 40 * 189520 * 2
def baseEnd_189520 : Nat := 32438284546734578609473

theorem tailTrace_189520 : CollatzResearch.WordTrace tailWord_189520 prefixEnd_189520 32438284546734578609473 := by
  unfold tailWord_189520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456181136704441142103007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4608241515605921522804009 3456181136704441142103007)
  ·
    refine ⟨5184271705056661713154511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456181136704441142103007 5184271705056661713154511)
    ·
      refine ⟨7776407557584992569731767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184271705056661713154511 7776407557584992569731767)
      ·
        refine ⟨11664611336377488854597651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7776407557584992569731767 11664611336377488854597651)
        ·
          refine ⟨17496917004566233281896477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11664611336377488854597651 17496917004566233281896477)
          ·
            refine ⟨6561343876712337480711179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17496917004566233281896477 6561343876712337480711179)
            ·
              refine ⟨9842015815068506221066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561343876712337480711179 9842015815068506221066769)
              ·
                refine ⟨7381511861301379665800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9842015815068506221066769 7381511861301379665800077)
                ·
                  refine ⟨2768066947988017374675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7381511861301379665800077 2768066947988017374675029)
                  ·
                    refine ⟨32438284546734578609473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2768066947988017374675029 32438284546734578609473)
                    ·
                      rfl

theorem cell23_189520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_189520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189520 prefixEnd_189520 := by exact prefixLift 189520
  have htrace : WordTrace (prefixWord ++ tailWord_189520) baseStart_189520 baseEnd_189520 := by
    simpa [prefixWord, tailWord_189520, baseEnd_189520] using wordTrace_append hprefix tailTrace_189520
  have hstable : (prefixWord ++ tailWord_189520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189520).length < 2 ^ (prefixWord ++ tailWord_189520).sum := by decide
  have hdescent : baseEnd_189520 < baseStart_189520 := by decide
  rcases family_descends (prefixWord ++ tailWord_189520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189522 : List Nat := [3, 2, 2, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_189522 : Nat := 118140960795 + 189522 * 2 ^ 59
def prefixEnd_189522 : Nat := 4983230072969 + 3 ^ 40 * 189522 * 2
def baseEnd_189522 : Nat := 97315880601512728003411

theorem tailTrace_189522 : CollatzResearch.WordTrace tailWord_189522 prefixEnd_189522 97315880601512728003411 := by
  unfold tailWord_189522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728108804850409156444705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4608290146267757750519213 1728108804850409156444705)
  ·
    refine ⟨1296081603637806867333529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1728108804850409156444705 1296081603637806867333529)
    ·
      refine ⟨972061202728355150500147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296081603637806867333529 972061202728355150500147)
      ·
        refine ⟨1458091804092532725750221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972061202728355150500147 1458091804092532725750221)
        ·
          refine ⟨546784426534699772156333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458091804092532725750221 546784426534699772156333)
          ·
            refine ⟨205044159950512414558625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546784426534699772156333 205044159950512414558625)
            ·
              refine ⟨153783119962884310918969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205044159950512414558625 153783119962884310918969)
              ·
                refine ⟨115337339972163233189227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153783119962884310918969 115337339972163233189227)
                ·
                  refine ⟨173006009958244849783841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115337339972163233189227 173006009958244849783841)
                  ·
                    refine ⟨129754507468683637337881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173006009958244849783841 129754507468683637337881)
                    ·
                      refine ⟨97315880601512728003411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129754507468683637337881 97315880601512728003411)
                      ·
                        rfl

theorem cell23_189522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_189522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189522 prefixEnd_189522 := by exact prefixLift 189522
  have htrace : WordTrace (prefixWord ++ tailWord_189522) baseStart_189522 baseEnd_189522 := by
    simpa [prefixWord, tailWord_189522, baseEnd_189522] using wordTrace_append hprefix tailTrace_189522
  have hstable : (prefixWord ++ tailWord_189522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189522).length < 2 ^ (prefixWord ++ tailWord_189522).sum := by decide
  have hdescent : baseEnd_189522 < baseStart_189522 := by decide
  rcases family_descends (prefixWord ++ tailWord_189522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189538 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_189538 : Nat := 118140960795 + 189538 * 2 ^ 59
def prefixEnd_189538 : Nat := 4983230072969 + 3 ^ 40 * 189538 * 2
def baseEnd_189538 : Nat := 97324096291984665403337

theorem tailTrace_189538 : CollatzResearch.WordTrace tailWord_189538 prefixEnd_189538 97324096291984665403337 := by
  unfold tailWord_189538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728254696835917839590317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4608679191562447572240845 1728254696835917839590317)
  ·
    refine ⟨648095511313469189846369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1728254696835917839590317 648095511313469189846369)
    ·
      refine ⟨486071633485101892384777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648095511313469189846369 486071633485101892384777)
      ·
        refine ⟨364553725113826419288583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486071633485101892384777 364553725113826419288583)
        ·
          refine ⟨546830587670739628932875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364553725113826419288583 546830587670739628932875)
          ·
            refine ⟨820245881506109443399313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546830587670739628932875 820245881506109443399313)
            ·
              refine ⟨615184411129582082549485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820245881506109443399313 615184411129582082549485)
              ·
                refine ⟨230694154173593280956057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615184411129582082549485 230694154173593280956057)
                ·
                  refine ⟨173020615630194960717043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230694154173593280956057 173020615630194960717043)
                  ·
                    refine ⟨259530923445292441075565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173020615630194960717043 259530923445292441075565)
                    ·
                      refine ⟨97324096291984665403337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 259530923445292441075565 97324096291984665403337)
                      ·
                        rfl

theorem cell23_189538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_189538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189538 prefixEnd_189538 := by exact prefixLift 189538
  have htrace : WordTrace (prefixWord ++ tailWord_189538) baseStart_189538 baseEnd_189538 := by
    simpa [prefixWord, tailWord_189538, baseEnd_189538] using wordTrace_append hprefix tailTrace_189538
  have hstable : (prefixWord ++ tailWord_189538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189538).length < 2 ^ (prefixWord ++ tailWord_189538).sum := by decide
  have hdescent : baseEnd_189538 < baseStart_189538 := by decide
  rcases family_descends (prefixWord ++ tailWord_189538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189597 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_189597 : Nat := 118140960795 + 189597 * 2 ^ 59
def prefixEnd_189597 : Nat := 4983230072969 + 3 ^ 40 * 189597 * 2
def baseEnd_189597 : Nat := 32451463883533311521855

theorem tailTrace_189597 : CollatzResearch.WordTrace tailWord_189597 prefixEnd_189597 32451463883533311521855 := by
  unfold tailWord_189597
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915170694129924434759045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4610113796086616289839363 6915170694129924434759045)
  ·
    refine ⟨1296594505149360831517321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6915170694129924434759045 1296594505149360831517321)
    ·
      refine ⟨972445878862020623637991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296594505149360831517321 972445878862020623637991)
      ·
        refine ⟨1458668818293030935456987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972445878862020623637991 1458668818293030935456987)
        ·
          refine ⟨2188003227439546403185481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458668818293030935456987 2188003227439546403185481)
          ·
            refine ⟨1641002420579659802389111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188003227439546403185481 1641002420579659802389111)
            ·
              refine ⟨2461503630869489703583667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641002420579659802389111 2461503630869489703583667)
              ·
                refine ⟨3692255446304234555375501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461503630869489703583667 3692255446304234555375501)
                ·
                  refine ⟨1384595792364087958265813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3692255446304234555375501 1384595792364087958265813)
                  ·
                    refine ⟨32451463883533311521855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1384595792364087958265813 32451463883533311521855)
                    ·
                      rfl

theorem cell23_189597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_189597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189597 prefixEnd_189597 := by exact prefixLift 189597
  have htrace : WordTrace (prefixWord ++ tailWord_189597) baseStart_189597 baseEnd_189597 := by
    simpa [prefixWord, tailWord_189597, baseEnd_189597] using wordTrace_append hprefix tailTrace_189597
  have hstable : (prefixWord ++ tailWord_189597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189597).length < 2 ^ (prefixWord ++ tailWord_189597).sum := by decide
  have hdescent : baseEnd_189597 < baseStart_189597 := by decide
  rcases family_descends (prefixWord ++ tailWord_189597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189647 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4]
def baseStart_189647 : Nat := 118140960795 + 189647 * 2 ^ 59
def prefixEnd_189647 : Nat := 4983230072969 + 3 ^ 40 * 189647 * 2
def baseEnd_189647 : Nat := 97380065683324738940335

theorem tailTrace_189647 : CollatzResearch.WordTrace tailWord_189647 prefixEnd_189647 97380065683324738940335 := by
  unfold tailWord_189647
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916994343948782974079195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4611329562632521982719463 6916994343948782974079195)
  ·
    refine ⟨10375491515923174461118793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6916994343948782974079195 10375491515923174461118793)
    ·
      refine ⟨7781618636942380845839095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10375491515923174461118793 7781618636942380845839095)
      ·
        refine ⟨11672427955413571268758643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781618636942380845839095 11672427955413571268758643)
        ·
          refine ⟨17508641933120356903137965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11672427955413571268758643 17508641933120356903137965)
          ·
            refine ⟨6565740724920133838676737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17508641933120356903137965 6565740724920133838676737)
            ·
              refine ⟨4924305543690100379007553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6565740724920133838676737 4924305543690100379007553)
              ·
                refine ⟨3693229157767575284255665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4924305543690100379007553 3693229157767575284255665)
                ·
                  refine ⟨2769921868325681463191749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3693229157767575284255665 2769921868325681463191749)
                  ·
                    refine ⟨519360350311065274348453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769921868325681463191749 519360350311065274348453)
                    ·
                      refine ⟨97380065683324738940335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 519360350311065274348453 97380065683324738940335)
                      ·
                        rfl

theorem cell23_189647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_189647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189647 prefixEnd_189647 := by exact prefixLift 189647
  have htrace : WordTrace (prefixWord ++ tailWord_189647) baseStart_189647 baseEnd_189647 := by
    simpa [prefixWord, tailWord_189647, baseEnd_189647] using wordTrace_append hprefix tailTrace_189647
  have hstable : (prefixWord ++ tailWord_189647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189647).length < 2 ^ (prefixWord ++ tailWord_189647).sum := by decide
  have hdescent : baseEnd_189647 < baseStart_189647 := by decide
  rcases family_descends (prefixWord ++ tailWord_189647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189695 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 1, 4]
def baseStart_189695 : Nat := 118140960795 + 189695 * 2 ^ 59
def prefixEnd_189695 : Nat := 4983230072969 + 3 ^ 40 * 189695 * 2
def baseEnd_189695 : Nat := 32468237584913517046705

theorem tailTrace_189695 : CollatzResearch.WordTrace tailWord_189695 prefixEnd_189695 32468237584913517046705 := by
  unfold tailWord_189695
  simp only [CollatzResearch.WordTrace]
  refine ⟨6918745047774887171826539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4612496698516591447884359 6918745047774887171826539)
  ·
    refine ⟨10378117571662330757739809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6918745047774887171826539 10378117571662330757739809)
    ·
      refine ⟨7783588178746748068304857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10378117571662330757739809 7783588178746748068304857)
      ·
        refine ⟨5837691134060061051228643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7783588178746748068304857 5837691134060061051228643)
        ·
          refine ⟨8756536701090091576842965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5837691134060061051228643 8756536701090091576842965)
          ·
            refine ⟨205231328931799021332257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8756536701090091576842965 205231328931799021332257)
            ·
              refine ⟨153923496698849265999193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205231328931799021332257 153923496698849265999193)
              ·
                refine ⟨115442622524136949499395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153923496698849265999193 115442622524136949499395)
                ·
                  refine ⟨173163933786205424249093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115442622524136949499395 173163933786205424249093)
                  ·
                    refine ⟨32468237584913517046705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173163933786205424249093 32468237584913517046705)
                    ·
                      rfl

theorem cell23_189695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 4].length) (baseStart_189695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189695 prefixEnd_189695 := by exact prefixLift 189695
  have htrace : WordTrace (prefixWord ++ tailWord_189695) baseStart_189695 baseEnd_189695 := by
    simpa [prefixWord, tailWord_189695, baseEnd_189695] using wordTrace_append hprefix tailTrace_189695
  have hstable : (prefixWord ++ tailWord_189695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189695).length < 2 ^ (prefixWord ++ tailWord_189695).sum := by decide
  have hdescent : baseEnd_189695 < baseStart_189695 := by decide
  rcases family_descends (prefixWord ++ tailWord_189695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189701 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_189701 : Nat := 118140960795 + 189701 * 2 ^ 59
def prefixEnd_189701 : Nat := 4983230072969 + 3 ^ 40 * 189701 * 2
def baseEnd_189701 : Nat := 97407793638667527665087

theorem tailTrace_189701 : CollatzResearch.WordTrace tailWord_189701 prefixEnd_189701 97407793638667527665087 := by
  unfold tailWord_189701
  simp only [CollatzResearch.WordTrace]
  refine ⟨6918963885753150196544957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4612642590502100131029971 6918963885753150196544957)
  ·
    refine ⟨2594611457157431323704359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6918963885753150196544957 2594611457157431323704359)
    ·
      refine ⟨3891917185736146985556539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594611457157431323704359 3891917185736146985556539)
      ·
        refine ⟨5837875778604220478334809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891917185736146985556539 5837875778604220478334809)
        ·
          refine ⟨4378406833953165358751107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5837875778604220478334809 4378406833953165358751107)
          ·
            refine ⟨6567610250929748038126661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4378406833953165358751107 6567610250929748038126661)
            ·
              refine ⟨1231426922049327757148749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6567610250929748038126661 1231426922049327757148749)
              ·
                refine ⟨461785095768497908930781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231426922049327757148749 461785095768497908930781)
                ·
                  refine ⟨173169410913186715849043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 461785095768497908930781 173169410913186715849043)
                  ·
                    refine ⟨259754116369780073773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173169410913186715849043 259754116369780073773565)
                    ·
                      refine ⟨97407793638667527665087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 259754116369780073773565 97407793638667527665087)
                      ·
                        rfl

theorem cell23_189701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_189701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189701 prefixEnd_189701 := by exact prefixLift 189701
  have htrace : WordTrace (prefixWord ++ tailWord_189701) baseStart_189701 baseEnd_189701 := by
    simpa [prefixWord, tailWord_189701, baseEnd_189701] using wordTrace_append hprefix tailTrace_189701
  have hstable : (prefixWord ++ tailWord_189701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189701).length < 2 ^ (prefixWord ++ tailWord_189701).sum := by decide
  have hdescent : baseEnd_189701 < baseStart_189701 := by decide
  rcases family_descends (prefixWord ++ tailWord_189701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189728 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2]
def baseStart_189728 : Nat := 118140960795 + 189728 * 2 ^ 59
def prefixEnd_189728 : Nat := 4983230072969 + 3 ^ 40 * 189728 * 2
def baseEnd_189728 : Nat := 97421657616338922027463

theorem tailTrace_189728 : CollatzResearch.WordTrace tailWord_189728 prefixEnd_189728 97421657616338922027463 := by
  unfold tailWord_189728
  simp only [CollatzResearch.WordTrace]
  refine ⟨3459974328327666903888919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4613299104436889205185225 3459974328327666903888919)
  ·
    refine ⟨5189961492491500355833379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3459974328327666903888919 5189961492491500355833379)
    ·
      refine ⟨7784942238737250533750069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5189961492491500355833379 7784942238737250533750069)
      ·
        refine ⟨729838334881617237539069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7784942238737250533750069 729838334881617237539069)
        ·
          refine ⟨273689375580606464077151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 729838334881617237539069 273689375580606464077151)
          ·
            refine ⟨410534063370909696115727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273689375580606464077151 410534063370909696115727)
            ·
              refine ⟨615801095056364544173591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410534063370909696115727 615801095056364544173591)
              ·
                refine ⟨923701642584546816260387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615801095056364544173591 923701642584546816260387)
                ·
                  refine ⟨1385552463876820224390581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923701642584546816260387 1385552463876820224390581)
                  ·
                    refine ⟨129895543488451896036617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1385552463876820224390581 129895543488451896036617)
                    ·
                      refine ⟨97421657616338922027463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129895543488451896036617 97421657616338922027463)
                      ·
                        rfl

theorem cell23_189728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_189728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189728 prefixEnd_189728 := by exact prefixLift 189728
  have htrace : WordTrace (prefixWord ++ tailWord_189728) baseStart_189728 baseEnd_189728 := by
    simpa [prefixWord, tailWord_189728, baseEnd_189728] using wordTrace_append hprefix tailTrace_189728
  have hstable : (prefixWord ++ tailWord_189728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189728).length < 2 ^ (prefixWord ++ tailWord_189728).sum := by decide
  have hdescent : baseEnd_189728 < baseStart_189728 := by decide
  rcases family_descends (prefixWord ++ tailWord_189728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189738 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_189738 : Nat := 118140960795 + 189738 * 2 ^ 59
def prefixEnd_189738 : Nat := 4983230072969 + 3 ^ 40 * 189738 * 2
def baseEnd_189738 : Nat := 32475597474294627634139

theorem tailTrace_189738 : CollatzResearch.WordTrace tailWord_189738 prefixEnd_189738 32475597474294627634139 := by
  unfold tailWord_189738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730078346654776378910467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4613542257746070343761245 1730078346654776378910467)
  ·
    refine ⟨2595117519982164568365701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730078346654776378910467 2595117519982164568365701)
    ·
      refine ⟨486584534996655856568569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2595117519982164568365701 486584534996655856568569)
      ·
        refine ⟨364938401247491892426427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486584534996655856568569 364938401247491892426427)
        ·
          refine ⟨547407601871237838639641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364938401247491892426427 547407601871237838639641)
          ·
            refine ⟨410555701403428378979731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547407601871237838639641 410555701403428378979731)
            ·
              refine ⟨615833552105142568469597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410555701403428378979731 615833552105142568469597)
              ·
                refine ⟨230937582039428463176099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615833552105142568469597 230937582039428463176099)
                ·
                  refine ⟨346406373059142694764149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230937582039428463176099 346406373059142694764149)
                  ·
                    refine ⟨32475597474294627634139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 346406373059142694764149 32475597474294627634139)
                    ·
                      rfl

theorem cell23_189738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_189738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189738 prefixEnd_189738 := by exact prefixLift 189738
  have htrace : WordTrace (prefixWord ++ tailWord_189738) baseStart_189738 baseEnd_189738 := by
    simpa [prefixWord, tailWord_189738, baseEnd_189738] using wordTrace_append hprefix tailTrace_189738
  have hstable : (prefixWord ++ tailWord_189738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189738).length < 2 ^ (prefixWord ++ tailWord_189738).sum := by decide
  have hdescent : baseEnd_189738 < baseStart_189738 := by decide
  rcases family_descends (prefixWord ++ tailWord_189738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
