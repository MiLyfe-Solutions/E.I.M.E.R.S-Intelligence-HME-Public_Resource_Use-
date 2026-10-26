import V185TrunkScan22Chunk420

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3753143 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 5]
def baseStart_3753143 : Nat := 118140960795 + 3753143 * 2 ^ 59
def prefixEnd_3753143 : Nat := 4983230072969 + 3 ^ 40 * 3753143 * 2
def baseEnd_3753143 : Nat := 428259183123892120989359

theorem tailTrace_3753143 : CollatzResearch.WordTrace tailWord_3753143 prefixEnd_3753143 428259183123892120989359 := by
  unfold tailWord_3753143
  simp only [CollatzResearch.WordTrace]
  refine ⟨136888371042011371638024083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91258914028007581092016055 136888371042011371638024083)
  ·
    refine ⟨205332556563017057457036125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136888371042011371638024083 205332556563017057457036125)
    ·
      refine ⟨76999708711131396546388547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205332556563017057457036125 76999708711131396546388547)
      ·
        refine ⟨115499563066697094819582821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76999708711131396546388547 115499563066697094819582821)
        ·
          refine ⟨21656168075005705278671779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115499563066697094819582821 21656168075005705278671779)
          ·
            refine ⟨32484252112508557918007669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656168075005705278671779 32484252112508557918007669)
            ·
              refine ⟨3045398635547677304813219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32484252112508557918007669 3045398635547677304813219)
              ·
                refine ⟨4568097953321515957219829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045398635547677304813219 4568097953321515957219829)
                ·
                  refine ⟨428259183123892120989359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4568097953321515957219829 428259183123892120989359)
                  ·
                    rfl

theorem cell22_3753143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 5].length) (baseStart_3753143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753143 prefixEnd_3753143 := by exact prefixLift 3753143
  have htrace : WordTrace (prefixWord ++ tailWord_3753143) baseStart_3753143 baseEnd_3753143 := by
    simpa [prefixWord, tailWord_3753143, baseEnd_3753143] using wordTrace_append hprefix tailTrace_3753143
  have hstable : (prefixWord ++ tailWord_3753143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753143).length < 2 ^ (prefixWord ++ tailWord_3753143).sum := by decide
  have hdescent : baseEnd_3753143 < baseStart_3753143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753188 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_3753188 : Nat := 118140960795 + 3753188 * 2 ^ 59
def prefixEnd_3753188 : Nat := 4983230072969 + 3 ^ 40 * 3753188 * 2
def baseEnd_3753188 : Nat := 428264317930437081864313

theorem tailTrace_3753188 : CollatzResearch.WordTrace tailWord_3753188 prefixEnd_3753188 428264317930437081864313 := by
  unfold tailWord_3753188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68445006163424172161706109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91260008217898896215608145 68445006163424172161706109)
  ·
    refine ⟨25666877311284064560639791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68445006163424172161706109 25666877311284064560639791)
    ·
      refine ⟨38500315966926096840959687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25666877311284064560639791 38500315966926096840959687)
      ·
        refine ⟨57750473950389145261439531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38500315966926096840959687 57750473950389145261439531)
        ·
          refine ⟨86625710925583717892159297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57750473950389145261439531 86625710925583717892159297)
          ·
            refine ⟨64969283194187788419119473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86625710925583717892159297 64969283194187788419119473)
            ·
              refine ⟨48726962395640841314339605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64969283194187788419119473 48726962395640841314339605)
              ·
                refine ⟨2284076362295664436609669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48726962395640841314339605 2284076362295664436609669)
                ·
                  refine ⟨428264317930437081864313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284076362295664436609669 428264317930437081864313)
                  ·
                    rfl

theorem cell22_3753188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_3753188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753188 prefixEnd_3753188 := by exact prefixLift 3753188
  have htrace : WordTrace (prefixWord ++ tailWord_3753188) baseStart_3753188 baseEnd_3753188 := by
    simpa [prefixWord, tailWord_3753188, baseEnd_3753188] using wordTrace_append hprefix tailTrace_3753188
  have hstable : (prefixWord ++ tailWord_3753188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753188).length < 2 ^ (prefixWord ++ tailWord_3753188).sum := by decide
  have hdescent : baseEnd_3753188 < baseStart_3753188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3753201 : Nat := 118140960795 + 3753201 * 2 ^ 59
def prefixEnd_3753201 : Nat := 4983230072969 + 3 ^ 40 * 3753201 * 2
def baseEnd_3753201 : Nat := 1284797403956983545017899

theorem tailTrace_3753201 : CollatzResearch.WordTrace tailWord_3753201 prefixEnd_3753201 1284797403956983545017899 := by
  unfold tailWord_3753201
  simp only [CollatzResearch.WordTrace]
  refine ⟨136890486475801247543635457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91260324317200831695756971 136890486475801247543635457)
  ·
    refine ⟨102667864856850935657726593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136890486475801247543635457 102667864856850935657726593)
    ·
      refine ⟨77000898642638201743294945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102667864856850935657726593 77000898642638201743294945)
      ·
        refine ⟨57750673981978651307471209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77000898642638201743294945 57750673981978651307471209)
        ·
          refine ⟨43313005486483988480603407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57750673981978651307471209 43313005486483988480603407)
          ·
            refine ⟨64969508229725982720905111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43313005486483988480603407 64969508229725982720905111)
            ·
              refine ⟨97454262344588974081357667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64969508229725982720905111 97454262344588974081357667)
              ·
                refine ⟨146181393516883461122036501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97454262344588974081357667 146181393516883461122036501)
                ·
                  refine ⟨6852252821103912240095461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146181393516883461122036501 6852252821103912240095461)
                  ·
                    refine ⟨1284797403956983545017899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852252821103912240095461 1284797403956983545017899)
                    ·
                      rfl

theorem cell22_3753201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3753201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753201 prefixEnd_3753201 := by exact prefixLift 3753201
  have htrace : WordTrace (prefixWord ++ tailWord_3753201) baseStart_3753201 baseEnd_3753201 := by
    simpa [prefixWord, tailWord_3753201, baseEnd_3753201] using wordTrace_append hprefix tailTrace_3753201
  have hstable : (prefixWord ++ tailWord_3753201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753201).length < 2 ^ (prefixWord ++ tailWord_3753201).sum := by decide
  have hdescent : baseEnd_3753201 < baseStart_3753201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753250 : List Nat := [3, 3, 1, 1, 4, 2, 1, 7]
def baseStart_3753250 : Nat := 118140960795 + 3753250 * 2 ^ 59
def prefixEnd_3753250 : Nat := 4983230072969 + 3 ^ 40 * 3753250 * 2
def baseEnd_3753250 : Nat := 142757130850929305615861

theorem tailTrace_3753250 : CollatzResearch.WordTrace tailWord_3753250 prefixEnd_3753250 142757130850929305615861 := by
  unfold tailWord_3753250
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223068413155932228042301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91261515768415819274779469 34223068413155932228042301)
  ·
    refine ⟨12833650654933474585515863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34223068413155932228042301 12833650654933474585515863)
    ·
      refine ⟨19250475982400211878273795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833650654933474585515863 19250475982400211878273795)
      ·
        refine ⟨28875713973600317817410693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19250475982400211878273795 28875713973600317817410693)
        ·
          refine ⟨5414196370050059590764505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28875713973600317817410693 5414196370050059590764505)
          ·
            refine ⟨4060647277537544693073379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414196370050059590764505 4060647277537544693073379)
            ·
              refine ⟨6090970916306317039610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060647277537544693073379 6090970916306317039610069)
              ·
                refine ⟨142757130850929305615861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6090970916306317039610069 142757130850929305615861)
                ·
                  rfl

theorem cell22_3753250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_3753250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753250 prefixEnd_3753250 := by exact prefixLift 3753250
  have htrace : WordTrace (prefixWord ++ tailWord_3753250) baseStart_3753250 baseEnd_3753250 := by
    simpa [prefixWord, tailWord_3753250, baseEnd_3753250] using wordTrace_append hprefix tailTrace_3753250
  have hstable : (prefixWord ++ tailWord_3753250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753250).length < 2 ^ (prefixWord ++ tailWord_3753250).sum := by decide
  have hdescent : baseEnd_3753250 < baseStart_3753250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753265 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_3753265 : Nat := 118140960795 + 3753265 * 2 ^ 59
def prefixEnd_3753265 : Nat := 4983230072969 + 3 ^ 40 * 3753265 * 2
def baseEnd_3753265 : Nat := 1284819312464908711417703

theorem tailTrace_3753265 : CollatzResearch.WordTrace tailWord_3753265 prefixEnd_3753265 1284819312464908711417703 := by
  unfold tailWord_3753265
  simp only [CollatzResearch.WordTrace]
  refine ⟨136892820747569386473965249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91261880498379590982643499 136892820747569386473965249)
  ·
    refine ⟨102669615560677039855473937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136892820747569386473965249 102669615560677039855473937)
    ·
      refine ⟨77002211670507779891605453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102669615560677039855473937 77002211670507779891605453)
      ·
        refine ⟨28875829376440417459352045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77002211670507779891605453 28875829376440417459352045)
        ·
          refine ⟨10828436016165156547257017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28875829376440417459352045 10828436016165156547257017)
          ·
            refine ⟨8121327012123867410442763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10828436016165156547257017 8121327012123867410442763)
            ·
              refine ⟨12181990518185801115664145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121327012123867410442763 12181990518185801115664145)
              ·
                refine ⟨9136492888639350836748109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12181990518185801115664145 9136492888639350836748109)
                ·
                  refine ⟨3426184833239756563780541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9136492888639350836748109 3426184833239756563780541)
                  ·
                    refine ⟨1284819312464908711417703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426184833239756563780541 1284819312464908711417703)
                    ·
                      rfl

theorem cell22_3753265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_3753265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753265 prefixEnd_3753265 := by exact prefixLift 3753265
  have htrace : WordTrace (prefixWord ++ tailWord_3753265) baseStart_3753265 baseEnd_3753265 := by
    simpa [prefixWord, tailWord_3753265, baseEnd_3753265] using wordTrace_append hprefix tailTrace_3753265
  have hstable : (prefixWord ++ tailWord_3753265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753265).length < 2 ^ (prefixWord ++ tailWord_3753265).sum := by decide
  have hdescent : baseEnd_3753265 < baseStart_3753265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753278 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_3753278 : Nat := 118140960795 + 3753278 * 2 ^ 59
def prefixEnd_3753278 : Nat := 4983230072969 + 3 ^ 40 * 3753278 * 2
def baseEnd_3753278 : Nat := 428274587543527003614221

theorem tailTrace_3753278 : CollatzResearch.WordTrace tailWord_3753278 prefixEnd_3753278 428274587543527003614221 := by
  unfold tailWord_3753278
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111661862065286211773561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91262196597681526462792325 17111661862065286211773561)
  ·
    refine ⟨12833746396548964658830171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17111661862065286211773561 12833746396548964658830171)
    ·
      refine ⟨19250619594823446988245257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833746396548964658830171 19250619594823446988245257)
      ·
        refine ⟨14437964696117585241183943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19250619594823446988245257 14437964696117585241183943)
        ·
          refine ⟨21656947044176377861775915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14437964696117585241183943 21656947044176377861775915)
          ·
            refine ⟨32485420566264566792663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656947044176377861775915 32485420566264566792663873)
            ·
              refine ⟨24364065424698425094497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32485420566264566792663873 24364065424698425094497905)
              ·
                refine ⟨18273049068523818820873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24364065424698425094497905 18273049068523818820873429)
                ·
                  refine ⟨428274587543527003614221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18273049068523818820873429 428274587543527003614221)
                  ·
                    rfl

theorem cell22_3753278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_3753278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753278 prefixEnd_3753278 := by exact prefixLift 3753278
  have htrace : WordTrace (prefixWord ++ tailWord_3753278) baseStart_3753278 baseEnd_3753278 := by
    simpa [prefixWord, tailWord_3753278, baseEnd_3753278] using wordTrace_append hprefix tailTrace_3753278
  have hstable : (prefixWord ++ tailWord_3753278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753278).length < 2 ^ (prefixWord ++ tailWord_3753278).sum := by decide
  have hdescent : baseEnd_3753278 < baseStart_3753278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753325 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3753325 : Nat := 118140960795 + 3753325 * 2 ^ 59
def prefixEnd_3753325 : Nat := 4983230072969 + 3 ^ 40 * 3753325 * 2
def baseEnd_3753325 : Nat := 1284839851691088554917519

theorem tailTrace_3753325 : CollatzResearch.WordTrace tailWord_3753325 prefixEnd_3753325 1284839851691088554917519 := by
  unfold tailWord_3753325
  simp only [CollatzResearch.WordTrace]
  refine ⟨136895009127352016721149429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91263339418234677814099619 136895009127352016721149429)
  ·
    refine ⟨12833907105689251567607759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136895009127352016721149429 12833907105689251567607759)
    ·
      refine ⟨19250860658533877351411639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833907105689251567607759 19250860658533877351411639)
      ·
        refine ⟨28876290987800816027117459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19250860658533877351411639 28876290987800816027117459)
        ·
          refine ⟨43314436481701224040676189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28876290987800816027117459 43314436481701224040676189)
          ·
            refine ⟨16242913680637959015253571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43314436481701224040676189 16242913680637959015253571)
            ·
              refine ⟨24364370520956938522880357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16242913680637959015253571 24364370520956938522880357)
              ·
                refine ⟨4568319472679425973040067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24364370520956938522880357 4568319472679425973040067)
                ·
                  refine ⟨6852479209019138959560101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568319472679425973040067 6852479209019138959560101)
                  ·
                    refine ⟨1284839851691088554917519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852479209019138959560101 1284839851691088554917519)
                    ·
                      rfl

theorem cell22_3753325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3753325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753325 prefixEnd_3753325 := by exact prefixLift 3753325
  have htrace : WordTrace (prefixWord ++ tailWord_3753325) baseStart_3753325 baseEnd_3753325 := by
    simpa [prefixWord, tailWord_3753325, baseEnd_3753325] using wordTrace_append hprefix tailTrace_3753325
  have hstable : (prefixWord ++ tailWord_3753325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753325).length < 2 ^ (prefixWord ++ tailWord_3753325).sum := by decide
  have hdescent : baseEnd_3753325 < baseStart_3753325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753355 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 2, 3]
def baseStart_3753355 : Nat := 118140960795 + 3753355 * 2 ^ 59
def prefixEnd_3753355 : Nat := 4983230072969 + 3 ^ 40 * 3753355 * 2
def baseEnd_3753355 : Nat := 1284850121304178476667427

theorem tailTrace_3753355 : CollatzResearch.WordTrace tailWord_3753355 prefixEnd_3753355 1284850121304178476667427 := by
  unfold tailWord_3753355
  simp only [CollatzResearch.WordTrace]
  refine ⟨136896103317243331844741519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91264068878162221229827679 136896103317243331844741519)
  ·
    refine ⟨205344154975864997767112279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136896103317243331844741519 205344154975864997767112279)
    ·
      refine ⟨308016232463797496650668419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205344154975864997767112279 308016232463797496650668419)
      ·
        refine ⟨462024348695696244976002629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308016232463797496650668419 462024348695696244976002629)
        ·
          refine ⟨86629565380443045933000493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462024348695696244976002629 86629565380443045933000493)
          ·
            refine ⟨32486087017666142224875185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86629565380443045933000493 32486087017666142224875185)
            ·
              refine ⟨24364565263249606668656389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32486087017666142224875185 24364565263249606668656389)
              ·
                refine ⟨4568355986859301250373073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24364565263249606668656389 4568355986859301250373073)
                ·
                  refine ⟨3426266990144475937779805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568355986859301250373073 3426266990144475937779805)
                  ·
                    refine ⟨1284850121304178476667427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426266990144475937779805 1284850121304178476667427)
                    ·
                      rfl

theorem cell22_3753355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 3].length) (baseStart_3753355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753355 prefixEnd_3753355 := by exact prefixLift 3753355
  have htrace : WordTrace (prefixWord ++ tailWord_3753355) baseStart_3753355 baseEnd_3753355 := by
    simpa [prefixWord, tailWord_3753355, baseEnd_3753355] using wordTrace_append hprefix tailTrace_3753355
  have hstable : (prefixWord ++ tailWord_3753355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753355).length < 2 ^ (prefixWord ++ tailWord_3753355).sum := by decide
  have hdescent : baseEnd_3753355 < baseStart_3753355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753502 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3753502 : Nat := 118140960795 + 3753502 * 2 ^ 59
def prefixEnd_3753502 : Nat := 4983230072969 + 3 ^ 40 * 3753502 * 2
def baseEnd_3753502 : Nat := 1284900442408319093241977

theorem tailTrace_3753502 : CollatzResearch.WordTrace tailWord_3753502 prefixEnd_3753502 1284900442408319093241977 := by
  unfold tailWord_3753502
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112683105963846993792845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91267643231807183966895173 17112683105963846993792845)
  ·
    refine ⟨6417256164736442622672317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17112683105963846993792845 6417256164736442622672317)
    ·
      refine ⟨2406471061776165983502119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6417256164736442622672317 2406471061776165983502119)
      ·
        refine ⟨3609706592664248975253179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406471061776165983502119 3609706592664248975253179)
        ·
          refine ⟨5414559888996373462879769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609706592664248975253179 5414559888996373462879769)
          ·
            refine ⟨4060919916747280097159827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414559888996373462879769 4060919916747280097159827)
            ·
              refine ⟨6091379875120920145739741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060919916747280097159827 6091379875120920145739741)
              ·
                refine ⟨2284267453170345054652403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6091379875120920145739741 2284267453170345054652403)
                ·
                  refine ⟨3426401179755517581978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284267453170345054652403 3426401179755517581978605)
                  ·
                    refine ⟨1284900442408319093241977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426401179755517581978605 1284900442408319093241977)
                    ·
                      rfl

theorem cell22_3753502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3753502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753502 prefixEnd_3753502 := by exact prefixLift 3753502
  have htrace : WordTrace (prefixWord ++ tailWord_3753502) baseStart_3753502 baseEnd_3753502 := by
    simpa [prefixWord, tailWord_3753502, baseEnd_3753502] using wordTrace_append hprefix tailTrace_3753502
  have hstable : (prefixWord ++ tailWord_3753502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753502).length < 2 ^ (prefixWord ++ tailWord_3753502).sum := by decide
  have hdescent : baseEnd_3753502 < baseStart_3753502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753505 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_3753505 : Nat := 118140960795 + 3753505 * 2 ^ 59
def prefixEnd_3753505 : Nat := 4983230072969 + 3 ^ 40 * 3753505 * 2
def baseEnd_3753505 : Nat := 1284901469369628085416967

theorem tailTrace_3753505 : CollatzResearch.WordTrace tailWord_3753505 prefixEnd_3753505 1284901469369628085416967 := by
  unfold tailWord_3753505
  simp only [CollatzResearch.WordTrace]
  refine ⟨136901574266699907462701969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91267716177799938308467979 136901574266699907462701969)
  ·
    refine ⟨102676180700024930597026477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136901574266699907462701969 102676180700024930597026477)
    ·
      refine ⟨38503567762509348973884929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102676180700024930597026477 38503567762509348973884929)
      ·
        refine ⟨28877675821882011730413697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38503567762509348973884929 28877675821882011730413697)
        ·
          refine ⟨21658256866411508797810273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28877675821882011730413697 21658256866411508797810273)
          ·
            refine ⟨16243692649808631598357705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21658256866411508797810273 16243692649808631598357705)
            ·
              refine ⟨12182769487356473698768279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16243692649808631598357705 12182769487356473698768279)
              ·
                refine ⟨18274154231034710548152419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182769487356473698768279 18274154231034710548152419)
                ·
                  refine ⟨27411231346552065822228629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18274154231034710548152419 27411231346552065822228629)
                  ·
                    refine ⟨1284901469369628085416967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27411231346552065822228629 1284901469369628085416967)
                    ·
                      rfl

theorem cell22_3753505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_3753505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753505 prefixEnd_3753505 := by exact prefixLift 3753505
  have htrace : WordTrace (prefixWord ++ tailWord_3753505) baseStart_3753505 baseEnd_3753505 := by
    simpa [prefixWord, tailWord_3753505, baseEnd_3753505] using wordTrace_append hprefix tailTrace_3753505
  have hstable : (prefixWord ++ tailWord_3753505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753505).length < 2 ^ (prefixWord ++ tailWord_3753505).sum := by decide
  have hdescent : baseEnd_3753505 < baseStart_3753505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753526 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3753526 : Nat := 118140960795 + 3753526 * 2 ^ 59
def prefixEnd_3753526 : Nat := 4983230072969 + 3 ^ 40 * 3753526 * 2
def baseEnd_3753526 : Nat := 428302886032930343547301

theorem tailTrace_3753526 : CollatzResearch.WordTrace tailWord_3753526 prefixEnd_3753526 428302886032930343547301 := by
  unfold tailWord_3753526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556396262476489253076027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91268226799749218699477621 8556396262476489253076027)
  ·
    refine ⟨12834594393714733879614041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556396262476489253076027 12834594393714733879614041)
    ·
      refine ⟨9625945795286050409710531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12834594393714733879614041 9625945795286050409710531)
      ·
        refine ⟨14438918692929075614565797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625945795286050409710531 14438918692929075614565797)
        ·
          refine ⟨2707297254924201677731087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14438918692929075614565797 2707297254924201677731087)
          ·
            refine ⟨4060945882386302516596631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707297254924201677731087 4060945882386302516596631)
            ·
              refine ⟨6091418823579453774894947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060945882386302516596631 6091418823579453774894947)
              ·
                refine ⟨9137128235369180662342421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091418823579453774894947 9137128235369180662342421)
                ·
                  refine ⟨428302886032930343547301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9137128235369180662342421 428302886032930343547301)
                  ·
                    rfl

theorem cell22_3753526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3753526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753526 prefixEnd_3753526 := by exact prefixLift 3753526
  have htrace : WordTrace (prefixWord ++ tailWord_3753526) baseStart_3753526 baseEnd_3753526 := by
    simpa [prefixWord, tailWord_3753526, baseEnd_3753526] using wordTrace_append hprefix tailTrace_3753526
  have hstable : (prefixWord ++ tailWord_3753526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753526).length < 2 ^ (prefixWord ++ tailWord_3753526).sum := by decide
  have hdescent : baseEnd_3753526 < baseStart_3753526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753569 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3753569 : Nat := 118140960795 + 3753569 * 2 ^ 59
def prefixEnd_3753569 : Nat := 4983230072969 + 3 ^ 40 * 3753569 * 2
def baseEnd_3753569 : Nat := 1284923377877553251816771

theorem tailTrace_3753569 : CollatzResearch.WordTrace tailWord_3753569 prefixEnd_3753569 1284923377877553251816771 := by
  unfold tailWord_3753569
  simp only [CollatzResearch.WordTrace]
  refine ⟨136903908538468046393031761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91269272358978697595354507 136903908538468046393031761)
  ·
    refine ⟨102677931403851034794773821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136903908538468046393031761 102677931403851034794773821)
    ·
      refine ⟨38504224276444138048040183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102677931403851034794773821 38504224276444138048040183)
      ·
        refine ⟨57756336414666207072060275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38504224276444138048040183 57756336414666207072060275)
        ·
          refine ⟨86634504621999310608090413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57756336414666207072060275 86634504621999310608090413)
          ·
            refine ⟨32487939233249741478033905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86634504621999310608090413 32487939233249741478033905)
            ·
              refine ⟨24365954424937306108525429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32487939233249741478033905 24365954424937306108525429)
              ·
                refine ⟨2284308227337872447674259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24365954424937306108525429 2284308227337872447674259)
                ·
                  refine ⟨3426462341006808671511389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284308227337872447674259 3426462341006808671511389)
                  ·
                    refine ⟨1284923377877553251816771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426462341006808671511389 1284923377877553251816771)
                    ·
                      rfl

theorem cell22_3753569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3753569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753569 prefixEnd_3753569 := by exact prefixLift 3753569
  have htrace : WordTrace (prefixWord ++ tailWord_3753569) baseStart_3753569 baseEnd_3753569 := by
    simpa [prefixWord, tailWord_3753569, baseEnd_3753569] using wordTrace_append hprefix tailTrace_3753569
  have hstable : (prefixWord ++ tailWord_3753569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753569).length < 2 ^ (prefixWord ++ tailWord_3753569).sum := by decide
  have hdescent : baseEnd_3753569 < baseStart_3753569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753580 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_3753580 : Nat := 118140960795 + 3753580 * 2 ^ 59
def prefixEnd_3753580 : Nat := 4983230072969 + 3 ^ 40 * 3753580 * 2
def baseEnd_3753580 : Nat := 1284927143402352889791737

theorem tailTrace_3753580 : CollatzResearch.WordTrace tailWord_3753580 prefixEnd_3753580 1284927143402352889791737 := by
  unfold tailWord_3753580
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452154870714097635841097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91269539827618796847788129 68452154870714097635841097)
  ·
    refine ⟨51339116153035573226880823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68452154870714097635841097 51339116153035573226880823)
    ·
      refine ⟨77008674229553359840321235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51339116153035573226880823 77008674229553359840321235)
      ·
        refine ⟨115513011344330039760481853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77008674229553359840321235 115513011344330039760481853)
        ·
          refine ⟨43317379254123764910180695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115513011344330039760481853 43317379254123764910180695)
          ·
            refine ⟨64976068881185647365271043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43317379254123764910180695 64976068881185647365271043)
            ·
              refine ⟨97464103321778471047906565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64976068881185647365271043 97464103321778471047906565)
              ·
                refine ⟨18274519372833463321482481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97464103321778471047906565 18274519372833463321482481)
                ·
                  refine ⟨13705889529625097491111861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18274519372833463321482481 13705889529625097491111861)
                  ·
                    refine ⟨1284927143402352889791737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13705889529625097491111861 1284927143402352889791737)
                    ·
                      rfl

theorem cell22_3753580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_3753580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753580 prefixEnd_3753580 := by exact prefixLift 3753580
  have htrace : WordTrace (prefixWord ++ tailWord_3753580) baseStart_3753580 baseEnd_3753580 := by
    simpa [prefixWord, tailWord_3753580, baseEnd_3753580] using wordTrace_append hprefix tailTrace_3753580
  have hstable : (prefixWord ++ tailWord_3753580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753580).length < 2 ^ (prefixWord ++ tailWord_3753580).sum := by decide
  have hdescent : baseEnd_3753580 < baseStart_3753580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753586 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_3753586 : Nat := 118140960795 + 3753586 * 2 ^ 59
def prefixEnd_3753586 : Nat := 4983230072969 + 3 ^ 40 * 3753586 * 2
def baseEnd_3753586 : Nat := 1284929197324970874141719

theorem tailTrace_3753586 : CollatzResearch.WordTrace tailWord_3753586 prefixEnd_3753586 1284929197324970874141719 := by
  unfold tailWord_3753586
  simp only [CollatzResearch.WordTrace]
  refine ⟨34226132144851614574100153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91269685719604305530933741 34226132144851614574100153)
  ·
    refine ⟨25669599108638710930575115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34226132144851614574100153 25669599108638710930575115)
    ·
      refine ⟨38504398662958066395862673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25669599108638710930575115 38504398662958066395862673)
      ·
        refine ⟨28878298997218549796897005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38504398662958066395862673 28878298997218549796897005)
        ·
          refine ⟨10829362123956956173836377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28878298997218549796897005 10829362123956956173836377)
          ·
            refine ⟨8122021592967717130377283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829362123956956173836377 8122021592967717130377283)
            ·
              refine ⟨12183032389451575695565925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122021592967717130377283 12183032389451575695565925)
              ·
                refine ⟨2284318573022170442918611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12183032389451575695565925 2284318573022170442918611)
                ·
                  refine ⟨3426477859533255664377917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284318573022170442918611 3426477859533255664377917)
                  ·
                    refine ⟨1284929197324970874141719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426477859533255664377917 1284929197324970874141719)
                    ·
                      rfl

theorem cell22_3753586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_3753586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753586 prefixEnd_3753586 := by exact prefixLift 3753586
  have htrace : WordTrace (prefixWord ++ tailWord_3753586) baseStart_3753586 baseEnd_3753586 := by
    simpa [prefixWord, tailWord_3753586, baseEnd_3753586] using wordTrace_append hprefix tailTrace_3753586
  have hstable : (prefixWord ++ tailWord_3753586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753586).length < 2 ^ (prefixWord ++ tailWord_3753586).sum := by decide
  have hdescent : baseEnd_3753586 < baseStart_3753586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753595 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_3753595 : Nat := 118140960795 + 3753595 * 2 ^ 59
def prefixEnd_3753595 : Nat := 4983230072969 + 3 ^ 40 * 3753595 * 2
def baseEnd_3753595 : Nat := 1284932278208897850666691

theorem tailTrace_3753595 : CollatzResearch.WordTrace tailWord_3753595 prefixEnd_3753595 1284932278208897850666691 := by
  unfold tailWord_3753595
  simp only [CollatzResearch.WordTrace]
  refine ⟨136904856836373852833478239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91269904557582568555652159 136904856836373852833478239)
  ·
    refine ⟨205357285254560779250217359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136904856836373852833478239 205357285254560779250217359)
    ·
      refine ⟨308035927881841168875326039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205357285254560779250217359 308035927881841168875326039)
      ·
        refine ⟨462053891822761753312989059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308035927881841168875326039 462053891822761753312989059)
        ·
          refine ⟨693080837734142629969483589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462053891822761753312989059 693080837734142629969483589)
          ·
            refine ⟨129952657075151743119278173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 693080837734142629969483589 129952657075151743119278173)
            ·
              refine ⟨48732246403181903669729315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129952657075151743119278173 48732246403181903669729315)
              ·
                refine ⟨73098369604772855504593973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48732246403181903669729315 73098369604772855504593973)
                ·
                  refine ⟨6852972150447455203555685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73098369604772855504593973 6852972150447455203555685)
                  ·
                    refine ⟨1284932278208897850666691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852972150447455203555685 1284932278208897850666691)
                    ·
                      rfl

theorem cell22_3753595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_3753595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753595 prefixEnd_3753595 := by exact prefixLift 3753595
  have htrace : WordTrace (prefixWord ++ tailWord_3753595) baseStart_3753595 baseEnd_3753595 := by
    simpa [prefixWord, tailWord_3753595, baseEnd_3753595] using wordTrace_append hprefix tailTrace_3753595
  have hstable : (prefixWord ++ tailWord_3753595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753595).length < 2 ^ (prefixWord ++ tailWord_3753595).sum := by decide
  have hdescent : baseEnd_3753595 < baseStart_3753595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753597 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3753597 : Nat := 118140960795 + 3753597 * 2 ^ 59
def prefixEnd_3753597 : Nat := 4983230072969 + 3 ^ 40 * 3753597 * 2
def baseEnd_3753597 : Nat := 1284932962849770512116685

theorem tailTrace_3753597 : CollatzResearch.WordTrace tailWord_3753597 prefixEnd_3753597 1284932962849770512116685 := by
  unfold tailWord_3753597
  simp only [CollatzResearch.WordTrace]
  refine ⟨136904929782366607175051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91269953188244404783367363 136904929782366607175051045)
  ·
    refine ⟨25669674334193738845322071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136904929782366607175051045 25669674334193738845322071)
    ·
      refine ⟨38504511501290608267983107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25669674334193738845322071 38504511501290608267983107)
      ·
        refine ⟨57756767251935912401974661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38504511501290608267983107 57756767251935912401974661)
        ·
          refine ⟨10829393859737983575370249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57756767251935912401974661 10829393859737983575370249)
          ·
            refine ⟨8122045394803487681527687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829393859737983575370249 8122045394803487681527687)
            ·
              refine ⟨12183068092205231522291531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122045394803487681527687 12183068092205231522291531)
              ·
                refine ⟨18274602138307847283437297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12183068092205231522291531 18274602138307847283437297)
                ·
                  refine ⟨13705951603730885462577973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18274602138307847283437297 13705951603730885462577973)
                  ·
                    refine ⟨1284932962849770512116685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13705951603730885462577973 1284932962849770512116685)
                    ·
                      rfl

theorem cell22_3753597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3753597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753597 prefixEnd_3753597 := by exact prefixLift 3753597
  have htrace : WordTrace (prefixWord ++ tailWord_3753597) baseStart_3753597 baseEnd_3753597 := by
    simpa [prefixWord, tailWord_3753597, baseEnd_3753597] using wordTrace_append hprefix tailTrace_3753597
  have hstable : (prefixWord ++ tailWord_3753597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753597).length < 2 ^ (prefixWord ++ tailWord_3753597).sum := by decide
  have hdescent : baseEnd_3753597 < baseStart_3753597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753612 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_3753612 : Nat := 118140960795 + 3753612 * 2 ^ 59
def prefixEnd_3753612 : Nat := 4983230072969 + 3 ^ 40 * 3753612 * 2
def baseEnd_3753612 : Nat := 1284938097656315472991639

theorem tailTrace_3753612 : CollatzResearch.WordTrace tailWord_3753612 prefixEnd_3753612 1284938097656315472991639 := by
  unfold tailWord_3753612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68452738438656132368423545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91270317918208176491231393 68452738438656132368423545)
  ·
    refine ⟨51339553828992099276317659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68452738438656132368423545 51339553828992099276317659)
    ·
      refine ⟨77009330743488148914476489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51339553828992099276317659 77009330743488148914476489)
      ·
        refine ⟨57756998057616111685857367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77009330743488148914476489 57756998057616111685857367)
        ·
          refine ⟨86635497086424167528786051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57756998057616111685857367 86635497086424167528786051)
          ·
            refine ⟨129953245629636251293179077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86635497086424167528786051 129953245629636251293179077)
            ·
              refine ⟨24366233555556797117471077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129953245629636251293179077 24366233555556797117471077)
              ·
                refine ⟨4568668791666899459525827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24366233555556797117471077 4568668791666899459525827)
                ·
                  refine ⟨6853003187500349189288741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568668791666899459525827 6853003187500349189288741)
                  ·
                    refine ⟨1284938097656315472991639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853003187500349189288741 1284938097656315472991639)
                    ·
                      rfl

theorem cell22_3753612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3753612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753612 prefixEnd_3753612 := by exact prefixLift 3753612
  have htrace : WordTrace (prefixWord ++ tailWord_3753612) baseStart_3753612 baseEnd_3753612 := by
    simpa [prefixWord, tailWord_3753612, baseEnd_3753612] using wordTrace_append hprefix tailTrace_3753612
  have hstable : (prefixWord ++ tailWord_3753612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753612).length < 2 ^ (prefixWord ++ tailWord_3753612).sum := by decide
  have hdescent : baseEnd_3753612 < baseStart_3753612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753625 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_3753625 : Nat := 118140960795 + 3753625 * 2 ^ 59
def prefixEnd_3753625 : Nat := 4983230072969 + 3 ^ 40 * 3753625 * 2
def baseEnd_3753625 : Nat := 1284942547821987772416599

theorem tailTrace_3753625 : CollatzResearch.WordTrace tailWord_3753625 prefixEnd_3753625 1284942547821987772416599 := by
  unfold tailWord_3753625
  simp only [CollatzResearch.WordTrace]
  refine ⟨136905951026265167957070329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91270634017510111971380219 136905951026265167957070329)
  ·
    refine ⟨102679463269698875967802747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136905951026265167957070329 102679463269698875967802747)
    ·
      refine ⟨154019194904548313951704121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102679463269698875967802747 154019194904548313951704121)
      ·
        refine ⟨115514396178411235463778091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154019194904548313951704121 115514396178411235463778091)
        ·
          refine ⟨173271594267616853195667137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115514396178411235463778091 173271594267616853195667137)
          ·
            refine ⟨129953695700712639896750353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173271594267616853195667137 129953695700712639896750353)
            ·
              refine ⟨97465271775534479922562765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129953695700712639896750353 97465271775534479922562765)
              ·
                refine ⟨36549476915825429970961037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97465271775534479922562765 36549476915825429970961037)
                ·
                  refine ⟨13706053843434536239110389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36549476915825429970961037 13706053843434536239110389)
                  ·
                    refine ⟨1284942547821987772416599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706053843434536239110389 1284942547821987772416599)
                    ·
                      rfl

theorem cell22_3753625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_3753625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753625 prefixEnd_3753625 := by exact prefixLift 3753625
  have htrace : WordTrace (prefixWord ++ tailWord_3753625) baseStart_3753625 baseEnd_3753625 := by
    simpa [prefixWord, tailWord_3753625, baseEnd_3753625] using wordTrace_append hprefix tailTrace_3753625
  have hstable : (prefixWord ++ tailWord_3753625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753625).length < 2 ^ (prefixWord ++ tailWord_3753625).sum := by decide
  have hdescent : baseEnd_3753625 < baseStart_3753625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753764 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 3, 4]
def baseStart_3753764 : Nat := 118140960795 + 3753764 * 2 ^ 59
def prefixEnd_3753764 : Nat := 4983230072969 + 3 ^ 40 * 3753764 * 2
def baseEnd_3753764 : Nat := 1284990130362637743191173

theorem tailTrace_3753764 : CollatzResearch.WordTrace tailWord_3753764 prefixEnd_3753764 1284990130362637743191173 := by
  unfold tailWord_3753764
  simp only [CollatzResearch.WordTrace]
  refine ⟨68455510386380797348190173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91274013848507729797586897 68455510386380797348190173)
  ·
    refine ⟨25670816394892799005571315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68455510386380797348190173 25670816394892799005571315)
    ·
      refine ⟨38506224592339198508356973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25670816394892799005571315 38506224592339198508356973)
      ·
        refine ⟨14439834222127199440633865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38506224592339198508356973 14439834222127199440633865)
        ·
          refine ⟨10829875666595399580475399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14439834222127199440633865 10829875666595399580475399)
          ·
            refine ⟨16244813499893099370713099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10829875666595399580475399 16244813499893099370713099)
            ·
              refine ⟨24367220249839649056069649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16244813499893099370713099 24367220249839649056069649)
              ·
                refine ⟨18275415187379736792052237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24367220249839649056069649 18275415187379736792052237)
                ·
                  refine ⟨6853280695267401297019589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18275415187379736792052237 6853280695267401297019589)
                  ·
                    refine ⟨1284990130362637743191173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853280695267401297019589 1284990130362637743191173)
                    ·
                      rfl

theorem cell22_3753764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_3753764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753764 prefixEnd_3753764 := by exact prefixLift 3753764
  have htrace : WordTrace (prefixWord ++ tailWord_3753764) baseStart_3753764 baseEnd_3753764 := by
    simpa [prefixWord, tailWord_3753764, baseEnd_3753764] using wordTrace_append hprefix tailTrace_3753764
  have hstable : (prefixWord ++ tailWord_3753764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753764).length < 2 ^ (prefixWord ++ tailWord_3753764).sum := by decide
  have hdescent : baseEnd_3753764 < baseStart_3753764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753779 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 6]
def baseStart_3753779 : Nat := 118140960795 + 3753779 * 2 ^ 59
def prefixEnd_3753779 : Nat := 4983230072969 + 3 ^ 40 * 3753779 * 2
def baseEnd_3753779 : Nat := 428331755056394234688709

theorem tailTrace_3753779 : CollatzResearch.WordTrace tailWord_3753779 prefixEnd_3753779 428331755056394234688709 := by
  unfold tailWord_3753779
  simp only [CollatzResearch.WordTrace]
  refine ⟨136911567867707252258176391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91274378578471501505450927 136911567867707252258176391)
  ·
    refine ⟨205367351801560878387264587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136911567867707252258176391 205367351801560878387264587)
    ·
      refine ⟨308051027702341317580896881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205367351801560878387264587 308051027702341317580896881)
      ·
        refine ⟨231038270776755988185672661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308051027702341317580896881 231038270776755988185672661)
        ·
          refine ⟨5414959471330218473101703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231038270776755988185672661 5414959471330218473101703)
          ·
            refine ⟨8122439206995327709652555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414959471330218473101703 8122439206995327709652555)
            ·
              refine ⟨12183658810492991564478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122439206995327709652555 12183658810492991564478833)
              ·
                refine ⟨9137744107869743673359125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12183658810492991564478833 9137744107869743673359125)
                ·
                  refine ⟨428331755056394234688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9137744107869743673359125 428331755056394234688709)
                  ·
                    rfl

theorem cell22_3753779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_3753779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753779 prefixEnd_3753779 := by exact prefixLift 3753779
  have htrace : WordTrace (prefixWord ++ tailWord_3753779) baseStart_3753779 baseEnd_3753779 := by
    simpa [prefixWord, tailWord_3753779, baseEnd_3753779] using wordTrace_append hprefix tailTrace_3753779
  have hstable : (prefixWord ++ tailWord_3753779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753779).length < 2 ^ (prefixWord ++ tailWord_3753779).sum := by decide
  have hdescent : baseEnd_3753779 < baseStart_3753779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753828 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3753828 : Nat := 118140960795 + 3753828 * 2 ^ 59
def prefixEnd_3753828 : Nat := 4983230072969 + 3 ^ 40 * 3753828 * 2
def baseEnd_3753828 : Nat := 1285012038870562909590977

theorem tailTrace_3753828 : CollatzResearch.WordTrace tailWord_3753828 prefixEnd_3753828 1285012038870562909590977 := by
  unfold tailWord_3753828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68456677522264866813355069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91275570029686489084473425 68456677522264866813355069)
  ·
    refine ⟨25671254070849325055008151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68456677522264866813355069 25671254070849325055008151)
    ·
      refine ⟨38506881106273987582512227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25671254070849325055008151 38506881106273987582512227)
      ·
        refine ⟨57760321659410981373768341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38506881106273987582512227 57760321659410981373768341)
        ·
          refine ⟨2707515077784889751895391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57760321659410981373768341 2707515077784889751895391)
          ·
            refine ⟨4061272616677334627843087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707515077784889751895391 4061272616677334627843087)
            ·
              refine ⟨6091908925016001941764631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061272616677334627843087 6091908925016001941764631)
              ·
                refine ⟨9137863387524002912646947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091908925016001941764631 9137863387524002912646947)
                ·
                  refine ⟨13706795081286004368970421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137863387524002912646947 13706795081286004368970421)
                  ·
                    refine ⟨1285012038870562909590977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706795081286004368970421 1285012038870562909590977)
                    ·
                      rfl

theorem cell22_3753828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3753828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753828 prefixEnd_3753828 := by exact prefixLift 3753828
  have htrace : WordTrace (prefixWord ++ tailWord_3753828) baseStart_3753828 baseEnd_3753828 := by
    simpa [prefixWord, tailWord_3753828, baseEnd_3753828] using wordTrace_append hprefix tailTrace_3753828
  have hstable : (prefixWord ++ tailWord_3753828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753828).length < 2 ^ (prefixWord ++ tailWord_3753828).sum := by decide
  have hdescent : baseEnd_3753828 < baseStart_3753828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753931 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 4]
def baseStart_3753931 : Nat := 118140960795 + 3753931 * 2 ^ 59
def prefixEnd_3753931 : Nat := 4983230072969 + 3 ^ 40 * 3753931 * 2
def baseEnd_3753931 : Nat := 428349099291834991421887

theorem tailTrace_3753931 : CollatzResearch.WordTrace tailWord_3753931 prefixEnd_3753931 428349099291834991421887 := by
  unfold tailWord_3753931
  simp only [CollatzResearch.WordTrace]
  refine ⟨136917111763156582217709647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91278074508771054811806431 136917111763156582217709647)
  ·
    refine ⟨205375667644734873326564471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136917111763156582217709647 205375667644734873326564471)
    ·
      refine ⟨308063501467102309989846707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205375667644734873326564471 308063501467102309989846707)
      ·
        refine ⟨462095252200653464984770061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308063501467102309989846707 462095252200653464984770061)
        ·
          refine ⟨173285719575245049369288773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462095252200653464984770061 173285719575245049369288773)
          ·
            refine ⟨32491072420358446756741645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173285719575245049369288773 32491072420358446756741645)
            ·
              refine ⟨12184152157634417533778117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32491072420358446756741645 12184152157634417533778117)
              ·
                refine ⟨2284528529556453287583397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12184152157634417533778117 2284528529556453287583397)
                ·
                  refine ⟨428349099291834991421887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284528529556453287583397 428349099291834991421887)
                  ·
                    rfl

theorem cell22_3753931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 4].length) (baseStart_3753931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753931 prefixEnd_3753931 := by exact prefixLift 3753931
  have htrace : WordTrace (prefixWord ++ tailWord_3753931) baseStart_3753931 baseEnd_3753931 := by
    simpa [prefixWord, tailWord_3753931, baseEnd_3753931] using wordTrace_append hprefix tailTrace_3753931
  have hstable : (prefixWord ++ tailWord_3753931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753931).length < 2 ^ (prefixWord ++ tailWord_3753931).sum := by decide
  have hdescent : baseEnd_3753931 < baseStart_3753931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3753944 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3753944 : Nat := 118140960795 + 3753944 * 2 ^ 59
def prefixEnd_3753944 : Nat := 4983230072969 + 3 ^ 40 * 3753944 * 2
def baseEnd_3753944 : Nat := 1285051748041177273690621

theorem tailTrace_3753944 : CollatzResearch.WordTrace tailWord_3753944 prefixEnd_3753944 1285051748041177273690621 := by
  unfold tailWord_3753944
  simp only [CollatzResearch.WordTrace]
  refine ⟨68458792956054742718966443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91278390608072990291955257 68458792956054742718966443)
  ·
    refine ⟨102688189434082114078449665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68458792956054742718966443 102688189434082114078449665)
    ·
      refine ⟨77016142075561585558837249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102688189434082114078449665 77016142075561585558837249)
      ·
        refine ⟨57762106556671189169127937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77016142075561585558837249 57762106556671189169127937)
        ·
          refine ⟨43321579917503391876845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57762106556671189169127937 43321579917503391876845953)
          ·
            refine ⟨32491184938127543907634465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43321579917503391876845953 32491184938127543907634465)
            ·
              refine ⟨24368388703595657930725849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32491184938127543907634465 24368388703595657930725849)
              ·
                refine ⟨18276291527696743448044387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24368388703595657930725849 18276291527696743448044387)
                ·
                  refine ⟨27414437291545115172066581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18276291527696743448044387 27414437291545115172066581)
                  ·
                    refine ⟨1285051748041177273690621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27414437291545115172066581 1285051748041177273690621)
                    ·
                      rfl

theorem cell22_3753944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3753944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3753944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3753944 prefixEnd_3753944 := by exact prefixLift 3753944
  have htrace : WordTrace (prefixWord ++ tailWord_3753944) baseStart_3753944 baseEnd_3753944 := by
    simpa [prefixWord, tailWord_3753944, baseEnd_3753944] using wordTrace_append hprefix tailTrace_3753944
  have hstable : (prefixWord ++ tailWord_3753944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3753944).length < 2 ^ (prefixWord ++ tailWord_3753944).sum := by decide
  have hdescent : baseEnd_3753944 < baseStart_3753944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3753944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754038 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_3754038 : Nat := 118140960795 + 3754038 * 2 ^ 59
def prefixEnd_3754038 : Nat := 4983230072969 + 3 ^ 40 * 3754038 * 2
def baseEnd_3754038 : Nat := 428361308720730787280111

theorem tailTrace_3754038 : CollatzResearch.WordTrace tailWord_3754038 prefixEnd_3754038 428361308720730787280111 := by
  unfold tailWord_3754038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557563398360558718240923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91280676249179292994569845 8557563398360558718240923)
  ·
    refine ⟨12836345097540838077361385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557563398360558718240923 12836345097540838077361385)
    ·
      refine ⟨9627258823155628558021039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12836345097540838077361385 9627258823155628558021039)
      ·
        refine ⟨14440888234733442837031559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627258823155628558021039 14440888234733442837031559)
        ·
          refine ⟨21661332352100164255547339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14440888234733442837031559 21661332352100164255547339)
          ·
            refine ⟨32491998528150246383321009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21661332352100164255547339 32491998528150246383321009)
            ·
              refine ⟨24368998896112684787490757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32491998528150246383321009 24368998896112684787490757)
              ·
                refine ⟨4569187293021128397654517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24368998896112684787490757 4569187293021128397654517)
                ·
                  refine ⟨428361308720730787280111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4569187293021128397654517 428361308720730787280111)
                  ·
                    rfl

theorem cell22_3754038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_3754038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754038 prefixEnd_3754038 := by exact prefixLift 3754038
  have htrace : WordTrace (prefixWord ++ tailWord_3754038) baseStart_3754038 baseEnd_3754038 := by
    simpa [prefixWord, tailWord_3754038, baseEnd_3754038] using wordTrace_append hprefix tailTrace_3754038
  have hstable : (prefixWord ++ tailWord_3754038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754038).length < 2 ^ (prefixWord ++ tailWord_3754038).sum := by decide
  have hdescent : baseEnd_3754038 < baseStart_3754038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754085 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_3754085 : Nat := 118140960795 + 3754085 * 2 ^ 59
def prefixEnd_3754085 : Nat := 4983230072969 + 3 ^ 40 * 3754085 * 2
def baseEnd_3754085 : Nat := 1285100015222699905915189

theorem tailTrace_3754085 : CollatzResearch.WordTrace tailWord_3754085 prefixEnd_3754085 1285100015222699905915189 := by
  unfold tailWord_3754085
  simp only [CollatzResearch.WordTrace]
  refine ⟨136922728604598666518815709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91281819069732444345877139 136922728604598666518815709)
  ·
    refine ⟨51346023226724499944555891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136922728604598666518815709 51346023226724499944555891)
    ·
      refine ⟨77019034840086749916833837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51346023226724499944555891 77019034840086749916833837)
      ·
        refine ⟨28882138065032531218812689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77019034840086749916833837 28882138065032531218812689)
        ·
          refine ⟨21661603548774398414109517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28882138065032531218812689 21661603548774398414109517)
          ·
            refine ⟨8123101330790399405291069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21661603548774398414109517 8123101330790399405291069)
            ·
              refine ⟨3046162999046399776984151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123101330790399405291069 3046162999046399776984151)
              ·
                refine ⟨4569244498569599665476227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046162999046399776984151 4569244498569599665476227)
                ·
                  refine ⟨6853866747854399498214341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569244498569599665476227 6853866747854399498214341)
                  ·
                    refine ⟨1285100015222699905915189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6853866747854399498214341 1285100015222699905915189)
                    ·
                      rfl

theorem cell22_3754085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_3754085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754085 prefixEnd_3754085 := by exact prefixLift 3754085
  have htrace : WordTrace (prefixWord ++ tailWord_3754085) baseStart_3754085 baseEnd_3754085 := by
    simpa [prefixWord, tailWord_3754085, baseEnd_3754085] using wordTrace_append hprefix tailTrace_3754085
  have hstable : (prefixWord ++ tailWord_3754085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754085).length < 2 ^ (prefixWord ++ tailWord_3754085).sum := by decide
  have hdescent : baseEnd_3754085 < baseStart_3754085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754171 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_3754171 : Nat := 118140960795 + 3754171 * 2 ^ 59
def prefixEnd_3754171 : Nat := 4983230072969 + 3 ^ 40 * 3754171 * 2
def baseEnd_3754171 : Nat := 1285129454780224348264925

theorem tailTrace_3754171 : CollatzResearch.WordTrace tailWord_3754171 prefixEnd_3754171 1285129454780224348264925 := by
  unfold tailWord_3754171
  simp only [CollatzResearch.WordTrace]
  refine ⟨136925865282287103206446367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91283910188191402137630911 136925865282287103206446367)
  ·
    refine ⟨205388797923430654809669551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136925865282287103206446367 205388797923430654809669551)
    ·
      refine ⟨308083196885145982214504327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205388797923430654809669551 308083196885145982214504327)
      ·
        refine ⟨462124795327718973321756491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308083196885145982214504327 462124795327718973321756491)
        ·
          refine ⟨693187192991578459982634737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462124795327718973321756491 693187192991578459982634737)
          ·
            refine ⟨519890394743683844986976053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 693187192991578459982634737 519890394743683844986976053)
            ·
              refine ⟨48739724507220360467529005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 519890394743683844986976053 48739724507220360467529005)
              ·
                refine ⟨18277396690207635175323377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48739724507220360467529005 18277396690207635175323377)
                ·
                  refine ⟨13708047517655726381492533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18277396690207635175323377 13708047517655726381492533)
                  ·
                    refine ⟨1285129454780224348264925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13708047517655726381492533 1285129454780224348264925)
                    ·
                      rfl

theorem cell22_3754171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_3754171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754171 prefixEnd_3754171 := by exact prefixLift 3754171
  have htrace : WordTrace (prefixWord ++ tailWord_3754171) baseStart_3754171 baseEnd_3754171 := by
    simpa [prefixWord, tailWord_3754171, baseEnd_3754171] using wordTrace_append hprefix tailTrace_3754171
  have hstable : (prefixWord ++ tailWord_3754171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754171).length < 2 ^ (prefixWord ++ tailWord_3754171).sum := by decide
  have hdescent : baseEnd_3754171 < baseStart_3754171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754194 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 1, 3]
def baseStart_3754194 : Nat := 118140960795 + 3754194 * 2 ^ 59
def prefixEnd_3754194 : Nat := 4983230072969 + 3 ^ 40 * 3754194 * 2
def baseEnd_3754194 : Nat := 1285137328150259954939855

theorem tailTrace_3754194 : CollatzResearch.WordTrace tailWord_3754194 prefixEnd_3754194 1285137328150259954939855 := by
  unfold tailWord_3754194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231676040300944533633409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91284469440802518756355757 34231676040300944533633409)
  ·
    refine ⟨25673757030225708400225057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34231676040300944533633409 25673757030225708400225057)
    ·
      refine ⟨19255317772669281300168793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25673757030225708400225057 19255317772669281300168793)
      ·
        refine ⟨14441488329501960975126595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19255317772669281300168793 14441488329501960975126595)
        ·
          refine ⟨21662232494252941462689893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14441488329501960975126595 21662232494252941462689893)
          ·
            refine ⟨4061668592672426524254355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21662232494252941462689893 4061668592672426524254355)
            ·
              refine ⟨6092502889008639786381533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061668592672426524254355 6092502889008639786381533)
              ·
                refine ⟨2284688583378239919893075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6092502889008639786381533 2284688583378239919893075)
                ·
                  refine ⟨3427032875067359879839613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284688583378239919893075 3427032875067359879839613)
                  ·
                    refine ⟨1285137328150259954939855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427032875067359879839613 1285137328150259954939855)
                    ·
                      rfl

theorem cell22_3754194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_3754194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754194 prefixEnd_3754194 := by exact prefixLift 3754194
  have htrace : WordTrace (prefixWord ++ tailWord_3754194) baseStart_3754194 baseEnd_3754194 := by
    simpa [prefixWord, tailWord_3754194, baseEnd_3754194] using wordTrace_append hprefix tailTrace_3754194
  have hstable : (prefixWord ++ tailWord_3754194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754194).length < 2 ^ (prefixWord ++ tailWord_3754194).sum := by decide
  have hdescent : baseEnd_3754194 < baseStart_3754194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754201 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 8]
def baseStart_3754201 : Nat := 118140960795 + 3754201 * 2 ^ 59
def prefixEnd_3754201 : Nat := 4983230072969 + 3 ^ 40 * 3754201 * 2
def baseEnd_3754201 : Nat := 428379908131104756671611

theorem tailTrace_3754201 : CollatzResearch.WordTrace tailWord_3754201 prefixEnd_3754201 428379908131104756671611 := by
  unfold tailWord_3754201
  simp only [CollatzResearch.WordTrace]
  refine ⟨136926959472178418330038457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91284639648118945553358971 136926959472178418330038457)
  ·
    refine ⟨102695219604133813747528843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136926959472178418330038457 102695219604133813747528843)
    ·
      refine ⟨154042829406200720621293265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102695219604133813747528843 154042829406200720621293265)
      ·
        refine ⟨115532122054650540465969949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154042829406200720621293265 115532122054650540465969949)
        ·
          refine ⟨43324545770493952674738731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115532122054650540465969949 43324545770493952674738731)
          ·
            refine ⟨64986818655740929012108097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43324545770493952674738731 64986818655740929012108097)
            ·
              refine ⟨48740113991805696759081073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64986818655740929012108097 48740113991805696759081073)
              ·
                refine ⟨36555085493854272569310805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48740113991805696759081073 36555085493854272569310805)
                ·
                  refine ⟨428379908131104756671611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36555085493854272569310805 428379908131104756671611)
                  ·
                    rfl

theorem cell22_3754201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_3754201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754201 prefixEnd_3754201 := by exact prefixLift 3754201
  have htrace : WordTrace (prefixWord ++ tailWord_3754201) baseStart_3754201 baseEnd_3754201 := by
    simpa [prefixWord, tailWord_3754201, baseEnd_3754201] using wordTrace_append hprefix tailTrace_3754201
  have hstable : (prefixWord ++ tailWord_3754201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754201).length < 2 ^ (prefixWord ++ tailWord_3754201).sum := by decide
  have hdescent : baseEnd_3754201 < baseStart_3754201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754211 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 1, 3]
def baseStart_3754211 : Nat := 118140960795 + 3754211 * 2 ^ 59
def prefixEnd_3754211 : Nat := 4983230072969 + 3 ^ 40 * 3754211 * 2
def baseEnd_3754211 : Nat := 1285143147597677577264803

theorem tailTrace_3754211 : CollatzResearch.WordTrace tailWord_3754211 prefixEnd_3754211 1285143147597677577264803 := by
  unfold tailWord_3754211
  simp only [CollatzResearch.WordTrace]
  refine ⟨136927324202142190037902487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91284882801428126691934991 136927324202142190037902487)
  ·
    refine ⟨205390986303213285056853731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136927324202142190037902487 205390986303213285056853731)
    ·
      refine ⟨308086479454819927585280597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205390986303213285056853731 308086479454819927585280597)
      ·
        refine ⟨3610388431111171026390007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 308086479454819927585280597 3610388431111171026390007)
        ·
          refine ⟨5415582646666756539585011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610388431111171026390007 5415582646666756539585011)
          ·
            refine ⟨8123373970000134809377517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415582646666756539585011 8123373970000134809377517)
            ·
              refine ⟨3046265238750050553516569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123373970000134809377517 3046265238750050553516569)
              ·
                refine ⟨2284698929062537915137427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3046265238750050553516569 2284698929062537915137427)
                ·
                  refine ⟨3427048393593806872706141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284698929062537915137427 3427048393593806872706141)
                  ·
                    refine ⟨1285143147597677577264803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427048393593806872706141 1285143147597677577264803)
                    ·
                      rfl

theorem cell22_3754211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 3].length) (baseStart_3754211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754211 prefixEnd_3754211 := by exact prefixLift 3754211
  have htrace : WordTrace (prefixWord ++ tailWord_3754211) baseStart_3754211 baseEnd_3754211 := by
    simpa [prefixWord, tailWord_3754211, baseEnd_3754211] using wordTrace_append hprefix tailTrace_3754211
  have hstable : (prefixWord ++ tailWord_3754211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754211).length < 2 ^ (prefixWord ++ tailWord_3754211).sum := by decide
  have hdescent : baseEnd_3754211 < baseStart_3754211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754233 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_3754233 : Nat := 118140960795 + 3754233 * 2 ^ 59
def prefixEnd_3754233 : Nat := 4983230072969 + 3 ^ 40 * 3754233 * 2
def baseEnd_3754233 : Nat := 1285150678647276853214735

theorem tailTrace_3754233 : CollatzResearch.WordTrace tailWord_3754233 prefixEnd_3754233 1285150678647276853214735 := by
  unfold tailWord_3754233
  simp only [CollatzResearch.WordTrace]
  refine ⟨136928126608062487795203353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91285417738708325196802235 136928126608062487795203353)
  ·
    refine ⟨102696094956046865846402515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136928126608062487795203353 102696094956046865846402515)
    ·
      refine ⟨154044142434070298769603773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102696094956046865846402515 154044142434070298769603773)
      ·
        refine ⟨57766553412776362038601415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154044142434070298769603773 57766553412776362038601415)
        ·
          refine ⟨86649830119164543057902123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57766553412776362038601415 86649830119164543057902123)
          ·
            refine ⟨129974745178746814586853185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649830119164543057902123 129974745178746814586853185)
            ·
              refine ⟨97481058884060110940139889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129974745178746814586853185 97481058884060110940139889)
              ·
                refine ⟨73110794163045083205104917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97481058884060110940139889 73110794163045083205104917)
                ·
                  refine ⟨3427068476392738275239293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73110794163045083205104917 3427068476392738275239293)
                  ·
                    refine ⟨1285150678647276853214735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427068476392738275239293 1285150678647276853214735)
                    ·
                      rfl

theorem cell22_3754233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_3754233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754233 prefixEnd_3754233 := by exact prefixLift 3754233
  have htrace : WordTrace (prefixWord ++ tailWord_3754233) baseStart_3754233 baseEnd_3754233 := by
    simpa [prefixWord, tailWord_3754233, baseEnd_3754233] using wordTrace_append hprefix tailTrace_3754233
  have hstable : (prefixWord ++ tailWord_3754233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754233).length < 2 ^ (prefixWord ++ tailWord_3754233).sum := by decide
  have hdescent : baseEnd_3754233 < baseStart_3754233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754293 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_3754293 : Nat := 118140960795 + 3754293 * 2 ^ 59
def prefixEnd_3754293 : Nat := 4983230072969 + 3 ^ 40 * 3754293 * 2
def baseEnd_3754293 : Nat := 1285171217873456696714551

theorem tailTrace_3754293 : CollatzResearch.WordTrace tailWord_3754293 prefixEnd_3754293 1285171217873456696714551 := by
  unfold tailWord_3754293
  simp only [CollatzResearch.WordTrace]
  refine ⟨136930314987845118042387533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91286876658563412028258355 136930314987845118042387533)
  ·
    refine ⟨51348868120441919265895325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136930314987845118042387533 51348868120441919265895325)
    ·
      refine ⟨19255825545165719724710747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51348868120441919265895325 19255825545165719724710747)
      ·
        refine ⟨28883738317748579587066121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255825545165719724710747 28883738317748579587066121)
        ·
          refine ⟨21662803738311434690299591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28883738317748579587066121 21662803738311434690299591)
          ·
            refine ⟨32494205607467152035449387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662803738311434690299591 32494205607467152035449387)
            ·
              refine ⟨48741308411200728053174081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32494205607467152035449387 48741308411200728053174081)
              ·
                refine ⟨36555981308400546039880561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48741308411200728053174081 36555981308400546039880561)
                ·
                  refine ⟨27416985981300409529910421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36555981308400546039880561 27416985981300409529910421)
                  ·
                    refine ⟨1285171217873456696714551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27416985981300409529910421 1285171217873456696714551)
                    ·
                      rfl

theorem cell22_3754293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_3754293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754293 prefixEnd_3754293 := by exact prefixLift 3754293
  have htrace : WordTrace (prefixWord ++ tailWord_3754293) baseStart_3754293 baseEnd_3754293 := by
    simpa [prefixWord, tailWord_3754293, baseEnd_3754293] using wordTrace_append hprefix tailTrace_3754293
  have hstable : (prefixWord ++ tailWord_3754293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754293).length < 2 ^ (prefixWord ++ tailWord_3754293).sum := by decide
  have hdescent : baseEnd_3754293 < baseStart_3754293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754312 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 1, 3]
def baseStart_3754312 : Nat := 118140960795 + 3754312 * 2 ^ 59
def prefixEnd_3754312 : Nat := 4983230072969 + 3 ^ 40 * 3754312 * 2
def baseEnd_3754312 : Nat := 1285177721961746980489493

theorem tailTrace_3754312 : CollatzResearch.WordTrace tailWord_3754312 prefixEnd_3754312 1285177721961746980489493 := by
  unfold tailWord_3754312
  simp only [CollatzResearch.WordTrace]
  refine ⟨68465503987388142143664595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91287338649850856191552793 68465503987388142143664595)
  ·
    refine ⟨102698255981082213215496893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68465503987388142143664595 102698255981082213215496893)
    ·
      refine ⟨38511845992905829955811335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102698255981082213215496893 38511845992905829955811335)
      ·
        refine ⟨57767768989358744933717003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38511845992905829955811335 57767768989358744933717003)
        ·
          refine ⟨86651653484038117400575505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57767768989358744933717003 86651653484038117400575505)
          ·
            refine ⟨64988740113028588050431629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86651653484038117400575505 64988740113028588050431629)
            ·
              refine ⟨24370777542385720518911861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64988740113028588050431629 24370777542385720518911861)
              ·
                refine ⟨2284760394598661298647987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24370777542385720518911861 2284760394598661298647987)
                ·
                  refine ⟨3427140591897991947971981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284760394598661298647987 3427140591897991947971981)
                  ·
                    refine ⟨1285177721961746980489493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427140591897991947971981 1285177721961746980489493)
                    ·
                      rfl

theorem cell22_3754312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_3754312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754312 prefixEnd_3754312 := by exact prefixLift 3754312
  have htrace : WordTrace (prefixWord ++ tailWord_3754312) baseStart_3754312 baseEnd_3754312 := by
    simpa [prefixWord, tailWord_3754312, baseEnd_3754312] using wordTrace_append hprefix tailTrace_3754312
  have hstable : (prefixWord ++ tailWord_3754312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754312).length < 2 ^ (prefixWord ++ tailWord_3754312).sum := by decide
  have hdescent : baseEnd_3754312 < baseStart_3754312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754325 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 7]
def baseStart_3754325 : Nat := 118140960795 + 3754325 * 2 ^ 59
def prefixEnd_3754325 : Nat := 4983230072969 + 3 ^ 40 * 3754325 * 2
def baseEnd_3754325 : Nat := 428394057375806426638151

theorem tailTrace_3754325 : CollatzResearch.WordTrace tailWord_3754325 prefixEnd_3754325 428394057375806426638151 := by
  unfold tailWord_3754325
  simp only [CollatzResearch.WordTrace]
  refine ⟨136931482123729187507552429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91287654749152791671701619 136931482123729187507552429)
  ·
    refine ⟨51349305796398445315332161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136931482123729187507552429 51349305796398445315332161)
    ·
      refine ⟨38511979347298833986499121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51349305796398445315332161 38511979347298833986499121)
      ·
        refine ⟨28883984510474125489874341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38511979347298833986499121 28883984510474125489874341)
        ·
          refine ⟨5415747095713898529351439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28883984510474125489874341 5415747095713898529351439)
          ·
            refine ⟨8123620643570847794027159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415747095713898529351439 8123620643570847794027159)
            ·
              refine ⟨12185430965356271691040739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123620643570847794027159 12185430965356271691040739)
              ·
                refine ⟨18278146448034407536561109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185430965356271691040739 18278146448034407536561109)
                ·
                  refine ⟨428394057375806426638151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18278146448034407536561109 428394057375806426638151)
                  ·
                    rfl

theorem cell22_3754325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_3754325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754325 prefixEnd_3754325 := by exact prefixLift 3754325
  have htrace : WordTrace (prefixWord ++ tailWord_3754325) baseStart_3754325 baseEnd_3754325 := by
    simpa [prefixWord, tailWord_3754325, baseEnd_3754325] using wordTrace_append hprefix tailTrace_3754325
  have hstable : (prefixWord ++ tailWord_3754325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754325).length < 2 ^ (prefixWord ++ tailWord_3754325).sum := by decide
  have hdescent : baseEnd_3754325 < baseStart_3754325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754417 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_3754417 : Nat := 118140960795 + 3754417 * 2 ^ 59
def prefixEnd_3754417 : Nat := 4983230072969 + 3 ^ 40 * 3754417 * 2
def baseEnd_3754417 : Nat := 1285213665607561706614171

theorem tailTrace_3754417 : CollatzResearch.WordTrace tailWord_3754417 prefixEnd_3754417 1285213665607561706614171 := by
  unfold tailWord_3754417
  simp only [CollatzResearch.WordTrace]
  refine ⟨136934837639395887219901505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91289891759597258146601003 136934837639395887219901505)
  ·
    refine ⟨102701128229546915414926129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136934837639395887219901505 102701128229546915414926129)
    ·
      refine ⟨77025846172160186561194597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102701128229546915414926129 77025846172160186561194597)
      ·
        refine ⟨14442346157280034980223987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77025846172160186561194597 14442346157280034980223987)
        ·
          refine ⟨21663519235920052470335981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442346157280034980223987 21663519235920052470335981)
          ·
            refine ⟨8123819713470019676375993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21663519235920052470335981 8123819713470019676375993)
            ·
              refine ⟨6092864785102514757281995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123819713470019676375993 6092864785102514757281995)
              ·
                refine ⟨9139297177653772135922993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092864785102514757281995 9139297177653772135922993)
                ·
                  refine ⟨6854472883240329101942245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9139297177653772135922993 6854472883240329101942245)
                  ·
                    refine ⟨1285213665607561706614171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854472883240329101942245 1285213665607561706614171)
                    ·
                      rfl

theorem cell22_3754417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_3754417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754417 prefixEnd_3754417 := by exact prefixLift 3754417
  have htrace : WordTrace (prefixWord ++ tailWord_3754417) baseStart_3754417 baseEnd_3754417 := by
    simpa [prefixWord, tailWord_3754417, baseEnd_3754417] using wordTrace_append hprefix tailTrace_3754417
  have hstable : (prefixWord ++ tailWord_3754417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754417).length < 2 ^ (prefixWord ++ tailWord_3754417).sum := by decide
  have hdescent : baseEnd_3754417 < baseStart_3754417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754436 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3754436 : Nat := 118140960795 + 3754436 * 2 ^ 59
def prefixEnd_3754436 : Nat := 4983230072969 + 3 ^ 40 * 3754436 * 2
def baseEnd_3754436 : Nat := 1285220169695851990389113

theorem tailTrace_3754436 : CollatzResearch.WordTrace tailWord_3754436 prefixEnd_3754436 1285220169695851990389113 := by
  unfold tailWord_3754436
  simp only [CollatzResearch.WordTrace]
  refine ⟨68467765313163526732421581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91290353750884702309895441 68467765313163526732421581)
  ·
    refine ⟨25675411992436322524658093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68467765313163526732421581 25675411992436322524658093)
    ·
      refine ⟨9628279497163620946746785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25675411992436322524658093 9628279497163620946746785)
      ·
        refine ⟨7221209622872715710060089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9628279497163620946746785 7221209622872715710060089)
        ·
          refine ⟨5415907217154536782545067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7221209622872715710060089 5415907217154536782545067)
          ·
            refine ⟨8123860825731805173817601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415907217154536782545067 8123860825731805173817601)
            ·
              refine ⟨6092895619298853880363201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123860825731805173817601 6092895619298853880363201)
              ·
                refine ⟨4569671714474140410272401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6092895619298853880363201 4569671714474140410272401)
                ·
                  refine ⟨3427253785855605307704301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569671714474140410272401 3427253785855605307704301)
                  ·
                    refine ⟨1285220169695851990389113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427253785855605307704301 1285220169695851990389113)
                    ·
                      rfl

theorem cell22_3754436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3754436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754436 prefixEnd_3754436 := by exact prefixLift 3754436
  have htrace : WordTrace (prefixWord ++ tailWord_3754436) baseStart_3754436 baseEnd_3754436 := by
    simpa [prefixWord, tailWord_3754436, baseEnd_3754436] using wordTrace_append hprefix tailTrace_3754436
  have hstable : (prefixWord ++ tailWord_3754436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754436).length < 2 ^ (prefixWord ++ tailWord_3754436).sum := by decide
  have hdescent : baseEnd_3754436 < baseStart_3754436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754466 : List Nat := [3, 3, 3, 2, 1, 1, 3, 6]
def baseStart_3754466 : Nat := 118140960795 + 3754466 * 2 ^ 59
def prefixEnd_3754466 : Nat := 4983230072969 + 3 ^ 40 * 3754466 * 2
def baseEnd_3754466 : Nat := 142803382145437990237669

theorem tailTrace_3754466 : CollatzResearch.WordTrace tailWord_3754466 prefixEnd_3754466 142803382145437990237669 := by
  unfold tailWord_3754466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234156204054592147108813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91291083210812245725623501 34234156204054592147108813)
  ·
    refine ⟨12837808576520472055165805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34234156204054592147108813 12837808576520472055165805)
    ·
      refine ⟨4814178216195177020687177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12837808576520472055165805 4814178216195177020687177)
      ·
        refine ⟨3610633662146382765515383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4814178216195177020687177 3610633662146382765515383)
        ·
          refine ⟨5415950493219574148273075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610633662146382765515383 5415950493219574148273075)
          ·
            refine ⟨8123925739829361222409613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415950493219574148273075 8123925739829361222409613)
            ·
              refine ⟨3046472152436010458403605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8123925739829361222409613 3046472152436010458403605)
              ·
                refine ⟨142803382145437990237669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3046472152436010458403605 142803382145437990237669)
                ·
                  rfl

theorem cell22_3754466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_3754466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754466 prefixEnd_3754466 := by exact prefixLift 3754466
  have htrace : WordTrace (prefixWord ++ tailWord_3754466) baseStart_3754466 baseEnd_3754466 := by
    simpa [prefixWord, tailWord_3754466, baseEnd_3754466] using wordTrace_append hprefix tailTrace_3754466
  have hstable : (prefixWord ++ tailWord_3754466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754466).length < 2 ^ (prefixWord ++ tailWord_3754466).sum := by decide
  have hdescent : baseEnd_3754466 < baseStart_3754466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_3754490 : Nat := 118140960795 + 3754490 * 2 ^ 59
def prefixEnd_3754490 : Nat := 4983230072969 + 3 ^ 40 * 3754490 * 2
def baseEnd_3754490 : Nat := 1285238654999413849538947

theorem tailTrace_3754490 : CollatzResearch.WordTrace tailWord_3754490 prefixEnd_3754490 1285238654999413849538947 := by
  unfold tailWord_3754490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234375042032855171827231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91291666778754280458205949 34234375042032855171827231)
  ·
    refine ⟨51351562563049282757740847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34234375042032855171827231 51351562563049282757740847)
    ·
      refine ⟨77027343844573924136611271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51351562563049282757740847 77027343844573924136611271)
      ·
        refine ⟨115541015766860886204916907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77027343844573924136611271 115541015766860886204916907)
        ·
          refine ⟨173311523650291329307375361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115541015766860886204916907 173311523650291329307375361)
          ·
            refine ⟨129983642737718496980531521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173311523650291329307375361 129983642737718496980531521)
            ·
              refine ⟨97487732053288872735398641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129983642737718496980531521 97487732053288872735398641)
              ·
                refine ⟨73115799039966654551548981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97487732053288872735398641 73115799039966654551548981)
                ·
                  refine ⟨6854606159996873864207717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73115799039966654551548981 6854606159996873864207717)
                  ·
                    refine ⟨1285238654999413849538947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854606159996873864207717 1285238654999413849538947)
                    ·
                      rfl

theorem cell22_3754490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_3754490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754490 prefixEnd_3754490 := by exact prefixLift 3754490
  have htrace : WordTrace (prefixWord ++ tailWord_3754490) baseStart_3754490 baseEnd_3754490 := by
    simpa [prefixWord, tailWord_3754490, baseEnd_3754490] using wordTrace_append hprefix tailTrace_3754490
  have hstable : (prefixWord ++ tailWord_3754490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754490).length < 2 ^ (prefixWord ++ tailWord_3754490).sum := by decide
  have hdescent : baseEnd_3754490 < baseStart_3754490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754524 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 1, 4]
def baseStart_3754524 : Nat := 118140960795 + 3754524 * 2 ^ 59
def prefixEnd_3754524 : Nat := 4983230072969 + 3 ^ 40 * 3754524 * 2
def baseEnd_3754524 : Nat := 1285250293894249094188843

theorem tailTrace_3754524 : CollatzResearch.WordTrace tailWord_3754524 prefixEnd_3754524 1285250293894249094188843 := by
  unfold tailWord_3754524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68469370125004122247023313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91292493500005496329364417 68469370125004122247023313)
  ·
    refine ⟨51352027593753091685267485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68469370125004122247023313 51352027593753091685267485)
    ·
      refine ⟨19257010347657409381975307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51352027593753091685267485 19257010347657409381975307)
      ·
        refine ⟨28885515521486114072962961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19257010347657409381975307 28885515521486114072962961)
        ·
          refine ⟨21664136641114585554722221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28885515521486114072962961 21664136641114585554722221)
          ·
            refine ⟨8124051240417969583020833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21664136641114585554722221 8124051240417969583020833)
            ·
              refine ⟨6093038430313477187265625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124051240417969583020833 6093038430313477187265625)
              ·
                refine ⟨4569778822735107890449219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093038430313477187265625 4569778822735107890449219)
                ·
                  refine ⟨6854668234102661835673829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569778822735107890449219 6854668234102661835673829)
                  ·
                    refine ⟨1285250293894249094188843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854668234102661835673829 1285250293894249094188843)
                    ·
                      rfl

theorem cell22_3754524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_3754524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754524 prefixEnd_3754524 := by exact prefixLift 3754524
  have htrace : WordTrace (prefixWord ++ tailWord_3754524) baseStart_3754524 baseEnd_3754524 := by
    simpa [prefixWord, tailWord_3754524, baseEnd_3754524] using wordTrace_append hprefix tailTrace_3754524
  have hstable : (prefixWord ++ tailWord_3754524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754524).length < 2 ^ (prefixWord ++ tailWord_3754524).sum := by decide
  have hdescent : baseEnd_3754524 < baseStart_3754524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754552 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 2, 4]
def baseStart_3754552 : Nat := 118140960795 + 3754552 * 2 ^ 59
def prefixEnd_3754552 : Nat := 4983230072969 + 3 ^ 40 * 3754552 * 2
def baseEnd_3754552 : Nat := 1285259878866466354488757

theorem tailTrace_3754552 : CollatzResearch.WordTrace tailWord_3754552 prefixEnd_3754552 1285259878866466354488757 := by
  unfold tailWord_3754552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68469880746953402638032955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91293174329271203517377273 68469880746953402638032955)
  ·
    refine ⟨102704821120430103957049433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68469880746953402638032955 102704821120430103957049433)
    ·
      refine ⟨77028615840322577967787075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102704821120430103957049433 77028615840322577967787075)
      ·
        refine ⟨115542923760483866951680613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77028615840322577967787075 115542923760483866951680613)
        ·
          refine ⟨21664298205090725053440115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115542923760483866951680613 21664298205090725053440115)
          ·
            refine ⟨32496447307636087580160173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21664298205090725053440115 32496447307636087580160173)
            ·
              refine ⟨12186167740363532842560065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32496447307636087580160173 12186167740363532842560065)
              ·
                refine ⟨9139625805272649631920049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12186167740363532842560065 9139625805272649631920049)
                ·
                  refine ⟨6854719353954487223940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9139625805272649631920049 6854719353954487223940037)
                  ·
                    refine ⟨1285259878866466354488757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854719353954487223940037 1285259878866466354488757)
                    ·
                      rfl

theorem cell22_3754552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_3754552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754552 prefixEnd_3754552 := by exact prefixLift 3754552
  have htrace : WordTrace (prefixWord ++ tailWord_3754552) baseStart_3754552 baseEnd_3754552 := by
    simpa [prefixWord, tailWord_3754552, baseEnd_3754552] using wordTrace_append hprefix tailTrace_3754552
  have hstable : (prefixWord ++ tailWord_3754552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754552).length < 2 ^ (prefixWord ++ tailWord_3754552).sum := by decide
  have hdescent : baseEnd_3754552 < baseStart_3754552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754556 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_3754556 : Nat := 118140960795 + 3754556 * 2 ^ 59
def prefixEnd_3754556 : Nat := 4983230072969 + 3 ^ 40 * 3754556 * 2
def baseEnd_3754556 : Nat := 428420416049403892462915

theorem tailTrace_3754556 : CollatzResearch.WordTrace tailWord_3754556 prefixEnd_3754556 428420416049403892462915 := by
  unfold tailWord_3754556
  simp only [CollatzResearch.WordTrace]
  refine ⟨68469953692946156979605761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91293271590594875972807681 68469953692946156979605761)
  ·
    refine ⟨51352465269709617734704321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68469953692946156979605761 51352465269709617734704321)
    ·
      refine ⟨38514348952282213301028241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51352465269709617734704321 38514348952282213301028241)
      ·
        refine ⟨28885761714211659975771181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38514348952282213301028241 28885761714211659975771181)
        ·
          refine ⟨10832160642829372490914193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28885761714211659975771181 10832160642829372490914193)
          ·
            refine ⟨8124120482122029368185645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10832160642829372490914193 8124120482122029368185645)
            ·
              refine ⟨3046545180795761013069617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8124120482122029368185645 3046545180795761013069617)
              ·
                refine ⟨2284908885596820759802213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3046545180795761013069617 2284908885596820759802213)
                ·
                  refine ⟨428420416049403892462915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284908885596820759802213 428420416049403892462915)
                  ·
                    rfl

theorem cell22_3754556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_3754556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754556 prefixEnd_3754556 := by exact prefixLift 3754556
  have htrace : WordTrace (prefixWord ++ tailWord_3754556) baseStart_3754556 baseEnd_3754556 := by
    simpa [prefixWord, tailWord_3754556, baseEnd_3754556] using wordTrace_append hprefix tailTrace_3754556
  have hstable : (prefixWord ++ tailWord_3754556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754556).length < 2 ^ (prefixWord ++ tailWord_3754556).sum := by decide
  have hdescent : baseEnd_3754556 < baseStart_3754556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754567 : List Nat := [1, 1, 4, 1, 4, 2, 2, 7]
def baseStart_3754567 : Nat := 118140960795 + 3754567 * 2 ^ 59
def prefixEnd_3754567 : Nat := 4983230072969 + 3 ^ 40 * 3754567 * 2
def baseEnd_3754567 : Nat := 142807223741445701707079

theorem tailTrace_3754567 : CollatzResearch.WordTrace tailWord_3754567 prefixEnd_3754567 142807223741445701707079 := by
  unfold tailWord_3754567
  simp only [CollatzResearch.WordTrace]
  refine ⟨136940308588852462837861955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91293539059234975225241303 136940308588852462837861955)
  ·
    refine ⟨205410462883278694256792933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136940308588852462837861955 205410462883278694256792933)
    ·
      refine ⟨38514461790614755173148675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205410462883278694256792933 38514461790614755173148675)
      ·
        refine ⟨57771692685922132759723013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38514461790614755173148675 57771692685922132759723013)
        ·
          refine ⟨10832192378610399892448065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57771692685922132759723013 10832192378610399892448065)
          ·
            refine ⟨8124144283957799919336049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10832192378610399892448065 8124144283957799919336049)
            ·
              refine ⟨6093108212968349939502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124144283957799919336049 6093108212968349939502037)
              ·
                refine ⟨142807223741445701707079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6093108212968349939502037 142807223741445701707079)
                ·
                  rfl

theorem cell22_3754567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 7].length) (baseStart_3754567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754567 prefixEnd_3754567 := by exact prefixLift 3754567
  have htrace : WordTrace (prefixWord ++ tailWord_3754567) baseStart_3754567 baseEnd_3754567 := by
    simpa [prefixWord, tailWord_3754567, baseEnd_3754567] using wordTrace_append hprefix tailTrace_3754567
  have hstable : (prefixWord ++ tailWord_3754567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754567).length < 2 ^ (prefixWord ++ tailWord_3754567).sum := by decide
  have hdescent : baseEnd_3754567 < baseStart_3754567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754650 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 1, 3]
def baseStart_3754650 : Nat := 118140960795 + 3754650 * 2 ^ 59
def prefixEnd_3754650 : Nat := 4983230072969 + 3 ^ 40 * 3754650 * 2
def baseEnd_3754650 : Nat := 1285293426269226765538457

theorem tailTrace_3754650 : CollatzResearch.WordTrace tailWord_3754650 prefixEnd_3754650 1285293426269226765538457 := by
  unfold tailWord_3754650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235833961887942003283351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91295557231701178675422269 34235833961887942003283351)
  ·
    refine ⟨51353750942831913004925027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34235833961887942003283351 51353750942831913004925027)
    ·
      refine ⟨77030626414247869507387541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51353750942831913004925027 77030626414247869507387541)
      ·
        refine ⟨3610810613167868883158791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77030626414247869507387541 3610810613167868883158791)
        ·
          refine ⟨5416215919751803324738187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610810613167868883158791 5416215919751803324738187)
          ·
            refine ⟨8124323879627704987107281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416215919751803324738187 8124323879627704987107281)
            ·
              refine ⟨6093242909720778740330461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124323879627704987107281 6093242909720778740330461)
              ·
                refine ⟨2284966091145292027623923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6093242909720778740330461 2284966091145292027623923)
                ·
                  refine ⟨3427449136717938041435885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284966091145292027623923 3427449136717938041435885)
                  ·
                    refine ⟨1285293426269226765538457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427449136717938041435885 1285293426269226765538457)
                    ·
                      rfl

theorem cell22_3754650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_3754650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754650 prefixEnd_3754650 := by exact prefixLift 3754650
  have htrace : WordTrace (prefixWord ++ tailWord_3754650) baseStart_3754650 baseEnd_3754650 := by
    simpa [prefixWord, tailWord_3754650, baseEnd_3754650] using wordTrace_append hprefix tailTrace_3754650
  have hstable : (prefixWord ++ tailWord_3754650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754650).length < 2 ^ (prefixWord ++ tailWord_3754650).sum := by decide
  have hdescent : baseEnd_3754650 < baseStart_3754650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754663 : List Nat := [1, 1, 6, 3, 1, 2, 1, 2, 5]
def baseStart_3754663 : Nat := 118140960795 + 3754663 * 2 ^ 59
def prefixEnd_3754663 : Nat := 4983230072969 + 3 ^ 40 * 3754663 * 2
def baseEnd_3754663 : Nat := 428432625478299688321139

theorem tailTrace_3754663 : CollatzResearch.WordTrace tailWord_3754663 prefixEnd_3754663 428432625478299688321139 := by
  unfold tailWord_3754663
  simp only [CollatzResearch.WordTrace]
  refine ⟨136943809996504671233356643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91295873331003114155571095 136943809996504671233356643)
  ·
    refine ⟨205415714994757006850034965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136943809996504671233356643 205415714994757006850034965)
    ·
      refine ⟨9628861640379234696095389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205415714994757006850034965 9628861640379234696095389)
      ·
        refine ⟨3610823115142213011035771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9628861640379234696095389 3610823115142213011035771)
        ·
          refine ⟨5416234672713319516553657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610823115142213011035771 5416234672713319516553657)
          ·
            refine ⟨4062176004534989637415243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416234672713319516553657 4062176004534989637415243)
            ·
              refine ⟨6093264006802484456122865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062176004534989637415243 6093264006802484456122865)
              ·
                refine ⟨4569948005101863342092149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093264006802484456122865 4569948005101863342092149)
                ·
                  refine ⟨428432625478299688321139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4569948005101863342092149 428432625478299688321139)
                  ·
                    rfl

theorem cell22_3754663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 2, 5].length) (baseStart_3754663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754663 prefixEnd_3754663 := by exact prefixLift 3754663
  have htrace : WordTrace (prefixWord ++ tailWord_3754663) baseStart_3754663 baseEnd_3754663 := by
    simpa [prefixWord, tailWord_3754663, baseEnd_3754663] using wordTrace_append hprefix tailTrace_3754663
  have hstable : (prefixWord ++ tailWord_3754663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754663).length < 2 ^ (prefixWord ++ tailWord_3754663).sum := by decide
  have hdescent : baseEnd_3754663 < baseStart_3754663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754687 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_3754687 : Nat := 118140960795 + 3754687 * 2 ^ 59
def prefixEnd_3754687 : Nat := 4983230072969 + 3 ^ 40 * 3754687 * 2
def baseEnd_3754687 : Nat := 1285306092125371002363343

theorem tailTrace_3754687 : CollatzResearch.WordTrace tailWord_3754687 prefixEnd_3754687 1285306092125371002363343 := by
  unfold tailWord_3754687
  simp only [CollatzResearch.WordTrace]
  refine ⟨136944685348417723332230315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91296456898945148888153543 136944685348417723332230315)
  ·
    refine ⟨205417028022626584998345473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136944685348417723332230315 205417028022626584998345473)
    ·
      refine ⟨154062771016969938748759105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205417028022626584998345473 154062771016969938748759105)
      ·
        refine ⟨115547078262727454061569329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154062771016969938748759105 115547078262727454061569329)
        ·
          refine ⟨86660308697045590546176997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115547078262727454061569329 86660308697045590546176997)
          ·
            refine ⟨16248807880696048227408187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86660308697045590546176997 16248807880696048227408187)
            ·
              refine ⟨24373211821044072341112281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16248807880696048227408187 24373211821044072341112281)
              ·
                refine ⟨18279908865783054255834211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24373211821044072341112281 18279908865783054255834211)
                ·
                  refine ⟨27419863298674581383751317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18279908865783054255834211 27419863298674581383751317)
                  ·
                    refine ⟨1285306092125371002363343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27419863298674581383751317 1285306092125371002363343)
                    ·
                      rfl

theorem cell22_3754687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_3754687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754687 prefixEnd_3754687 := by exact prefixLift 3754687
  have htrace : WordTrace (prefixWord ++ tailWord_3754687) baseStart_3754687 baseEnd_3754687 := by
    simpa [prefixWord, tailWord_3754687, baseEnd_3754687] using wordTrace_append hprefix tailTrace_3754687
  have hstable : (prefixWord ++ tailWord_3754687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754687).length < 2 ^ (prefixWord ++ tailWord_3754687).sum := by decide
  have hdescent : baseEnd_3754687 < baseStart_3754687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754732 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_3754732 : Nat := 118140960795 + 3754732 * 2 ^ 59
def prefixEnd_3754732 : Nat := 4983230072969 + 3 ^ 40 * 3754732 * 2
def baseEnd_3754732 : Nat := 1285321496545005884988205

theorem tailTrace_3754732 : CollatzResearch.WordTrace tailWord_3754732 prefixEnd_3754732 1285321496545005884988205 := by
  unfold tailWord_3754732
  simp only [CollatzResearch.WordTrace]
  refine ⟨68473163316627348008809225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91297551088836464011745633 68473163316627348008809225)
  ·
    refine ⟨51354872487470511006606919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68473163316627348008809225 51354872487470511006606919)
    ·
      refine ⟨77032308731205766509910379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51354872487470511006606919 77032308731205766509910379)
      ·
        refine ⟨115548463096808649764865569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77032308731205766509910379 115548463096808649764865569)
        ·
          refine ⟨86661347322606487323649177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115548463096808649764865569 86661347322606487323649177)
          ·
            refine ⟨64996010491954865492736883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86661347322606487323649177 64996010491954865492736883)
            ·
              refine ⟨97494015737932298239105325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64996010491954865492736883 97494015737932298239105325)
              ·
                refine ⟨36560255901724611839664497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97494015737932298239105325 36560255901724611839664497)
                ·
                  refine ⟨27420191926293458879748373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36560255901724611839664497 27420191926293458879748373)
                  ·
                    refine ⟨1285321496545005884988205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27420191926293458879748373 1285321496545005884988205)
                    ·
                      rfl

theorem cell22_3754732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_3754732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754732 prefixEnd_3754732 := by exact prefixLift 3754732
  have htrace : WordTrace (prefixWord ++ tailWord_3754732) baseStart_3754732 baseEnd_3754732 := by
    simpa [prefixWord, tailWord_3754732, baseEnd_3754732] using wordTrace_append hprefix tailTrace_3754732
  have hstable : (prefixWord ++ tailWord_3754732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754732).length < 2 ^ (prefixWord ++ tailWord_3754732).sum := by decide
  have hdescent : baseEnd_3754732 < baseStart_3754732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754824 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 5]
def baseStart_3754824 : Nat := 118140960795 + 3754824 * 2 ^ 59
def prefixEnd_3754824 : Nat := 4983230072969 + 3 ^ 40 * 3754824 * 2
def baseEnd_3754824 : Nat := 1285352990025148311687923

theorem tailTrace_3754824 : CollatzResearch.WordTrace tailWord_3754824 prefixEnd_3754824 1285352990025148311687923 := by
  unfold tailWord_3754824
  simp only [CollatzResearch.WordTrace]
  refine ⟨68474841074460697864983763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91299788099280930486645017 68474841074460697864983763)
  ·
    refine ⟨102712261611691046797475645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68474841074460697864983763 102712261611691046797475645)
    ·
      refine ⟨38517098104384142549053367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102712261611691046797475645 38517098104384142549053367)
      ·
        refine ⟨57775647156576213823580051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38517098104384142549053367 57775647156576213823580051)
        ·
          refine ⟨86663470734864320735370077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57775647156576213823580051 86663470734864320735370077)
          ·
            refine ⟨32498801525574120275763779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86663470734864320735370077 32498801525574120275763779)
            ·
              refine ⟨48748202288361180413645669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32498801525574120275763779 48748202288361180413645669)
              ·
                refine ⟨9140287929067721327558563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48748202288361180413645669 9140287929067721327558563)
                ·
                  refine ⟨13710431893601581991337845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9140287929067721327558563 13710431893601581991337845)
                  ·
                    refine ⟨1285352990025148311687923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13710431893601581991337845 1285352990025148311687923)
                    ·
                      rfl

theorem cell22_3754824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_3754824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754824 prefixEnd_3754824 := by exact prefixLift 3754824
  have htrace : WordTrace (prefixWord ++ tailWord_3754824) baseStart_3754824 baseEnd_3754824 := by
    simpa [prefixWord, tailWord_3754824, baseEnd_3754824] using wordTrace_append hprefix tailTrace_3754824
  have hstable : (prefixWord ++ tailWord_3754824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754824).length < 2 ^ (prefixWord ++ tailWord_3754824).sum := by decide
  have hdescent : baseEnd_3754824 < baseStart_3754824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754828 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_3754828 : Nat := 118140960795 + 3754828 * 2 ^ 59
def prefixEnd_3754828 : Nat := 4983230072969 + 3 ^ 40 * 3754828 * 2
def baseEnd_3754828 : Nat := 1285354359306893634587911

theorem tailTrace_3754828 : CollatzResearch.WordTrace tailWord_3754828 prefixEnd_3754828 1285354359306893634587911 := by
  unfold tailWord_3754828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68474914020453452206556569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91299885360604602942075425 68474914020453452206556569)
  ·
    refine ⟨51356185515340089154917427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68474914020453452206556569 51356185515340089154917427)
    ·
      refine ⟨77034278273010133732376141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51356185515340089154917427 77034278273010133732376141)
      ·
        refine ⟨28887854352378800149641053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77034278273010133732376141 28887854352378800149641053)
        ·
          refine ⟨10832945382142050056115395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28887854352378800149641053 10832945382142050056115395)
          ·
            refine ⟨16249418073213075084173093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10832945382142050056115395 16249418073213075084173093)
            ·
              refine ⟨3046765888727451578282455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16249418073213075084173093 3046765888727451578282455)
              ·
                refine ⟨4570148833091177367423683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046765888727451578282455 4570148833091177367423683)
                ·
                  refine ⟨6855223249636766051135525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570148833091177367423683 6855223249636766051135525)
                  ·
                    refine ⟨1285354359306893634587911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855223249636766051135525 1285354359306893634587911)
                    ·
                      rfl

theorem cell22_3754828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_3754828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754828 prefixEnd_3754828 := by exact prefixLift 3754828
  have htrace : WordTrace (prefixWord ++ tailWord_3754828) baseStart_3754828 baseEnd_3754828 := by
    simpa [prefixWord, tailWord_3754828, baseEnd_3754828] using wordTrace_append hprefix tailTrace_3754828
  have hstable : (prefixWord ++ tailWord_3754828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754828).length < 2 ^ (prefixWord ++ tailWord_3754828).sum := by decide
  have hdescent : baseEnd_3754828 < baseStart_3754828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754841 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_3754841 : Nat := 118140960795 + 3754841 * 2 ^ 59
def prefixEnd_3754841 : Nat := 4983230072969 + 3 ^ 40 * 3754841 * 2
def baseEnd_3754841 : Nat := 1285358809472565934012871

theorem tailTrace_3754841 : CollatzResearch.WordTrace tailWord_3754841 prefixEnd_3754841 1285358809472565934012871 := by
  unfold tailWord_3754841
  simp only [CollatzResearch.WordTrace]
  refine ⟨136950302189859807633336377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91300201459906538422224251 136950302189859807633336377)
  ·
    refine ⟨102712726642394855725002283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136950302189859807633336377 102712726642394855725002283)
    ·
      refine ⟨154069089963592283587503425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102712726642394855725002283 154069089963592283587503425)
      ·
        refine ⟨115551817472694212690627569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154069089963592283587503425 115551817472694212690627569)
        ·
          refine ⟨86663863104520659517970677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115551817472694212690627569 86663863104520659517970677)
          ·
            refine ⟨8124737166048811829809751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86663863104520659517970677 8124737166048811829809751)
            ·
              refine ⟨12187105749073217744714627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124737166048811829809751 12187105749073217744714627)
              ·
                refine ⟨18280658623609826617071941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187105749073217744714627 18280658623609826617071941)
                ·
                  refine ⟨3427623491926842490700989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18280658623609826617071941 3427623491926842490700989)
                  ·
                    refine ⟨1285358809472565934012871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427623491926842490700989 1285358809472565934012871)
                    ·
                      rfl

theorem cell22_3754841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_3754841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754841 prefixEnd_3754841 := by exact prefixLift 3754841
  have htrace : WordTrace (prefixWord ++ tailWord_3754841) baseStart_3754841 baseEnd_3754841 := by
    simpa [prefixWord, tailWord_3754841, baseEnd_3754841] using wordTrace_append hprefix tailTrace_3754841
  have hstable : (prefixWord ++ tailWord_3754841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754841).length < 2 ^ (prefixWord ++ tailWord_3754841).sum := by decide
  have hdescent : baseEnd_3754841 < baseStart_3754841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754884 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3754884 : Nat := 118140960795 + 3754884 * 2 ^ 59
def prefixEnd_3754884 : Nat := 4983230072969 + 3 ^ 40 * 3754884 * 2
def baseEnd_3754884 : Nat := 1285373529251328155187739

theorem tailTrace_3754884 : CollatzResearch.WordTrace tailWord_3754884 prefixEnd_3754884 1285373529251328155187739 := by
  unfold tailWord_3754884
  simp only [CollatzResearch.WordTrace]
  refine ⟨68475935264352012988575853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91301247019136017318101137 68475935264352012988575853)
  ·
    refine ⟨25678475724132004870715945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68475935264352012988575853 25678475724132004870715945)
    ·
      refine ⟨19258856793099003653036959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25678475724132004870715945 19258856793099003653036959)
      ·
        refine ⟨28888285189648505479555439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19258856793099003653036959 28888285189648505479555439)
        ·
          refine ⟨43332427784472758219333159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28888285189648505479555439 43332427784472758219333159)
          ·
            refine ⟨64998641676709137328999739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43332427784472758219333159 64998641676709137328999739)
            ·
              refine ⟨97497962515063705993499609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64998641676709137328999739 97497962515063705993499609)
              ·
                refine ⟨73123471886297779495124707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97497962515063705993499609 73123471886297779495124707)
                ·
                  refine ⟨109685207829446669242687061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73123471886297779495124707 109685207829446669242687061)
                  ·
                    refine ⟨1285373529251328155187739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109685207829446669242687061 1285373529251328155187739)
                    ·
                      rfl

theorem cell22_3754884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3754884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754884 prefixEnd_3754884 := by exact prefixLift 3754884
  have htrace : WordTrace (prefixWord ++ tailWord_3754884) baseStart_3754884 baseEnd_3754884 := by
    simpa [prefixWord, tailWord_3754884, baseEnd_3754884] using wordTrace_append hprefix tailTrace_3754884
  have hstable : (prefixWord ++ tailWord_3754884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754884).length < 2 ^ (prefixWord ++ tailWord_3754884).sum := by decide
  have hdescent : baseEnd_3754884 < baseStart_3754884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754916 : List Nat := [2, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_3754916 : Nat := 118140960795 + 3754916 * 2 ^ 59
def prefixEnd_3754916 : Nat := 4983230072969 + 3 ^ 40 * 3754916 * 2
def baseEnd_3754916 : Nat := 428461494501763579462547

theorem tailTrace_3754916 : CollatzResearch.WordTrace tailWord_3754916 prefixEnd_3754916 428461494501763579462547 := by
  unfold tailWord_3754916
  simp only [CollatzResearch.WordTrace]
  refine ⟨68476518832294047721158301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91302025109725396961544401 68476518832294047721158301)
  ·
    refine ⟨25678694562110267895434363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68476518832294047721158301 25678694562110267895434363)
    ·
      refine ⟨38518041843165401843151545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678694562110267895434363 38518041843165401843151545)
      ·
        refine ⟨28888531382374051382363659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38518041843165401843151545 28888531382374051382363659)
        ·
          refine ⟨43332797073561077073545489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28888531382374051382363659 43332797073561077073545489)
          ·
            refine ⟨32499597805170807805159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43332797073561077073545489 32499597805170807805159117)
            ·
              refine ⟨12187349176939052926934669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32499597805170807805159117 12187349176939052926934669)
              ·
                refine ⟨4570255941352144847600501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187349176939052926934669 4570255941352144847600501)
                ·
                  refine ⟨428461494501763579462547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570255941352144847600501 428461494501763579462547)
                  ·
                    rfl

theorem cell22_3754916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_3754916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754916 prefixEnd_3754916 := by exact prefixLift 3754916
  have htrace : WordTrace (prefixWord ++ tailWord_3754916) baseStart_3754916 baseEnd_3754916 := by
    simpa [prefixWord, tailWord_3754916, baseEnd_3754916] using wordTrace_append hprefix tailTrace_3754916
  have hstable : (prefixWord ++ tailWord_3754916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754916).length < 2 ^ (prefixWord ++ tailWord_3754916).sum := by decide
  have hdescent : baseEnd_3754916 < baseStart_3754916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754976 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 8, 3]
def baseStart_3754976 : Nat := 118140960795 + 3754976 * 2 ^ 59
def prefixEnd_3754976 : Nat := 4983230072969 + 3 ^ 40 * 3754976 * 2
def baseEnd_3754976 : Nat := 1285405022731470581887457

theorem tailTrace_3754976 : CollatzResearch.WordTrace tailWord_3754976 prefixEnd_3754976 1285405022731470581887457 := by
  unfold tailWord_3754976
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477613022185362844750391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91303484029580483793000521 68477613022185362844750391)
  ·
    refine ⟨102716419533278044267125587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68477613022185362844750391 102716419533278044267125587)
    ·
      refine ⟨154074629299917066400688381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102716419533278044267125587 154074629299917066400688381)
      ·
        refine ⟨57777985987468899900258143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154074629299917066400688381 57777985987468899900258143)
        ·
          refine ⟨86666978981203349850387215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57777985987468899900258143 86666978981203349850387215)
          ·
            refine ⟨130000468471805024775580823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86666978981203349850387215 130000468471805024775580823)
            ·
              refine ⟨195000702707707537163371235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130000468471805024775580823 195000702707707537163371235)
              ·
                refine ⟨292501054061561305745056853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195000702707707537163371235 292501054061561305745056853)
                ·
                  refine ⟨3427746727283921551699885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 292501054061561305745056853 3427746727283921551699885)
                  ·
                    refine ⟨1285405022731470581887457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427746727283921551699885 1285405022731470581887457)
                    ·
                      rfl

theorem cell22_3754976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 3].length) (baseStart_3754976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754976 prefixEnd_3754976 := by exact prefixLift 3754976
  have htrace : WordTrace (prefixWord ++ tailWord_3754976) baseStart_3754976 baseEnd_3754976 := by
    simpa [prefixWord, tailWord_3754976, baseEnd_3754976] using wordTrace_append hprefix tailTrace_3754976
  have hstable : (prefixWord ++ tailWord_3754976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754976).length < 2 ^ (prefixWord ++ tailWord_3754976).sum := by decide
  have hdescent : baseEnd_3754976 < baseStart_3754976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754978 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3754978 : Nat := 118140960795 + 3754978 * 2 ^ 59
def prefixEnd_3754978 : Nat := 4983230072969 + 3 ^ 40 * 3754978 * 2
def baseEnd_3754978 : Nat := 428468569124114414445817

theorem tailTrace_3754978 : CollatzResearch.WordTrace tailWord_3754978 prefixEnd_3754978 428468569124114414445817 := by
  unfold tailWord_3754978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34238824747590870007768397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91303532660242320020715725 34238824747590870007768397)
  ·
    refine ⟨12839559280346576252913149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34238824747590870007768397 12839559280346576252913149)
    ·
      refine ⟨4814834730129966094842431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12839559280346576252913149 4814834730129966094842431)
      ·
        refine ⟨7222252095194949142263647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814834730129966094842431 7222252095194949142263647)
        ·
          refine ⟨10833378142792423713395471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222252095194949142263647 10833378142792423713395471)
          ·
            refine ⟨16250067214188635570093207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833378142792423713395471 16250067214188635570093207)
            ·
              refine ⟨24375100821282953355139811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16250067214188635570093207 24375100821282953355139811)
              ·
                refine ⟨36562651231924430032709717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24375100821282953355139811 36562651231924430032709717)
                ·
                  refine ⟨428468569124114414445817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36562651231924430032709717 428468569124114414445817)
                  ·
                    rfl

theorem cell22_3754978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3754978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754978 prefixEnd_3754978 := by exact prefixLift 3754978
  have htrace : WordTrace (prefixWord ++ tailWord_3754978) baseStart_3754978 baseEnd_3754978 := by
    simpa [prefixWord, tailWord_3754978, baseEnd_3754978] using wordTrace_append hprefix tailTrace_3754978
  have hstable : (prefixWord ++ tailWord_3754978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754978).length < 2 ^ (prefixWord ++ tailWord_3754978).sum := by decide
  have hdescent : baseEnd_3754978 < baseStart_3754978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754991 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_3754991 : Nat := 118140960795 + 3754991 * 2 ^ 59
def prefixEnd_3754991 : Nat := 4983230072969 + 3 ^ 40 * 3754991 * 2
def baseEnd_3754991 : Nat := 1285410157538015542762411

theorem tailTrace_3754991 : CollatzResearch.WordTrace tailWord_3754991 prefixEnd_3754991 1285410157538015542762411 := by
  unfold tailWord_3754991
  simp only [CollatzResearch.WordTrace]
  refine ⟨136955773139316383251296827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91303848759544255500864551 136955773139316383251296827)
  ·
    refine ⟨205433659708974574876945241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136955773139316383251296827 205433659708974574876945241)
    ·
      refine ⟨154075244781730931157708931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205433659708974574876945241 154075244781730931157708931)
      ·
        refine ⟨231112867172596396736563397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154075244781730931157708931 231112867172596396736563397)
        ·
          refine ⟨43333662594861824388105637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231112867172596396736563397 43333662594861824388105637)
          ·
            refine ⟨8125061736536592072769807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43333662594861824388105637 8125061736536592072769807)
            ·
              refine ⟨12187592604804888109154711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125061736536592072769807 12187592604804888109154711)
              ·
                refine ⟨18281388907207332163732067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187592604804888109154711 18281388907207332163732067)
                ·
                  refine ⟨27422083360810998245598101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18281388907207332163732067 27422083360810998245598101)
                  ·
                    refine ⟨1285410157538015542762411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27422083360810998245598101 1285410157538015542762411)
                    ·
                      rfl

theorem cell22_3754991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_3754991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754991 prefixEnd_3754991 := by exact prefixLift 3754991
  have htrace : WordTrace (prefixWord ++ tailWord_3754991) baseStart_3754991 baseEnd_3754991 := by
    simpa [prefixWord, tailWord_3754991, baseEnd_3754991] using wordTrace_append hprefix tailTrace_3754991
  have hstable : (prefixWord ++ tailWord_3754991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754991).length < 2 ^ (prefixWord ++ tailWord_3754991).sum := by decide
  have hdescent : baseEnd_3754991 < baseStart_3754991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3754997 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3754997 : Nat := 118140960795 + 3754997 * 2 ^ 59
def prefixEnd_3754997 : Nat := 4983230072969 + 3 ^ 40 * 3754997 * 2
def baseEnd_3754997 : Nat := 1285412211460633527112393

theorem tailTrace_3754997 : CollatzResearch.WordTrace tailWord_3754997 prefixEnd_3754997 1285412211460633527112393 := by
  unfold tailWord_3754997
  simp only [CollatzResearch.WordTrace]
  refine ⟨136955991977294646276015245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91303994651529764184010163 136955991977294646276015245)
  ·
    refine ⟨51358496991485492353505717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136955991977294646276015245 51358496991485492353505717)
    ·
      refine ⟨4814859092951764908141161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51358496991485492353505717 4814859092951764908141161)
      ·
        refine ⟨3611144319713823681105871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4814859092951764908141161 3611144319713823681105871)
        ·
          refine ⟨5416716479570735521658807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611144319713823681105871 5416716479570735521658807)
          ·
            refine ⟨8125074719356103282488211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416716479570735521658807 8125074719356103282488211)
            ·
              refine ⟨12187612079034154923732317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125074719356103282488211 12187612079034154923732317)
              ·
                refine ⟨4570354529637808096399619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187612079034154923732317 4570354529637808096399619)
                ·
                  refine ⟨6855531794456712144599429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570354529637808096399619 6855531794456712144599429)
                  ·
                    refine ⟨1285412211460633527112393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855531794456712144599429 1285412211460633527112393)
                    ·
                      rfl

theorem cell22_3754997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3754997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3754997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3754997 prefixEnd_3754997 := by exact prefixLift 3754997
  have htrace : WordTrace (prefixWord ++ tailWord_3754997) baseStart_3754997 baseEnd_3754997 := by
    simpa [prefixWord, tailWord_3754997, baseEnd_3754997] using wordTrace_append hprefix tailTrace_3754997
  have hstable : (prefixWord ++ tailWord_3754997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3754997).length < 2 ^ (prefixWord ++ tailWord_3754997).sum := by decide
  have hdescent : baseEnd_3754997 < baseStart_3754997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3754997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755066 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3755066 : Nat := 118140960795 + 3755066 * 2 ^ 59
def prefixEnd_3755066 : Nat := 4983230072969 + 3 ^ 40 * 3755066 * 2
def baseEnd_3755066 : Nat := 1285435831570740347137181

theorem tailTrace_3755066 : CollatzResearch.WordTrace tailWord_3755066 prefixEnd_3755066 1285435831570740347137181 := by
  unfold tailWord_3755066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239627153511167765069263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91305672409363114040184701 34239627153511167765069263)
  ·
    refine ⟨51359440730266751647603895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34239627153511167765069263 51359440730266751647603895)
    ·
      refine ⟨77039161095400127471405843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51359440730266751647603895 77039161095400127471405843)
      ·
        refine ⟨115558741643100191207108765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77039161095400127471405843 115558741643100191207108765)
        ·
          refine ⟨43334528116162571702665787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115558741643100191207108765 43334528116162571702665787)
          ·
            refine ⟨65001792174243857553998681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43334528116162571702665787 65001792174243857553998681)
            ·
              refine ⟨48751344130682893165499011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65001792174243857553998681 48751344130682893165499011)
              ·
                refine ⟨73127016196024339748248517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48751344130682893165499011 73127016196024339748248517)
                ·
                  refine ⟨13711315536754563702796597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73127016196024339748248517 13711315536754563702796597)
                  ·
                    refine ⟨1285435831570740347137181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13711315536754563702796597 1285435831570740347137181)
                    ·
                      rfl

theorem cell22_3755066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3755066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755066 prefixEnd_3755066 := by exact prefixLift 3755066
  have htrace : WordTrace (prefixWord ++ tailWord_3755066) baseStart_3755066 baseEnd_3755066 := by
    simpa [prefixWord, tailWord_3755066, baseEnd_3755066] using wordTrace_append hprefix tailTrace_3755066
  have hstable : (prefixWord ++ tailWord_3755066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755066).length < 2 ^ (prefixWord ++ tailWord_3755066).sum := by decide
  have hdescent : baseEnd_3755066 < baseStart_3755066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755072 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 1, 3]
def baseStart_3755072 : Nat := 118140960795 + 3755072 * 2 ^ 59
def prefixEnd_3755072 : Nat := 4983230072969 + 3 ^ 40 * 3755072 * 2
def baseEnd_3755072 : Nat := 1285437885493358331487163

theorem tailTrace_3755072 : CollatzResearch.WordTrace tailWord_3755072 prefixEnd_3755072 1285437885493358331487163 := by
  unfold tailWord_3755072
  simp only [CollatzResearch.WordTrace]
  refine ⟨68479363726011467042497735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91305818301348622723330313 68479363726011467042497735)
  ·
    refine ⟨102719045589017200563746603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68479363726011467042497735 102719045589017200563746603)
    ·
      refine ⟨154078568383525800845619905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102719045589017200563746603 154078568383525800845619905)
      ·
        refine ⟨115558926287644350634214929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154078568383525800845619905 115558926287644350634214929)
        ·
          refine ⟨86669194715733262975661197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115558926287644350634214929 86669194715733262975661197)
          ·
            refine ⟨32500948018399973615872949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86669194715733262975661197 32500948018399973615872949)
            ·
              refine ⟨3046963876724997526488089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32500948018399973615872949 3046963876724997526488089)
              ·
                refine ⟨2285222907543748144866067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3046963876724997526488089 2285222907543748144866067)
                ·
                  refine ⟨3427834361315622217299101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285222907543748144866067 3427834361315622217299101)
                  ·
                    refine ⟨1285437885493358331487163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427834361315622217299101 1285437885493358331487163)
                    ·
                      rfl

theorem cell22_3755072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 3].length) (baseStart_3755072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755072 prefixEnd_3755072 := by exact prefixLift 3755072
  have htrace : WordTrace (prefixWord ++ tailWord_3755072) baseStart_3755072 baseEnd_3755072 := by
    simpa [prefixWord, tailWord_3755072, baseEnd_3755072] using wordTrace_append hprefix tailTrace_3755072
  have hstable : (prefixWord ++ tailWord_3755072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755072).length < 2 ^ (prefixWord ++ tailWord_3755072).sum := by decide
  have hdescent : baseEnd_3755072 < baseStart_3755072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755085 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3755085 : Nat := 118140960795 + 3755085 * 2 ^ 59
def prefixEnd_3755085 : Nat := 4983230072969 + 3 ^ 40 * 3755085 * 2
def baseEnd_3755085 : Nat := 428480778553010210304041

theorem tailTrace_3755085 : CollatzResearch.WordTrace tailWord_3755085 prefixEnd_3755085 428480778553010210304041 := by
  unfold tailWord_3755085
  simp only [CollatzResearch.WordTrace]
  refine ⟨136959201600975837305218709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91306134400650558203479139 136959201600975837305218709)
  ·
    refine ⟨6419962575045742373682127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136959201600975837305218709 6419962575045742373682127)
    ·
      refine ⟨9629943862568613560523191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6419962575045742373682127 9629943862568613560523191)
      ·
        refine ⟨14444915793852920340784787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629943862568613560523191 14444915793852920340784787)
        ·
          refine ⟨21667373690779380511177181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14444915793852920340784787 21667373690779380511177181)
          ·
            refine ⟨8125265134042267691691443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21667373690779380511177181 8125265134042267691691443)
            ·
              refine ⟨12187897701063401537537165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125265134042267691691443 12187897701063401537537165)
              ·
                refine ⟨4570461637898775576576437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187897701063401537537165 4570461637898775576576437)
                ·
                  refine ⟨428480778553010210304041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4570461637898775576576437 428480778553010210304041)
                  ·
                    rfl

theorem cell22_3755085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3755085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755085 prefixEnd_3755085 := by exact prefixLift 3755085
  have htrace : WordTrace (prefixWord ++ tailWord_3755085) baseStart_3755085 baseEnd_3755085 := by
    simpa [prefixWord, tailWord_3755085, baseEnd_3755085] using wordTrace_append hprefix tailTrace_3755085
  have hstable : (prefixWord ++ tailWord_3755085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755085).length < 2 ^ (prefixWord ++ tailWord_3755085).sum := by decide
  have hdescent : baseEnd_3755085 < baseStart_3755085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755096 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_3755096 : Nat := 118140960795 + 3755096 * 2 ^ 59
def prefixEnd_3755096 : Nat := 4983230072969 + 3 ^ 40 * 3755096 * 2
def baseEnd_3755096 : Nat := 428482033727943422962363

theorem tailTrace_3755096 : CollatzResearch.WordTrace tailWord_3755096 prefixEnd_3755096 428482033727943422962363 := by
  unfold tailWord_3755096
  simp only [CollatzResearch.WordTrace]
  refine ⟨68479801401967993091934571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91306401869290657455912761 68479801401967993091934571)
  ·
    refine ⟨102719702102951989637901857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68479801401967993091934571 102719702102951989637901857)
    ·
      refine ⟨77039776577213992228426393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102719702102951989637901857 77039776577213992228426393)
      ·
        refine ⟨57779832432910494171319795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77039776577213992228426393 57779832432910494171319795)
        ·
          refine ⟨86669748649365741256979693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57779832432910494171319795 86669748649365741256979693)
          ·
            refine ⟨32501155743512152971367385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86669748649365741256979693 32501155743512152971367385)
            ·
              refine ⟨24375866807634114728525539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32501155743512152971367385 24375866807634114728525539)
              ·
                refine ⟨36563800211451172092788309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24375866807634114728525539 36563800211451172092788309)
                ·
                  refine ⟨428482033727943422962363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36563800211451172092788309 428482033727943422962363)
                  ·
                    rfl

theorem cell22_3755096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_3755096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755096 prefixEnd_3755096 := by exact prefixLift 3755096
  have htrace : WordTrace (prefixWord ++ tailWord_3755096) baseStart_3755096 baseEnd_3755096 := by
    simpa [prefixWord, tailWord_3755096, baseEnd_3755096] using wordTrace_append hprefix tailTrace_3755096
  have hstable : (prefixWord ++ tailWord_3755096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755096).length < 2 ^ (prefixWord ++ tailWord_3755096).sum := by decide
  have hdescent : baseEnd_3755096 < baseStart_3755096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755098 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_3755098 : Nat := 118140960795 + 3755098 * 2 ^ 59
def prefixEnd_3755098 : Nat := 4983230072969 + 3 ^ 40 * 3755098 * 2
def baseEnd_3755098 : Nat := 1285446785824702930337083

theorem tailTrace_3755098 : CollatzResearch.WordTrace tailWord_3755098 prefixEnd_3755098 1285446785824702930337083 := by
  unfold tailWord_3755098
  simp only [CollatzResearch.WordTrace]
  refine ⟨34239918937482185131360487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91306450499952493683627965 34239918937482185131360487)
  ·
    refine ⟨51359878406223277697040731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34239918937482185131360487 51359878406223277697040731)
    ·
      refine ⟨77039817609334916545561097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51359878406223277697040731 77039817609334916545561097)
      ·
        refine ⟨57779863207001187409170823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77039817609334916545561097 57779863207001187409170823)
        ·
          refine ⟨86669794810501781113756235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57779863207001187409170823 86669794810501781113756235)
          ·
            refine ⟨130004692215752671670634353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86669794810501781113756235 130004692215752671670634353)
            ·
              refine ⟨97503519161814503752975765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130004692215752671670634353 97503519161814503752975765)
              ·
                refine ⟨4570477460710054863420739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97503519161814503752975765 4570477460710054863420739)
                ·
                  refine ⟨6855716191065082295131109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570477460710054863420739 6855716191065082295131109)
                  ·
                    refine ⟨1285446785824702930337083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855716191065082295131109 1285446785824702930337083)
                    ·
                      rfl

theorem cell22_3755098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_3755098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755098 prefixEnd_3755098 := by exact prefixLift 3755098
  have htrace : WordTrace (prefixWord ++ tailWord_3755098) baseStart_3755098 baseEnd_3755098 := by
    simpa [prefixWord, tailWord_3755098, baseEnd_3755098] using wordTrace_append hprefix tailTrace_3755098
  have hstable : (prefixWord ++ tailWord_3755098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755098).length < 2 ^ (prefixWord ++ tailWord_3755098).sum := by decide
  have hdescent : baseEnd_3755098 < baseStart_3755098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755128 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 4, 3]
def baseStart_3755128 : Nat := 118140960795 + 3755128 * 2 ^ 59
def prefixEnd_3755128 : Nat := 4983230072969 + 3 ^ 40 * 3755128 * 2
def baseEnd_3755128 : Nat := 1285457055437792852086991

theorem tailTrace_3755128 : CollatzResearch.WordTrace tailWord_3755128 prefixEnd_3755128 1285457055437792852086991 := by
  unfold tailWord_3755128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68480384969910027824517019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91307179959880037099356025 68480384969910027824517019)
  ·
    refine ⟨102720577454865041736775529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68480384969910027824517019 102720577454865041736775529)
    ·
      refine ⟨77040433091148781302581647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102720577454865041736775529 77040433091148781302581647)
      ·
        refine ⟨115560649636723171953872471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77040433091148781302581647 115560649636723171953872471)
        ·
          refine ⟨173340974455084757930808707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115560649636723171953872471 173340974455084757930808707)
          ·
            refine ⟨260011461682627136896213061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173340974455084757930808707 260011461682627136896213061)
            ·
              refine ⟨48752149065492588168039949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260011461682627136896213061 48752149065492588168039949)
              ·
                refine ⟨18282055899559720563014981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48752149065492588168039949 18282055899559720563014981)
                ·
                  refine ⟨3427885481167447605565309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18282055899559720563014981 3427885481167447605565309)
                  ·
                    refine ⟨1285457055437792852086991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427885481167447605565309 1285457055437792852086991)
                    ·
                      rfl

theorem cell22_3755128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_3755128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755128 prefixEnd_3755128 := by exact prefixLift 3755128
  have htrace : WordTrace (prefixWord ++ tailWord_3755128) baseStart_3755128 baseEnd_3755128 := by
    simpa [prefixWord, tailWord_3755128, baseEnd_3755128] using wordTrace_append hprefix tailTrace_3755128
  have hstable : (prefixWord ++ tailWord_3755128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755128).length < 2 ^ (prefixWord ++ tailWord_3755128).sum := by decide
  have hdescent : baseEnd_3755128 < baseStart_3755128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755134 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3755134 : Nat := 118140960795 + 3755134 * 2 ^ 59
def prefixEnd_3755134 : Nat := 4983230072969 + 3 ^ 40 * 3755134 * 2
def baseEnd_3755134 : Nat := 1285459109360410836436973

theorem tailTrace_3755134 : CollatzResearch.WordTrace tailWord_3755134 prefixEnd_3755134 1285459109360410836436973 := by
  unfold tailWord_3755134
  simp only [CollatzResearch.WordTrace]
  refine ⟨17120123597224789834219057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91307325851865545782501637 17120123597224789834219057)
  ·
    refine ⟨12840092697918592375664293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17120123597224789834219057 12840092697918592375664293)
    ·
      refine ⟨2407517380859736070437055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12840092697918592375664293 2407517380859736070437055)
      ·
        refine ⟨3611276071289604105655583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407517380859736070437055 3611276071289604105655583)
        ·
          refine ⟨5416914106934406158483375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611276071289604105655583 5416914106934406158483375)
          ·
            refine ⟨8125371160401609237725063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416914106934406158483375 8125371160401609237725063)
            ·
              refine ⟨12188056740602413856587595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125371160401609237725063 12188056740602413856587595)
              ·
                refine ⟨18282085110903620784881393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12188056740602413856587595 18282085110903620784881393)
                ·
                  refine ⟨13711563833177715588661045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18282085110903620784881393 13711563833177715588661045)
                  ·
                    refine ⟨1285459109360410836436973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13711563833177715588661045 1285459109360410836436973)
                    ·
                      rfl

theorem cell22_3755134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3755134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755134 prefixEnd_3755134 := by exact prefixLift 3755134
  have htrace : WordTrace (prefixWord ++ tailWord_3755134) baseStart_3755134 baseEnd_3755134 := by
    simpa [prefixWord, tailWord_3755134, baseEnd_3755134] using wordTrace_append hprefix tailTrace_3755134
  have hstable : (prefixWord ++ tailWord_3755134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755134).length < 2 ^ (prefixWord ++ tailWord_3755134).sum := by decide
  have hdescent : baseEnd_3755134 < baseStart_3755134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755145 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_3755145 : Nat := 118140960795 + 3755145 * 2 ^ 59
def prefixEnd_3755145 : Nat := 4983230072969 + 3 ^ 40 * 3755145 * 2
def baseEnd_3755145 : Nat := 1285462874885210474411939

theorem tailTrace_3755145 : CollatzResearch.WordTrace tailWord_3755145 prefixEnd_3755145 1285462874885210474411939 := by
  unfold tailWord_3755145
  simp only [CollatzResearch.WordTrace]
  refine ⟨136961389980758467552402889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91307593320505645034935259 136961389980758467552402889)
  ·
    refine ⟨102721042485568850664302167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136961389980758467552402889 102721042485568850664302167)
    ·
      refine ⟨154081563728353275996453251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102721042485568850664302167 154081563728353275996453251)
      ·
        refine ⟨231122345592529913994679877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154081563728353275996453251 231122345592529913994679877)
        ·
          refine ⟨43335439798599358874002477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231122345592529913994679877 43335439798599358874002477)
          ·
            refine ⟨16250789924474759577750929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43335439798599358874002477 16250789924474759577750929)
            ·
              refine ⟨12188092443356069683313197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16250789924474759577750929 12188092443356069683313197)
              ·
                refine ⟨4570534666258526131242449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12188092443356069683313197 4570534666258526131242449)
                ·
                  refine ⟨3427900999693894598431837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4570534666258526131242449 3427900999693894598431837)
                  ·
                    refine ⟨1285462874885210474411939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427900999693894598431837 1285462874885210474411939)
                    ·
                      rfl

theorem cell22_3755145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_3755145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755145 prefixEnd_3755145 := by exact prefixLift 3755145
  have htrace : WordTrace (prefixWord ++ tailWord_3755145) baseStart_3755145 baseEnd_3755145 := by
    simpa [prefixWord, tailWord_3755145, baseEnd_3755145] using wordTrace_append hprefix tailTrace_3755145
  have hstable : (prefixWord ++ tailWord_3755145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755145).length < 2 ^ (prefixWord ++ tailWord_3755145).sum := by decide
  have hdescent : baseEnd_3755145 < baseStart_3755145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755160 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 2, 4]
def baseStart_3755160 : Nat := 118140960795 + 3755160 * 2 ^ 59
def prefixEnd_3755160 : Nat := 4983230072969 + 3 ^ 40 * 3755160 * 2
def baseEnd_3755160 : Nat := 1285468009691755435286893

theorem tailTrace_3755160 : CollatzResearch.WordTrace tailWord_3755160 prefixEnd_3755160 1285468009691755435286893 := by
  unfold tailWord_3755160
  simp only [CollatzResearch.WordTrace]
  refine ⟨68480968537852062557099467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91307958050469416742799289 68480968537852062557099467)
  ·
    refine ⟨102721452806778093835649201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68480968537852062557099467 102721452806778093835649201)
    ·
      refine ⟨77041089605083570376736901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102721452806778093835649201 77041089605083570376736901)
      ·
        refine ⟨14445204300953169445638169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77041089605083570376736901 14445204300953169445638169)
        ·
          refine ⟨10833903225714877084228627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14445204300953169445638169 10833903225714877084228627)
          ·
            refine ⟨16250854838572315626342941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833903225714877084228627 16250854838572315626342941)
            ·
              refine ⟨6094070564464618359878603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16250854838572315626342941 6094070564464618359878603)
              ·
                refine ⟨9141105846696927539817905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094070564464618359878603 9141105846696927539817905)
                ·
                  refine ⟨6855829385022695654863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141105846696927539817905 6855829385022695654863429)
                  ·
                    refine ⟨1285468009691755435286893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6855829385022695654863429 1285468009691755435286893)
                    ·
                      rfl

theorem cell22_3755160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_3755160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755160 prefixEnd_3755160 := by exact prefixLift 3755160
  have htrace : WordTrace (prefixWord ++ tailWord_3755160) baseStart_3755160 baseEnd_3755160 := by
    simpa [prefixWord, tailWord_3755160, baseEnd_3755160] using wordTrace_append hprefix tailTrace_3755160
  have hstable : (prefixWord ++ tailWord_3755160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755160).length < 2 ^ (prefixWord ++ tailWord_3755160).sum := by decide
  have hdescent : baseEnd_3755160 < baseStart_3755160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755267 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 1, 4]
def baseStart_3755267 : Nat := 118140960795 + 3755267 * 2 ^ 59
def prefixEnd_3755267 : Nat := 4983230072969 + 3 ^ 40 * 3755267 * 2
def baseEnd_3755267 : Nat := 1285504637978442822861565

theorem tailTrace_3755267 : CollatzResearch.WordTrace tailWord_3755267 prefixEnd_3755267 1285504637978442822861565 := by
  unfold tailWord_3755267
  simp only [CollatzResearch.WordTrace]
  refine ⟨136965839686316482388344055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91310559790877654925562703 136965839686316482388344055)
  ·
    refine ⟨205448759529474723582516083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136965839686316482388344055 205448759529474723582516083)
    ·
      refine ⟨308173139294212085373774125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205448759529474723582516083 308173139294212085373774125)
      ·
        refine ⟨115564927235329532015165297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308173139294212085373774125 115564927235329532015165297)
        ·
          refine ⟨86673695426497149011373973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115564927235329532015165297 86673695426497149011373973)
          ·
            refine ⟨4062829473117053859908155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86673695426497149011373973 4062829473117053859908155)
            ·
              refine ⟨6094244209675580789862233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062829473117053859908155 6094244209675580789862233)
              ·
                refine ⟨4570683157256685592396675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094244209675580789862233 4570683157256685592396675)
                ·
                  refine ⟨6856024735885028388595013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570683157256685592396675 6856024735885028388595013)
                  ·
                    refine ⟨1285504637978442822861565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856024735885028388595013 1285504637978442822861565)
                    ·
                      rfl

theorem cell22_3755267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 4].length) (baseStart_3755267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755267 prefixEnd_3755267 := by exact prefixLift 3755267
  have htrace : WordTrace (prefixWord ++ tailWord_3755267) baseStart_3755267 baseEnd_3755267 := by
    simpa [prefixWord, tailWord_3755267, baseEnd_3755267] using wordTrace_append hprefix tailTrace_3755267
  have hstable : (prefixWord ++ tailWord_3755267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755267).length < 2 ^ (prefixWord ++ tailWord_3755267).sum := by decide
  have hdescent : baseEnd_3755267 < baseStart_3755267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755299 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 4]
def baseStart_3755299 : Nat := 118140960795 + 3755299 * 2 ^ 59
def prefixEnd_3755299 : Nat := 4983230072969 + 3 ^ 40 * 3755299 * 2
def baseEnd_3755299 : Nat := 428505197410801802020489

theorem tailTrace_3755299 : CollatzResearch.WordTrace tailWord_3755299 prefixEnd_3755299 428505197410801802020489 := by
  unfold tailWord_3755299
  simp only [CollatzResearch.WordTrace]
  refine ⟨136967006822200551853508951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91311337881467034569005967 136967006822200551853508951)
  ·
    refine ⟨205450510233300827780263427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136967006822200551853508951 205450510233300827780263427)
    ·
      refine ⟨308175765349951241670395141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205450510233300827780263427 308175765349951241670395141)
      ·
        refine ⟨57782956003115857813199089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 308175765349951241670395141 57782956003115857813199089)
        ·
          refine ⟨43337217002336893359899317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57782956003115857813199089 43337217002336893359899317)
          ·
            refine ⟨4062864093969083752490561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43337217002336893359899317 4062864093969083752490561)
            ·
              refine ⟨3047148070476812814367921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062864093969083752490561 3047148070476812814367921)
              ·
                refine ⟨2285361052857609610775941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047148070476812814367921 2285361052857609610775941)
                ·
                  refine ⟨428505197410801802020489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285361052857609610775941 428505197410801802020489)
                  ·
                    rfl

theorem cell22_3755299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 4].length) (baseStart_3755299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755299 prefixEnd_3755299 := by exact prefixLift 3755299
  have htrace : WordTrace (prefixWord ++ tailWord_3755299) baseStart_3755299 baseEnd_3755299 := by
    simpa [prefixWord, tailWord_3755299, baseEnd_3755299] using wordTrace_append hprefix tailTrace_3755299
  have hstable : (prefixWord ++ tailWord_3755299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755299).length < 2 ^ (prefixWord ++ tailWord_3755299).sum := by decide
  have hdescent : baseEnd_3755299 < baseStart_3755299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755308 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_3755308 : Nat := 118140960795 + 3755308 * 2 ^ 59
def prefixEnd_3755308 : Nat := 4983230072969 + 3 ^ 40 * 3755308 * 2
def baseEnd_3755308 : Nat := 1285518673116332382586439

theorem tailTrace_3755308 : CollatzResearch.WordTrace tailWord_3755308 prefixEnd_3755308 1285518673116332382586439 := by
  unfold tailWord_3755308
  simp only [CollatzResearch.WordTrace]
  refine ⟨68483667539583973195293289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91311556719445297593724385 68483667539583973195293289)
  ·
    refine ⟨51362750654687979896469967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68483667539583973195293289 51362750654687979896469967)
    ·
      refine ⟨77044125982031969844704951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51362750654687979896469967 77044125982031969844704951)
      ·
        refine ⟨115566188973047954767057427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77044125982031969844704951 115566188973047954767057427)
        ·
          refine ⟨173349283459571932150586141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115566188973047954767057427 173349283459571932150586141)
          ·
            refine ⟨65005981297339474556469803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173349283459571932150586141 65005981297339474556469803)
            ·
              refine ⟨97508971946009211834704705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65005981297339474556469803 97508971946009211834704705)
              ·
                refine ⟨73131728959506908876028529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97508971946009211834704705 73131728959506908876028529)
                ·
                  refine ⟨54848796719630181657021397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73131728959506908876028529 54848796719630181657021397)
                  ·
                    refine ⟨1285518673116332382586439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54848796719630181657021397 1285518673116332382586439)
                    ·
                      rfl

theorem cell22_3755308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_3755308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755308 prefixEnd_3755308 := by exact prefixLift 3755308
  have htrace : WordTrace (prefixWord ++ tailWord_3755308) baseStart_3755308 baseEnd_3755308 := by
    simpa [prefixWord, tailWord_3755308, baseEnd_3755308] using wordTrace_append hprefix tailTrace_3755308
  have hstable : (prefixWord ++ tailWord_3755308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755308).length < 2 ^ (prefixWord ++ tailWord_3755308).sum := by decide
  have hdescent : baseEnd_3755308 < baseStart_3755308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755329 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_3755329 : Nat := 118140960795 + 3755329 * 2 ^ 59
def prefixEnd_3755329 : Nat := 4983230072969 + 3 ^ 40 * 3755329 * 2
def baseEnd_3755329 : Nat := 1285525861845495327811375

theorem tailTrace_3755329 : CollatzResearch.WordTrace tailWord_3755329 prefixEnd_3755329 1285525861845495327811375 := by
  unfold tailWord_3755329
  simp only [CollatzResearch.WordTrace]
  refine ⟨136968101012091866977101041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91312067341394577984734027 136968101012091866977101041)
  ·
    refine ⟨102726075759068900232825781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136968101012091866977101041 102726075759068900232825781)
    ·
      refine ⟨9630569602412709396827417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102726075759068900232825781 9630569602412709396827417)
      ·
        refine ⟨7222927201809532047620563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9630569602412709396827417 7222927201809532047620563)
        ·
          refine ⟨10834390802714298071430845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222927201809532047620563 10834390802714298071430845)
          ·
            refine ⟨4062896551017861776786567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10834390802714298071430845 4062896551017861776786567)
            ·
              refine ⟨6094344826526792665179851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062896551017861776786567 6094344826526792665179851)
              ·
                refine ⟨9141517239790188997769777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094344826526792665179851 9141517239790188997769777)
                ·
                  refine ⟨6856137929842641748327333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141517239790188997769777 6856137929842641748327333)
                  ·
                    refine ⟨1285525861845495327811375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856137929842641748327333 1285525861845495327811375)
                    ·
                      rfl

theorem cell22_3755329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_3755329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755329 prefixEnd_3755329 := by exact prefixLift 3755329
  have htrace : WordTrace (prefixWord ++ tailWord_3755329) baseStart_3755329 baseEnd_3755329 := by
    simpa [prefixWord, tailWord_3755329, baseEnd_3755329] using wordTrace_append hprefix tailTrace_3755329
  have hstable : (prefixWord ++ tailWord_3755329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755329).length < 2 ^ (prefixWord ++ tailWord_3755329).sum := by decide
  have hdescent : baseEnd_3755329 < baseStart_3755329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755385 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_3755385 : Nat := 118140960795 + 3755385 * 2 ^ 59
def prefixEnd_3755385 : Nat := 4983230072969 + 3 ^ 40 * 3755385 * 2
def baseEnd_3755385 : Nat := 1285545031789929848411203

theorem tailTrace_3755385 : CollatzResearch.WordTrace tailWord_3755385 prefixEnd_3755385 1285545031789929848411203 := by
  unfold tailWord_3755385
  simp only [CollatzResearch.WordTrace]
  refine ⟨136970143499888988541139609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91313428999925992360759739 136970143499888988541139609)
  ·
    refine ⟨102727607624916741405854707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136970143499888988541139609 102727607624916741405854707)
    ·
      refine ⟨154091411437375112108782061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102727607624916741405854707 154091411437375112108782061)
      ·
        refine ⟨57784279289015667040793273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154091411437375112108782061 57784279289015667040793273)
        ·
          refine ⟨43338209466761750280594955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57784279289015667040793273 43338209466761750280594955)
          ·
            refine ⟨65007314200142625420892433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43338209466761750280594955 65007314200142625420892433)
            ·
              refine ⟨48755485650106969065669325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65007314200142625420892433 48755485650106969065669325)
              ·
                refine ⟨18283307118790113399625997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48755485650106969065669325 18283307118790113399625997)
                ·
                  refine ⟨6856240169546292524859749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18283307118790113399625997 6856240169546292524859749)
                  ·
                    refine ⟨1285545031789929848411203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856240169546292524859749 1285545031789929848411203)
                    ·
                      rfl

theorem cell22_3755385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_3755385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755385 prefixEnd_3755385 := by exact prefixLift 3755385
  have htrace : WordTrace (prefixWord ++ tailWord_3755385) baseStart_3755385 baseEnd_3755385 := by
    simpa [prefixWord, tailWord_3755385, baseEnd_3755385] using wordTrace_append hprefix tailTrace_3755385
  have hstable : (prefixWord ++ tailWord_3755385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755385).length < 2 ^ (prefixWord ++ tailWord_3755385).sum := by decide
  have hdescent : baseEnd_3755385 < baseStart_3755385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755393 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3755393 : Nat := 118140960795 + 3755393 * 2 ^ 59
def prefixEnd_3755393 : Nat := 4983230072969 + 3 ^ 40 * 3755393 * 2
def baseEnd_3755393 : Nat := 1285547770353420494211179

theorem tailTrace_3755393 : CollatzResearch.WordTrace tailWord_3755393 prefixEnd_3755393 1285547770353420494211179 := by
  unfold tailWord_3755393
  simp only [CollatzResearch.WordTrace]
  refine ⟨136970435283860005907430833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91313623522573337271620555 136970435283860005907430833)
  ·
    refine ⟨102727826462895004430573125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136970435283860005907430833 102727826462895004430573125)
    ·
      refine ⟨19261467461792813330732461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102727826462895004430573125 19261467461792813330732461)
      ·
        refine ⟨7223050298172304999024673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19261467461792813330732461 7223050298172304999024673)
        ·
          refine ⟨5417287723629228749268505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223050298172304999024673 5417287723629228749268505)
          ·
            refine ⟨4062965792721921561951379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417287723629228749268505 4062965792721921561951379)
            ·
              refine ⟨6094448689082882342927069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062965792721921561951379 6094448689082882342927069)
              ·
                refine ⟨2285418258406080878597651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6094448689082882342927069 2285418258406080878597651)
                ·
                  refine ⟨3428127387609121317896477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285418258406080878597651 3428127387609121317896477)
                  ·
                    refine ⟨1285547770353420494211179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428127387609121317896477 1285547770353420494211179)
                    ·
                      rfl

theorem cell22_3755393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3755393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755393 prefixEnd_3755393 := by exact prefixLift 3755393
  have htrace : WordTrace (prefixWord ++ tailWord_3755393) baseStart_3755393 baseEnd_3755393 := by
    simpa [prefixWord, tailWord_3755393, baseEnd_3755393] using wordTrace_append hprefix tailTrace_3755393
  have hstable : (prefixWord ++ tailWord_3755393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755393).length < 2 ^ (prefixWord ++ tailWord_3755393).sum := by decide
  have hdescent : baseEnd_3755393 < baseStart_3755393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755410 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 1, 3]
def baseStart_3755410 : Nat := 118140960795 + 3755410 * 2 ^ 59
def prefixEnd_3755410 : Nat := 4983230072969 + 3 ^ 40 * 3755410 * 2
def baseEnd_3755410 : Nat := 1285553589800838116536127

theorem tailTrace_3755410 : CollatzResearch.WordTrace tailWord_3755410 prefixEnd_3755410 1285553589800838116536127 := by
  unfold tailWord_3755410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242763831199604452699921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91314036883198945207199789 34242763831199604452699921)
  ·
    refine ⟨25682072873399703339524941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34242763831199604452699921 25682072873399703339524941)
    ·
      refine ⟨9630777327524888752321853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25682072873399703339524941 9630777327524888752321853)
      ·
        refine ⟨3611541497821833282120695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9630777327524888752321853 3611541497821833282120695)
        ·
          refine ⟨5417312246732749923181043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611541497821833282120695 5417312246732749923181043)
          ·
            refine ⟨8125968370099124884771565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417312246732749923181043 8125968370099124884771565)
            ·
              refine ⟨3047238138787171831789337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8125968370099124884771565 3047238138787171831789337)
              ·
                refine ⟨2285428604090378873842003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047238138787171831789337 2285428604090378873842003)
                ·
                  refine ⟨3428142906135568310763005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285428604090378873842003 3428142906135568310763005)
                  ·
                    refine ⟨1285553589800838116536127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428142906135568310763005 1285553589800838116536127)
                    ·
                      rfl

theorem cell22_3755410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_3755410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755410 prefixEnd_3755410 := by exact prefixLift 3755410
  have htrace : WordTrace (prefixWord ++ tailWord_3755410) baseStart_3755410 baseEnd_3755410 := by
    simpa [prefixWord, tailWord_3755410, baseEnd_3755410] using wordTrace_append hprefix tailTrace_3755410
  have hstable : (prefixWord ++ tailWord_3755410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755410).length < 2 ^ (prefixWord ++ tailWord_3755410).sum := by decide
  have hdescent : baseEnd_3755410 < baseStart_3755410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755417 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 6]
def baseStart_3755417 : Nat := 118140960795 + 3755417 * 2 ^ 59
def prefixEnd_3755417 : Nat := 4983230072969 + 3 ^ 40 * 3755417 * 2
def baseEnd_3755417 : Nat := 428518662014630810537035

theorem tailTrace_3755417 : CollatzResearch.WordTrace tailWord_3755417 prefixEnd_3755417 428518662014630810537035 := by
  unfold tailWord_3755417
  simp only [CollatzResearch.WordTrace]
  refine ⟨136971310635773058006304505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91314207090515372004203003 136971310635773058006304505)
  ·
    refine ⟨102728482976829793504728379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136971310635773058006304505 102728482976829793504728379)
    ·
      refine ⟨154092724465244690257092569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102728482976829793504728379 154092724465244690257092569)
      ·
        refine ⟨115569543348933517692819427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154092724465244690257092569 115569543348933517692819427)
        ·
          refine ⟨173354315023400276539229141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115569543348933517692819427 173354315023400276539229141)
          ·
            refine ⟨4062991758360943981388183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 173354315023400276539229141 4062991758360943981388183)
            ·
              refine ⟨6094487637541415972082275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062991758360943981388183 6094487637541415972082275)
              ·
                refine ⟨9141731456312123958123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094487637541415972082275 9141731456312123958123413)
                ·
                  refine ⟨428518662014630810537035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9141731456312123958123413 428518662014630810537035)
                  ·
                    rfl

theorem cell22_3755417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_3755417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755417 prefixEnd_3755417 := by exact prefixLift 3755417
  have htrace : WordTrace (prefixWord ++ tailWord_3755417) baseStart_3755417 baseEnd_3755417 := by
    simpa [prefixWord, tailWord_3755417, baseEnd_3755417] using wordTrace_append hprefix tailTrace_3755417
  have hstable : (prefixWord ++ tailWord_3755417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755417).length < 2 ^ (prefixWord ++ tailWord_3755417).sum := by decide
  have hdescent : baseEnd_3755417 < baseStart_3755417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755447 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_3755447 : Nat := 118140960795 + 3755447 * 2 ^ 59
def prefixEnd_3755447 : Nat := 4983230072969 + 3 ^ 40 * 3755447 * 2
def baseEnd_3755447 : Nat := 1285566255656982353361013

theorem tailTrace_3755447 : CollatzResearch.WordTrace tailWord_3755447 prefixEnd_3755447 1285566255656982353361013 := by
  unfold tailWord_3755447
  simp only [CollatzResearch.WordTrace]
  refine ⟨136972404825664373129896595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91314936550442915419931063 136972404825664373129896595)
  ·
    refine ⟨205458607238496559694844893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136972404825664373129896595 205458607238496559694844893)
    ·
      refine ⟨77046977714436209885566835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205458607238496559694844893 77046977714436209885566835)
      ·
        refine ⟨115570466571654314828350253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77046977714436209885566835 115570466571654314828350253)
        ·
          refine ⟨43338924964370368060631345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115570466571654314828350253 43338924964370368060631345)
          ·
            refine ⟨32504193723277776045473509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43338924964370368060631345 32504193723277776045473509)
            ·
              refine ⟨6094536323114583008526283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32504193723277776045473509 6094536323114583008526283)
              ·
                refine ⟨9141804484671874512789425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094536323114583008526283 9141804484671874512789425)
                ·
                  refine ⟨6856353363503905884592069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9141804484671874512789425 6856353363503905884592069)
                  ·
                    refine ⟨1285566255656982353361013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856353363503905884592069 1285566255656982353361013)
                    ·
                      rfl

theorem cell22_3755447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_3755447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755447 prefixEnd_3755447 := by exact prefixLift 3755447
  have htrace : WordTrace (prefixWord ++ tailWord_3755447) baseStart_3755447 baseEnd_3755447 := by
    simpa [prefixWord, tailWord_3755447, baseEnd_3755447] using wordTrace_append hprefix tailTrace_3755447
  have hstable : (prefixWord ++ tailWord_3755447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755447).length < 2 ^ (prefixWord ++ tailWord_3755447).sum := by decide
  have hdescent : baseEnd_3755447 < baseStart_3755447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755524 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3755524 : Nat := 118140960795 + 3755524 * 2 ^ 59
def prefixEnd_3755524 : Nat := 4983230072969 + 3 ^ 40 * 3755524 * 2
def baseEnd_3755524 : Nat := 428530871443526606395259

theorem tailTrace_3755524 : CollatzResearch.WordTrace tailWord_3755524 prefixEnd_3755524 428530871443526606395259 := by
  unfold tailWord_3755524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68487606623192707640224813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91316808830923610186966417 68487606623192707640224813)
  ·
    refine ⟨25682852483697265365084305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68487606623192707640224813 25682852483697265365084305)
    ·
      refine ⟨19262139362772949023813229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25682852483697265365084305 19262139362772949023813229)
      ·
        refine ⟨7223302261039855883929961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19262139362772949023813229 7223302261039855883929961)
        ·
          refine ⟨5417476695779891912947471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223302261039855883929961 5417476695779891912947471)
          ·
            refine ⟨8126215043669837869421207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417476695779891912947471 8126215043669837869421207)
            ·
              refine ⟨12189322565504756804131811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126215043669837869421207 12189322565504756804131811)
              ·
                refine ⟨18283983848257135206197717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12189322565504756804131811 18283983848257135206197717)
                ·
                  refine ⟨428530871443526606395259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18283983848257135206197717 428530871443526606395259)
                  ·
                    rfl

theorem cell22_3755524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3755524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755524 prefixEnd_3755524 := by exact prefixLift 3755524
  have htrace : WordTrace (prefixWord ++ tailWord_3755524) baseStart_3755524 baseEnd_3755524 := by
    simpa [prefixWord, tailWord_3755524, baseEnd_3755524] using wordTrace_append hprefix tailTrace_3755524
  have hstable : (prefixWord ++ tailWord_3755524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755524).length < 2 ^ (prefixWord ++ tailWord_3755524).sum := by decide
  have hdescent : baseEnd_3755524 < baseStart_3755524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755554 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_3755554 : Nat := 118140960795 + 3755554 * 2 ^ 59
def prefixEnd_3755554 : Nat := 4983230072969 + 3 ^ 40 * 3755554 * 2
def baseEnd_3755554 : Nat := 1285602883943669740935685

theorem tailTrace_3755554 : CollatzResearch.WordTrace tailWord_3755554 prefixEnd_3755554 1285602883943669740935685 := by
  unfold tailWord_3755554
  simp only [CollatzResearch.WordTrace]
  refine ⟨34244076859069182601010429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91317538290851153602694477 34244076859069182601010429)
  ·
    refine ⟨12841528822150943475378911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34244076859069182601010429 12841528822150943475378911)
    ·
      refine ⟨19262293233226415213068367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841528822150943475378911 19262293233226415213068367)
      ·
        refine ⟨28893439849839622819602551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19262293233226415213068367 28893439849839622819602551)
        ·
          refine ⟨43340159774759434229403827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28893439849839622819602551 43340159774759434229403827)
          ·
            refine ⟨65010239662139151344105741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43340159774759434229403827 65010239662139151344105741)
            ·
              refine ⟨24378839873302181754039653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65010239662139151344105741 24378839873302181754039653)
              ·
                refine ⟨4571032476244159078882435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24378839873302181754039653 4571032476244159078882435)
                ·
                  refine ⟨6856548714366238618323653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571032476244159078882435 6856548714366238618323653)
                  ·
                    refine ⟨1285602883943669740935685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6856548714366238618323653 1285602883943669740935685)
                    ·
                      rfl

theorem cell22_3755554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_3755554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755554 prefixEnd_3755554 := by exact prefixLift 3755554
  have htrace : WordTrace (prefixWord ++ tailWord_3755554) baseStart_3755554 baseEnd_3755554 := by
    simpa [prefixWord, tailWord_3755554, baseEnd_3755554] using wordTrace_append hprefix tailTrace_3755554
  have hstable : (prefixWord ++ tailWord_3755554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755554).length < 2 ^ (prefixWord ++ tailWord_3755554).sum := by decide
  have hdescent : baseEnd_3755554 < baseStart_3755554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755584 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 2, 3]
def baseStart_3755584 : Nat := 118140960795 + 3755584 * 2 ^ 59
def prefixEnd_3755584 : Nat := 4983230072969 + 3 ^ 40 * 3755584 * 2
def baseEnd_3755584 : Nat := 1285613153556759662685593

theorem tailTrace_3755584 : CollatzResearch.WordTrace tailWord_3755584 prefixEnd_3755584 1285613153556759662685593 := by
  unfold tailWord_3755584
  simp only [CollatzResearch.WordTrace]
  refine ⟨68488700813084022763816903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91318267750778697018422537 68488700813084022763816903)
  ·
    refine ⟨102733051219626034145725355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68488700813084022763816903 102733051219626034145725355)
    ·
      refine ⟨154099576829439051218588033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102733051219626034145725355 154099576829439051218588033)
      ·
        refine ⟨115574682622079288413941025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154099576829439051218588033 115574682622079288413941025)
        ·
          refine ⟨86681011966559466310455769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115574682622079288413941025 86681011966559466310455769)
          ·
            refine ⟨65010758974919599732841827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86681011966559466310455769 65010758974919599732841827)
            ·
              refine ⟨97516138462379399599262741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65010758974919599732841827 97516138462379399599262741)
              ·
                refine ⟨4571068990424034356215441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97516138462379399599262741 4571068990424034356215441)
                ·
                  refine ⟨3428301742818025767161581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4571068990424034356215441 3428301742818025767161581)
                  ·
                    refine ⟨1285613153556759662685593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428301742818025767161581 1285613153556759662685593)
                    ·
                      rfl

theorem cell22_3755584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_3755584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755584 prefixEnd_3755584 := by exact prefixLift 3755584
  have htrace : WordTrace (prefixWord ++ tailWord_3755584) baseStart_3755584 baseEnd_3755584 := by
    simpa [prefixWord, tailWord_3755584, baseEnd_3755584] using wordTrace_append hprefix tailTrace_3755584
  have hstable : (prefixWord ++ tailWord_3755584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755584).length < 2 ^ (prefixWord ++ tailWord_3755584).sum := by decide
  have hdescent : baseEnd_3755584 < baseStart_3755584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755657 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_3755657 : Nat := 118140960795 + 3755657 * 2 ^ 59
def prefixEnd_3755657 : Nat := 4983230072969 + 3 ^ 40 * 3755657 * 2
def baseEnd_3755657 : Nat := 1285638142948611805610369

theorem tailTrace_3755657 : CollatzResearch.WordTrace tailWord_3755657 prefixEnd_3755657 1285638142948611805610369 := by
  unfold tailWord_3755657
  simp only [CollatzResearch.WordTrace]
  refine ⟨136980064154903578995041225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91320042769935719330027483 136980064154903578995041225)
  ·
    refine ⟨102735048116177684246280919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136980064154903578995041225 102735048116177684246280919)
    ·
      refine ⟨154102572174266526369421379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102735048116177684246280919 154102572174266526369421379)
      ·
        refine ⟨231153858261399789554132069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154102572174266526369421379 231153858261399789554132069)
        ·
          refine ⟨43341348424012460541399763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231153858261399789554132069 43341348424012460541399763)
          ·
            refine ⟨65012022636018690812099645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43341348424012460541399763 65012022636018690812099645)
            ·
              refine ⟨24379508488507009054537367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65012022636018690812099645 24379508488507009054537367)
              ·
                refine ⟨36569262732760513581806051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24379508488507009054537367 36569262732760513581806051)
                ·
                  refine ⟨54853894099140770372709077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36569262732760513581806051 54853894099140770372709077)
                  ·
                    refine ⟨1285638142948611805610369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54853894099140770372709077 1285638142948611805610369)
                    ·
                      rfl

theorem cell22_3755657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_3755657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755657 prefixEnd_3755657 := by exact prefixLift 3755657
  have htrace : WordTrace (prefixWord ++ tailWord_3755657) baseStart_3755657 baseEnd_3755657 := by
    simpa [prefixWord, tailWord_3755657, baseEnd_3755657] using wordTrace_append hprefix tailTrace_3755657
  have hstable : (prefixWord ++ tailWord_3755657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755657).length < 2 ^ (prefixWord ++ tailWord_3755657).sum := by decide
  have hdescent : baseEnd_3755657 < baseStart_3755657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755738 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_3755738 : Nat := 118140960795 + 3755738 * 2 ^ 59
def prefixEnd_3755738 : Nat := 4983230072969 + 3 ^ 40 * 3755738 * 2
def baseEnd_3755738 : Nat := 428555290301318198111707

theorem tailTrace_3755738 : CollatzResearch.WordTrace tailWord_3755738 prefixEnd_3755738 428555290301318198111707 := by
  unfold tailWord_3755738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34245754616902532457184967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91322012311740086552493245 34245754616902532457184967)
  ·
    refine ⟨51368631925353798685777451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34245754616902532457184967 51368631925353798685777451)
    ·
      refine ⟨77052947888030698028666177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51368631925353798685777451 77052947888030698028666177)
      ·
        refine ⟨57789710916023023521499633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77052947888030698028666177 57789710916023023521499633)
        ·
          refine ⟨43342283187017267641124725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57789710916023023521499633 43342283187017267641124725)
          ·
            refine ⟨4063339048782868841355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43342283187017267641124725 4063339048782868841355443)
            ·
              refine ⟨6095008573174303262033165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063339048782868841355443 6095008573174303262033165)
              ·
                refine ⟨2285628214940363723262437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095008573174303262033165 2285628214940363723262437)
                ·
                  refine ⟨428555290301318198111707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285628214940363723262437 428555290301318198111707)
                  ·
                    rfl

theorem cell22_3755738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_3755738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755738 prefixEnd_3755738 := by exact prefixLift 3755738
  have htrace : WordTrace (prefixWord ++ tailWord_3755738) baseStart_3755738 baseEnd_3755738 := by
    simpa [prefixWord, tailWord_3755738, baseEnd_3755738] using wordTrace_append hprefix tailTrace_3755738
  have hstable : (prefixWord ++ tailWord_3755738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755738).length < 2 ^ (prefixWord ++ tailWord_3755738).sum := by decide
  have hdescent : baseEnd_3755738 < baseStart_3755738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755766 : List Nat := [5, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3755766 : Nat := 118140960795 + 3755766 * 2 ^ 59
def prefixEnd_3755766 : Nat := 4983230072969 + 3 ^ 40 * 3755766 * 2
def baseEnd_3755766 : Nat := 142852828430685761626115

theorem tailTrace_3755766 : CollatzResearch.WordTrace tailWord_3755766 prefixEnd_3755766 142852828430685761626115 := by
  unfold tailWord_3755766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561502481969293163172447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91322693141005793740506101 8561502481969293163172447)
  ·
    refine ⟨12842253722953939744758671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8561502481969293163172447 12842253722953939744758671)
    ·
      refine ⟨19263380584430909617138007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12842253722953939744758671 19263380584430909617138007)
      ·
        refine ⟨28895070876646364425707011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19263380584430909617138007 28895070876646364425707011)
        ·
          refine ⟨43342606314969546638560517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28895070876646364425707011 43342606314969546638560517)
          ·
            refine ⟨8126738684056789994730097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43342606314969546638560517 8126738684056789994730097)
            ·
              refine ⟨6095054013042592496047573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126738684056789994730097 6095054013042592496047573)
              ·
                refine ⟨142852828430685761626115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6095054013042592496047573 142852828430685761626115)
                ·
                  rfl

theorem cell22_3755766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3755766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755766 prefixEnd_3755766 := by exact prefixLift 3755766
  have htrace : WordTrace (prefixWord ++ tailWord_3755766) baseStart_3755766 baseEnd_3755766 := by
    simpa [prefixWord, tailWord_3755766, baseEnd_3755766] using wordTrace_append hprefix tailTrace_3755766
  have hstable : (prefixWord ++ tailWord_3755766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755766).length < 2 ^ (prefixWord ++ tailWord_3755766).sum := by decide
  have hdescent : baseEnd_3755766 < baseStart_3755766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755806 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3755806 : Nat := 118140960795 + 3755806 * 2 ^ 59
def prefixEnd_3755806 : Nat := 4983230072969 + 3 ^ 40 * 3755806 * 2
def baseEnd_3755806 : Nat := 428563049564541694544971

theorem tailTrace_3755806 : CollatzResearch.WordTrace tailWord_3755806 prefixEnd_3755806 428563049564541694544971 := by
  unfold tailWord_3755806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17123187328920472180276909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91323665754242518294810181 17123187328920472180276909)
  ·
    refine ⟨6421195248345177067603841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17123187328920472180276909 6421195248345177067603841)
    ·
      refine ⟨4815896436258882800702881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6421195248345177067603841 4815896436258882800702881)
      ·
        refine ⟨3611922327194162100527161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4815896436258882800702881 3611922327194162100527161)
        ·
          refine ⟨2708941745395621575395371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611922327194162100527161 2708941745395621575395371)
          ·
            refine ⟨4063412618093432363093057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708941745395621575395371 4063412618093432363093057)
            ·
              refine ⟨3047559463570074272319793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063412618093432363093057 3047559463570074272319793)
              ·
                refine ⟨2285669597677555704239845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047559463570074272319793 2285669597677555704239845)
                ·
                  refine ⟨428563049564541694544971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285669597677555704239845 428563049564541694544971)
                  ·
                    rfl

theorem cell22_3755806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3755806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755806 prefixEnd_3755806 := by exact prefixLift 3755806
  have htrace : WordTrace (prefixWord ++ tailWord_3755806) baseStart_3755806 baseEnd_3755806 := by
    simpa [prefixWord, tailWord_3755806, baseEnd_3755806] using wordTrace_append hprefix tailTrace_3755806
  have hstable : (prefixWord ++ tailWord_3755806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755806).length < 2 ^ (prefixWord ++ tailWord_3755806).sum := by decide
  have hdescent : baseEnd_3755806 < baseStart_3755806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755826 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_3755826 : Nat := 118140960795 + 3755826 * 2 ^ 59
def prefixEnd_3755826 : Nat := 4983230072969 + 3 ^ 40 * 3755826 * 2
def baseEnd_3755826 : Nat := 1285695995102351698134851

theorem tailTrace_3755826 : CollatzResearch.WordTrace tailWord_3755826 prefixEnd_3755826 1285695995102351698134851 := by
  unfold tailWord_3755826
  simp only [CollatzResearch.WordTrace]
  refine ⟨34246557022822830214485833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91324152060860880571962221 34246557022822830214485833)
  ·
    refine ⟨25684917767117122660864375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34246557022822830214485833 25684917767117122660864375)
    ·
      refine ⟨38527376650675683991296563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25684917767117122660864375 38527376650675683991296563)
      ·
        refine ⟨57791064976013525986944845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38527376650675683991296563 57791064976013525986944845)
        ·
          refine ⟨21671649366005072245104317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57791064976013525986944845 21671649366005072245104317)
          ·
            refine ⟨8126868512251902091914119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21671649366005072245104317 8126868512251902091914119)
            ·
              refine ⟨12190302768377853137871179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126868512251902091914119 12190302768377853137871179)
              ·
                refine ⟨18285454152566779706806769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190302768377853137871179 18285454152566779706806769)
                ·
                  refine ⟨13714090614425084780105077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18285454152566779706806769 13714090614425084780105077)
                  ·
                    refine ⟨1285695995102351698134851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13714090614425084780105077 1285695995102351698134851)
                    ·
                      rfl

theorem cell22_3755826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_3755826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755826 prefixEnd_3755826 := by exact prefixLift 3755826
  have htrace : WordTrace (prefixWord ++ tailWord_3755826) baseStart_3755826 baseEnd_3755826 := by
    simpa [prefixWord, tailWord_3755826, baseEnd_3755826] using wordTrace_append hprefix tailTrace_3755826
  have hstable : (prefixWord ++ tailWord_3755826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755826).length < 2 ^ (prefixWord ++ tailWord_3755826).sum := by decide
  have hdescent : baseEnd_3755826 < baseStart_3755826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755828 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3755828 : Nat := 118140960795 + 3755828 * 2 ^ 59
def prefixEnd_3755828 : Nat := 4983230072969 + 3 ^ 40 * 3755828 * 2
def baseEnd_3755828 : Nat := 428565559914408119861615

theorem tailTrace_3755828 : CollatzResearch.WordTrace tailWord_3755828 prefixEnd_3755828 428565559914408119861615 := by
  unfold tailWord_3755828
  simp only [CollatzResearch.WordTrace]
  refine ⟨68493150518642037599758069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91324200691522716799677425 68493150518642037599758069)
  ·
    refine ⟨6421232861122691024977319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68493150518642037599758069 6421232861122691024977319)
    ·
      refine ⟨9631849291684036537465979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421232861122691024977319 9631849291684036537465979)
      ·
        refine ⟨14447773937526054806198969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9631849291684036537465979 14447773937526054806198969)
        ·
          refine ⟨10835830453144541104649227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14447773937526054806198969 10835830453144541104649227)
          ·
            refine ⟨16253745679716811656973841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10835830453144541104649227 16253745679716811656973841)
            ·
              refine ⟨12190309259787608742730381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16253745679716811656973841 12190309259787608742730381)
              ·
                refine ⟨4571365972420353278523893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12190309259787608742730381 4571365972420353278523893)
                ·
                  refine ⟨428565559914408119861615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571365972420353278523893 428565559914408119861615)
                  ·
                    rfl

theorem cell22_3755828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3755828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755828 prefixEnd_3755828 := by exact prefixLift 3755828
  have htrace : WordTrace (prefixWord ++ tailWord_3755828) baseStart_3755828 baseEnd_3755828 := by
    simpa [prefixWord, tailWord_3755828, baseEnd_3755828] using wordTrace_append hprefix tailTrace_3755828
  have hstable : (prefixWord ++ tailWord_3755828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755828).length < 2 ^ (prefixWord ++ tailWord_3755828).sum := by decide
  have hdescent : baseEnd_3755828 < baseStart_3755828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755858 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3755858 : Nat := 118140960795 + 3755858 * 2 ^ 59
def prefixEnd_3755858 : Nat := 4983230072969 + 3 ^ 40 * 3755858 * 2
def baseEnd_3755858 : Nat := 1285706949356314281334753

theorem tailTrace_3755858 : CollatzResearch.WordTrace tailWord_3755858 prefixEnd_3755858 1285706949356314281334753 := by
  unfold tailWord_3755858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34246848806793847580777057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91324930151450260215405485 34246848806793847580777057)
  ·
    refine ⟨25685136605095385685582793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34246848806793847580777057 25685136605095385685582793)
    ·
      refine ⟨19263852453821539264187095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25685136605095385685582793 19263852453821539264187095)
      ·
        refine ⟨28895778680732308896280643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19263852453821539264187095 28895778680732308896280643)
        ·
          refine ⟨43343668021098463344420965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28895778680732308896280643 43343668021098463344420965)
          ·
            refine ⟨8126937753955961877078931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43343668021098463344420965 8126937753955961877078931)
            ·
              refine ⟨12190406630933942815618397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126937753955961877078931 12190406630933942815618397)
              ·
                refine ⟨4571402486600228555856899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12190406630933942815618397 4571402486600228555856899)
                ·
                  refine ⟨6857103729900342833785349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571402486600228555856899 6857103729900342833785349)
                  ·
                    refine ⟨1285706949356314281334753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857103729900342833785349 1285706949356314281334753)
                    ·
                      rfl

theorem cell22_3755858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3755858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755858 prefixEnd_3755858 := by exact prefixLift 3755858
  have htrace : WordTrace (prefixWord ++ tailWord_3755858) baseStart_3755858 baseEnd_3755858 := by
    simpa [prefixWord, tailWord_3755858, baseEnd_3755858] using wordTrace_append hprefix tailTrace_3755858
  have hstable : (prefixWord ++ tailWord_3755858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755858).length < 2 ^ (prefixWord ++ tailWord_3755858).sum := by decide
  have hdescent : baseEnd_3755858 < baseStart_3755858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755899 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_3755899 : Nat := 118140960795 + 3755899 * 2 ^ 59
def prefixEnd_3755899 : Nat := 4983230072969 + 3 ^ 40 * 3755899 * 2
def baseEnd_3755899 : Nat := 1285720984494203841059627

theorem tailTrace_3755899 : CollatzResearch.WordTrace tailWord_3755899 prefixEnd_3755899 1285720984494203841059627 := by
  unfold tailWord_3755899
  simp only [CollatzResearch.WordTrace]
  refine ⟨136988890620026854325350751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91325927080017902883567167 136988890620026854325350751)
  ·
    refine ⟨205483335930040281488026127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136988890620026854325350751 205483335930040281488026127)
    ·
      refine ⟨308225003895060422232039191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205483335930040281488026127 308225003895060422232039191)
      ·
        refine ⟨462337505842590633348058787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308225003895060422232039191 462337505842590633348058787)
        ·
          refine ⟨693506258763885950022088181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462337505842590633348058787 693506258763885950022088181)
          ·
            refine ⟨65016211759114307814570767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 693506258763885950022088181 65016211759114307814570767)
            ·
              refine ⟨97524317638671461721856151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65016211759114307814570767 97524317638671461721856151)
              ·
                refine ⟨146286476458007192582784227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97524317638671461721856151 146286476458007192582784227)
                ·
                  refine ⟨219429714687010788874176341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146286476458007192582784227 219429714687010788874176341)
                  ·
                    refine ⟨1285720984494203841059627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 219429714687010788874176341 1285720984494203841059627)
                    ·
                      rfl

theorem cell22_3755899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_3755899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755899 prefixEnd_3755899 := by exact prefixLift 3755899
  have htrace : WordTrace (prefixWord ++ tailWord_3755899) baseStart_3755899 baseEnd_3755899 := by
    simpa [prefixWord, tailWord_3755899, baseEnd_3755899] using wordTrace_append hprefix tailTrace_3755899
  have hstable : (prefixWord ++ tailWord_3755899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755899).length < 2 ^ (prefixWord ++ tailWord_3755899).sum := by decide
  have hdescent : baseEnd_3755899 < baseStart_3755899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3755991 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 6]
def baseStart_3755991 : Nat := 118140960795 + 3755991 * 2 ^ 59
def prefixEnd_3755991 : Nat := 4983230072969 + 3 ^ 40 * 3755991 * 2
def baseEnd_3755991 : Nat := 428584159324782089253115

theorem tailTrace_3755991 : CollatzResearch.WordTrace tailWord_3755991 prefixEnd_3755991 428584159324782089253115 := by
  unfold tailWord_3755991
  simp only [CollatzResearch.WordTrace]
  refine ⟨136992246135693554037699827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91328164090462369358466551 136992246135693554037699827)
  ·
    refine ⟨205488369203540331056549741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136992246135693554037699827 205488369203540331056549741)
    ·
      refine ⟨77058138451327624146206153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205488369203540331056549741 77058138451327624146206153)
      ·
        refine ⟨57793603838495718109654615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77058138451327624146206153 57793603838495718109654615)
        ·
          refine ⟨86690405757743577164481923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57793603838495718109654615 86690405757743577164481923)
          ·
            refine ⟨130035608636615365746722885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86690405757743577164481923 130035608636615365746722885)
            ·
              refine ⟨24381676619365381077510541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130035608636615365746722885 24381676619365381077510541)
              ·
                refine ⟨9143128732262017904066453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24381676619365381077510541 9143128732262017904066453)
                ·
                  refine ⟨428584159324782089253115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9143128732262017904066453 428584159324782089253115)
                  ·
                    rfl

theorem cell22_3755991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_3755991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3755991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3755991 prefixEnd_3755991 := by exact prefixLift 3755991
  have htrace : WordTrace (prefixWord ++ tailWord_3755991) baseStart_3755991 baseEnd_3755991 := by
    simpa [prefixWord, tailWord_3755991, baseEnd_3755991] using wordTrace_append hprefix tailTrace_3755991
  have hstable : (prefixWord ++ tailWord_3755991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3755991).length < 2 ^ (prefixWord ++ tailWord_3755991).sum := by decide
  have hdescent : baseEnd_3755991 < baseStart_3755991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3755991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756025 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 4]
def baseStart_3756025 : Nat := 118140960795 + 3756025 * 2 ^ 59
def prefixEnd_3756025 : Nat := 4983230072969 + 3 ^ 40 * 3756025 * 2
def baseEnd_3756025 : Nat := 428588038956393837469747

theorem tailTrace_3756025 : CollatzResearch.WordTrace tailWord_3756025 prefixEnd_3756025 428588038956393837469747 := by
  unfold tailWord_3756025
  simp only [CollatzResearch.WordTrace]
  refine ⟨136993486217570377844437529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91328990811713585229625019 136993486217570377844437529)
  ·
    refine ⟨102745114663177783383328147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136993486217570377844437529 102745114663177783383328147)
    ·
      refine ⟨154117671994766675074992221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102745114663177783383328147 154117671994766675074992221)
      ·
        refine ⟨57794126998037503153122083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154117671994766675074992221 57794126998037503153122083)
        ·
          refine ⟨86691190497056254729683125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57794126998037503153122083 86691190497056254729683125)
          ·
            refine ⟨8127299109099023880907793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86691190497056254729683125 8127299109099023880907793)
            ·
              refine ⟨6095474331824267910680845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8127299109099023880907793 6095474331824267910680845)
              ·
                refine ⟨2285802874434100466505317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095474331824267910680845 2285802874434100466505317)
                ·
                  refine ⟨428588038956393837469747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285802874434100466505317 428588038956393837469747)
                  ·
                    rfl

theorem cell22_3756025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_3756025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756025 prefixEnd_3756025 := by exact prefixLift 3756025
  have htrace : WordTrace (prefixWord ++ tailWord_3756025) baseStart_3756025 baseEnd_3756025 := by
    simpa [prefixWord, tailWord_3756025, baseEnd_3756025] using wordTrace_append hprefix tailTrace_3756025
  have hstable : (prefixWord ++ tailWord_3756025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756025).length < 2 ^ (prefixWord ++ tailWord_3756025).sum := by decide
  have hdescent : baseEnd_3756025 < baseStart_3756025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756194 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3756194 : Nat := 118140960795 + 3756194 * 2 ^ 59
def prefixEnd_3756194 : Nat := 4983230072969 + 3 ^ 40 * 3756194 * 2
def baseEnd_3756194 : Nat := 428607323007640468311241

theorem tailTrace_3756194 : CollatzResearch.WordTrace tailWord_3756194 prefixEnd_3756194 428607323007640468311241 := by
  unfold tailWord_3756194
  simp only [CollatzResearch.WordTrace]
  refine ⟨34249912538489529926834909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91333100102638746471559757 34249912538489529926834909)
  ·
    refine ⟨12843717201933573722563091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34249912538489529926834909 12843717201933573722563091)
    ·
      refine ⟨19265575802900360583844637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843717201933573722563091 19265575802900360583844637)
      ·
        refine ⟨7224590926087635218941739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19265575802900360583844637 7224590926087635218941739)
        ·
          refine ⟨10836886389131452828412609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224590926087635218941739 10836886389131452828412609)
          ·
            refine ⟨8127664791848589621309457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836886389131452828412609 8127664791848589621309457)
            ·
              refine ⟨6095748593886442215982093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8127664791848589621309457 6095748593886442215982093)
              ·
                refine ⟨2285905722707415830993285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095748593886442215982093 2285905722707415830993285)
                ·
                  refine ⟨428607323007640468311241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285905722707415830993285 428607323007640468311241)
                  ·
                    rfl

theorem cell22_3756194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3756194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756194 prefixEnd_3756194 := by exact prefixLift 3756194
  have htrace : WordTrace (prefixWord ++ tailWord_3756194) baseStart_3756194 baseEnd_3756194 := by
    simpa [prefixWord, tailWord_3756194, baseEnd_3756194] using wordTrace_append hprefix tailTrace_3756194
  have hstable : (prefixWord ++ tailWord_3756194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756194).length < 2 ^ (prefixWord ++ tailWord_3756194).sum := by decide
  have hdescent : baseEnd_3756194 < baseStart_3756194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756196 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_3756196 : Nat := 118140960795 + 3756196 * 2 ^ 59
def prefixEnd_3756196 : Nat := 4983230072969 + 3 ^ 40 * 3756196 * 2
def baseEnd_3756196 : Nat := 1285822653663794066383717

theorem tailTrace_3756196 : CollatzResearch.WordTrace tailWord_3756196 prefixEnd_3756196 1285822653663794066383717 := by
  unfold tailWord_3756196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499861549975437024456221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91333148733300582699274961 68499861549975437024456221)
  ·
    refine ⟨25687448081240788884171083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68499861549975437024456221 25687448081240788884171083)
    ·
      refine ⟨38531172121861183326256625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687448081240788884171083 38531172121861183326256625)
      ·
        refine ⟨28898379091395887494692469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38531172121861183326256625 28898379091395887494692469)
        ·
          refine ⟨2709223039818364452627419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28898379091395887494692469 2709223039818364452627419)
          ·
            refine ⟨4063834559727546678941129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709223039818364452627419 4063834559727546678941129)
            ·
              refine ⟨3047875919795660009205847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063834559727546678941129 3047875919795660009205847)
              ·
                refine ⟨4571813879693490013808771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047875919795660009205847 4571813879693490013808771)
                ·
                  refine ⟨6857720819540235020713157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571813879693490013808771 6857720819540235020713157)
                  ·
                    refine ⟨1285822653663794066383717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857720819540235020713157 1285822653663794066383717)
                    ·
                      rfl

theorem cell22_3756196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_3756196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756196 prefixEnd_3756196 := by exact prefixLift 3756196
  have htrace : WordTrace (prefixWord ++ tailWord_3756196) baseStart_3756196 baseEnd_3756196 := by
    simpa [prefixWord, tailWord_3756196, baseEnd_3756196] using wordTrace_append hprefix tailTrace_3756196
  have hstable : (prefixWord ++ tailWord_3756196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756196).length < 2 ^ (prefixWord ++ tailWord_3756196).sum := by decide
  have hdescent : baseEnd_3756196 < baseStart_3756196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756205 : List Nat := [1, 5, 2, 1, 2, 2, 9]
def baseStart_3756205 : Nat := 118140960795 + 3756205 * 2 ^ 59
def prefixEnd_3756205 : Nat := 4983230072969 + 3 ^ 40 * 3756205 * 2
def baseEnd_3756205 : Nat := 47623175353619297885507

theorem tailTrace_3756205 : CollatzResearch.WordTrace tailWord_3756205 prefixEnd_3756205 47623175353619297885507 := by
  unfold tailWord_3756205
  simp only [CollatzResearch.WordTrace]
  refine ⟨137000051356918268585990069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91333367571278845723993379 137000051356918268585990069)
  ·
    refine ⟨12843754814711087679936569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137000051356918268585990069 12843754814711087679936569)
    ·
      refine ⟨9632816111033315759952427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843754814711087679936569 9632816111033315759952427)
      ·
        refine ⟨14449224166549973639928641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632816111033315759952427 14449224166549973639928641)
        ·
          refine ⟨10836918124912480229946481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14449224166549973639928641 10836918124912480229946481)
          ·
            refine ⟨8127688593684360172459861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10836918124912480229946481 8127688593684360172459861)
            ·
              refine ⟨47623175353619297885507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8127688593684360172459861 47623175353619297885507)
              ·
                rfl

theorem cell22_3756205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 9].length) (baseStart_3756205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756205 prefixEnd_3756205 := by exact prefixLift 3756205
  have htrace : WordTrace (prefixWord ++ tailWord_3756205) baseStart_3756205 baseEnd_3756205 := by
    simpa [prefixWord, tailWord_3756205, baseEnd_3756205] using wordTrace_append hprefix tailTrace_3756205
  have hstable : (prefixWord ++ tailWord_3756205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756205).length < 2 ^ (prefixWord ++ tailWord_3756205).sum := by decide
  have hdescent : baseEnd_3756205 < baseStart_3756205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756218 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3756218 : Nat := 118140960795 + 3756218 * 2 ^ 59
def prefixEnd_3756218 : Nat := 4983230072969 + 3 ^ 40 * 3756218 * 2
def baseEnd_3756218 : Nat := 1285830184713393342333649

theorem tailTrace_3756218 : CollatzResearch.WordTrace tailWord_3756218 prefixEnd_3756218 1285830184713393342333649 := by
  unfold tailWord_3756218
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250131376467792951553327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91333683670580781204142205 34250131376467792951553327)
  ·
    refine ⟨51375197064701689427329991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34250131376467792951553327 51375197064701689427329991)
    ·
      refine ⟨77062795597052534140994987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51375197064701689427329991 77062795597052534140994987)
      ·
        refine ⟨115594193395578801211492481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77062795597052534140994987 115594193395578801211492481)
        ·
          refine ⟨86695645046684100908619361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115594193395578801211492481 86695645046684100908619361)
          ·
            refine ⟨65021733785013075681464521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86695645046684100908619361 65021733785013075681464521)
            ·
              refine ⟨48766300338759806761098391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65021733785013075681464521 48766300338759806761098391)
              ·
                refine ⟨73149450508139710141647587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48766300338759806761098391 73149450508139710141647587)
                ·
                  refine ⟨109724175762209565212471381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73149450508139710141647587 109724175762209565212471381)
                  ·
                    refine ⟨1285830184713393342333649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109724175762209565212471381 1285830184713393342333649)
                    ·
                      rfl

theorem cell22_3756218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3756218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756218 prefixEnd_3756218 := by exact prefixLift 3756218
  have htrace : WordTrace (prefixWord ++ tailWord_3756218) baseStart_3756218 baseEnd_3756218 := by
    simpa [prefixWord, tailWord_3756218, baseEnd_3756218] using wordTrace_append hprefix tailTrace_3756218
  have hstable : (prefixWord ++ tailWord_3756218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756218).length < 2 ^ (prefixWord ++ tailWord_3756218).sum := by decide
  have hdescent : baseEnd_3756218 < baseStart_3756218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756226 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3756226 : Nat := 118140960795 + 3756226 * 2 ^ 59
def prefixEnd_3756226 : Nat := 4983230072969 + 3 ^ 40 * 3756226 * 2
def baseEnd_3756226 : Nat := 1285832923276883988133625

theorem tailTrace_3756226 : CollatzResearch.WordTrace tailWord_3756226 prefixEnd_3756226 1285832923276883988133625 := by
  unfold tailWord_3756226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250204322460547293126133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91333878193228126115003021 34250204322460547293126133)
  ·
    refine ⟨3210956655230676308730575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34250204322460547293126133 3210956655230676308730575)
    ·
      refine ⟨4816434982846014463095863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210956655230676308730575 4816434982846014463095863)
      ·
        refine ⟨7224652474269021694643795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816434982846014463095863 7224652474269021694643795)
        ·
          refine ⟨10836978711403532541965693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224652474269021694643795 10836978711403532541965693)
          ·
            refine ⟨4063867016776324703237135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10836978711403532541965693 4063867016776324703237135)
            ·
              refine ⟨6095800525164487054855703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063867016776324703237135 6095800525164487054855703)
              ·
                refine ⟨9143700787746730582283555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095800525164487054855703 9143700787746730582283555)
                ·
                  refine ⟨13715551181620095873425333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143700787746730582283555 13715551181620095873425333)
                  ·
                    refine ⟨1285832923276883988133625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13715551181620095873425333 1285832923276883988133625)
                    ·
                      rfl

theorem cell22_3756226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3756226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756226 prefixEnd_3756226 := by exact prefixLift 3756226
  have htrace : WordTrace (prefixWord ++ tailWord_3756226) baseStart_3756226 baseEnd_3756226 := by
    simpa [prefixWord, tailWord_3756226, baseEnd_3756226] using wordTrace_append hprefix tailTrace_3756226
  have hstable : (prefixWord ++ tailWord_3756226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756226).length < 2 ^ (prefixWord ++ tailWord_3756226).sum := by decide
  have hdescent : baseEnd_3756226 < baseStart_3756226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756271 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 1, 3]
def baseStart_3756271 : Nat := 118140960795 + 3756271 * 2 ^ 59
def prefixEnd_3756271 : Nat := 4983230072969 + 3 ^ 40 * 3756271 * 2
def baseEnd_3756271 : Nat := 1285848327696518870758487

theorem tailTrace_3756271 : CollatzResearch.WordTrace tailWord_3756271 prefixEnd_3756271 1285848327696518870758487 := by
  unfold tailWord_3756271
  simp only [CollatzResearch.WordTrace]
  refine ⟨137002458574679161857892667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91334972383119441238595111 137002458574679161857892667)
  ·
    refine ⟨205503687862018742786839001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137002458574679161857892667 205503687862018742786839001)
    ·
      refine ⟨154127765896514057090129251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205503687862018742786839001 154127765896514057090129251)
      ·
        refine ⟨231191648844771085635193877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154127765896514057090129251 231191648844771085635193877)
        ·
          refine ⟨10837108539598644639149713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231191648844771085635193877 10837108539598644639149713)
          ·
            refine ⟨8127831404698983479362285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10837108539598644639149713 8127831404698983479362285)
            ·
              refine ⟨3047936776762118804760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8127831404698983479362285 3047936776762118804760857)
              ·
                refine ⟨2285952582571589103570643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047936776762118804760857 2285952582571589103570643)
                ·
                  refine ⟨3428928873857383655355965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285952582571589103570643 3428928873857383655355965)
                  ·
                    refine ⟨1285848327696518870758487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428928873857383655355965 1285848327696518870758487)
                    ·
                      rfl

theorem cell22_3756271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_3756271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756271 prefixEnd_3756271 := by exact prefixLift 3756271
  have htrace : WordTrace (prefixWord ++ tailWord_3756271) baseStart_3756271 baseEnd_3756271 := by
    simpa [prefixWord, tailWord_3756271, baseEnd_3756271] using wordTrace_append hprefix tailTrace_3756271
  have hstable : (prefixWord ++ tailWord_3756271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756271).length < 2 ^ (prefixWord ++ tailWord_3756271).sum := by decide
  have hdescent : baseEnd_3756271 < baseStart_3756271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756284 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_3756284 : Nat := 118140960795 + 3756284 * 2 ^ 59
def prefixEnd_3756284 : Nat := 4983230072969 + 3 ^ 40 * 3756284 * 2
def baseEnd_3756284 : Nat := 428617592620730390061149

theorem tailTrace_3756284 : CollatzResearch.WordTrace tailWord_3756284 prefixEnd_3756284 428617592620730390061149 := by
  unfold tailWord_3756284
  simp only [CollatzResearch.WordTrace]
  refine ⟨68501466361816032539057953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91335288482421376718743937 68501466361816032539057953)
  ·
    refine ⟨51376099771362024404293465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68501466361816032539057953 51376099771362024404293465)
    ·
      refine ⟨38532074828521518303220099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51376099771362024404293465 38532074828521518303220099)
      ·
        refine ⟨57798112242782277454830149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38532074828521518303220099 57798112242782277454830149)
        ·
          refine ⟨10837146045521677022780653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57798112242782277454830149 10837146045521677022780653)
          ·
            refine ⟨4063929767070628883542745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10837146045521677022780653 4063929767070628883542745)
            ·
              refine ⟨3047947325302971662657059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063929767070628883542745 3047947325302971662657059)
              ·
                refine ⟨4571920987954457493985589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047947325302971662657059 4571920987954457493985589)
                ·
                  refine ⟨428617592620730390061149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571920987954457493985589 428617592620730390061149)
                  ·
                    rfl

theorem cell22_3756284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_3756284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756284 prefixEnd_3756284 := by exact prefixLift 3756284
  have htrace : WordTrace (prefixWord ++ tailWord_3756284) baseStart_3756284 baseEnd_3756284 := by
    simpa [prefixWord, tailWord_3756284, baseEnd_3756284] using wordTrace_append hprefix tailTrace_3756284
  have hstable : (prefixWord ++ tailWord_3756284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756284).length < 2 ^ (prefixWord ++ tailWord_3756284).sum := by decide
  have hdescent : baseEnd_3756284 < baseStart_3756284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756297 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_3756297 : Nat := 118140960795 + 3756297 * 2 ^ 59
def prefixEnd_3756297 : Nat := 4983230072969 + 3 ^ 40 * 3756297 * 2
def baseEnd_3756297 : Nat := 1285857228027863469608407

theorem tailTrace_3756297 : CollatzResearch.WordTrace tailWord_3756297 prefixEnd_3756297 1285857228027863469608407 := by
  unfold tailWord_3756297
  simp only [CollatzResearch.WordTrace]
  refine ⟨137003406872584968298339145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91335604581723312198892763 137003406872584968298339145)
  ·
    refine ⟨102752555154438726223754359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137003406872584968298339145 102752555154438726223754359)
    ·
      refine ⟨154128832731658089335631539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102752555154438726223754359 154128832731658089335631539)
      ·
        refine ⟨231193249097487134003447309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154128832731658089335631539 231193249097487134003447309)
        ·
          refine ⟨86697468411557675251292741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231193249097487134003447309 86697468411557675251292741)
          ·
            refine ⟨16255775327167064109617389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86697468411557675251292741 16255775327167064109617389)
            ·
              refine ⟨6095915747687649041106521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16255775327167064109617389 6095915747687649041106521)
              ·
                refine ⟨4571936810765736780829891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095915747687649041106521 4571936810765736780829891)
                ·
                  refine ⟨6857905216148605171244837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571936810765736780829891 6857905216148605171244837)
                  ·
                    refine ⟨1285857228027863469608407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6857905216148605171244837 1285857228027863469608407)
                    ·
                      rfl

theorem cell22_3756297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_3756297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756297 prefixEnd_3756297 := by exact prefixLift 3756297
  have htrace : WordTrace (prefixWord ++ tailWord_3756297) baseStart_3756297 baseEnd_3756297 := by
    simpa [prefixWord, tailWord_3756297, baseEnd_3756297] using wordTrace_append hprefix tailTrace_3756297
  have hstable : (prefixWord ++ tailWord_3756297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756297).length < 2 ^ (prefixWord ++ tailWord_3756297).sum := by decide
  have hdescent : baseEnd_3756297 < baseStart_3756297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756312 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_3756312 : Nat := 118140960795 + 3756312 * 2 ^ 59
def prefixEnd_3756312 : Nat := 4983230072969 + 3 ^ 40 * 3756312 * 2
def baseEnd_3756312 : Nat := 428620787611469476827787

theorem tailTrace_3756312 : CollatzResearch.WordTrace tailWord_3756312 prefixEnd_3756312 428620787611469476827787 := by
  unfold tailWord_3756312
  simp only [CollatzResearch.WordTrace]
  refine ⟨68501976983765312930067595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91335969311687083906756793 68501976983765312930067595)
  ·
    refine ⟨102752965475647969395101393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68501976983765312930067595 102752965475647969395101393)
    ·
      refine ⟨77064724106735977046326045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102752965475647969395101393 77064724106735977046326045)
      ·
        refine ⟨28899271540025991392372267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77064724106735977046326045 28899271540025991392372267)
        ·
          refine ⟨43348907310038987088558401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28899271540025991392372267 43348907310038987088558401)
          ·
            refine ⟨32511680482529240316418801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43348907310038987088558401 32511680482529240316418801)
            ·
              refine ⟨24383760361896930237314101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32511680482529240316418801 24383760361896930237314101)
              ·
                refine ⟨2285977533927837209748197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24383760361896930237314101 2285977533927837209748197)
                ·
                  refine ⟨428620787611469476827787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285977533927837209748197 428620787611469476827787)
                  ·
                    rfl

theorem cell22_3756312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_3756312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756312 prefixEnd_3756312 := by exact prefixLift 3756312
  have htrace : WordTrace (prefixWord ++ tailWord_3756312) baseStart_3756312 baseEnd_3756312 := by
    simpa [prefixWord, tailWord_3756312, baseEnd_3756312] using wordTrace_append hprefix tailTrace_3756312
  have hstable : (prefixWord ++ tailWord_3756312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756312).length < 2 ^ (prefixWord ++ tailWord_3756312).sum := by decide
  have hdescent : baseEnd_3756312 < baseStart_3756312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756389 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_3756389 : Nat := 118140960795 + 3756389 * 2 ^ 59
def prefixEnd_3756389 : Nat := 4983230072969 + 3 ^ 40 * 3756389 * 2
def baseEnd_3756389 : Nat := 1285888721508005896308125

theorem tailTrace_3756389 : CollatzResearch.WordTrace tailWord_3756389 prefixEnd_3756389 1285888721508005896308125 := by
  unfold tailWord_3756389
  simp only [CollatzResearch.WordTrace]
  refine ⟨137006762388251668010688221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91337841592167778673792147 137006762388251668010688221)
  ·
    refine ⟨51377535895594375504008083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137006762388251668010688221 51377535895594375504008083)
    ·
      refine ⟨77066303843391563256012125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51377535895594375504008083 77066303843391563256012125)
      ·
        refine ⟨28899863941271836221004547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77066303843391563256012125 28899863941271836221004547)
        ·
          refine ⟨43349795911907754331506821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28899863941271836221004547 43349795911907754331506821)
          ·
            refine ⟨8128086733482703937157529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43349795911907754331506821 8128086733482703937157529)
            ·
              refine ⟨6096065050112027952868147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128086733482703937157529 6096065050112027952868147)
              ·
                refine ⟨9144097575168041929302221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096065050112027952868147 9144097575168041929302221)
                ·
                  refine ⟨3429036590688015723488333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9144097575168041929302221 3429036590688015723488333)
                  ·
                    refine ⟨1285888721508005896308125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429036590688015723488333 1285888721508005896308125)
                    ·
                      rfl

theorem cell22_3756389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_3756389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756389 prefixEnd_3756389 := by exact prefixLift 3756389
  have htrace : WordTrace (prefixWord ++ tailWord_3756389) baseStart_3756389 baseEnd_3756389 := by
    simpa [prefixWord, tailWord_3756389, baseEnd_3756389] using wordTrace_append hprefix tailTrace_3756389
  have hstable : (prefixWord ++ tailWord_3756389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756389).length < 2 ^ (prefixWord ++ tailWord_3756389).sum := by decide
  have hdescent : baseEnd_3756389 < baseStart_3756389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756492 : List Nat := [2, 2, 1, 4, 3, 10]
def baseStart_3756492 : Nat := 118140960795 + 3756492 * 2 ^ 59
def prefixEnd_3756492 : Nat := 4983230072969 + 3 ^ 40 * 3756492 * 2
def baseEnd_3756492 : Nat := 15875604697690715567689

theorem tailTrace_3756492 : CollatzResearch.WordTrace tailWord_3756492 prefixEnd_3756492 15875604697690715567689 := by
  unfold tailWord_3756492
  simp only [CollatzResearch.WordTrace]
  refine ⟨68505259553439258300843865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91340346071252344401125153 68505259553439258300843865)
  ·
    refine ⟨51378944665079443725632899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68505259553439258300843865 51378944665079443725632899)
    ·
      refine ⟨77068416997619165588449349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51378944665079443725632899 77068416997619165588449349)
      ·
        refine ⟨14450328187053593547834253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77068416997619165588449349 14450328187053593547834253)
        ·
          refine ⟨5418873070145097580437845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14450328187053593547834253 5418873070145097580437845)
          ·
            refine ⟨15875604697690715567689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5418873070145097580437845 15875604697690715567689)
            ·
              rfl

theorem cell22_3756492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 10].length) (baseStart_3756492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756492 prefixEnd_3756492 := by exact prefixLift 3756492
  have htrace : WordTrace (prefixWord ++ tailWord_3756492) baseStart_3756492 baseEnd_3756492 := by
    simpa [prefixWord, tailWord_3756492, baseEnd_3756492] using wordTrace_append hprefix tailTrace_3756492
  have hstable : (prefixWord ++ tailWord_3756492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756492).length < 2 ^ (prefixWord ++ tailWord_3756492).sum := by decide
  have hdescent : baseEnd_3756492 < baseStart_3756492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756498 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_3756498 : Nat := 118140960795 + 3756498 * 2 ^ 59
def prefixEnd_3756498 : Nat := 4983230072969 + 3 ^ 40 * 3756498 * 2
def baseEnd_3756498 : Nat := 428642011478521981777597

theorem tailTrace_3756498 : CollatzResearch.WordTrace tailWord_3756498 prefixEnd_3756498 428642011478521981777597 := by
  unfold tailWord_3756498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34252684486214194906601537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91340491963237853084270765 34252684486214194906601537)
  ·
    refine ⟨25689513364660646179951153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34252684486214194906601537 25689513364660646179951153)
    ·
      refine ⟨19267135023495484634963365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25689513364660646179951153 19267135023495484634963365)
      ·
        refine ⟨3612587816905403369055631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19267135023495484634963365 3612587816905403369055631)
        ·
          refine ⟨5418881725358105053583447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612587816905403369055631 5418881725358105053583447)
          ·
            refine ⟨8128322588037157580375171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5418881725358105053583447 8128322588037157580375171)
            ·
              refine ⟨12192483882055736370562757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8128322588037157580375171 12192483882055736370562757)
              ·
                refine ⟨2286090727885450569480517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12192483882055736370562757 2286090727885450569480517)
                ·
                  refine ⟨428642011478521981777597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2286090727885450569480517 428642011478521981777597)
                  ·
                    rfl

theorem cell22_3756498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_3756498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756498 prefixEnd_3756498 := by exact prefixLift 3756498
  have htrace : WordTrace (prefixWord ++ tailWord_3756498) baseStart_3756498 baseEnd_3756498 := by
    simpa [prefixWord, tailWord_3756498, baseEnd_3756498] using wordTrace_append hprefix tailTrace_3756498
  have hstable : (prefixWord ++ tailWord_3756498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756498).length < 2 ^ (prefixWord ++ tailWord_3756498).sum := by decide
  have hdescent : baseEnd_3756498 < baseStart_3756498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756524 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 3, 3]
def baseStart_3756524 : Nat := 118140960795 + 3756524 * 2 ^ 59
def prefixEnd_3756524 : Nat := 4983230072969 + 3 ^ 40 * 3756524 * 2
def baseEnd_3756524 : Nat := 1285934934766910544182711

theorem tailTrace_3756524 : CollatzResearch.WordTrace tailWord_3756524 prefixEnd_3756524 1285934934766910544182711 := by
  unfold tailWord_3756524
  simp only [CollatzResearch.WordTrace]
  refine ⟨68505843121381293033426313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91341124161841724044568417 68505843121381293033426313)
  ·
    refine ⟨51379382341035969775069735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68505843121381293033426313 51379382341035969775069735)
    ·
      refine ⟨77069073511553954662604603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51379382341035969775069735 77069073511553954662604603)
      ·
        refine ⟨115603610267330931993906905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77069073511553954662604603 115603610267330931993906905)
        ·
          refine ⟨86702707700498198995430179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115603610267330931993906905 86702707700498198995430179)
          ·
            refine ⟨130054061550747298493145269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86702707700498198995430179 130054061550747298493145269)
            ·
              refine ⟨12192568270382559233732369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130054061550747298493145269 12192568270382559233732369)
              ·
                refine ⟨9144426202786919425299277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12192568270382559233732369 9144426202786919425299277)
                ·
                  refine ⟨3429159826045094784487229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9144426202786919425299277 3429159826045094784487229)
                  ·
                    refine ⟨1285934934766910544182711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429159826045094784487229 1285934934766910544182711)
                    ·
                      rfl

theorem cell22_3756524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_3756524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756524 prefixEnd_3756524 := by exact prefixLift 3756524
  have htrace : WordTrace (prefixWord ++ tailWord_3756524) baseStart_3756524 baseEnd_3756524 := by
    simpa [prefixWord, tailWord_3756524, baseEnd_3756524] using wordTrace_append hprefix tailTrace_3756524
  have hstable : (prefixWord ++ tailWord_3756524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756524).length < 2 ^ (prefixWord ++ tailWord_3756524).sum := by decide
  have hdescent : baseEnd_3756524 < baseStart_3756524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756558 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 1, 3]
def baseStart_3756558 : Nat := 118140960795 + 3756558 * 2 ^ 59
def prefixEnd_3756558 : Nat := 4983230072969 + 3 ^ 40 * 3756558 * 2
def baseEnd_3756558 : Nat := 1285946573661745788832607

theorem tailTrace_3756558 : CollatzResearch.WordTrace tailWord_3756558 prefixEnd_3756558 1285946573661745788832607 := by
  unfold tailWord_3756558
  simp only [CollatzResearch.WordTrace]
  refine ⟨17126615790579926234198791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91341950883092939915726885 17126615790579926234198791)
  ·
    refine ⟨25689923685869889351298187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17126615790579926234198791 25689923685869889351298187)
    ·
      refine ⟨38534885528804834026947281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25689923685869889351298187 38534885528804834026947281)
      ·
        refine ⟨28901164146603625520210461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38534885528804834026947281 28901164146603625520210461)
        ·
          refine ⟨10837936554976359570078923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28901164146603625520210461 10837936554976359570078923)
          ·
            refine ⟨16256904832464539355118385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837936554976359570078923 16256904832464539355118385)
            ·
              refine ⟨12192678624348404516338789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16256904832464539355118385 12192678624348404516338789)
              ·
                refine ⟨2286127242065325846813523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12192678624348404516338789 2286127242065325846813523)
                ·
                  refine ⟨3429190863097988770220285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286127242065325846813523 3429190863097988770220285)
                  ·
                    refine ⟨1285946573661745788832607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429190863097988770220285 1285946573661745788832607)
                    ·
                      rfl

theorem cell22_3756558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_3756558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756558 prefixEnd_3756558 := by exact prefixLift 3756558
  have htrace : WordTrace (prefixWord ++ tailWord_3756558) baseStart_3756558 baseEnd_3756558 := by
    simpa [prefixWord, tailWord_3756558, baseEnd_3756558] using wordTrace_append hprefix tailTrace_3756558
  have hstable : (prefixWord ++ tailWord_3756558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756558).length < 2 ^ (prefixWord ++ tailWord_3756558).sum := by decide
  have hdescent : baseEnd_3756558 < baseStart_3756558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756631 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 2, 3]
def baseStart_3756631 : Nat := 118140960795 + 3756631 * 2 ^ 59
def prefixEnd_3756631 : Nat := 4983230072969 + 3 ^ 40 * 3756631 * 2
def baseEnd_3756631 : Nat := 1285971563053597931757383

theorem tailTrace_3756631 : CollatzResearch.WordTrace tailWord_3756631 prefixEnd_3756631 1285971563053597931757383 := by
  unfold tailWord_3756631
  simp only [CollatzResearch.WordTrace]
  refine ⟨137015588853374943340997747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91343725902249962227331831 137015588853374943340997747)
  ·
    refine ⟨205523383280062415011496621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137015588853374943340997747 205523383280062415011496621)
    ·
      refine ⟨77071268730023405629311233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205523383280062415011496621 77071268730023405629311233)
      ·
        refine ⟨57803451547517554221983425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77071268730023405629311233 57803451547517554221983425)
        ·
          refine ⟨43352588660638165666487569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57803451547517554221983425 43352588660638165666487569)
          ·
            refine ⟨32514441495478624249865677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43352588660638165666487569 32514441495478624249865677)
            ·
              refine ⟨12192915560804484093699629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32514441495478624249865677 12192915560804484093699629)
              ·
                refine ⟨4572343335301681535137361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12192915560804484093699629 4572343335301681535137361)
                ·
                  refine ⟨3429257501476261151353021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572343335301681535137361 3429257501476261151353021)
                  ·
                    refine ⟨1285971563053597931757383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429257501476261151353021 1285971563053597931757383)
                    ·
                      rfl

theorem cell22_3756631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 3].length) (baseStart_3756631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756631 prefixEnd_3756631 := by exact prefixLift 3756631
  have htrace : WordTrace (prefixWord ++ tailWord_3756631) baseStart_3756631 baseEnd_3756631 := by
    simpa [prefixWord, tailWord_3756631, baseEnd_3756631] using wordTrace_append hprefix tailTrace_3756631
  have hstable : (prefixWord ++ tailWord_3756631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756631).length < 2 ^ (prefixWord ++ tailWord_3756631).sum := by decide
  have hdescent : baseEnd_3756631 < baseStart_3756631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756659 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 7, 3]
def baseStart_3756659 : Nat := 118140960795 + 3756659 * 2 ^ 59
def prefixEnd_3756659 : Nat := 4983230072969 + 3 ^ 40 * 3756659 * 2
def baseEnd_3756659 : Nat := 1285981148025815192057297

theorem tailTrace_3756659 : CollatzResearch.WordTrace tailWord_3756659 prefixEnd_3756659 1285981148025815192057297 := by
  unfold tailWord_3756659
  simp only [CollatzResearch.WordTrace]
  refine ⟨137016610097273504123017031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91344406731515669415344687 137016610097273504123017031)
  ·
    refine ⟨205524915145910256184525547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137016610097273504123017031 205524915145910256184525547)
    ·
      refine ⟨308287372718865384276788321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205524915145910256184525547 308287372718865384276788321)
      ·
        refine ⟨231215529539149038207591241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308287372718865384276788321 231215529539149038207591241)
        ·
          refine ⟨173411647154361778655693431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231215529539149038207591241 173411647154361778655693431)
          ·
            refine ⟨260117470731542667983540147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173411647154361778655693431 260117470731542667983540147)
            ·
              refine ⟨390176206097314001975310221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260117470731542667983540147 390176206097314001975310221)
              ·
                refine ⟨146316077286492750740741333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390176206097314001975310221 146316077286492750740741333)
                ·
                  refine ⟨3429283061402173845486125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 146316077286492750740741333 3429283061402173845486125)
                  ·
                    refine ⟨1285981148025815192057297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429283061402173845486125 1285981148025815192057297)
                    ·
                      rfl

theorem cell22_3756659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 3].length) (baseStart_3756659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756659 prefixEnd_3756659 := by exact prefixLift 3756659
  have htrace : WordTrace (prefixWord ++ tailWord_3756659) baseStart_3756659 baseEnd_3756659 := by
    simpa [prefixWord, tailWord_3756659, baseEnd_3756659] using wordTrace_append hprefix tailTrace_3756659
  have hstable : (prefixWord ++ tailWord_3756659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756659).length < 2 ^ (prefixWord ++ tailWord_3756659).sum := by decide
  have hdescent : baseEnd_3756659 < baseStart_3756659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756661 : List Nat := [1, 3, 4, 2, 3, 9]
def baseStart_3756661 : Nat := 118140960795 + 3756661 * 2 ^ 59
def prefixEnd_3756661 : Nat := 4983230072969 + 3 ^ 40 * 3756661 * 2
def baseEnd_3756661 : Nat := 15876318921810961154411

theorem tailTrace_3756661 : CollatzResearch.WordTrace tailWord_3756661 prefixEnd_3756661 15876318921810961154411 := by
  unfold tailWord_3756661
  simp only [CollatzResearch.WordTrace]
  refine ⟨137016683043266258464589837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91344455362177505643059891 137016683043266258464589837)
  ·
    refine ⟨51381256141224846924221189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137016683043266258464589837 51381256141224846924221189)
    ·
      refine ⟨9633985526479658798291473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51381256141224846924221189 9633985526479658798291473)
      ·
        refine ⟨7225489144859744098718605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9633985526479658798291473 7225489144859744098718605)
        ·
          refine ⟨2709558429322404037019477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7225489144859744098718605 2709558429322404037019477)
          ·
            refine ⟨15876318921810961154411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2709558429322404037019477 15876318921810961154411)
            ·
              rfl

theorem cell22_3756661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 9].length) (baseStart_3756661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756661 prefixEnd_3756661 := by exact prefixLift 3756661
  have htrace : WordTrace (prefixWord ++ tailWord_3756661) baseStart_3756661 baseEnd_3756661 := by
    simpa [prefixWord, tailWord_3756661, baseEnd_3756661] using wordTrace_append hprefix tailTrace_3756661
  have hstable : (prefixWord ++ tailWord_3756661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756661).length < 2 ^ (prefixWord ++ tailWord_3756661).sum := by decide
  have hdescent : baseEnd_3756661 < baseStart_3756661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756796 : List Nat := [2, 2, 2, 1, 3, 3, 2, 7]
def baseStart_3756796 : Nat := 118140960795 + 3756796 * 2 ^ 59
def prefixEnd_3756796 : Nat := 4983230072969 + 3 ^ 40 * 3756796 * 2
def baseEnd_3756796 : Nat := 142892005102843611264653

theorem tailTrace_3756796 : CollatzResearch.WordTrace tailWord_3756796 prefixEnd_3756796 142892005102843611264653 := by
  unfold tailWord_3756796
  simp only [CollatzResearch.WordTrace]
  refine ⟨68510803448888588260377121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91347737931851451013836161 68510803448888588260377121)
  ·
    refine ⟨51383102586666441195282841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68510803448888588260377121 51383102586666441195282841)
    ·
      refine ⟨38537326939999830896462131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51383102586666441195282841 38537326939999830896462131)
      ·
        refine ⟨57805990409999746344693197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38537326939999830896462131 57805990409999746344693197)
        ·
          refine ⟨21677246403749904879259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57805990409999746344693197 21677246403749904879259949)
          ·
            refine ⟨8128967401406214329722481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21677246403749904879259949 8128967401406214329722481)
            ·
              refine ⟨6096725551054660747291861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8128967401406214329722481 6096725551054660747291861)
              ·
                refine ⟨142892005102843611264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6096725551054660747291861 142892005102843611264653)
                ·
                  rfl

theorem cell22_3756796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_3756796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756796 prefixEnd_3756796 := by exact prefixLift 3756796
  have htrace : WordTrace (prefixWord ++ tailWord_3756796) baseStart_3756796 baseEnd_3756796 := by
    simpa [prefixWord, tailWord_3756796, baseEnd_3756796] using wordTrace_append hprefix tailTrace_3756796
  have hstable : (prefixWord ++ tailWord_3756796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756796).length < 2 ^ (prefixWord ++ tailWord_3756796).sum := by decide
  have hdescent : baseEnd_3756796 < baseStart_3756796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756811 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 5, 3]
def baseStart_3756811 : Nat := 118140960795 + 3756811 * 2 ^ 59
def prefixEnd_3756811 : Nat := 4983230072969 + 3 ^ 40 * 3756811 * 2
def baseEnd_3756811 : Nat := 1286033180732137462256831

theorem tailTrace_3756811 : CollatzResearch.WordTrace tailWord_3756811 prefixEnd_3756811 1286033180732137462256831 := by
  unfold tailWord_3756811
  simp only [CollatzResearch.WordTrace]
  refine ⟨137022153992722834082550287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91348102661815222721700191 137022153992722834082550287)
  ·
    refine ⟨205533230989084251123825431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137022153992722834082550287 205533230989084251123825431)
    ·
      refine ⟨308299846483626376685738147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205533230989084251123825431 308299846483626376685738147)
      ·
        refine ⟨462449769725439565028607221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308299846483626376685738147 462449769725439565028607221)
        ·
          refine ⟨43354665911759959221431927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 462449769725439565028607221 43354665911759959221431927)
          ·
            refine ⟨65031998867639938832147891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43354665911759959221431927 65031998867639938832147891)
            ·
              refine ⟨97547998301459908248221837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65031998867639938832147891 97547998301459908248221837)
              ·
                refine ⟨36580499363047465593083189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97547998301459908248221837 36580499363047465593083189)
                ·
                  refine ⟨3429421815285699899351549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36580499363047465593083189 3429421815285699899351549)
                  ·
                    refine ⟨1286033180732137462256831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429421815285699899351549 1286033180732137462256831)
                    ·
                      rfl

theorem cell22_3756811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 3].length) (baseStart_3756811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756811 prefixEnd_3756811 := by exact prefixLift 3756811
  have htrace : WordTrace (prefixWord ++ tailWord_3756811) baseStart_3756811 baseEnd_3756811 := by
    simpa [prefixWord, tailWord_3756811, baseEnd_3756811] using wordTrace_append hprefix tailTrace_3756811
  have hstable : (prefixWord ++ tailWord_3756811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756811).length < 2 ^ (prefixWord ++ tailWord_3756811).sum := by decide
  have hdescent : baseEnd_3756811 < baseStart_3756811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756856 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 5]
def baseStart_3756856 : Nat := 118140960795 + 3756856 * 2 ^ 59
def prefixEnd_3756856 : Nat := 4983230072969 + 3 ^ 40 * 3756856 * 2
def baseEnd_3756856 : Nat := 1286048585151772344881693

theorem tailTrace_3756856 : CollatzResearch.WordTrace tailWord_3756856 prefixEnd_3756856 1286048585151772344881693 := by
  unfold tailWord_3756856
  simp only [CollatzResearch.WordTrace]
  refine ⟨68511897638779903383969211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91349196851706537845292281 68511897638779903383969211)
  ·
    refine ⟨102767846458169855075953817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68511897638779903383969211 102767846458169855075953817)
    ·
      refine ⟨77075884843627391306965363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102767846458169855075953817 77075884843627391306965363)
      ·
        refine ⟨115613827265441086960448045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77075884843627391306965363 115613827265441086960448045)
        ·
          refine ⟨43355185224540407610168017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115613827265441086960448045 43355185224540407610168017)
          ·
            refine ⟨32516388918405305707626013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43355185224540407610168017 32516388918405305707626013)
            ·
              refine ⟨12193645844401989640359755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32516388918405305707626013 12193645844401989640359755)
              ·
                refine ⟨18290468766602984460539633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193645844401989640359755 18290468766602984460539633)
                ·
                  refine ⟨13717851574952238345404725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290468766602984460539633 13717851574952238345404725)
                  ·
                    refine ⟨1286048585151772344881693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13717851574952238345404725 1286048585151772344881693)
                    ·
                      rfl

theorem cell22_3756856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_3756856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756856 prefixEnd_3756856 := by exact prefixLift 3756856
  have htrace : WordTrace (prefixWord ++ tailWord_3756856) baseStart_3756856 baseEnd_3756856 := by
    simpa [prefixWord, tailWord_3756856, baseEnd_3756856] using wordTrace_append hprefix tailTrace_3756856
  have hstable : (prefixWord ++ tailWord_3756856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756856).length < 2 ^ (prefixWord ++ tailWord_3756856).sum := by decide
  have hdescent : baseEnd_3756856 < baseStart_3756856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756901 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_3756901 : Nat := 118140960795 + 3756901 * 2 ^ 59
def prefixEnd_3756901 : Nat := 4983230072969 + 3 ^ 40 * 3756901 * 2
def baseEnd_3756901 : Nat := 1286063989571407227506555

theorem tailTrace_3756901 : CollatzResearch.WordTrace tailWord_3756901 prefixEnd_3756901 1286063989571407227506555 := by
  unfold tailWord_3756901
  simp only [CollatzResearch.WordTrace]
  refine ⟨137025436562396779453326557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91350291041597852968884371 137025436562396779453326557)
  ·
    refine ⟨51384538710898792294997459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137025436562396779453326557 51384538710898792294997459)
    ·
      refine ⟨77076808066348188442496189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51384538710898792294997459 77076808066348188442496189)
      ·
        refine ⟨28903803024880570665936071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77076808066348188442496189 28903803024880570665936071)
        ·
          refine ⟨43355704537320855998904107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28903803024880570665936071 43355704537320855998904107)
          ·
            refine ⟨65033556805981283998356161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43355704537320855998904107 65033556805981283998356161)
            ·
              refine ⟨48775167604485962998767121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65033556805981283998356161 48775167604485962998767121)
              ·
                refine ⟨36581375703364472249075341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48775167604485962998767121 36581375703364472249075341)
                ·
                  refine ⟨13718015888761677093403253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36581375703364472249075341 13718015888761677093403253)
                  ·
                    refine ⟨1286063989571407227506555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13718015888761677093403253 1286063989571407227506555)
                    ·
                      rfl

theorem cell22_3756901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_3756901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756901 prefixEnd_3756901 := by exact prefixLift 3756901
  have htrace : WordTrace (prefixWord ++ tailWord_3756901) baseStart_3756901 baseEnd_3756901 := by
    simpa [prefixWord, tailWord_3756901, baseEnd_3756901] using wordTrace_append hprefix tailTrace_3756901
  have hstable : (prefixWord ++ tailWord_3756901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756901).length < 2 ^ (prefixWord ++ tailWord_3756901).sum := by decide
  have hdescent : baseEnd_3756901 < baseStart_3756901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756903 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 6]
def baseStart_3756903 : Nat := 118140960795 + 3756903 * 2 ^ 59
def prefixEnd_3756903 : Nat := 4983230072969 + 3 ^ 40 * 3756903 * 2
def baseEnd_3756903 : Nat := 428688224737426629652183

theorem tailTrace_3756903 : CollatzResearch.WordTrace tailWord_3756903 prefixEnd_3756903 428688224737426629652183 := by
  unfold tailWord_3756903
  simp only [CollatzResearch.WordTrace]
  refine ⟨137025509508389533794899363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91350339672259689196599575 137025509508389533794899363)
  ·
    refine ⟨205538264262584300692349045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137025509508389533794899363 205538264262584300692349045)
    ·
      refine ⟨19269212274617278189907723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205538264262584300692349045 19269212274617278189907723)
      ·
        refine ⟨28903818411925917284861585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19269212274617278189907723 28903818411925917284861585)
        ·
          refine ⟨21677863808944437963646189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28903818411925917284861585 21677863808944437963646189)
          ·
            refine ⟨8129198928354164236367321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21677863808944437963646189 8129198928354164236367321)
            ·
              refine ⟨6096899196265623177275491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129198928354164236367321 6096899196265623177275491)
              ·
                refine ⟨9145348794398434765913237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096899196265623177275491 9145348794398434765913237)
                ·
                  refine ⟨428688224737426629652183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9145348794398434765913237 428688224737426629652183)
                  ·
                    rfl

theorem cell22_3756903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_3756903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756903 prefixEnd_3756903 := by exact prefixLift 3756903
  have htrace : WordTrace (prefixWord ++ tailWord_3756903) baseStart_3756903 baseEnd_3756903 := by
    simpa [prefixWord, tailWord_3756903, baseEnd_3756903] using wordTrace_append hprefix tailTrace_3756903
  have hstable : (prefixWord ++ tailWord_3756903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756903).length < 2 ^ (prefixWord ++ tailWord_3756903).sum := by decide
  have hdescent : baseEnd_3756903 < baseStart_3756903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756931 : List Nat := [1, 1, 1, 3, 4, 1, 3, 8]
def baseStart_3756931 : Nat := 118140960795 + 3756931 * 2 ^ 59
def prefixEnd_3756931 : Nat := 4983230072969 + 3 ^ 40 * 3756931 * 2
def baseEnd_3756931 : Nat := 142897139909388572139607

theorem tailTrace_3756931 : CollatzResearch.WordTrace tailWord_3756931 prefixEnd_3756931 142897139909388572139607 := by
  unfold tailWord_3756931
  simp only [CollatzResearch.WordTrace]
  refine ⟨137026530752288094576918647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91351020501525396384612431 137026530752288094576918647)
  ·
    refine ⟨205539796128432141865377971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137026530752288094576918647 205539796128432141865377971)
    ·
      refine ⟨308309694192648212798066957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205539796128432141865377971 308309694192648212798066957)
      ·
        refine ⟨115616135322243079799275109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308309694192648212798066957 115616135322243079799275109)
        ·
          refine ⟨21678025372920577462364083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115616135322243079799275109 21678025372920577462364083)
          ·
            refine ⟨32517038059380866193546125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21678025372920577462364083 32517038059380866193546125)
            ·
              refine ⟨12193889272267824822579797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32517038059380866193546125 12193889272267824822579797)
              ·
                refine ⟨142897139909388572139607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12193889272267824822579797 142897139909388572139607)
                ·
                  rfl

theorem cell22_3756931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 8].length) (baseStart_3756931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756931 prefixEnd_3756931 := by exact prefixLift 3756931
  have htrace : WordTrace (prefixWord ++ tailWord_3756931) baseStart_3756931 baseEnd_3756931 := by
    simpa [prefixWord, tailWord_3756931, baseEnd_3756931] using wordTrace_append hprefix tailTrace_3756931
  have hstable : (prefixWord ++ tailWord_3756931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756931).length < 2 ^ (prefixWord ++ tailWord_3756931).sum := by decide
  have hdescent : baseEnd_3756931 < baseStart_3756931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3756991 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_3756991 : Nat := 118140960795 + 3756991 * 2 ^ 59
def prefixEnd_3756991 : Nat := 4983230072969 + 3 ^ 40 * 3756991 * 2
def baseEnd_3756991 : Nat := 1286094798410676992756279

theorem tailTrace_3756991 : CollatzResearch.WordTrace tailWord_3756991 prefixEnd_3756991 1286094798410676992756279 := by
  unfold tailWord_3756991
  simp only [CollatzResearch.WordTrace]
  refine ⟨137028719132070724824102827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91352479421380483216068551 137028719132070724824102827)
  ·
    refine ⟨205543078698106087236154241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137028719132070724824102827 205543078698106087236154241)
    ·
      refine ⟨154157309023579565427115681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205543078698106087236154241 154157309023579565427115681)
      ·
        refine ⟨115617981767684674070336761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154157309023579565427115681 115617981767684674070336761)
        ·
          refine ⟨86713486325763505552752571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115617981767684674070336761 86713486325763505552752571)
          ·
            refine ⟨130070229488645258329128857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86713486325763505552752571 130070229488645258329128857)
            ·
              refine ⟨97552672116483943746846643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130070229488645258329128857 97552672116483943746846643)
              ·
                refine ⟨146329008174725915620269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97552672116483943746846643 146329008174725915620269965)
                ·
                  refine ⟨54873378065522218357601237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146329008174725915620269965 54873378065522218357601237)
                  ·
                    refine ⟨1286094798410676992756279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54873378065522218357601237 1286094798410676992756279)
                    ·
                      rfl

theorem cell22_3756991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_3756991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3756991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3756991 prefixEnd_3756991 := by exact prefixLift 3756991
  have htrace : WordTrace (prefixWord ++ tailWord_3756991) baseStart_3756991 baseEnd_3756991 := by
    simpa [prefixWord, tailWord_3756991, baseEnd_3756991] using wordTrace_append hprefix tailTrace_3756991
  have hstable : (prefixWord ++ tailWord_3756991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3756991).length < 2 ^ (prefixWord ++ tailWord_3756991).sum := by decide
  have hdescent : baseEnd_3756991 < baseStart_3756991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3756991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757005 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3757005 : Nat := 118140960795 + 3757005 * 2 ^ 59
def prefixEnd_3757005 : Nat := 4983230072969 + 3 ^ 40 * 3757005 * 2
def baseEnd_3757005 : Nat := 428699863632261874302079

theorem tailTrace_3757005 : CollatzResearch.WordTrace tailWord_3757005 prefixEnd_3757005 428699863632261874302079 := by
  unfold tailWord_3757005
  simp only [CollatzResearch.WordTrace]
  refine ⟨137029229754020005215112469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91352819836013336810074979 137029229754020005215112469)
  ·
    refine ⟨6423245144719687744458397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137029229754020005215112469 6423245144719687744458397)
    ·
      refine ⟨2408716929269882904171899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6423245144719687744458397 2408716929269882904171899)
      ·
        refine ⟨3613075393904824356257849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408716929269882904171899 3613075393904824356257849)
        ·
          refine ⟨2709806545428618267193387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613075393904824356257849 2709806545428618267193387)
          ·
            refine ⟨4064709818142927400790081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709806545428618267193387 4064709818142927400790081)
            ·
              refine ⟨3048532363607195550592561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064709818142927400790081 3048532363607195550592561)
              ·
                refine ⟨2286399272705396662944421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048532363607195550592561 2286399272705396662944421)
                ·
                  refine ⟨428699863632261874302079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2286399272705396662944421 428699863632261874302079)
                  ·
                    rfl

theorem cell22_3757005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3757005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757005 prefixEnd_3757005 := by exact prefixLift 3757005
  have htrace : WordTrace (prefixWord ++ tailWord_3757005) baseStart_3757005 baseEnd_3757005 := by
    simpa [prefixWord, tailWord_3757005, baseEnd_3757005] using wordTrace_append hprefix tailTrace_3757005
  have hstable : (prefixWord ++ tailWord_3757005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757005).length < 2 ^ (prefixWord ++ tailWord_3757005).sum := by decide
  have hdescent : baseEnd_3757005 < baseStart_3757005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757010 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_3757010 : Nat := 118140960795 + 3757010 * 2 ^ 59
def prefixEnd_3757010 : Nat := 4983230072969 + 3 ^ 40 * 3757010 * 2
def baseEnd_3757010 : Nat := 428700434166322425510407

theorem tailTrace_3757010 : CollatzResearch.WordTrace tailWord_3757010 prefixEnd_3757010 428700434166322425510407 := by
  unfold tailWord_3757010
  simp only [CollatzResearch.WordTrace]
  refine ⟨34257353029750472767261121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91352941412667927379362989 34257353029750472767261121)
  ·
    refine ⟨25693014772312854575445841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34257353029750472767261121 25693014772312854575445841)
    ·
      refine ⟨19269761079234640931584381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25693014772312854575445841 19269761079234640931584381)
      ·
        refine ⟨7226160404712990349344143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19269761079234640931584381 7226160404712990349344143)
        ·
          refine ⟨10839240607069485524016215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226160404712990349344143 10839240607069485524016215)
          ·
            refine ⟨16258860910604228286024323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839240607069485524016215 16258860910604228286024323)
            ·
              refine ⟨24388291365906342429036485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16258860910604228286024323 24388291365906342429036485)
              ·
                refine ⟨4572804631107439205444341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24388291365906342429036485 4572804631107439205444341)
                ·
                  refine ⟨428700434166322425510407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4572804631107439205444341 428700434166322425510407)
                  ·
                    rfl

theorem cell22_3757010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_3757010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757010 prefixEnd_3757010 := by exact prefixLift 3757010
  have htrace : WordTrace (prefixWord ++ tailWord_3757010) baseStart_3757010 baseEnd_3757010 := by
    simpa [prefixWord, tailWord_3757010, baseEnd_3757010] using wordTrace_append hprefix tailTrace_3757010
  have hstable : (prefixWord ++ tailWord_3757010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757010).length < 2 ^ (prefixWord ++ tailWord_3757010).sum := by decide
  have hdescent : baseEnd_3757010 < baseStart_3757010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757057 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_3757057 : Nat := 118140960795 + 3757057 * 2 ^ 59
def prefixEnd_3757057 : Nat := 4983230072969 + 3 ^ 40 * 3757057 * 2
def baseEnd_3757057 : Nat := 1286117391559474820606077

theorem tailTrace_3757057 : CollatzResearch.WordTrace tailWord_3757057 prefixEnd_3757057 1286117391559474820606077 := by
  unfold tailWord_3757057
  simp only [CollatzResearch.WordTrace]
  refine ⟨137031126349831618096005425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91354084233221078730670283 137031126349831618096005425)
  ·
    refine ⟨102773344762373713572004069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137031126349831618096005425 102773344762373713572004069)
    ·
      refine ⟨19270002142945071294750763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102773344762373713572004069 19270002142945071294750763)
      ·
        refine ⟨28905003214417606942126145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19270002142945071294750763 28905003214417606942126145)
        ·
          refine ⟨21678752410813205206594609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28905003214417606942126145 21678752410813205206594609)
          ·
            refine ⟨16259064308109903904945957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21678752410813205206594609 16259064308109903904945957)
            ·
              refine ⟨3048574557770606982177367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16259064308109903904945957 3048574557770606982177367)
              ·
                refine ⟨4572861836655910473266051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048574557770606982177367 4572861836655910473266051)
                ·
                  refine ⟨6859292754983865709899077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4572861836655910473266051 6859292754983865709899077)
                  ·
                    refine ⟨1286117391559474820606077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859292754983865709899077 1286117391559474820606077)
                    ·
                      rfl

theorem cell22_3757057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_3757057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757057 prefixEnd_3757057 := by exact prefixLift 3757057
  have htrace : WordTrace (prefixWord ++ tailWord_3757057) baseStart_3757057 baseEnd_3757057 := by
    simpa [prefixWord, tailWord_3757057, baseEnd_3757057] using wordTrace_append hprefix tailTrace_3757057
  have hstable : (prefixWord ++ tailWord_3757057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757057).length < 2 ^ (prefixWord ++ tailWord_3757057).sum := by decide
  have hdescent : baseEnd_3757057 < baseStart_3757057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757128 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_3757128 : Nat := 118140960795 + 3757128 * 2 ^ 59
def prefixEnd_3757128 : Nat := 4983230072969 + 3 ^ 40 * 3757128 * 2
def baseEnd_3757128 : Nat := 428713898770151434026953

theorem tailTrace_3757128 : CollatzResearch.WordTrace tailWord_3757128 prefixEnd_3757128 428713898770151434026953 := by
  unfold tailWord_3757128
  simp only [CollatzResearch.WordTrace]
  refine ⟨68516857966287198610920019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91355810621716264814560025 68516857966287198610920019)
  ·
    refine ⟨102775286949430797916380029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68516857966287198610920019 102775286949430797916380029)
    ·
      refine ⟨38540732606036549218642511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102775286949430797916380029 38540732606036549218642511)
      ·
        refine ⟨57811098909054823827963767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38540732606036549218642511 57811098909054823827963767)
        ·
          refine ⟨86716648363582235741945651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57811098909054823827963767 86716648363582235741945651)
          ·
            refine ⟨130074972545373353612918477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86716648363582235741945651 130074972545373353612918477)
            ·
              refine ⟨48778114704515007604844429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130074972545373353612918477 48778114704515007604844429)
              ·
                refine ⟨18291793014193127851816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48778114704515007604844429 18291793014193127851816661)
                ·
                  refine ⟨428713898770151434026953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18291793014193127851816661 428713898770151434026953)
                  ·
                    rfl

theorem cell22_3757128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_3757128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757128 prefixEnd_3757128 := by exact prefixLift 3757128
  have htrace : WordTrace (prefixWord ++ tailWord_3757128) baseStart_3757128 baseEnd_3757128 := by
    simpa [prefixWord, tailWord_3757128, baseEnd_3757128] using wordTrace_append hprefix tailTrace_3757128
  have hstable : (prefixWord ++ tailWord_3757128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757128).length < 2 ^ (prefixWord ++ tailWord_3757128).sum := by decide
  have hdescent : baseEnd_3757128 < baseStart_3757128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757143 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_3757143 : Nat := 118140960795 + 3757143 * 2 ^ 59
def prefixEnd_3757143 : Nat := 4983230072969 + 3 ^ 40 * 3757143 * 2
def baseEnd_3757143 : Nat := 1286146831116999262955813

theorem tailTrace_3757143 : CollatzResearch.WordTrace tailWord_3757143 prefixEnd_3757143 1286146831116999262955813 := by
  unfold tailWord_3757143
  simp only [CollatzResearch.WordTrace]
  refine ⟨137034263027520054783636083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91356175351680036522424055 137034263027520054783636083)
  ·
    refine ⟨205551394541280082175454125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137034263027520054783636083 205551394541280082175454125)
    ·
      refine ⟨77081772952980030815795297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205551394541280082175454125 77081772952980030815795297)
      ·
        refine ⟨57811329714735023111846473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77081772952980030815795297 57811329714735023111846473)
        ·
          refine ⟨43358497286051267333884855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57811329714735023111846473 43358497286051267333884855)
          ·
            refine ⟨65037745929076901000827283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43358497286051267333884855 65037745929076901000827283)
            ·
              refine ⟨97556618893615351501240925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65037745929076901000827283 97556618893615351501240925)
              ·
                refine ⟨36583732085105756812965347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97556618893615351501240925 36583732085105756812965347)
                ·
                  refine ⟨54875598127658635219448021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36583732085105756812965347 54875598127658635219448021)
                  ·
                    refine ⟨1286146831116999262955813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54875598127658635219448021 1286146831116999262955813)
                    ·
                      rfl

theorem cell22_3757143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_3757143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757143 prefixEnd_3757143 := by exact prefixLift 3757143
  have htrace : WordTrace (prefixWord ++ tailWord_3757143) baseStart_3757143 baseEnd_3757143 := by
    simpa [prefixWord, tailWord_3757143, baseEnd_3757143] using wordTrace_append hprefix tailTrace_3757143
  have hstable : (prefixWord ++ tailWord_3757143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757143).length < 2 ^ (prefixWord ++ tailWord_3757143).sum := by decide
  have hdescent : baseEnd_3757143 < baseStart_3757143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757226 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3757226 : Nat := 118140960795 + 3757226 * 2 ^ 59
def prefixEnd_3757226 : Nat := 4983230072969 + 3 ^ 40 * 3757226 * 2
def baseEnd_3757226 : Nat := 1286175243713214713130559

theorem tailTrace_3757226 : CollatzResearch.WordTrace tailWord_3757226 prefixEnd_3757226 1286175243713214713130559 := by
  unfold tailWord_3757226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34259322571554839989726883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91358193524146239972605021 34259322571554839989726883)
  ·
    refine ⟨51388983857332259984590325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34259322571554839989726883 51388983857332259984590325)
    ·
      refine ⟨4817717236624899373555343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51388983857332259984590325 4817717236624899373555343)
      ·
        refine ⟨7226575854937349060333015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4817717236624899373555343 7226575854937349060333015)
        ·
          refine ⟨10839863782406023590499523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226575854937349060333015 10839863782406023590499523)
          ·
            refine ⟨16259795673609035385749285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10839863782406023590499523 16259795673609035385749285)
            ·
              refine ⟨3048711688801694134827991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16259795673609035385749285 3048711688801694134827991)
              ·
                refine ⟨4573067533202541202241987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048711688801694134827991 4573067533202541202241987)
                ·
                  refine ⟨6859601299803811803362981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573067533202541202241987 6859601299803811803362981)
                  ·
                    refine ⟨1286175243713214713130559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6859601299803811803362981 1286175243713214713130559)
                    ·
                      rfl

theorem cell22_3757226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3757226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757226 prefixEnd_3757226 := by exact prefixLift 3757226
  have htrace : WordTrace (prefixWord ++ tailWord_3757226) baseStart_3757226 baseEnd_3757226 := by
    simpa [prefixWord, tailWord_3757226, baseEnd_3757226] using wordTrace_append hprefix tailTrace_3757226
  have hstable : (prefixWord ++ tailWord_3757226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757226).length < 2 ^ (prefixWord ++ tailWord_3757226).sum := by decide
  have hdescent : baseEnd_3757226 < baseStart_3757226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757269 : List Nat := [1, 3, 2, 4, 1, 3, 2, 6]
def baseStart_3757269 : Nat := 118140960795 + 3757269 * 2 ^ 59
def prefixEnd_3757269 : Nat := 4983230072969 + 3 ^ 40 * 3757269 * 2
def baseEnd_3757269 : Nat := 142909995943552992700603

theorem tailTrace_3757269 : CollatzResearch.WordTrace tailWord_3757269 prefixEnd_3757269 142909995943552992700603 := by
  unfold tailWord_3757269
  simp only [CollatzResearch.WordTrace]
  refine ⟨137038858625063578302722861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91359239083375718868481907 137038858625063578302722861)
  ·
    refine ⟨51389571984398841863521073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137038858625063578302722861 51389571984398841863521073)
    ·
      refine ⟨38542178988299131397640805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51389571984398841863521073 38542178988299131397640805)
      ·
        refine ⟨7226658560306087137057651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38542178988299131397640805 7226658560306087137057651)
        ·
          refine ⟨10839987840459130705586477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7226658560306087137057651 10839987840459130705586477)
          ·
            refine ⟨4064995440172174014594929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10839987840459130705586477 4064995440172174014594929)
            ·
              refine ⟨3048746580129130510946197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064995440172174014594929 3048746580129130510946197)
              ·
                refine ⟨142909995943552992700603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3048746580129130510946197 142909995943552992700603)
                ·
                  rfl

theorem cell22_3757269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 6].length) (baseStart_3757269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757269 prefixEnd_3757269 := by exact prefixLift 3757269
  have htrace : WordTrace (prefixWord ++ tailWord_3757269) baseStart_3757269 baseEnd_3757269 := by
    simpa [prefixWord, tailWord_3757269, baseEnd_3757269] using wordTrace_append hprefix tailTrace_3757269
  have hstable : (prefixWord ++ tailWord_3757269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757269).length < 2 ^ (prefixWord ++ tailWord_3757269).sum := by decide
  have hdescent : baseEnd_3757269 < baseStart_3757269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757280 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_3757280 : Nat := 118140960795 + 3757280 * 2 ^ 59
def prefixEnd_3757280 : Nat := 4983230072969 + 3 ^ 40 * 3757280 * 2
def baseEnd_3757280 : Nat := 428731243005592190760131

theorem tailTrace_3757280 : CollatzResearch.WordTrace tailWord_3757280 prefixEnd_3757280 428731243005592190760131 := by
  unfold tailWord_3757280
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519629914011863590686647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91359506552015818120915529 68519629914011863590686647)
  ·
    refine ⟨102779444871017795386029971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68519629914011863590686647 102779444871017795386029971)
    ·
      refine ⟨154169167306526693079044957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102779444871017795386029971 154169167306526693079044957)
      ·
        refine ⟨57813437739947509904641859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154169167306526693079044957 57813437739947509904641859)
        ·
          refine ⟨86720156609921264856962789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57813437739947509904641859 86720156609921264856962789)
          ·
            refine ⟨16260029364360237160680523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86720156609921264856962789 16260029364360237160680523)
            ·
              refine ⟨24390044046540355741020785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260029364360237160680523 24390044046540355741020785)
              ·
                refine ⟨18292533034905266805765589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24390044046540355741020785 18292533034905266805765589)
                ·
                  refine ⟨428731243005592190760131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18292533034905266805765589 428731243005592190760131)
                  ·
                    rfl

theorem cell22_3757280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_3757280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757280 prefixEnd_3757280 := by exact prefixLift 3757280
  have htrace : WordTrace (prefixWord ++ tailWord_3757280) baseStart_3757280 baseEnd_3757280 := by
    simpa [prefixWord, tailWord_3757280, baseEnd_3757280] using wordTrace_append hprefix tailTrace_3757280
  have hstable : (prefixWord ++ tailWord_3757280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757280).length < 2 ^ (prefixWord ++ tailWord_3757280).sum := by decide
  have hdescent : baseEnd_3757280 < baseStart_3757280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757374 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3757374 : Nat := 118140960795 + 3757374 * 2 ^ 59
def prefixEnd_3757374 : Nat := 4983230072969 + 3 ^ 40 * 3757374 * 2
def baseEnd_3757374 : Nat := 1286225907137791660430105

theorem tailTrace_3757374 : CollatzResearch.WordTrace tailWord_3757374 prefixEnd_3757374 1286225907137791660430105 := by
  unfold tailWord_3757374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130336036210397654411897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91361792193122120823530117 17130336036210397654411897)
  ·
    refine ⟨12847752027157798240808923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17130336036210397654411897 12847752027157798240808923)
    ·
      refine ⟨19271628040736697361213385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12847752027157798240808923 19271628040736697361213385)
      ·
        refine ⟨14453721030552523020910039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19271628040736697361213385 14453721030552523020910039)
        ·
          refine ⟨21680581545828784531365059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14453721030552523020910039 21680581545828784531365059)
          ·
            refine ⟨32520872318743176797047589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21680581545828784531365059 32520872318743176797047589)
            ·
              refine ⟨6097663559764345649446423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32520872318743176797047589 6097663559764345649446423)
              ·
                refine ⟨9146495339646518474169635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097663559764345649446423 9146495339646518474169635)
                ·
                  refine ⟨13719743009469777711254453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9146495339646518474169635 13719743009469777711254453)
                  ·
                    refine ⟨1286225907137791660430105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13719743009469777711254453 1286225907137791660430105)
                    ·
                      rfl

theorem cell22_3757374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3757374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757374 prefixEnd_3757374 := by exact prefixLift 3757374
  have htrace : WordTrace (prefixWord ++ tailWord_3757374) baseStart_3757374 baseEnd_3757374 := by
    simpa [prefixWord, tailWord_3757374, baseEnd_3757374] using wordTrace_append hprefix tailTrace_3757374
  have hstable : (prefixWord ++ tailWord_3757374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757374).length < 2 ^ (prefixWord ++ tailWord_3757374).sum := by decide
  have hdescent : baseEnd_3757374 < baseStart_3757374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757470 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_3757470 : Nat := 118140960795 + 3757470 * 2 ^ 59
def prefixEnd_3757470 : Nat := 4983230072969 + 3 ^ 40 * 3757470 * 2
def baseEnd_3757470 : Nat := 1286258769899679410029811

theorem tailTrace_3757470 : CollatzResearch.WordTrace tailWord_3757470 prefixEnd_3757470 1286258769899679410029811 := by
  unfold tailWord_3757470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130773712166923703848733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91364126464890259753859909 17130773712166923703848733)
  ·
    refine ⟨6424040142062596388943275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17130773712166923703848733 6424040142062596388943275)
    ·
      refine ⟨9636060213093894583414913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424040142062596388943275 9636060213093894583414913)
      ·
        refine ⟨7227045159820420937561185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9636060213093894583414913 7227045159820420937561185)
        ·
          refine ⟨5420283869865315703170889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7227045159820420937561185 5420283869865315703170889)
          ·
            refine ⟨4065212902398986777378167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420283869865315703170889 4065212902398986777378167)
            ·
              refine ⟨6097819353598480166067251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065212902398986777378167 6097819353598480166067251)
              ·
                refine ⟨9146729030397720249100877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097819353598480166067251 9146729030397720249100877)
                ·
                  refine ⟨3430023386399145093412829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9146729030397720249100877 3430023386399145093412829)
                  ·
                    refine ⟨1286258769899679410029811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430023386399145093412829 1286258769899679410029811)
                    ·
                      rfl

theorem cell22_3757470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_3757470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757470 prefixEnd_3757470 := by exact prefixLift 3757470
  have htrace : WordTrace (prefixWord ++ tailWord_3757470) baseStart_3757470 baseEnd_3757470 := by
    simpa [prefixWord, tailWord_3757470, baseEnd_3757470] using wordTrace_append hprefix tailTrace_3757470
  have hstable : (prefixWord ++ tailWord_3757470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757470).length < 2 ^ (prefixWord ++ tailWord_3757470).sum := by decide
  have hdescent : baseEnd_3757470 < baseStart_3757470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757477 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 6]
def baseStart_3757477 : Nat := 118140960795 + 3757477 * 2 ^ 59
def prefixEnd_3757477 : Nat := 4983230072969 + 3 ^ 40 * 3757477 * 2
def baseEnd_3757477 : Nat := 428753722047577908368263

theorem tailTrace_3757477 : CollatzResearch.WordTrace tailWord_3757477 prefixEnd_3757477 428753722047577908368263 := by
  unfold tailWord_3757477
  simp only [CollatzResearch.WordTrace]
  refine ⟨137046445008310029826294685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91364296672206686550863123 137046445008310029826294685)
  ·
    refine ⟨51392416878116261184860507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137046445008310029826294685 51392416878116261184860507)
    ·
      refine ⟨77088625317174391777290761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51392416878116261184860507 77088625317174391777290761)
      ·
        refine ⟨57816468987880793832968071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77088625317174391777290761 57816468987880793832968071)
        ·
          refine ⟨86724703481821190749452107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57816468987880793832968071 86724703481821190749452107)
          ·
            refine ⟨130087055222731786124178161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86724703481821190749452107 130087055222731786124178161)
            ·
              refine ⟨97565291417048839593133621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130087055222731786124178161 97565291417048839593133621)
              ·
                refine ⟨9146746070348328711856277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97565291417048839593133621 9146746070348328711856277)
                ·
                  refine ⟨428753722047577908368263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9146746070348328711856277 428753722047577908368263)
                  ·
                    rfl

theorem cell22_3757477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_3757477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757477 prefixEnd_3757477 := by exact prefixLift 3757477
  have htrace : WordTrace (prefixWord ++ tailWord_3757477) baseStart_3757477 baseEnd_3757477 := by
    simpa [prefixWord, tailWord_3757477, baseEnd_3757477] using wordTrace_append hprefix tailTrace_3757477
  have hstable : (prefixWord ++ tailWord_3757477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757477).length < 2 ^ (prefixWord ++ tailWord_3757477).sum := by decide
  have hdescent : baseEnd_3757477 < baseStart_3757477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757479 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_3757479 : Nat := 118140960795 + 3757479 * 2 ^ 59
def prefixEnd_3757479 : Nat := 4983230072969 + 3 ^ 40 * 3757479 * 2
def baseEnd_3757479 : Nat := 1286261850783606386554783

theorem tailTrace_3757479 : CollatzResearch.WordTrace tailWord_3757479 prefixEnd_3757479 1286261850783606386554783 := by
  unfold tailWord_3757479
  simp only [CollatzResearch.WordTrace]
  refine ⟨137046517954302784167867491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91364345302868522778578327 137046517954302784167867491)
  ·
    refine ⟨205569776931454176251801237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137046517954302784167867491 205569776931454176251801237)
    ·
      refine ⟨9636083293661914511803183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 205569776931454176251801237 9636083293661914511803183)
      ·
        refine ⟨14454124940492871767704775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9636083293661914511803183 14454124940492871767704775)
        ·
          refine ⟨21681187410739307651557163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454124940492871767704775 21681187410739307651557163)
          ·
            refine ⟨32521781116108961477335745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681187410739307651557163 32521781116108961477335745)
            ·
              refine ⟨24391335837081721108001809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32521781116108961477335745 24391335837081721108001809)
              ·
                refine ⟨18293501877811290831001357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24391335837081721108001809 18293501877811290831001357)
                ·
                  refine ⟨6860063204179234061625509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18293501877811290831001357 6860063204179234061625509)
                  ·
                    refine ⟨1286261850783606386554783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860063204179234061625509 1286261850783606386554783)
                    ·
                      rfl

theorem cell22_3757479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_3757479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757479 prefixEnd_3757479 := by exact prefixLift 3757479
  have htrace : WordTrace (prefixWord ++ tailWord_3757479) baseStart_3757479 baseEnd_3757479 := by
    simpa [prefixWord, tailWord_3757479, baseEnd_3757479] using wordTrace_append hprefix tailTrace_3757479
  have hstable : (prefixWord ++ tailWord_3757479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757479).length < 2 ^ (prefixWord ++ tailWord_3757479).sum := by decide
  have hdescent : baseEnd_3757479 < baseStart_3757479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757507 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_3757507 : Nat := 118140960795 + 3757507 * 2 ^ 59
def prefixEnd_3757507 : Nat := 4983230072969 + 3 ^ 40 * 3757507 * 2
def baseEnd_3757507 : Nat := 1286271435755823646854697

theorem tailTrace_3757507 : CollatzResearch.WordTrace tailWord_3757507 prefixEnd_3757507 1286271435755823646854697 := by
  unfold tailWord_3757507
  simp only [CollatzResearch.WordTrace]
  refine ⟨137047539198201344949886775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91365026132134229966591183 137047539198201344949886775)
  ·
    refine ⟨205571308797302017424830163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137047539198201344949886775 205571308797302017424830163)
    ·
      refine ⟨308356963195953026137245245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205571308797302017424830163 308356963195953026137245245)
      ·
        refine ⟨115633861198482384801466967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308356963195953026137245245 115633861198482384801466967)
        ·
          refine ⟨173450791797723577202200451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115633861198482384801466967 173450791797723577202200451)
          ·
            refine ⟨260176187696585365803300677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173450791797723577202200451 260176187696585365803300677)
            ·
              refine ⟨48783035193109756088118877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260176187696585365803300677 48783035193109756088118877)
              ·
                refine ⟨18293638197416158533044579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48783035193109756088118877 18293638197416158533044579)
                ·
                  refine ⟨27440457296124237799566869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18293638197416158533044579 27440457296124237799566869)
                  ·
                    refine ⟨1286271435755823646854697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27440457296124237799566869 1286271435755823646854697)
                    ·
                      rfl

theorem cell22_3757507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_3757507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757507 prefixEnd_3757507 := by exact prefixLift 3757507
  have htrace : WordTrace (prefixWord ++ tailWord_3757507) baseStart_3757507 baseEnd_3757507 := by
    simpa [prefixWord, tailWord_3757507, baseEnd_3757507] using wordTrace_append hprefix tailTrace_3757507
  have hstable : (prefixWord ++ tailWord_3757507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757507).length < 2 ^ (prefixWord ++ tailWord_3757507).sum := by decide
  have hdescent : baseEnd_3757507 < baseStart_3757507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757522 : List Nat := [3, 2, 2, 15]
def baseStart_3757522 : Nat := 118140960795 + 3757522 * 2 ^ 59
def prefixEnd_3757522 : Nat := 4983230072969 + 3 ^ 40 * 3757522 * 2
def baseEnd_3757522 : Nat := 1764439740140423330219

theorem tailTrace_3757522 : CollatzResearch.WordTrace tailWord_3757522 prefixEnd_3757522 1764439740140423330219 := by
  unfold tailWord_3757522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34262021573286750627920705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91365390862098001674455213 34262021573286750627920705)
  ·
    refine ⟨25696516179965062970940529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34262021573286750627920705 25696516179965062970940529)
    ·
      refine ⟨19272387134973797228205397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25696516179965062970940529 19272387134973797228205397)
      ·
        refine ⟨1764439740140423330219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 19272387134973797228205397 1764439740140423330219)
        ·
          rfl

theorem cell22_3757522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 15].length) (baseStart_3757522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757522 prefixEnd_3757522 := by exact prefixLift 3757522
  have htrace : WordTrace (prefixWord ++ tailWord_3757522) baseStart_3757522 baseEnd_3757522 := by
    simpa [prefixWord, tailWord_3757522, baseEnd_3757522] using wordTrace_append hprefix tailTrace_3757522
  have hstable : (prefixWord ++ tailWord_3757522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757522).length < 2 ^ (prefixWord ++ tailWord_3757522).sum := by decide
  have hdescent : baseEnd_3757522 < baseStart_3757522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757539 : List Nat := [1, 1, 1, 6, 2, 1, 3, 7]
def baseStart_3757539 : Nat := 118140960795 + 3757539 * 2 ^ 59
def prefixEnd_3757539 : Nat := 4983230072969 + 3 ^ 40 * 3757539 * 2
def baseEnd_3757539 : Nat := 142920265556642914450511

theorem tailTrace_3757539 : CollatzResearch.WordTrace tailWord_3757539 prefixEnd_3757539 142920265556642914450511 := by
  unfold tailWord_3757539
  simp only [CollatzResearch.WordTrace]
  refine ⟨137048706334085414415051671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91365804222723609610034447 137048706334085414415051671)
  ·
    refine ⟨205573059501128121622577507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137048706334085414415051671 205573059501128121622577507)
    ·
      refine ⟨308359589251692182433866261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205573059501128121622577507 308359589251692182433866261)
      ·
        refine ⟨14454355746173071051587481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308359589251692182433866261 14454355746173071051587481)
        ·
          refine ⟨10840766809629803288690611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14454355746173071051587481 10840766809629803288690611)
          ·
            refine ⟨16261150214444704933035917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840766809629803288690611 16261150214444704933035917)
            ·
              refine ⟨6097931330416764349888469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16261150214444704933035917 6097931330416764349888469)
              ·
                refine ⟨142920265556642914450511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6097931330416764349888469 142920265556642914450511)
                ·
                  rfl

theorem cell22_3757539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 7].length) (baseStart_3757539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757539 prefixEnd_3757539 := by exact prefixLift 3757539
  have htrace : WordTrace (prefixWord ++ tailWord_3757539) baseStart_3757539 baseEnd_3757539 := by
    simpa [prefixWord, tailWord_3757539, baseEnd_3757539] using wordTrace_append hprefix tailTrace_3757539
  have hstable : (prefixWord ++ tailWord_3757539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757539).length < 2 ^ (prefixWord ++ tailWord_3757539).sum := by decide
  have hdescent : baseEnd_3757539 < baseStart_3757539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757558 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3757558 : Nat := 118140960795 + 3757558 * 2 ^ 59
def prefixEnd_3757558 : Nat := 4983230072969 + 3 ^ 40 * 3757558 * 2
def baseEnd_3757558 : Nat := 1286288894098076513829541

theorem tailTrace_3757558 : CollatzResearch.WordTrace tailWord_3757558 prefixEnd_3757558 1286288894098076513829541 := by
  unfold tailWord_3757558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565587457563536291249583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91366266214011053773328885 8565587457563536291249583)
  ·
    refine ⟨12848381186345304436874375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565587457563536291249583 12848381186345304436874375)
    ·
      refine ⟨19272571779517956655311563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848381186345304436874375 19272571779517956655311563)
      ·
        refine ⟨28908857669276934982967345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272571779517956655311563 28908857669276934982967345)
        ·
          refine ⟨21681643251957701237225509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28908857669276934982967345 21681643251957701237225509)
          ·
            refine ⟨4065308109742068981979783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21681643251957701237225509 4065308109742068981979783)
            ·
              refine ⟨6097962164613103472969675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065308109742068981979783 6097962164613103472969675)
              ·
                refine ⟨9146943246919655209454513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097962164613103472969675 9146943246919655209454513)
                ·
                  refine ⟨6860207435189741407090885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9146943246919655209454513 6860207435189741407090885)
                  ·
                    refine ⟨1286288894098076513829541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860207435189741407090885 1286288894098076513829541)
                    ·
                      rfl

theorem cell22_3757558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3757558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757558 prefixEnd_3757558 := by exact prefixLift 3757558
  have htrace : WordTrace (prefixWord ++ tailWord_3757558) baseStart_3757558 baseEnd_3757558 := by
    simpa [prefixWord, tailWord_3757558, baseEnd_3757558] using wordTrace_append hprefix tailTrace_3757558
  have hstable : (prefixWord ++ tailWord_3757558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757558).length < 2 ^ (prefixWord ++ tailWord_3757558).sum := by decide
  have hdescent : baseEnd_3757558 < baseStart_3757558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757599 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_3757599 : Nat := 118140960795 + 3757599 * 2 ^ 59
def prefixEnd_3757599 : Nat := 4983230072969 + 3 ^ 40 * 3757599 * 2
def baseEnd_3757599 : Nat := 1286302929235966073554415

theorem tailTrace_3757599 : CollatzResearch.WordTrace tailWord_3757599 prefixEnd_3757599 1286302929235966073554415 := by
  unfold tailWord_3757599
  simp only [CollatzResearch.WordTrace]
  refine ⟨137050894713868044662235851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91367263142578696441490567 137050894713868044662235851)
  ·
    refine ⟨205576342070802066993353777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137050894713868044662235851 205576342070802066993353777)
    ·
      refine ⟨154182256553101550245015333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205576342070802066993353777 154182256553101550245015333)
      ·
        refine ⟨28909173103706540670940375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154182256553101550245015333 28909173103706540670940375)
        ·
          refine ⟨43363759655559811006410563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28909173103706540670940375 43363759655559811006410563)
          ·
            refine ⟨65045639483339716509615845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43363759655559811006410563 65045639483339716509615845)
            ·
              refine ⟨12196057403126196845552971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65045639483339716509615845 12196057403126196845552971)
              ·
                refine ⟨18294086104689295268329457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12196057403126196845552971 18294086104689295268329457)
                ·
                  refine ⟨13720564578516971451247093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18294086104689295268329457 13720564578516971451247093)
                  ·
                    refine ⟨1286302929235966073554415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13720564578516971451247093 1286302929235966073554415)
                    ·
                      rfl

theorem cell22_3757599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_3757599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757599 prefixEnd_3757599 := by exact prefixLift 3757599
  have htrace : WordTrace (prefixWord ++ tailWord_3757599) baseStart_3757599 baseEnd_3757599 := by
    simpa [prefixWord, tailWord_3757599, baseEnd_3757599] using wordTrace_append hprefix tailTrace_3757599
  have hstable : (prefixWord ++ tailWord_3757599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757599).length < 2 ^ (prefixWord ++ tailWord_3757599).sum := by decide
  have hdescent : baseEnd_3757599 < baseStart_3757599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757631 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 1, 4]
def baseStart_3757631 : Nat := 118140960795 + 3757631 * 2 ^ 59
def prefixEnd_3757631 : Nat := 4983230072969 + 3 ^ 40 * 3757631 * 2
def baseEnd_3757631 : Nat := 1286313883489928656754317

theorem tailTrace_3757631 : CollatzResearch.WordTrace tailWord_3757631 prefixEnd_3757631 1286313883489928656754317 := by
  unfold tailWord_3757631
  simp only [CollatzResearch.WordTrace]
  refine ⟨137052061849752114127400747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91368041233168076084933831 137052061849752114127400747)
  ·
    refine ⟨205578092774628171191101121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137052061849752114127400747 205578092774628171191101121)
    ·
      refine ⟨154183569580971128393325841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205578092774628171191101121 154183569580971128393325841)
      ·
        refine ⟨115637677185728346294994381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154183569580971128393325841 115637677185728346294994381)
        ·
          refine ⟨43364128944648129860622893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115637677185728346294994381 43364128944648129860622893)
          ·
            refine ⟨16261548354243048697733585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43364128944648129860622893 16261548354243048697733585)
            ·
              refine ⟨12196161265682286523300189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16261548354243048697733585 12196161265682286523300189)
              ·
                refine ⟨4573560474630857446237571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12196161265682286523300189 4573560474630857446237571)
                ·
                  refine ⟨6860340711946286169356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573560474630857446237571 6860340711946286169356357)
                  ·
                    refine ⟨1286313883489928656754317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860340711946286169356357 1286313883489928656754317)
                    ·
                      rfl

theorem cell22_3757631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_3757631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757631 prefixEnd_3757631 := by exact prefixLift 3757631
  have htrace : WordTrace (prefixWord ++ tailWord_3757631) baseStart_3757631 baseEnd_3757631 := by
    simpa [prefixWord, tailWord_3757631, baseEnd_3757631] using wordTrace_append hprefix tailTrace_3757631
  have hstable : (prefixWord ++ tailWord_3757631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757631).length < 2 ^ (prefixWord ++ tailWord_3757631).sum := by decide
  have hdescent : baseEnd_3757631 < baseStart_3757631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757678 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3757678 : Nat := 118140960795 + 3757678 * 2 ^ 59
def prefixEnd_3757678 : Nat := 4983230072969 + 3 ^ 40 * 3757678 * 2
def baseEnd_3757678 : Nat := 1286329972550436200829173

theorem tailTrace_3757678 : CollatzResearch.WordTrace tailWord_3757678 prefixEnd_3757678 1286329972550436200829173 := by
  unfold tailWord_3757678
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131722010072730144295211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91369184053721227436241125 17131722010072730144295211)
  ·
    refine ⟨25697583015109095216442817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17131722010072730144295211 25697583015109095216442817)
    ·
      refine ⟨19273187261331821412332113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25697583015109095216442817 19273187261331821412332113)
      ·
        refine ⟨14454890445998866059249085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19273187261331821412332113 14454890445998866059249085)
        ·
          refine ⟨5420583917249574772218407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14454890445998866059249085 5420583917249574772218407)
          ·
            refine ⟨8130875875874362158327611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420583917249574772218407 8130875875874362158327611)
            ·
              refine ⟨12196313813811543237491417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8130875875874362158327611 12196313813811543237491417)
              ·
                refine ⟨9147235360358657428118563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12196313813811543237491417 9147235360358657428118563)
                ·
                  refine ⟨13720853040537986142177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147235360358657428118563 13720853040537986142177845)
                  ·
                    refine ⟨1286329972550436200829173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13720853040537986142177845 1286329972550436200829173)
                    ·
                      rfl

theorem cell22_3757678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3757678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757678 prefixEnd_3757678 := by exact prefixLift 3757678
  have htrace : WordTrace (prefixWord ++ tailWord_3757678) baseStart_3757678 baseEnd_3757678 := by
    simpa [prefixWord, tailWord_3757678, baseEnd_3757678] using wordTrace_append hprefix tailTrace_3757678
  have hstable : (prefixWord ++ tailWord_3757678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757678).length < 2 ^ (prefixWord ++ tailWord_3757678).sum := by decide
  have hdescent : baseEnd_3757678 < baseStart_3757678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757727 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 2, 4]
def baseStart_3757727 : Nat := 118140960795 + 3757727 * 2 ^ 59
def prefixEnd_3757727 : Nat := 4983230072969 + 3 ^ 40 * 3757727 * 2
def baseEnd_3757727 : Nat := 1286346746251816406354023

theorem tailTrace_3757727 : CollatzResearch.WordTrace tailWord_3757727 prefixEnd_3757727 1286346746251816406354023 := by
  unfold tailWord_3757727
  simp only [CollatzResearch.WordTrace]
  refine ⟨137055563257404322522895435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91370375504936215015263623 137055563257404322522895435)
  ·
    refine ⟨205583344886106483784343153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137055563257404322522895435 205583344886106483784343153)
    ·
      refine ⟨154187508664579862838257365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205583344886106483784343153 154187508664579862838257365)
      ·
        refine ⟨3613769734326090535271657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 154187508664579862838257365 3613769734326090535271657)
        ·
          refine ⟨2710327300744567901453743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613769734326090535271657 2710327300744567901453743)
          ·
            refine ⟨4065490951116851852180615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710327300744567901453743 4065490951116851852180615)
            ·
              refine ⟨6098236426675277778270923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065490951116851852180615 6098236426675277778270923)
              ·
                refine ⟨9147354640012916667406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098236426675277778270923 9147354640012916667406385)
                ·
                  refine ⟨6860515980009687500554789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9147354640012916667406385 6860515980009687500554789)
                  ·
                    refine ⟨1286346746251816406354023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860515980009687500554789 1286346746251816406354023)
                    ·
                      rfl

theorem cell22_3757727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 4].length) (baseStart_3757727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757727 prefixEnd_3757727 := by exact prefixLift 3757727
  have htrace : WordTrace (prefixWord ++ tailWord_3757727) baseStart_3757727 baseEnd_3757727 := by
    simpa [prefixWord, tailWord_3757727, baseEnd_3757727] using wordTrace_append hprefix tailTrace_3757727
  have hstable : (prefixWord ++ tailWord_3757727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757727).length < 2 ^ (prefixWord ++ tailWord_3757727).sum := by decide
  have hdescent : baseEnd_3757727 < baseStart_3757727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757751 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_3757751 : Nat := 118140960795 + 3757751 * 2 ^ 59
def prefixEnd_3757751 : Nat := 4983230072969 + 3 ^ 40 * 3757751 * 2
def baseEnd_3757751 : Nat := 1286354961942288343753949

theorem tailTrace_3757751 : CollatzResearch.WordTrace tailWord_3757751 prefixEnd_3757751 1286354961942288343753949 := by
  unfold tailWord_3757751
  simp only [CollatzResearch.WordTrace]
  refine ⟨137056438609317374621769107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91370959072878249747846071 137056438609317374621769107)
  ·
    refine ⟨205584657913976061932653661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137056438609317374621769107 205584657913976061932653661)
    ·
      refine ⟨77094246717741023224745123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205584657913976061932653661 77094246717741023224745123)
      ·
        refine ⟨115641370076611534837117685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77094246717741023224745123 115641370076611534837117685)
        ·
          refine ⟨10841378444682331390979783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115641370076611534837117685 10841378444682331390979783)
          ·
            refine ⟨16262067667023497086469675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10841378444682331390979783 16262067667023497086469675)
            ·
              refine ⟨24393101500535245629704513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16262067667023497086469675 24393101500535245629704513)
              ·
                refine ⟨18294826125401434222278385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24393101500535245629704513 18294826125401434222278385)
                ·
                  refine ⟨13721119594051075666708789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18294826125401434222278385 13721119594051075666708789)
                  ·
                    refine ⟨1286354961942288343753949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13721119594051075666708789 1286354961942288343753949)
                    ·
                      rfl

theorem cell22_3757751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_3757751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757751 prefixEnd_3757751 := by exact prefixLift 3757751
  have htrace : WordTrace (prefixWord ++ tailWord_3757751) baseStart_3757751 baseEnd_3757751 := by
    simpa [prefixWord, tailWord_3757751, baseEnd_3757751] using wordTrace_append hprefix tailTrace_3757751
  have hstable : (prefixWord ++ tailWord_3757751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757751).length < 2 ^ (prefixWord ++ tailWord_3757751).sum := by decide
  have hdescent : baseEnd_3757751 < baseStart_3757751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757770 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_3757770 : Nat := 118140960795 + 3757770 * 2 ^ 59
def prefixEnd_3757770 : Nat := 4983230072969 + 3 ^ 40 * 3757770 * 2
def baseEnd_3757770 : Nat := 428787155343526209176297

theorem tailTrace_3757770 : CollatzResearch.WordTrace tailWord_3757770 prefixEnd_3757770 428787155343526209176297 := by
  unfold tailWord_3757770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264282899062135216677691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91371421064165693911140509 34264282899062135216677691)
  ·
    refine ⟨51396424348593202825016537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34264282899062135216677691 51396424348593202825016537)
    ·
      refine ⟨38547318261444902118762403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51396424348593202825016537 38547318261444902118762403)
      ·
        refine ⟨57820977392167353178143605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38547318261444902118762403 57820977392167353178143605)
        ·
          refine ⟨5420716630515689360450963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57820977392167353178143605 5420716630515689360450963)
          ·
            refine ⟨8131074945773534040676445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420716630515689360450963 8131074945773534040676445)
            ·
              refine ⟨3049153104665075265253667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8131074945773534040676445 3049153104665075265253667)
              ·
                refine ⟨4573729656997612897880501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049153104665075265253667 4573729656997612897880501)
                ·
                  refine ⟨428787155343526209176297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4573729656997612897880501 428787155343526209176297)
                  ·
                    rfl

theorem cell22_3757770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_3757770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757770 prefixEnd_3757770 := by exact prefixLift 3757770
  have htrace : WordTrace (prefixWord ++ tailWord_3757770) baseStart_3757770 baseEnd_3757770 := by
    simpa [prefixWord, tailWord_3757770, baseEnd_3757770] using wordTrace_append hprefix tailTrace_3757770
  have hstable : (prefixWord ++ tailWord_3757770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757770).length < 2 ^ (prefixWord ++ tailWord_3757770).sum := by decide
  have hdescent : baseEnd_3757770 < baseStart_3757770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757783 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 1, 4]
def baseStart_3757783 : Nat := 118140960795 + 3757783 * 2 ^ 59
def prefixEnd_3757783 : Nat := 4983230072969 + 3 ^ 40 * 3757783 * 2
def baseEnd_3757783 : Nat := 1286365916196250926953851

theorem tailTrace_3757783 : CollatzResearch.WordTrace tailWord_3757783 prefixEnd_3757783 1286365916196250926953851 := by
  unfold tailWord_3757783
  simp only [CollatzResearch.WordTrace]
  refine ⟨137057605745201444086934003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91371737163467629391289335 137057605745201444086934003)
  ·
    refine ⟨205586408617802166130401005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137057605745201444086934003 205586408617802166130401005)
    ·
      refine ⟨77094903231675812298900377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205586408617802166130401005 77094903231675812298900377)
      ·
        refine ⟨57821177423756859224175283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77094903231675812298900377 57821177423756859224175283)
        ·
          refine ⟨86731766135635288836262925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57821177423756859224175283 86731766135635288836262925)
          ·
            refine ⟨32524412300863233313598597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86731766135635288836262925 32524412300863233313598597)
            ·
              refine ⟨6098327306411856246299737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32524412300863233313598597 6098327306411856246299737)
              ·
                refine ⟨4573745479808892184724803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098327306411856246299737 4573745479808892184724803)
                ·
                  refine ⟨6860618219713338277087205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573745479808892184724803 6860618219713338277087205)
                  ·
                    refine ⟨1286365916196250926953851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860618219713338277087205 1286365916196250926953851)
                    ·
                      rfl

theorem cell22_3757783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_3757783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757783 prefixEnd_3757783 := by exact prefixLift 3757783
  have htrace : WordTrace (prefixWord ++ tailWord_3757783) baseStart_3757783 baseEnd_3757783 := by
    simpa [prefixWord, tailWord_3757783, baseEnd_3757783] using wordTrace_append hprefix tailTrace_3757783
  have hstable : (prefixWord ++ tailWord_3757783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757783).length < 2 ^ (prefixWord ++ tailWord_3757783).sum := by decide
  have hdescent : baseEnd_3757783 < baseStart_3757783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757796 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_3757796 : Nat := 118140960795 + 3757796 * 2 ^ 59
def prefixEnd_3757796 : Nat := 4983230072969 + 3 ^ 40 * 3757796 * 2
def baseEnd_3757796 : Nat := 1286370366361923226378811

theorem tailTrace_3757796 : CollatzResearch.WordTrace tailWord_3757796 prefixEnd_3757796 1286370366361923226378811 := by
  unfold tailWord_3757796
  simp only [CollatzResearch.WordTrace]
  refine ⟨68529039947077173653578621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91372053262769564871438161 68529039947077173653578621)
  ·
    refine ⟨25698389980153940120091983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68529039947077173653578621 25698389980153940120091983)
    ·
      refine ⟨38547584970230910180137975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25698389980153940120091983 38547584970230910180137975)
      ·
        refine ⟨57821377455346365270206963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38547584970230910180137975 57821377455346365270206963)
        ·
          refine ⟨86732066183019547905310445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57821377455346365270206963 86732066183019547905310445)
          ·
            refine ⟨32524524818632330464491417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86732066183019547905310445 32524524818632330464491417)
            ·
              refine ⟨24393393613974247848368563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32524524818632330464491417 24393393613974247848368563)
              ·
                refine ⟨36590090420961371772552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24393393613974247848368563 36590090420961371772552845)
                ·
                  refine ⟨13721283907860514414707317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36590090420961371772552845 13721283907860514414707317)
                  ·
                    refine ⟨1286370366361923226378811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13721283907860514414707317 1286370366361923226378811)
                    ·
                      rfl

theorem cell22_3757796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_3757796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757796 prefixEnd_3757796 := by exact prefixLift 3757796
  have htrace : WordTrace (prefixWord ++ tailWord_3757796) baseStart_3757796 baseEnd_3757796 := by
    simpa [prefixWord, tailWord_3757796, baseEnd_3757796] using wordTrace_append hprefix tailTrace_3757796
  have hstable : (prefixWord ++ tailWord_3757796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757796).length < 2 ^ (prefixWord ++ tailWord_3757796).sum := by decide
  have hdescent : baseEnd_3757796 < baseStart_3757796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757811 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_3757811 : Nat := 118140960795 + 3757811 * 2 ^ 59
def prefixEnd_3757811 : Nat := 4983230072969 + 3 ^ 40 * 3757811 * 2
def baseEnd_3757811 : Nat := 1286375501168468187253765

theorem tailTrace_3757811 : CollatzResearch.WordTrace tailWord_3757811 prefixEnd_3757811 1286375501168468187253765 := by
  unfold tailWord_3757811
  simp only [CollatzResearch.WordTrace]
  refine ⟨137058626989100004868953287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91372417992733336579302191 137058626989100004868953287)
  ·
    refine ⟨205587940483650007303429931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137058626989100004868953287 205587940483650007303429931)
    ·
      refine ⟨308381910725475010955144897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205587940483650007303429931 308381910725475010955144897)
      ·
        refine ⟨231286433044106258216358673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308381910725475010955144897 231286433044106258216358673)
        ·
          refine ⟨173464824783079693662269005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231286433044106258216358673 173464824783079693662269005)
          ·
            refine ⟨65049309293654885123350877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173464824783079693662269005 65049309293654885123350877)
            ·
              refine ⟨24393490985120581921256579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65049309293654885123350877 24393490985120581921256579)
              ·
                refine ⟨36590236477680872881884869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24393490985120581921256579 36590236477680872881884869)
                ·
                  refine ⟨6860669339565163665353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36590236477680872881884869 6860669339565163665353413)
                  ·
                    refine ⟨1286375501168468187253765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860669339565163665353413 1286375501168468187253765)
                    ·
                      rfl

theorem cell22_3757811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_3757811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757811 prefixEnd_3757811 := by exact prefixLift 3757811
  have htrace : WordTrace (prefixWord ++ tailWord_3757811) baseStart_3757811 baseEnd_3757811 := by
    simpa [prefixWord, tailWord_3757811, baseEnd_3757811] using wordTrace_append hprefix tailTrace_3757811
  have hstable : (prefixWord ++ tailWord_3757811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757811).length < 2 ^ (prefixWord ++ tailWord_3757811).sum := by decide
  have hdescent : baseEnd_3757811 < baseStart_3757811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757922 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3757922 : Nat := 118140960795 + 3757922 * 2 ^ 59
def prefixEnd_3757922 : Nat := 4983230072969 + 3 ^ 40 * 3757922 * 2
def baseEnd_3757922 : Nat := 428804499578966965909475

theorem tailTrace_3757922 : CollatzResearch.WordTrace tailWord_3757922 prefixEnd_3757922 428804499578966965909475 := by
  unfold tailWord_3757922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34265668872924467706561005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91375116994465247217496013 34265668872924467706561005)
  ·
    refine ⟨12849625827346675389960377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34265668872924467706561005 12849625827346675389960377)
    ·
      refine ⟨9637219370510006542470283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12849625827346675389960377 9637219370510006542470283)
      ·
        refine ⟨14455829055765009813705425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9637219370510006542470283 14455829055765009813705425)
        ·
          refine ⟨10841871791823757360279069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14455829055765009813705425 10841871791823757360279069)
          ·
            refine ⟨4065701921933909010104651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10841871791823757360279069 4065701921933909010104651)
            ·
              refine ⟨6098552882900863515156977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065701921933909010104651 6098552882900863515156977)
              ·
                refine ⟨4573914662175647636367733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098552882900863515156977 4573914662175647636367733)
                ·
                  refine ⟨428804499578966965909475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4573914662175647636367733 428804499578966965909475)
                  ·
                    rfl

theorem cell22_3757922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3757922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757922 prefixEnd_3757922 := by exact prefixLift 3757922
  have htrace : WordTrace (prefixWord ++ tailWord_3757922) baseStart_3757922 baseEnd_3757922 := by
    simpa [prefixWord, tailWord_3757922, baseEnd_3757922] using wordTrace_append hprefix tailTrace_3757922
  have hstable : (prefixWord ++ tailWord_3757922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757922).length < 2 ^ (prefixWord ++ tailWord_3757922).sum := by decide
  have hdescent : baseEnd_3757922 < baseStart_3757922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757933 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 6]
def baseStart_3757933 : Nat := 118140960795 + 3757933 * 2 ^ 59
def prefixEnd_3757933 : Nat := 4983230072969 + 3 ^ 40 * 3757933 * 2
def baseEnd_3757933 : Nat := 428805754753900178567797

theorem tailTrace_3757933 : CollatzResearch.WordTrace tailWord_3757933 prefixEnd_3757933 428805754753900178567797 := by
  unfold tailWord_3757933
  simp only [CollatzResearch.WordTrace]
  refine ⟨137063076694658019704894453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91375384463105346469929635 137063076694658019704894453)
  ·
    refine ⟨12849663440124189347333855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137063076694658019704894453 12849663440124189347333855)
    ·
      refine ⟨19274495160186284021000783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12849663440124189347333855 19274495160186284021000783)
      ·
        refine ⟨28911742740279426031501175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19274495160186284021000783 28911742740279426031501175)
        ·
          refine ⟨43367614110419139047251763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28911742740279426031501175 43367614110419139047251763)
          ·
            refine ⟨65051421165628708570877645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43367614110419139047251763 65051421165628708570877645)
            ·
              refine ⟨24394282937110765714079117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65051421165628708570877645 24394282937110765714079117)
              ·
                refine ⟨9147856101416537142779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24394282937110765714079117 9147856101416537142779669)
                ·
                  refine ⟨428805754753900178567797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9147856101416537142779669 428805754753900178567797)
                  ·
                    rfl

theorem cell22_3757933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_3757933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757933 prefixEnd_3757933 := by exact prefixLift 3757933
  have htrace : WordTrace (prefixWord ++ tailWord_3757933) baseStart_3757933 baseEnd_3757933 := by
    simpa [prefixWord, tailWord_3757933, baseEnd_3757933] using wordTrace_append hprefix tailTrace_3757933
  have hstable : (prefixWord ++ tailWord_3757933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757933).length < 2 ^ (prefixWord ++ tailWord_3757933).sum := by decide
  have hdescent : baseEnd_3757933 < baseStart_3757933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757963 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_3757963 : Nat := 118140960795 + 3757963 * 2 ^ 59
def prefixEnd_3757963 : Nat := 4983230072969 + 3 ^ 40 * 3757963 * 2
def baseEnd_3757963 : Nat := 1286427533874790457453299

theorem tailTrace_3757963 : CollatzResearch.WordTrace tailWord_3757963 prefixEnd_3757963 1286427533874790457453299 := by
  unfold tailWord_3757963
  simp only [CollatzResearch.WordTrace]
  refine ⟨137064170884549334828486543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91376113923032889885657695 137064170884549334828486543)
  ·
    refine ⟨205596256326824002242729815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137064170884549334828486543 205596256326824002242729815)
    ·
      refine ⟨308394384490236003364094723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205596256326824002242729815 308394384490236003364094723)
      ·
        refine ⟨462591576735354005046142085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308394384490236003364094723 462591576735354005046142085)
        ·
          refine ⟨86735920637878875946151641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462591576735354005046142085 86735920637878875946151641)
          ·
            refine ⟨65051940478409156959613731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86735920637878875946151641 65051940478409156959613731)
            ·
              refine ⟨97577910717613735439420597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65051940478409156959613731 97577910717613735439420597)
              ·
                refine ⟨9147929129776287697445681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97577910717613735439420597 9147929129776287697445681)
                ·
                  refine ⟨6860946847332215773084261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9147929129776287697445681 6860946847332215773084261)
                  ·
                    refine ⟨1286427533874790457453299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860946847332215773084261 1286427533874790457453299)
                    ·
                      rfl

theorem cell22_3757963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_3757963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757963 prefixEnd_3757963 := by exact prefixLift 3757963
  have htrace : WordTrace (prefixWord ++ tailWord_3757963) baseStart_3757963 baseEnd_3757963 := by
    simpa [prefixWord, tailWord_3757963, baseEnd_3757963] using wordTrace_append hprefix tailTrace_3757963
  have hstable : (prefixWord ++ tailWord_3757963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757963).length < 2 ^ (prefixWord ++ tailWord_3757963).sum := by decide
  have hdescent : baseEnd_3757963 < baseStart_3757963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757978 : List Nat := [3, 1, 1, 4, 2, 1, 10]
def baseStart_3757978 : Nat := 118140960795 + 3757978 * 2 ^ 59
def prefixEnd_3757978 : Nat := 4983230072969 + 3 ^ 40 * 3757978 * 2
def baseEnd_3757978 : Nat := 47645654395605015493639

theorem tailTrace_3757978 : CollatzResearch.WordTrace tailWord_3757978 prefixEnd_3757978 47645654395605015493639 := by
  unfold tailWord_3757978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266179494873748097570647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91376478652996661593521725 34266179494873748097570647)
  ·
    refine ⟨51399269242310622146355971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34266179494873748097570647 51399269242310622146355971)
    ·
      refine ⟨77098903863465933219533957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51399269242310622146355971 77098903863465933219533957)
      ·
        refine ⟨14456044474399862478662617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77098903863465933219533957 14456044474399862478662617)
        ·
          refine ⟨10842033355799896858996963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14456044474399862478662617 10842033355799896858996963)
          ·
            refine ⟨16263050033699845288495445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842033355799896858996963 16263050033699845288495445)
            ·
              refine ⟨47645654395605015493639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16263050033699845288495445 47645654395605015493639)
              ·
                rfl

theorem cell22_3757978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 10].length) (baseStart_3757978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757978 prefixEnd_3757978 := by exact prefixLift 3757978
  have htrace : WordTrace (prefixWord ++ tailWord_3757978) baseStart_3757978 baseEnd_3757978 := by
    simpa [prefixWord, tailWord_3757978, baseEnd_3757978] using wordTrace_append hprefix tailTrace_3757978
  have hstable : (prefixWord ++ tailWord_3757978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757978).length < 2 ^ (prefixWord ++ tailWord_3757978).sum := by decide
  have hdescent : baseEnd_3757978 < baseStart_3757978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3757980 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 4, 4]
def baseStart_3757980 : Nat := 118140960795 + 3757980 * 2 ^ 59
def prefixEnd_3757980 : Nat := 4983230072969 + 3 ^ 40 * 3757980 * 2
def baseEnd_3757980 : Nat := 1286433353322208079778247

theorem tailTrace_3757980 : CollatzResearch.WordTrace tailWord_3757980 prefixEnd_3757980 1286433353322208079778247 := by
  unfold tailWord_3757980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68532395462743873365927697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91376527283658497821236929 68532395462743873365927697)
  ·
    refine ⟨51399296597057905024445773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68532395462743873365927697 51399296597057905024445773)
    ·
      refine ⟨19274736223896714384167165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51399296597057905024445773 19274736223896714384167165)
      ·
        refine ⟨7228026083961267894062687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19274736223896714384167165 7228026083961267894062687)
        ·
          refine ⟨10842039125941901841094031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228026083961267894062687 10842039125941901841094031)
          ·
            refine ⟨16263058688912852761641047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10842039125941901841094031 16263058688912852761641047)
            ·
              refine ⟨24394588033369279142461571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16263058688912852761641047 24394588033369279142461571)
              ·
                refine ⟨36591882050053918713692357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24394588033369279142461571 36591882050053918713692357)
                ·
                  refine ⟨6860977884385109758817317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36591882050053918713692357 6860977884385109758817317)
                  ·
                    refine ⟨1286433353322208079778247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6860977884385109758817317 1286433353322208079778247)
                    ·
                      rfl

theorem cell22_3757980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_3757980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3757980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3757980 prefixEnd_3757980 := by exact prefixLift 3757980
  have htrace : WordTrace (prefixWord ++ tailWord_3757980) baseStart_3757980 baseEnd_3757980 := by
    simpa [prefixWord, tailWord_3757980, baseEnd_3757980] using wordTrace_append hprefix tailTrace_3757980
  have hstable : (prefixWord ++ tailWord_3757980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3757980).length < 2 ^ (prefixWord ++ tailWord_3757980).sum := by decide
  have hdescent : baseEnd_3757980 < baseStart_3757980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3757980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758027 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 1, 3]
def baseStart_3758027 : Nat := 118140960795 + 3758027 * 2 ^ 59
def prefixEnd_3758027 : Nat := 4983230072969 + 3 ^ 40 * 3758027 * 2
def baseEnd_3758027 : Nat := 1286449442382715623853103

theorem tailTrace_3758027 : CollatzResearch.WordTrace tailWord_3758027 prefixEnd_3758027 1286449442382715623853103 := by
  unfold tailWord_3758027
  simp only [CollatzResearch.WordTrace]
  refine ⟨137066505156317473758816335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91377670104211649172544223 137066505156317473758816335)
  ·
    refine ⟨205599757734476210638224503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137066505156317473758816335 205599757734476210638224503)
    ·
      refine ⟨308399636601714315957336755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205599757734476210638224503 308399636601714315957336755)
      ·
        refine ⟨462599454902571473936005133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308399636601714315957336755 462599454902571473936005133)
        ·
          refine ⟨173474795588464302726001925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462599454902571473936005133 173474795588464302726001925)
          ·
            refine ⟨32526524172837056761125361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173474795588464302726001925 32526524172837056761125361)
            ·
              refine ⟨24394893129627792570844021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32526524172837056761125361 24394893129627792570844021)
              ·
                refine ⟨2287021230902605553516627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24394893129627792570844021 2287021230902605553516627)
                ·
                  refine ⟨3430531846353908330274941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287021230902605553516627 3430531846353908330274941)
                  ·
                    refine ⟨1286449442382715623853103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430531846353908330274941 1286449442382715623853103)
                    ·
                      rfl

theorem cell22_3758027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 3].length) (baseStart_3758027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758027 prefixEnd_3758027 := by exact prefixLift 3758027
  have htrace : WordTrace (prefixWord ++ tailWord_3758027) baseStart_3758027 baseEnd_3758027 := by
    simpa [prefixWord, tailWord_3758027, baseEnd_3758027] using wordTrace_append hprefix tailTrace_3758027
  have hstable : (prefixWord ++ tailWord_3758027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758027).length < 2 ^ (prefixWord ++ tailWord_3758027).sum := by decide
  have hdescent : baseEnd_3758027 < baseStart_3758027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758040 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_3758040 : Nat := 118140960795 + 3758040 * 2 ^ 59
def prefixEnd_3758040 : Nat := 4983230072969 + 3 ^ 40 * 3758040 * 2
def baseEnd_3758040 : Nat := 428817964182795974426021

theorem tailTrace_3758040 : CollatzResearch.WordTrace tailWord_3758040 prefixEnd_3758040 428817964182795974426021 := by
  unfold tailWord_3758040
  simp only [CollatzResearch.WordTrace]
  refine ⟨68533489652635188489519787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91377986203513584652693049 68533489652635188489519787)
  ·
    refine ⟨102800234478952782734279681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68533489652635188489519787 102800234478952782734279681)
    ·
      refine ⟨77100175859214587050709761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102800234478952782734279681 77100175859214587050709761)
      ·
        refine ⟨57825131894410940288032321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77100175859214587050709761 57825131894410940288032321)
        ·
          refine ⟨43368848920808205216024241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57825131894410940288032321 43368848920808205216024241)
          ·
            refine ⟨32526636690606153912018181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43368848920808205216024241 32526636690606153912018181)
            ·
              refine ⟨6098744379488653858503409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32526636690606153912018181 6098744379488653858503409)
              ·
                refine ⟨4574058284616490393877557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6098744379488653858503409 4574058284616490393877557)
                ·
                  refine ⟨428817964182795974426021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574058284616490393877557 428817964182795974426021)
                  ·
                    rfl

theorem cell22_3758040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_3758040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758040 prefixEnd_3758040 := by exact prefixLift 3758040
  have htrace : WordTrace (prefixWord ++ tailWord_3758040) baseStart_3758040 baseEnd_3758040 := by
    simpa [prefixWord, tailWord_3758040, baseEnd_3758040] using wordTrace_append hprefix tailTrace_3758040
  have hstable : (prefixWord ++ tailWord_3758040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758040).length < 2 ^ (prefixWord ++ tailWord_3758040).sum := by decide
  have hdescent : baseEnd_3758040 < baseStart_3758040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758087 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 1, 4]
def baseStart_3758087 : Nat := 118140960795 + 3758087 * 2 ^ 59
def prefixEnd_3758087 : Nat := 4983230072969 + 3 ^ 40 * 3758087 * 2
def baseEnd_3758087 : Nat := 1286469981608895467352919

theorem tailTrace_3758087 : CollatzResearch.WordTrace tailWord_3758087 prefixEnd_3758087 1286469981608895467352919 := by
  unfold tailWord_3758087
  simp only [CollatzResearch.WordTrace]
  refine ⟨137068693536100104006000515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91379129024066736004000343 137068693536100104006000515)
  ·
    refine ⟨205603040304150156009000773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137068693536100104006000515 205603040304150156009000773)
    ·
      refine ⟨38550570057028154251687645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205603040304150156009000773 38550570057028154251687645)
      ·
        refine ⟨14456463771385557844382867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38550570057028154251687645 14456463771385557844382867)
        ·
          refine ⟨21684695657078336766574301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14456463771385557844382867 21684695657078336766574301)
          ·
            refine ⟨8131760871404376287465363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21684695657078336766574301 8131760871404376287465363)
            ·
              refine ⟨12197641307106564431198045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131760871404376287465363 12197641307106564431198045)
              ·
                refine ⟨4574115490164961661699267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12197641307106564431198045 4574115490164961661699267)
                ·
                  refine ⟨6861173235247442492548901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574115490164961661699267 6861173235247442492548901)
                  ·
                    refine ⟨1286469981608895467352919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6861173235247442492548901 1286469981608895467352919)
                    ·
                      rfl

theorem cell22_3758087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_3758087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758087 prefixEnd_3758087 := by exact prefixLift 3758087
  have htrace : WordTrace (prefixWord ++ tailWord_3758087) baseStart_3758087 baseEnd_3758087 := by
    simpa [prefixWord, tailWord_3758087, baseEnd_3758087] using wordTrace_append hprefix tailTrace_3758087
  have hstable : (prefixWord ++ tailWord_3758087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758087).length < 2 ^ (prefixWord ++ tailWord_3758087).sum := by decide
  have hdescent : baseEnd_3758087 < baseStart_3758087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758117 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_3758117 : Nat := 118140960795 + 3758117 * 2 ^ 59
def prefixEnd_3758117 : Nat := 4983230072969 + 3 ^ 40 * 3758117 * 2
def baseEnd_3758117 : Nat := 1286480251221985389102827

theorem tailTrace_3758117 : CollatzResearch.WordTrace tailWord_3758117 prefixEnd_3758117 1286480251221985389102827 := by
  unfold tailWord_3758117
  simp only [CollatzResearch.WordTrace]
  refine ⟨137069787725991419129592605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91379858483994279419728403 137069787725991419129592605)
  ·
    refine ⟨51401170397246782173597227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137069787725991419129592605 51401170397246782173597227)
    ·
      refine ⟨77101755595870173260395841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51401170397246782173597227 77101755595870173260395841)
      ·
        refine ⟨57826316696902629945296881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77101755595870173260395841 57826316696902629945296881)
        ·
          refine ⟨43369737522676972458972661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57826316696902629945296881 43369737522676972458972661)
          ·
            refine ⟨4065912892750966168028687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43369737522676972458972661 4065912892750966168028687)
            ·
              refine ⟨6098869339126449252043031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065912892750966168028687 6098869339126449252043031)
              ·
                refine ⟨9148304008689673878064547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098869339126449252043031 9148304008689673878064547)
                ·
                  refine ⟨13722456013034510817096821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9148304008689673878064547 13722456013034510817096821)
                  ·
                    refine ⟨1286480251221985389102827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13722456013034510817096821 1286480251221985389102827)
                    ·
                      rfl

theorem cell22_3758117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_3758117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758117 prefixEnd_3758117 := by exact prefixLift 3758117
  have htrace : WordTrace (prefixWord ++ tailWord_3758117) baseStart_3758117 baseEnd_3758117 := by
    simpa [prefixWord, tailWord_3758117, baseEnd_3758117] using wordTrace_append hprefix tailTrace_3758117
  have hstable : (prefixWord ++ tailWord_3758117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758117).length < 2 ^ (prefixWord ++ tailWord_3758117).sum := by decide
  have hdescent : baseEnd_3758117 < baseStart_3758117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758130 : List Nat := [3, 2, 1, 1, 2, 4, 1, 8]
def baseStart_3758130 : Nat := 118140960795 + 3758130 * 2 ^ 59
def prefixEnd_3758130 : Nat := 4983230072969 + 3 ^ 40 * 3758130 * 2
def baseEnd_3758130 : Nat := 142942744598628632058643

theorem tailTrace_3758130 : CollatzResearch.WordTrace tailWord_3758130 prefixEnd_3758130 142942744598628632058643 := by
  unfold tailWord_3758130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34267565468736080587453961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91380174583296214899877229 34267565468736080587453961)
  ·
    refine ⟨25700674101552060440590471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34267565468736080587453961 25700674101552060440590471)
    ·
      refine ⟨38551011152328090660885707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25700674101552060440590471 38551011152328090660885707)
      ·
        refine ⟨57826516728492135991328561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38551011152328090660885707 57826516728492135991328561)
        ·
          refine ⟨43369887546369101993496421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57826516728492135991328561 43369887546369101993496421)
          ·
            refine ⟨8131853914944206623780579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43369887546369101993496421 8131853914944206623780579)
            ·
              refine ⟨12197780872416309935670869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131853914944206623780579 12197780872416309935670869)
              ·
                refine ⟨142942744598628632058643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12197780872416309935670869 142942744598628632058643)
                ·
                  rfl

theorem cell22_3758130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_3758130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758130 prefixEnd_3758130 := by exact prefixLift 3758130
  have htrace : WordTrace (prefixWord ++ tailWord_3758130) baseStart_3758130 baseEnd_3758130 := by
    simpa [prefixWord, tailWord_3758130, baseEnd_3758130] using wordTrace_append hprefix tailTrace_3758130
  have hstable : (prefixWord ++ tailWord_3758130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758130).length < 2 ^ (prefixWord ++ tailWord_3758130).sum := by decide
  have hdescent : baseEnd_3758130 < baseStart_3758130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758136 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_3758136 : Nat := 118140960795 + 3758136 * 2 ^ 59
def prefixEnd_3758136 : Nat := 4983230072969 + 3 ^ 40 * 3758136 * 2
def baseEnd_3758136 : Nat := 428828918436758557625923

theorem tailTrace_3758136 : CollatzResearch.WordTrace tailWord_3758136 prefixEnd_3758136 428828918436758557625923 := by
  unfold tailWord_3758136
  simp only [CollatzResearch.WordTrace]
  refine ⟨68535240356461292687267131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91380320475281723583022841 68535240356461292687267131)
  ·
    refine ⟨102802860534691939030900697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68535240356461292687267131 102802860534691939030900697)
    ·
      refine ⟨77102145401018954273175523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102802860534691939030900697 77102145401018954273175523)
      ·
        refine ⟨115653218101528431409763285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77102145401018954273175523 115653218101528431409763285)
        ·
          refine ⟨2710622299254572611166327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115653218101528431409763285 2710622299254572611166327)
          ·
            refine ⟨4065933448881858916749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710622299254572611166327 4065933448881858916749491)
            ·
              refine ⟨6098900173322788375124237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065933448881858916749491 6098900173322788375124237)
              ·
                refine ⟨2287087564996045640671589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6098900173322788375124237 2287087564996045640671589)
                ·
                  refine ⟨428828918436758557625923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287087564996045640671589 428828918436758557625923)
                  ·
                    rfl

theorem cell22_3758136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_3758136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758136 prefixEnd_3758136 := by exact prefixLift 3758136
  have htrace : WordTrace (prefixWord ++ tailWord_3758136) baseStart_3758136 baseEnd_3758136 := by
    simpa [prefixWord, tailWord_3758136, baseEnd_3758136] using wordTrace_append hprefix tailTrace_3758136
  have hstable : (prefixWord ++ tailWord_3758136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758136).length < 2 ^ (prefixWord ++ tailWord_3758136).sum := by decide
  have hdescent : baseEnd_3758136 < baseStart_3758136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758209 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 5]
def baseStart_3758209 : Nat := 118140960795 + 3758209 * 2 ^ 59
def prefixEnd_3758209 : Nat := 4983230072969 + 3 ^ 40 * 3758209 * 2
def baseEnd_3758209 : Nat := 428837248234042605267515

theorem tailTrace_3758209 : CollatzResearch.WordTrace tailWord_3758209 prefixEnd_3758209 428837248234042605267515 := by
  unfold tailWord_3758209
  simp only [CollatzResearch.WordTrace]
  refine ⟨137073143241658118841941681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91382095494438745894627787 137073143241658118841941681)
  ·
    refine ⟨102804857431243589131456261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137073143241658118841941681 102804857431243589131456261)
    ·
      refine ⟨19275910768358172962148049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102804857431243589131456261 19275910768358172962148049)
      ·
        refine ⟨14456933076268629721611037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19275910768358172962148049 14456933076268629721611037)
        ·
          refine ⟨5421349903600736145604139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14456933076268629721611037 5421349903600736145604139)
          ·
            refine ⟨8132024855401104218406209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421349903600736145604139 8132024855401104218406209)
            ·
              refine ⟨6099018641550828163804657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8132024855401104218406209 6099018641550828163804657)
              ·
                refine ⟨4574263981163121122853493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099018641550828163804657 4574263981163121122853493)
                ·
                  refine ⟨428837248234042605267515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574263981163121122853493 428837248234042605267515)
                  ·
                    rfl

theorem cell22_3758209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_3758209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758209 prefixEnd_3758209 := by exact prefixLift 3758209
  have htrace : WordTrace (prefixWord ++ tailWord_3758209) baseStart_3758209 baseEnd_3758209 := by
    simpa [prefixWord, tailWord_3758209, baseEnd_3758209] using wordTrace_append hprefix tailTrace_3758209
  have hstable : (prefixWord ++ tailWord_3758209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758209).length < 2 ^ (prefixWord ++ tailWord_3758209).sum := by decide
  have hdescent : baseEnd_3758209 < baseStart_3758209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758213 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_3758213 : Nat := 118140960795 + 3758213 * 2 ^ 59
def prefixEnd_3758213 : Nat := 4983230072969 + 3 ^ 40 * 3758213 * 2
def baseEnd_3758213 : Nat := 1286513113983873138702533

theorem tailTrace_3758213 : CollatzResearch.WordTrace tailWord_3758213 prefixEnd_3758213 1286513113983873138702533 := by
  unfold tailWord_3758213
  simp only [CollatzResearch.WordTrace]
  refine ⟨137073289133643627525087293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91382192755762418350058195 137073289133643627525087293)
  ·
    refine ⟨51402483425116360321907735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137073289133643627525087293 51402483425116360321907735)
    ·
      refine ⟨77103725137674540482861603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51402483425116360321907735 77103725137674540482861603)
      ·
        refine ⟨115655587706511810724292405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77103725137674540482861603 115655587706511810724292405)
        ·
          refine ⟨10842711347485482255402413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115655587706511810724292405 10842711347485482255402413)
          ·
            refine ⟨4066016755307055845775905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10842711347485482255402413 4066016755307055845775905)
            ·
              refine ⟨3049512566480291884331929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066016755307055845775905 3049512566480291884331929)
              ·
                refine ⟨2287134424860218913248947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049512566480291884331929 2287134424860218913248947)
                ·
                  refine ⟨3430701637290328369873421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287134424860218913248947 3430701637290328369873421)
                  ·
                    refine ⟨1286513113983873138702533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430701637290328369873421 1286513113983873138702533)
                    ·
                      rfl

theorem cell22_3758213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_3758213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758213 prefixEnd_3758213 := by exact prefixLift 3758213
  have htrace : WordTrace (prefixWord ++ tailWord_3758213) baseStart_3758213 baseEnd_3758213 := by
    simpa [prefixWord, tailWord_3758213, baseEnd_3758213] using wordTrace_append hprefix tailTrace_3758213
  have hstable : (prefixWord ++ tailWord_3758213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758213).length < 2 ^ (prefixWord ++ tailWord_3758213).sum := by decide
  have hdescent : baseEnd_3758213 < baseStart_3758213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758237 : List Nat := [1, 4, 2, 1, 1, 4, 1, 2, 6]
def baseStart_3758237 : Nat := 118140960795 + 3758237 * 2 ^ 59
def prefixEnd_3758237 : Nat := 4983230072969 + 3 ^ 40 * 3758237 * 2
def baseEnd_3758237 : Nat := 428840443224781692034153

theorem tailTrace_3758237 : CollatzResearch.WordTrace tailWord_3758237 prefixEnd_3758237 428840443224781692034153 := by
  unfold tailWord_3758237
  simp only [CollatzResearch.WordTrace]
  refine ⟨137074164485556679623960965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91382776323704453082640643 137074164485556679623960965)
  ·
    refine ⟨25701405841041877429492681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137074164485556679623960965 25701405841041877429492681)
    ·
      refine ⟨19276054380781408072119511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25701405841041877429492681 19276054380781408072119511)
      ·
        refine ⟨28914081571172112108179267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19276054380781408072119511 28914081571172112108179267)
        ·
          refine ⟨43371122356758168162268901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28914081571172112108179267 43371122356758168162268901)
          ·
            refine ⟨8132085441892156530425419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43371122356758168162268901 8132085441892156530425419)
            ·
              refine ⟨12198128162838234795638129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8132085441892156530425419 12198128162838234795638129)
              ·
                refine ⟨9148596122128676096728597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12198128162838234795638129 9148596122128676096728597)
                ·
                  refine ⟨428840443224781692034153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9148596122128676096728597 428840443224781692034153)
                  ·
                    rfl

theorem cell22_3758237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_3758237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758237 prefixEnd_3758237 := by exact prefixLift 3758237
  have htrace : WordTrace (prefixWord ++ tailWord_3758237) baseStart_3758237 baseEnd_3758237 := by
    simpa [prefixWord, tailWord_3758237, baseEnd_3758237] using wordTrace_append hprefix tailTrace_3758237
  have hstable : (prefixWord ++ tailWord_3758237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758237).length < 2 ^ (prefixWord ++ tailWord_3758237).sum := by decide
  have hdescent : baseEnd_3758237 < baseStart_3758237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758260 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3758260 : Nat := 118140960795 + 3758260 * 2 ^ 59
def prefixEnd_3758260 : Nat := 4983230072969 + 3 ^ 40 * 3758260 * 2
def baseEnd_3758260 : Nat := 428843067681460227592463

theorem tailTrace_3758260 : CollatzResearch.WordTrace tailWord_3758260 prefixEnd_3758260 428843067681460227592463 := by
  unfold tailWord_3758260
  simp only [CollatzResearch.WordTrace]
  refine ⟨68537501682236677276024117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91383335576315569701365489 68537501682236677276024117)
  ·
    refine ⟨6425390782709688494627261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68537501682236677276024117 6425390782709688494627261)
    ·
      refine ⟨2409521543516133185485223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6425390782709688494627261 2409521543516133185485223)
      ·
        refine ⟨3614282315274199778227835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409521543516133185485223 3614282315274199778227835)
        ·
          refine ⟨5421423472911299667341753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614282315274199778227835 5421423472911299667341753)
          ·
            refine ⟨4066067604683474750506315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421423472911299667341753 4066067604683474750506315)
            ·
              refine ⟨6099101407025212125759473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066067604683474750506315 6099101407025212125759473)
              ·
                refine ⟨4574326055268909094319605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099101407025212125759473 4574326055268909094319605)
                ·
                  refine ⟨428843067681460227592463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574326055268909094319605 428843067681460227592463)
                  ·
                    rfl

theorem cell22_3758260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3758260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758260 prefixEnd_3758260 := by exact prefixLift 3758260
  have htrace : WordTrace (prefixWord ++ tailWord_3758260) baseStart_3758260 baseEnd_3758260 := by
    simpa [prefixWord, tailWord_3758260, baseEnd_3758260] using wordTrace_append hprefix tailTrace_3758260
  have hstable : (prefixWord ++ tailWord_3758260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758260).length < 2 ^ (prefixWord ++ tailWord_3758260).sum := by decide
  have hdescent : baseEnd_3758260 < baseStart_3758260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758265 : List Nat := [1, 2, 1, 4, 1, 2, 11]
def baseStart_3758265 : Nat := 118140960795 + 3758265 * 2 ^ 59
def prefixEnd_3758265 : Nat := 4983230072969 + 3 ^ 40 * 3758265 * 2
def baseEnd_3758265 : Nat := 47649293135057864311199

theorem tailTrace_3758265 : CollatzResearch.WordTrace tailWord_3758265 prefixEnd_3758265 47649293135057864311199 := by
  unfold tailWord_3758265
  simp only [CollatzResearch.WordTrace]
  refine ⟨137075185729455240405980249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91383457152970160270653499 137075185729455240405980249)
  ·
    refine ⟨102806389297091430304485187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137075185729455240405980249 102806389297091430304485187)
    ·
      refine ⟨154209583945637145456727781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102806389297091430304485187 154209583945637145456727781)
      ·
        refine ⟨28914296989806964773136459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154209583945637145456727781 28914296989806964773136459)
        ·
          refine ⟨43371445484710447159704689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28914296989806964773136459 43371445484710447159704689)
          ·
            refine ⟨32528584113532835369778517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43371445484710447159704689 32528584113532835369778517)
            ·
              refine ⟨47649293135057864311199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32528584113532835369778517 47649293135057864311199)
              ·
                rfl

theorem cell22_3758265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 11].length) (baseStart_3758265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758265 prefixEnd_3758265 := by exact prefixLift 3758265
  have htrace : WordTrace (prefixWord ++ tailWord_3758265) baseStart_3758265 baseEnd_3758265 := by
    simpa [prefixWord, tailWord_3758265, baseEnd_3758265] using wordTrace_append hprefix tailTrace_3758265
  have hstable : (prefixWord ++ tailWord_3758265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758265).length < 2 ^ (prefixWord ++ tailWord_3758265).sum := by decide
  have hdescent : baseEnd_3758265 < baseStart_3758265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758344 : List Nat := [2, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_3758344 : Nat := 118140960795 + 3758344 * 2 ^ 59
def prefixEnd_3758344 : Nat := 4983230072969 + 3 ^ 40 * 3758344 * 2
def baseEnd_3758344 : Nat := 428852652653677487892377

theorem tailTrace_3758344 : CollatzResearch.WordTrace tailWord_3758344 prefixEnd_3758344 428852652653677487892377 := by
  unfold tailWord_3758344
  simp only [CollatzResearch.WordTrace]
  refine ⟨68539033548084518449053043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91385378064112691265404057 68539033548084518449053043)
  ·
    refine ⟨102808550322126777673579565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68539033548084518449053043 102808550322126777673579565)
    ·
      refine ⟨38553206370797541627592337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102808550322126777673579565 38553206370797541627592337)
      ·
        refine ⟨28914904778098156220694253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38553206370797541627592337 28914904778098156220694253)
        ·
          refine ⟨10843089291786808582760345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28914904778098156220694253 10843089291786808582760345)
          ·
            refine ⟨8132316968840106437070259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10843089291786808582760345 8132316968840106437070259)
            ·
              refine ⟨12198475453260159655605389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8132316968840106437070259 12198475453260159655605389)
              ·
                refine ⟨4574428294972559870852021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12198475453260159655605389 4574428294972559870852021)
                ·
                  refine ⟨428852652653677487892377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574428294972559870852021 428852652653677487892377)
                  ·
                    rfl

theorem cell22_3758344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_3758344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758344 prefixEnd_3758344 := by exact prefixLift 3758344
  have htrace : WordTrace (prefixWord ++ tailWord_3758344) baseStart_3758344 baseEnd_3758344 := by
    simpa [prefixWord, tailWord_3758344, baseEnd_3758344] using wordTrace_append hprefix tailTrace_3758344
  have hstable : (prefixWord ++ tailWord_3758344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758344).length < 2 ^ (prefixWord ++ tailWord_3758344).sum := by decide
  have hdescent : baseEnd_3758344 < baseStart_3758344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758387 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_3758387 : Nat := 118140960795 + 3758387 * 2 ^ 59
def prefixEnd_3758387 : Nat := 4983230072969 + 3 ^ 40 * 3758387 * 2
def baseEnd_3758387 : Nat := 1286572677739794684851999

theorem tailTrace_3758387 : CollatzResearch.WordTrace tailWord_3758387 prefixEnd_3758387 1286572677739794684851999 := by
  unfold tailWord_3758387
  simp only [CollatzResearch.WordTrace]
  refine ⟨137079635435013255241921415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91386423623342170161280943 137079635435013255241921415)
  ·
    refine ⟨205619453152519882862882123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137079635435013255241921415 205619453152519882862882123)
    ·
      refine ⟨308429179728779824294323185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205619453152519882862882123 308429179728779824294323185)
      ·
        refine ⟨231321884796584868220742389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308429179728779824294323185 231321884796584868220742389)
        ·
          refine ⟨21686426699679831395694599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231321884796584868220742389 21686426699679831395694599)
          ·
            refine ⟨32529640049519747093541899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21686426699679831395694599 32529640049519747093541899)
            ·
              refine ⟨48794460074279620640312849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32529640049519747093541899 48794460074279620640312849)
              ·
                refine ⟨36595845055709715480234637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48794460074279620640312849 36595845055709715480234637)
                ·
                  refine ⟨13723441895891143305087989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36595845055709715480234637 13723441895891143305087989)
                  ·
                    refine ⟨1286572677739794684851999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13723441895891143305087989 1286572677739794684851999)
                    ·
                      rfl

theorem cell22_3758387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_3758387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758387 prefixEnd_3758387 := by exact prefixLift 3758387
  have htrace : WordTrace (prefixWord ++ tailWord_3758387) baseStart_3758387 baseEnd_3758387 := by
    simpa [prefixWord, tailWord_3758387, baseEnd_3758387] using wordTrace_append hprefix tailTrace_3758387
  have hstable : (prefixWord ++ tailWord_3758387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758387).length < 2 ^ (prefixWord ++ tailWord_3758387).sum := by decide
  have hdescent : baseEnd_3758387 < baseStart_3758387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758434 : List Nat := [3, 3, 2, 1, 1, 3, 9]
def baseStart_3758434 : Nat := 118140960795 + 3758434 * 2 ^ 59
def prefixEnd_3758434 : Nat := 4983230072969 + 3 ^ 40 * 3758434 * 2
def baseEnd_3758434 : Nat := 47651435807418601071365

theorem tailTrace_3758434 : CollatzResearch.WordTrace tailWord_3758434 prefixEnd_3758434 47651435807418601071365 := by
  unfold tailWord_3758434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270337416460745567220589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91387566443895321512588237 34270337416460745567220589)
  ·
    refine ⟨12851376531172779587707721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34270337416460745567220589 12851376531172779587707721)
    ·
      refine ⟨9638532398379584690780791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12851376531172779587707721 9638532398379584690780791)
      ·
        refine ⟨14457798597569377036171187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9638532398379584690780791 14457798597569377036171187)
        ·
          refine ⟨21686697896354065554256781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457798597569377036171187 21686697896354065554256781)
          ·
            refine ⟨8132511711132774582846293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21686697896354065554256781 8132511711132774582846293)
            ·
              refine ⟨47651435807418601071365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8132511711132774582846293 47651435807418601071365)
              ·
                rfl

theorem cell22_3758434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 9].length) (baseStart_3758434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758434 prefixEnd_3758434 := by exact prefixLift 3758434
  have htrace : WordTrace (prefixWord ++ tailWord_3758434) baseStart_3758434 baseEnd_3758434 := by
    simpa [prefixWord, tailWord_3758434, baseEnd_3758434] using wordTrace_append hprefix tailTrace_3758434
  have hstable : (prefixWord ++ tailWord_3758434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758434).length < 2 ^ (prefixWord ++ tailWord_3758434).sum := by decide
  have hdescent : baseEnd_3758434 < baseStart_3758434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758447 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_3758447 : Nat := 118140960795 + 3758447 * 2 ^ 59
def prefixEnd_3758447 : Nat := 4983230072969 + 3 ^ 40 * 3758447 * 2
def baseEnd_3758447 : Nat := 1286593216965974528351815

theorem tailTrace_3758447 : CollatzResearch.WordTrace tailWord_3758447 prefixEnd_3758447 1286593216965974528351815 := by
  unfold tailWord_3758447
  simp only [CollatzResearch.WordTrace]
  refine ⟨137081823814795885489105595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91387882543197256992737063 137081823814795885489105595)
  ·
    refine ⟨205622735722193828233658393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137081823814795885489105595 205622735722193828233658393)
    ·
      refine ⟨154217051791645371175243795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205622735722193828233658393 154217051791645371175243795)
      ·
        refine ⟨231325577687468056762865693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154217051791645371175243795 231325577687468056762865693)
        ·
          refine ⟨86747091632800521286074635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231325577687468056762865693 86747091632800521286074635)
          ·
            refine ⟨130120637449200781929111953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86747091632800521286074635 130120637449200781929111953)
            ·
              refine ⟨97590478086900586446833965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130120637449200781929111953 97590478086900586446833965)
              ·
                refine ⟨36596429282587719917562737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97590478086900586446833965 36596429282587719917562737)
                ·
                  refine ⟨27447321961940789938172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36596429282587719917562737 27447321961940789938172053)
                  ·
                    refine ⟨1286593216965974528351815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27447321961940789938172053 1286593216965974528351815)
                    ·
                      rfl

theorem cell22_3758447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_3758447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758447 prefixEnd_3758447 := by exact prefixLift 3758447
  have htrace : WordTrace (prefixWord ++ tailWord_3758447) baseStart_3758447 baseEnd_3758447 := by
    simpa [prefixWord, tailWord_3758447, baseEnd_3758447] using wordTrace_append hprefix tailTrace_3758447
  have hstable : (prefixWord ++ tailWord_3758447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758447).length < 2 ^ (prefixWord ++ tailWord_3758447).sum := by decide
  have hdescent : baseEnd_3758447 < baseStart_3758447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758506 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3758506 : Nat := 118140960795 + 3758506 * 2 ^ 59
def prefixEnd_3758506 : Nat := 4983230072969 + 3 ^ 40 * 3758506 * 2
def baseEnd_3758506 : Nat := 1286613413871718041126635

theorem tailTrace_3758506 : CollatzResearch.WordTrace tailWord_3758506 prefixEnd_3758506 1286613413871718041126635 := by
  unfold tailWord_3758506
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270993930395534641375843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91389317147721425710335581 34270993930395534641375843)
  ·
    refine ⟨51406490895593301962063765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34270993930395534641375843 51406490895593301962063765)
    ·
      refine ⟨2409679260730936029471739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51406490895593301962063765 2409679260730936029471739)
      ·
        refine ⟨3614518891096404044207609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409679260730936029471739 3614518891096404044207609)
        ·
          refine ⟨2710889168322303033155707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614518891096404044207609 2710889168322303033155707)
          ·
            refine ⟨4066333752483454549733561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710889168322303033155707 4066333752483454549733561)
            ·
              refine ⟨3049750314362590912300171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066333752483454549733561 3049750314362590912300171)
              ·
                refine ⟨4574625471543886368450257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049750314362590912300171 4574625471543886368450257)
                ·
                  refine ⟨3430969103657914776337693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574625471543886368450257 3430969103657914776337693)
                  ·
                    refine ⟨1286613413871718041126635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430969103657914776337693 1286613413871718041126635)
                    ·
                      rfl

theorem cell22_3758506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3758506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758506 prefixEnd_3758506 := by exact prefixLift 3758506
  have htrace : WordTrace (prefixWord ++ tailWord_3758506) baseStart_3758506 baseEnd_3758506 := by
    simpa [prefixWord, tailWord_3758506, baseEnd_3758506] using wordTrace_append hprefix tailTrace_3758506
  have hstable : (prefixWord ++ tailWord_3758506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758506).length < 2 ^ (prefixWord ++ tailWord_3758506).sum := by decide
  have hdescent : baseEnd_3758506 < baseStart_3758506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758513 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 5]
def baseStart_3758513 : Nat := 118140960795 + 3758513 * 2 ^ 59
def prefixEnd_3758513 : Nat := 4983230072969 + 3 ^ 40 * 3758513 * 2
def baseEnd_3758513 : Nat := 428871936704924118733871

theorem tailTrace_3758513 : CollatzResearch.WordTrace tailWord_3758513 prefixEnd_3758513 428871936704924118733871 := by
  unfold tailWord_3758513
  simp only [CollatzResearch.WordTrace]
  refine ⟨137084231032556778761008193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91389487355037852507338795 137084231032556778761008193)
  ·
    refine ⟨102813173274417584070756145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137084231032556778761008193 102813173274417584070756145)
    ·
      refine ⟨77109879955813188053067109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102813173274417584070756145 77109879955813188053067109)
      ·
        refine ⟨14458102491714972759950083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77109879955813188053067109 14458102491714972759950083)
        ·
          refine ⟨21687153737572459139925125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14458102491714972759950083 21687153737572459139925125)
          ·
            refine ⟨4066341325794836088735961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21687153737572459139925125 4066341325794836088735961)
            ·
              refine ⟨3049755994346127066551971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066341325794836088735961 3049755994346127066551971)
              ·
                refine ⟨4574633991519190599827957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049755994346127066551971 4574633991519190599827957)
                ·
                  refine ⟨428871936704924118733871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574633991519190599827957 428871936704924118733871)
                  ·
                    rfl

theorem cell22_3758513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_3758513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758513 prefixEnd_3758513 := by exact prefixLift 3758513
  have htrace : WordTrace (prefixWord ++ tailWord_3758513) baseStart_3758513 baseEnd_3758513 := by
    simpa [prefixWord, tailWord_3758513, baseEnd_3758513] using wordTrace_append hprefix tailTrace_3758513
  have hstable : (prefixWord ++ tailWord_3758513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758513).length < 2 ^ (prefixWord ++ tailWord_3758513).sum := by decide
  have hdescent : baseEnd_3758513 < baseStart_3758513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758573 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3758573 : Nat := 118140960795 + 3758573 * 2 ^ 59
def prefixEnd_3758573 : Nat := 4983230072969 + 3 ^ 40 * 3758573 * 2
def baseEnd_3758573 : Nat := 1286636349340952199701429

theorem tailTrace_3758573 : CollatzResearch.WordTrace tailWord_3758573 prefixEnd_3758573 1286636349340952199701429 := by
  unfold tailWord_3758573
  simp only [CollatzResearch.WordTrace]
  refine ⟨137086419412339409008192373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91390946274892939338794915 137086419412339409008192373)
  ·
    refine ⟨12851851819906819594518035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137086419412339409008192373 12851851819906819594518035)
    ·
      refine ⟨19277777729860229391777053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851851819906819594518035 19277777729860229391777053)
      ·
        refine ⟨7229166648697586021916395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19277777729860229391777053 7229166648697586021916395)
        ·
          refine ⟨10843749973046379032874593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229166648697586021916395 10843749973046379032874593)
          ·
            refine ⟨8132812479784784274655945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10843749973046379032874593 8132812479784784274655945)
            ·
              refine ⟨6099609359838588205991959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8132812479784784274655945 6099609359838588205991959)
              ·
                refine ⟨9149414039757882308987939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099609359838588205991959 9149414039757882308987939)
                ·
                  refine ⟨13724121059636823463481909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149414039757882308987939 13724121059636823463481909)
                  ·
                    refine ⟨1286636349340952199701429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724121059636823463481909 1286636349340952199701429)
                    ·
                      rfl

theorem cell22_3758573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3758573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758573 prefixEnd_3758573 := by exact prefixLift 3758573
  have htrace : WordTrace (prefixWord ++ tailWord_3758573) baseStart_3758573 baseEnd_3758573 := by
    simpa [prefixWord, tailWord_3758573, baseEnd_3758573] using wordTrace_append hprefix tailTrace_3758573
  have hstable : (prefixWord ++ tailWord_3758573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758573).length < 2 ^ (prefixWord ++ tailWord_3758573).sum := by decide
  have hdescent : baseEnd_3758573 < baseStart_3758573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758594 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3758594 : Nat := 118140960795 + 3758594 * 2 ^ 59
def prefixEnd_3758594 : Nat := 4983230072969 + 3 ^ 40 * 3758594 * 2
def baseEnd_3758594 : Nat := 1286643538070115144926365

theorem tailTrace_3758594 : CollatzResearch.WordTrace tailWord_3758594 prefixEnd_3758594 1286643538070115144926365 := by
  unfold tailWord_3758594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34271796336315832398676709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91391456896842219729804557 34271796336315832398676709)
  ·
    refine ⟨6425961813059218574751883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34271796336315832398676709 6425961813059218574751883)
    ·
      refine ⟨9638942719588827862127825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6425961813059218574751883 9638942719588827862127825)
      ·
        refine ⟨7229207039691620896595869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638942719588827862127825 7229207039691620896595869)
        ·
          refine ⟨2710952639884357836223451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7229207039691620896595869 2710952639884357836223451)
          ·
            refine ⟨4066428959826536754335177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710952639884357836223451 4066428959826536754335177)
            ·
              refine ⟨3049821719869902565751383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066428959826536754335177 3049821719869902565751383)
              ·
                refine ⟨4574732579804853848627075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049821719869902565751383 4574732579804853848627075)
                ·
                  refine ⟨6862098869707280772940613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4574732579804853848627075 6862098869707280772940613)
                  ·
                    refine ⟨1286643538070115144926365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862098869707280772940613 1286643538070115144926365)
                    ·
                      rfl

theorem cell22_3758594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3758594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758594 prefixEnd_3758594 := by exact prefixLift 3758594
  have htrace : WordTrace (prefixWord ++ tailWord_3758594) baseStart_3758594 baseEnd_3758594 := by
    simpa [prefixWord, tailWord_3758594, baseEnd_3758594] using wordTrace_append hprefix tailTrace_3758594
  have hstable : (prefixWord ++ tailWord_3758594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758594).length < 2 ^ (prefixWord ++ tailWord_3758594).sum := by decide
  have hdescent : baseEnd_3758594 < baseStart_3758594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758652 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_3758652 : Nat := 118140960795 + 3758652 * 2 ^ 59
def prefixEnd_3758652 : Nat := 4983230072969 + 3 ^ 40 * 3758652 * 2
def baseEnd_3758652 : Nat := 1286663392655422326976187

theorem tailTrace_3758652 : CollatzResearch.WordTrace tailWord_3758652 prefixEnd_3758652 1286663392655422326976187 := by
  unfold tailWord_3758652
  simp only [CollatzResearch.WordTrace]
  refine ⟨68544650389526602750159105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91392867186035470333545473 68544650389526602750159105)
  ·
    refine ⟨51408487792144952062619329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68544650389526602750159105 51408487792144952062619329)
    ·
      refine ⟨38556365844108714046964497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51408487792144952062619329 38556365844108714046964497)
      ·
        refine ⟨28917274383081535535223373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38556365844108714046964497 28917274383081535535223373)
        ·
          refine ⟨10843977893655575825708765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28917274383081535535223373 10843977893655575825708765)
          ·
            refine ⟨4066491710120840934640787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10843977893655575825708765 4066491710120840934640787)
            ·
              refine ⟨6099737565181261401961181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066491710120840934640787 6099737565181261401961181)
              ·
                refine ⟨2287401586942973025735443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6099737565181261401961181 2287401586942973025735443)
                ·
                  refine ⟨3431102380414459538603165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287401586942973025735443 3431102380414459538603165)
                  ·
                    refine ⟨1286663392655422326976187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431102380414459538603165 1286663392655422326976187)
                    ·
                      rfl

theorem cell22_3758652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_3758652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758652 prefixEnd_3758652 := by exact prefixLift 3758652
  have htrace : WordTrace (prefixWord ++ tailWord_3758652) baseStart_3758652 baseEnd_3758652 := by
    simpa [prefixWord, tailWord_3758652, baseEnd_3758652] using wordTrace_append hprefix tailTrace_3758652
  have hstable : (prefixWord ++ tailWord_3758652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758652).length < 2 ^ (prefixWord ++ tailWord_3758652).sum := by decide
  have hdescent : baseEnd_3758652 < baseStart_3758652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758659 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 8]
def baseStart_3758659 : Nat := 118140960795 + 3758659 * 2 ^ 59
def prefixEnd_3758659 : Nat := 4983230072969 + 3 ^ 40 * 3758659 * 2
def baseEnd_3758659 : Nat := 428888596299492214017055

theorem tailTrace_3758659 : CollatzResearch.WordTrace tailWord_3758659 prefixEnd_3758659 428888596299492214017055 := by
  unfold tailWord_3758659
  simp only [CollatzResearch.WordTrace]
  refine ⟨137089556090027845695823031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91393037393351897130548687 137089556090027845695823031)
  ·
    refine ⟨205634334135041768543734547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137089556090027845695823031 205634334135041768543734547)
    ·
      refine ⟨308451501202562652815601821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205634334135041768543734547 308451501202562652815601821)
      ·
        refine ⟨115669312950960994805850683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308451501202562652815601821 115669312950960994805850683)
        ·
          refine ⟨173503969426441492208776025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115669312950960994805850683 173503969426441492208776025)
          ·
            refine ⟨130127977069831119156582019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173503969426441492208776025 130127977069831119156582019)
            ·
              refine ⟨195191965604746678734873029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130127977069831119156582019 195191965604746678734873029)
              ·
                refine ⟨36598493550890002262788693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195191965604746678734873029 36598493550890002262788693)
                ·
                  refine ⟨428888596299492214017055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36598493550890002262788693 428888596299492214017055)
                  ·
                    rfl

theorem cell22_3758659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_3758659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758659 prefixEnd_3758659 := by exact prefixLift 3758659
  have htrace : WordTrace (prefixWord ++ tailWord_3758659) baseStart_3758659 baseEnd_3758659 := by
    simpa [prefixWord, tailWord_3758659, baseEnd_3758659] using wordTrace_append hprefix tailTrace_3758659
  have hstable : (prefixWord ++ tailWord_3758659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758659).length < 2 ^ (prefixWord ++ tailWord_3758659).sum := by decide
  have hdescent : baseEnd_3758659 < baseStart_3758659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758669 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3758669 : Nat := 118140960795 + 3758669 * 2 ^ 59
def prefixEnd_3758669 : Nat := 4983230072969 + 3 ^ 40 * 3758669 * 2
def baseEnd_3758669 : Nat := 1286669212102839949301135

theorem tailTrace_3758669 : CollatzResearch.WordTrace tailWord_3758669 prefixEnd_3758669 1286669212102839949301135 := by
  unfold tailWord_3758669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137089920819991617403687061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91393280546661078269124707 137089920819991617403687061)
  ·
    refine ⟨6426090038437107065797831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137089920819991617403687061 6426090038437107065797831)
    ·
      refine ⟨9639135057655660598696747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426090038437107065797831 9639135057655660598696747)
      ·
        refine ⟨14458702586483490898045121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639135057655660598696747 14458702586483490898045121)
        ·
          refine ⟨10844026939862618173533841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14458702586483490898045121 10844026939862618173533841)
          ·
            refine ⟨8133020204896963630150381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10844026939862618173533841 8133020204896963630150381)
            ·
              refine ⟨3049882576836361361306393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8133020204896963630150381 3049882576836361361306393)
              ·
                refine ⟨2287411932627271020979795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049882576836361361306393 2287411932627271020979795)
                ·
                  refine ⟨3431117898940906531469693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287411932627271020979795 3431117898940906531469693)
                  ·
                    refine ⟨1286669212102839949301135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431117898940906531469693 1286669212102839949301135)
                    ·
                      rfl

theorem cell22_3758669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3758669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758669 prefixEnd_3758669 := by exact prefixLift 3758669
  have htrace : WordTrace (prefixWord ++ tailWord_3758669) baseStart_3758669 baseEnd_3758669 := by
    simpa [prefixWord, tailWord_3758669, baseEnd_3758669] using wordTrace_append hprefix tailTrace_3758669
  have hstable : (prefixWord ++ tailWord_3758669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758669).length < 2 ^ (prefixWord ++ tailWord_3758669).sum := by decide
  have hdescent : baseEnd_3758669 < baseStart_3758669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758691 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_3758691 : Nat := 118140960795 + 3758691 * 2 ^ 59
def prefixEnd_3758691 : Nat := 4983230072969 + 3 ^ 40 * 3758691 * 2
def baseEnd_3758691 : Nat := 1286676743152439225251067

theorem tailTrace_3758691 : CollatzResearch.WordTrace tailWord_3758691 prefixEnd_3758691 1286676743152439225251067 := by
  unfold tailWord_3758691
  simp only [CollatzResearch.WordTrace]
  refine ⟨137090723225911915160987927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91393815483941276773991951 137090723225911915160987927)
  ·
    refine ⟨205636084838867872741481891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137090723225911915160987927 205636084838867872741481891)
    ·
      refine ⟨308454127258301809112222837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205636084838867872741481891 308454127258301809112222837)
      ·
        refine ⟨28917574430465794604270891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308454127258301809112222837 28917574430465794604270891)
        ·
          refine ⟨43376361645698691906406337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28917574430465794604270891 43376361645698691906406337)
          ·
            refine ⟨32532271234274018929804753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43376361645698691906406337 32532271234274018929804753)
            ·
              refine ⟨24399203425705514197353565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32532271234274018929804753 24399203425705514197353565)
              ·
                refine ⟨9149701284639567824007587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24399203425705514197353565 9149701284639567824007587)
                ·
                  refine ⟨13724551926959351736011381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149701284639567824007587 13724551926959351736011381)
                  ·
                    refine ⟨1286676743152439225251067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724551926959351736011381 1286676743152439225251067)
                    ·
                      rfl

theorem cell22_3758691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_3758691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758691 prefixEnd_3758691 := by exact prefixLift 3758691
  have htrace : WordTrace (prefixWord ++ tailWord_3758691) baseStart_3758691 baseEnd_3758691 := by
    simpa [prefixWord, tailWord_3758691, baseEnd_3758691] using wordTrace_append hprefix tailTrace_3758691
  have hstable : (prefixWord ++ tailWord_3758691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758691).length < 2 ^ (prefixWord ++ tailWord_3758691).sum := by decide
  have hdescent : baseEnd_3758691 < baseStart_3758691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758725 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_3758725 : Nat := 118140960795 + 3758725 * 2 ^ 59
def prefixEnd_3758725 : Nat := 4983230072969 + 3 ^ 40 * 3758725 * 2
def baseEnd_3758725 : Nat := 1286688382047274469900963

theorem tailTrace_3758725 : CollatzResearch.WordTrace tailWord_3758725 prefixEnd_3758725 1286688382047274469900963 := by
  unfold tailWord_3758725
  simp only [CollatzResearch.WordTrace]
  refine ⟨137091963307788738967725629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91394642205192492645150419 137091963307788738967725629)
  ·
    refine ⟨51409486240420777112897111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137091963307788738967725629 51409486240420777112897111)
    ·
      refine ⟨77114229360631165669345667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51409486240420777112897111 77114229360631165669345667)
      ·
        refine ⟨115671344040946748504018501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77114229360631165669345667 115671344040946748504018501)
        ·
          refine ⟨21688377007677515344503469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115671344040946748504018501 21688377007677515344503469)
          ·
            refine ⟨8133141377879068254188801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21688377007677515344503469 8133141377879068254188801)
            ·
              refine ⟨6099856033409301190641601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133141377879068254188801 6099856033409301190641601)
              ·
                refine ⟨4574892025056975892981201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099856033409301190641601 4574892025056975892981201)
                ·
                  refine ⟨3431169018792731919735901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574892025056975892981201 3431169018792731919735901)
                  ·
                    refine ⟨1286688382047274469900963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431169018792731919735901 1286688382047274469900963)
                    ·
                      rfl

theorem cell22_3758725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_3758725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758725 prefixEnd_3758725 := by exact prefixLift 3758725
  have htrace : WordTrace (prefixWord ++ tailWord_3758725) baseStart_3758725 baseEnd_3758725 := by
    simpa [prefixWord, tailWord_3758725, baseEnd_3758725] using wordTrace_append hprefix tailTrace_3758725
  have hstable : (prefixWord ++ tailWord_3758725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758725).length < 2 ^ (prefixWord ++ tailWord_3758725).sum := by decide
  have hdescent : baseEnd_3758725 < baseStart_3758725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758738 : List Nat := [3, 2, 3, 1, 2, 1, 3, 7]
def baseStart_3758738 : Nat := 118140960795 + 3758738 * 2 ^ 59
def prefixEnd_3758738 : Nat := 4983230072969 + 3 ^ 40 * 3758738 * 2
def baseEnd_3758738 : Nat := 142965870245882974369547

theorem tailTrace_3758738 : CollatzResearch.WordTrace tailWord_3758738 prefixEnd_3758738 142965870245882974369547 := by
  unfold tailWord_3758738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34273109364185410546987217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91394958304494428125299245 34273109364185410546987217)
  ·
    refine ⟨25704832023139057910240413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34273109364185410546987217 25704832023139057910240413)
    ·
      refine ⟨9639312008677146716340155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25704832023139057910240413 9639312008677146716340155)
      ·
        refine ⟨14458968013015720074510233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639312008677146716340155 14458968013015720074510233)
        ·
          refine ⟨10844226009761790055882675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14458968013015720074510233 10844226009761790055882675)
          ·
            refine ⟨16266339014642685083824013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844226009761790055882675 16266339014642685083824013)
            ·
              refine ⟨6099877130491006906434005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16266339014642685083824013 6099877130491006906434005)
              ·
                refine ⟨142965870245882974369547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6099877130491006906434005 142965870245882974369547)
                ·
                  rfl

theorem cell22_3758738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_3758738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758738 prefixEnd_3758738 := by exact prefixLift 3758738
  have htrace : WordTrace (prefixWord ++ tailWord_3758738) baseStart_3758738 baseEnd_3758738 := by
    simpa [prefixWord, tailWord_3758738, baseEnd_3758738] using wordTrace_append hprefix tailTrace_3758738
  have hstable : (prefixWord ++ tailWord_3758738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758738).length < 2 ^ (prefixWord ++ tailWord_3758738).sum := by decide
  have hdescent : baseEnd_3758738 < baseStart_3758738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758783 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 5]
def baseStart_3758783 : Nat := 118140960795 + 3758783 * 2 ^ 59
def prefixEnd_3758783 : Nat := 4983230072969 + 3 ^ 40 * 3758783 * 2
def baseEnd_3758783 : Nat := 428902745544193883983595

theorem tailTrace_3758783 : CollatzResearch.WordTrace tailWord_3758783 prefixEnd_3758783 428902745544193883983595 := by
  unfold tailWord_3758783
  simp only [CollatzResearch.WordTrace]
  refine ⟨137094078741578614873337003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91396052494385743248891335 137094078741578614873337003)
  ·
    refine ⟨205641118112367922310005505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137094078741578614873337003 205641118112367922310005505)
    ·
      refine ⟨154230838584275941732504129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205641118112367922310005505 154230838584275941732504129)
      ·
        refine ⟨115673128938206956299378097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154230838584275941732504129 115673128938206956299378097)
        ·
          refine ⟨86754846703655217224533573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115673128938206956299378097 86754846703655217224533573)
          ·
            refine ⟨16266533756935353229600045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86754846703655217224533573 16266533756935353229600045)
            ·
              refine ⟨6099950158850757461100017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16266533756935353229600045 6099950158850757461100017)
              ·
                refine ⟨4574962619138068095825013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6099950158850757461100017 4574962619138068095825013)
                ·
                  refine ⟨428902745544193883983595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4574962619138068095825013 428902745544193883983595)
                  ·
                    rfl

theorem cell22_3758783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].length) (baseStart_3758783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758783 prefixEnd_3758783 := by exact prefixLift 3758783
  have htrace : WordTrace (prefixWord ++ tailWord_3758783) baseStart_3758783 baseEnd_3758783 := by
    simpa [prefixWord, tailWord_3758783, baseEnd_3758783] using wordTrace_append hprefix tailTrace_3758783
  have hstable : (prefixWord ++ tailWord_3758783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758783).length < 2 ^ (prefixWord ++ tailWord_3758783).sum := by decide
  have hdescent : baseEnd_3758783 < baseStart_3758783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758798 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 2, 5]
def baseStart_3758798 : Nat := 118140960795 + 3758798 * 2 ^ 59
def prefixEnd_3758798 : Nat := 4983230072969 + 3 ^ 40 * 3758798 * 2
def baseEnd_3758798 : Nat := 1286713371439126612825739

theorem tailTrace_3758798 : CollatzResearch.WordTrace tailWord_3758798 prefixEnd_3758798 1286713371439126612825739 := by
  unfold tailWord_3758798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136828229565534054391631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91396417224349514956755365 17136828229565534054391631)
  ·
    refine ⟨25705242344348301081587447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17136828229565534054391631 25705242344348301081587447)
    ·
      refine ⟨38557863516522451622381171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25705242344348301081587447 38557863516522451622381171)
      ·
        refine ⟨57836795274783677433571757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38557863516522451622381171 57836795274783677433571757)
        ·
          refine ⟨21688798228043879037589409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57836795274783677433571757 21688798228043879037589409)
          ·
            refine ⟨16266598671032909278192057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21688798228043879037589409 16266598671032909278192057)
            ·
              refine ⟨12199949003274681958644043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16266598671032909278192057 12199949003274681958644043)
              ·
                refine ⟨18299923504912022937966065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12199949003274681958644043 18299923504912022937966065)
                ·
                  refine ⟨13724942628684017203474549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18299923504912022937966065 13724942628684017203474549)
                  ·
                    refine ⟨1286713371439126612825739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13724942628684017203474549 1286713371439126612825739)
                    ·
                      rfl

theorem cell22_3758798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_3758798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758798 prefixEnd_3758798 := by exact prefixLift 3758798
  have htrace : WordTrace (prefixWord ++ tailWord_3758798) baseStart_3758798 baseEnd_3758798 := by
    simpa [prefixWord, tailWord_3758798, baseEnd_3758798] using wordTrace_append hprefix tailTrace_3758798
  have hstable : (prefixWord ++ tailWord_3758798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758798).length < 2 ^ (prefixWord ++ tailWord_3758798).sum := by decide
  have hdescent : baseEnd_3758798 < baseStart_3758798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758830 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3758830 : Nat := 118140960795 + 3758830 * 2 ^ 59
def prefixEnd_3758830 : Nat := 4983230072969 + 3 ^ 40 * 3758830 * 2
def baseEnd_3758830 : Nat := 1286724325693089196025641

theorem tailTrace_3758830 : CollatzResearch.WordTrace tailWord_3758830 prefixEnd_3758830 1286724325693089196025641 := by
  unfold tailWord_3758830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136974121551042737537243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91397195314938894600198629 17136974121551042737537243)
  ·
    refine ⟨25705461182326564106305865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17136974121551042737537243 25705461182326564106305865)
    ·
      refine ⟨19279095886744923079729399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25705461182326564106305865 19279095886744923079729399)
      ·
        refine ⟨28918643830117384619594099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279095886744923079729399 28918643830117384619594099)
        ·
          refine ⟨43377965745176076929391149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918643830117384619594099 43377965745176076929391149)
          ·
            refine ⟨16266737154441028848521681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43377965745176076929391149 16266737154441028848521681)
            ·
              refine ⟨12200052865830771636391261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16266737154441028848521681 12200052865830771636391261)
              ·
                refine ⟨4575019824686539363646723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12200052865830771636391261 4575019824686539363646723)
                ·
                  refine ⟨6862529737029809045470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575019824686539363646723 6862529737029809045470085)
                  ·
                    refine ⟨1286724325693089196025641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862529737029809045470085 1286724325693089196025641)
                    ·
                      rfl

theorem cell22_3758830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3758830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758830 prefixEnd_3758830 := by exact prefixLift 3758830
  have htrace : WordTrace (prefixWord ++ tailWord_3758830) baseStart_3758830 baseEnd_3758830 := by
    simpa [prefixWord, tailWord_3758830, baseEnd_3758830] using wordTrace_append hprefix tailTrace_3758830
  have hstable : (prefixWord ++ tailWord_3758830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758830).length < 2 ^ (prefixWord ++ tailWord_3758830).sum := by decide
  have hdescent : baseEnd_3758830 < baseStart_3758830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758858 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_3758858 : Nat := 118140960795 + 3758858 * 2 ^ 59
def prefixEnd_3758858 : Nat := 4983230072969 + 3 ^ 40 * 3758858 * 2
def baseEnd_3758858 : Nat := 1286733910665306456325555

theorem tailTrace_3758858 : CollatzResearch.WordTrace tailWord_3758858 prefixEnd_3758858 1286733910665306456325555 := by
  unfold tailWord_3758858
  simp only [CollatzResearch.WordTrace]
  refine ⟨34274203554076725670579307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91397876144204601788211485 34274203554076725670579307)
  ·
    refine ⟨51411305331115088505868961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34274203554076725670579307 51411305331115088505868961)
    ·
      refine ⟨38558478998336316379401721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51411305331115088505868961 38558478998336316379401721)
      ·
        refine ⟨28918859248752237284551291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38558478998336316379401721 28918859248752237284551291)
        ·
          refine ⟨43378288873128355926826937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918859248752237284551291 43378288873128355926826937)
          ·
            refine ⟨32533716654846266945120203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43378288873128355926826937 32533716654846266945120203)
            ·
              refine ⟨48800574982269400417680305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32533716654846266945120203 48800574982269400417680305)
              ·
                refine ⟨36600431236702050313260229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48800574982269400417680305 36600431236702050313260229)
                ·
                  refine ⟨6862580856881634433736293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36600431236702050313260229 6862580856881634433736293)
                  ·
                    refine ⟨1286733910665306456325555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6862580856881634433736293 1286733910665306456325555)
                    ·
                      rfl

theorem cell22_3758858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_3758858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758858 prefixEnd_3758858 := by exact prefixLift 3758858
  have htrace : WordTrace (prefixWord ++ tailWord_3758858) baseStart_3758858 baseEnd_3758858 := by
    simpa [prefixWord, tailWord_3758858, baseEnd_3758858] using wordTrace_append hprefix tailTrace_3758858
  have hstable : (prefixWord ++ tailWord_3758858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758858).length < 2 ^ (prefixWord ++ tailWord_3758858).sum := by decide
  have hdescent : baseEnd_3758858 < baseStart_3758858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758877 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_3758877 : Nat := 118140960795 + 3758877 * 2 ^ 59
def prefixEnd_3758877 : Nat := 4983230072969 + 3 ^ 40 * 3758877 * 2
def baseEnd_3758877 : Nat := 1286740414753596740100497

theorem tailTrace_3758877 : CollatzResearch.WordTrace tailWord_3758877 prefixEnd_3758877 1286740414753596740100497 := by
  unfold tailWord_3758877
  simp only [CollatzResearch.WordTrace]
  refine ⟨137097507203238068927258885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91398338135492045951505923 137097507203238068927258885)
  ·
    refine ⟨25705782600607137923861041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137097507203238068927258885 25705782600607137923861041)
    ·
      refine ⟨19279336950455353442895781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25705782600607137923861041 19279336950455353442895781)
      ·
        refine ⟨3614875678210378770542959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19279336950455353442895781 3614875678210378770542959)
        ·
          refine ⟨5422313517315568155814439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614875678210378770542959 5422313517315568155814439)
          ·
            refine ⟨8133470275973352233721659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422313517315568155814439 8133470275973352233721659)
            ·
              refine ⟨12200205413960028350582489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133470275973352233721659 12200205413960028350582489)
              ·
                refine ⟨9150154060470021262936867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12200205413960028350582489 9150154060470021262936867)
                ·
                  refine ⟨13725231090705031894405301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150154060470021262936867 13725231090705031894405301)
                  ·
                    refine ⟨1286740414753596740100497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13725231090705031894405301 1286740414753596740100497)
                    ·
                      rfl

theorem cell22_3758877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_3758877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758877 prefixEnd_3758877 := by exact prefixLift 3758877
  have htrace : WordTrace (prefixWord ++ tailWord_3758877) baseStart_3758877 baseEnd_3758877 := by
    simpa [prefixWord, tailWord_3758877, baseEnd_3758877] using wordTrace_append hprefix tailTrace_3758877
  have hstable : (prefixWord ++ tailWord_3758877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758877).length < 2 ^ (prefixWord ++ tailWord_3758877).sum := by decide
  have hdescent : baseEnd_3758877 < baseStart_3758877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758890 : List Nat := [3, 1, 4, 3, 1, 10]
def baseStart_3758890 : Nat := 118140960795 + 3758890 * 2 ^ 59
def prefixEnd_3758890 : Nat := 4983230072969 + 3 ^ 40 * 3758890 * 2
def baseEnd_3758890 : Nat := 15885739073077395549697

theorem tailTrace_3758890 : CollatzResearch.WordTrace tailWord_3758890 prefixEnd_3758890 15885739073077395549697 := by
  unfold tailWord_3758890
  simp only [CollatzResearch.WordTrace]
  refine ⟨34274495338047743036870531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91398654234793981431654749 34274495338047743036870531)
  ·
    refine ⟨51411743007071614555305797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34274495338047743036870531 51411743007071614555305797)
    ·
      refine ⟨9639701813825927729119837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51411743007071614555305797 9639701813825927729119837)
      ·
        refine ⟨3614888180184722898419939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9639701813825927729119837 3614888180184722898419939)
        ·
          refine ⟨5422332270277084347629909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614888180184722898419939 5422332270277084347629909)
          ·
            refine ⟨15885739073077395549697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5422332270277084347629909 15885739073077395549697)
            ·
              rfl

theorem cell22_3758890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 10].length) (baseStart_3758890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758890 prefixEnd_3758890 := by exact prefixLift 3758890
  have htrace : WordTrace (prefixWord ++ tailWord_3758890) baseStart_3758890 baseEnd_3758890 := by
    simpa [prefixWord, tailWord_3758890, baseEnd_3758890] using wordTrace_append hprefix tailTrace_3758890
  have hstable : (prefixWord ++ tailWord_3758890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758890).length < 2 ^ (prefixWord ++ tailWord_3758890).sum := by decide
  have hdescent : baseEnd_3758890 < baseStart_3758890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758894 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3758894 : Nat := 118140960795 + 3758894 * 2 ^ 59
def prefixEnd_3758894 : Nat := 4983230072969 + 3 ^ 40 * 3758894 * 2
def baseEnd_3758894 : Nat := 1286746234201014362425445

theorem tailTrace_3758894 : CollatzResearch.WordTrace tailWord_3758894 prefixEnd_3758894 1286746234201014362425445 := by
  unfold tailWord_3758894
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137265905522060103828467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91398751496117653887085157 17137265905522060103828467)
  ·
    refine ⟨25705898858283090155742701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17137265905522060103828467 25705898858283090155742701)
    ·
      refine ⟨9639712071856158808403513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25705898858283090155742701 9639712071856158808403513)
      ·
        refine ⟨7229784053892119106302635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9639712071856158808403513 7229784053892119106302635)
        ·
          refine ⟨10844676080838178659453953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229784053892119106302635 10844676080838178659453953)
          ·
            refine ⟨8133507060628633994590465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10844676080838178659453953 8133507060628633994590465)
            ·
              refine ⟨6100130295471475495942849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8133507060628633994590465 6100130295471475495942849)
              ·
                refine ⟨4575097721603606621957137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6100130295471475495942849 4575097721603606621957137)
                ·
                  refine ⟨3431323291202704966467853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575097721603606621957137 3431323291202704966467853)
                  ·
                    refine ⟨1286746234201014362425445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431323291202704966467853 1286746234201014362425445)
                    ·
                      rfl

theorem cell22_3758894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3758894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758894 prefixEnd_3758894 := by exact prefixLift 3758894
  have htrace : WordTrace (prefixWord ++ tailWord_3758894) baseStart_3758894 baseEnd_3758894 := by
    simpa [prefixWord, tailWord_3758894, baseEnd_3758894] using wordTrace_append hprefix tailTrace_3758894
  have hstable : (prefixWord ++ tailWord_3758894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758894).length < 2 ^ (prefixWord ++ tailWord_3758894).sum := by decide
  have hdescent : baseEnd_3758894 < baseStart_3758894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758933 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3758933 : Nat := 118140960795 + 3758933 * 2 ^ 59
def prefixEnd_3758933 : Nat := 4983230072969 + 3 ^ 40 * 3758933 * 2
def baseEnd_3758933 : Nat := 1286759584698031260700325

theorem tailTrace_3758933 : CollatzResearch.WordTrace tailWord_3758933 prefixEnd_3758933 1286759584698031260700325 := by
  unfold tailWord_3758933
  simp only [CollatzResearch.WordTrace]
  refine ⟨137099549691035190491297453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91399699794023460327531635 137099549691035190491297453)
  ·
    refine ⟨51412331134138196434236545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137099549691035190491297453 51412331134138196434236545)
    ·
      refine ⟨38559248350603647325677409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51412331134138196434236545 38559248350603647325677409)
      ·
        refine ⟨28919436262952735494258057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38559248350603647325677409 28919436262952735494258057)
        ·
          refine ⟨21689577197214551620693543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28919436262952735494258057 21689577197214551620693543)
          ·
            refine ⟨32534365795821827431040315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21689577197214551620693543 32534365795821827431040315)
            ·
              refine ⟨48801548693732741146560473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32534365795821827431040315 48801548693732741146560473)
              ·
                refine ⟨36601161520299555859920355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48801548693732741146560473 36601161520299555859920355)
                ·
                  refine ⟨54901742280449333789880533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36601161520299555859920355 54901742280449333789880533)
                  ·
                    refine ⟨1286759584698031260700325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54901742280449333789880533 1286759584698031260700325)
                    ·
                      rfl

theorem cell22_3758933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3758933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758933 prefixEnd_3758933 := by exact prefixLift 3758933
  have htrace : WordTrace (prefixWord ++ tailWord_3758933) baseStart_3758933 baseEnd_3758933 := by
    simpa [prefixWord, tailWord_3758933, baseEnd_3758933] using wordTrace_append hprefix tailTrace_3758933
  have hstable : (prefixWord ++ tailWord_3758933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758933).length < 2 ^ (prefixWord ++ tailWord_3758933).sum := by decide
  have hdescent : baseEnd_3758933 < baseStart_3758933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758952 : List Nat := [2, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_3758952 : Nat := 118140960795 + 3758952 * 2 ^ 59
def prefixEnd_3758952 : Nat := 4983230072969 + 3 ^ 40 * 3758952 * 2
def baseEnd_3758952 : Nat := 428922029595440514825089

theorem tailTrace_3758952 : CollatzResearch.WordTrace tailWord_3758952 prefixEnd_3758952 428922029595440514825089 := by
  unfold tailWord_3758952
  simp only [CollatzResearch.WordTrace]
  refine ⟨68550121338983178368119555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91400161785310904490826073 68550121338983178368119555)
  ·
    refine ⟨102825182008474767552179333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68550121338983178368119555 102825182008474767552179333)
    ·
      refine ⟨19279721626589018916033625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102825182008474767552179333 19279721626589018916033625)
      ·
        refine ⟨14459791219941764187025219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19279721626589018916033625 14459791219941764187025219)
        ·
          refine ⟨21689686829912646280537829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459791219941764187025219 21689686829912646280537829)
          ·
            refine ⟨4066816280608621177600843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21689686829912646280537829 4066816280608621177600843)
            ·
              refine ⟨6100224420912931766401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066816280608621177600843 6100224420912931766401265)
              ·
                refine ⟨4575168315684698824800949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6100224420912931766401265 4575168315684698824800949)
                ·
                  refine ⟨428922029595440514825089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4575168315684698824800949 428922029595440514825089)
                  ·
                    rfl

theorem cell22_3758952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_3758952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758952 prefixEnd_3758952 := by exact prefixLift 3758952
  have htrace : WordTrace (prefixWord ++ tailWord_3758952) baseStart_3758952 baseEnd_3758952 := by
    simpa [prefixWord, tailWord_3758952, baseEnd_3758952] using wordTrace_append hprefix tailTrace_3758952
  have hstable : (prefixWord ++ tailWord_3758952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758952).length < 2 ^ (prefixWord ++ tailWord_3758952).sum := by decide
  have hdescent : baseEnd_3758952 < baseStart_3758952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758963 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 6]
def baseStart_3758963 : Nat := 118140960795 + 3758963 * 2 ^ 59
def prefixEnd_3758963 : Nat := 4983230072969 + 3 ^ 40 * 3758963 * 2
def baseEnd_3758963 : Nat := 428923284770373727483411

theorem tailTrace_3758963 : CollatzResearch.WordTrace tailWord_3758963 prefixEnd_3758963 428923284770373727483411 := by
  unfold tailWord_3758963
  simp only [CollatzResearch.WordTrace]
  refine ⟨137100643880926505614889543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91400429253951003743259695 137100643880926505614889543)
  ·
    refine ⟨205650965821389758422334315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137100643880926505614889543 205650965821389758422334315)
    ·
      refine ⟨308476448732084637633501473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205650965821389758422334315 308476448732084637633501473)
      ·
        refine ⟨231357336549063478225126105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308476448732084637633501473 231357336549063478225126105)
        ·
          refine ⟨173518002411797608668844579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231357336549063478225126105 173518002411797608668844579)
          ·
            refine ⟨260277003617696413003266869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173518002411797608668844579 260277003617696413003266869)
            ·
              refine ⟨24400969089159038719056269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260277003617696413003266869 24400969089159038719056269)
              ·
                refine ⟨9150363408434639519646101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24400969089159038719056269 9150363408434639519646101)
                ·
                  refine ⟨428923284770373727483411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9150363408434639519646101 428923284770373727483411)
                  ·
                    rfl

theorem cell22_3758963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_3758963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758963 prefixEnd_3758963 := by exact prefixLift 3758963
  have htrace : WordTrace (prefixWord ++ tailWord_3758963) baseStart_3758963 baseEnd_3758963 := by
    simpa [prefixWord, tailWord_3758963, baseEnd_3758963] using wordTrace_append hprefix tailTrace_3758963
  have hstable : (prefixWord ++ tailWord_3758963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758963).length < 2 ^ (prefixWord ++ tailWord_3758963).sum := by decide
  have hdescent : baseEnd_3758963 < baseStart_3758963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3758997 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 4]
def baseStart_3758997 : Nat := 118140960795 + 3758997 * 2 ^ 59
def prefixEnd_3758997 : Nat := 4983230072969 + 3 ^ 40 * 3758997 * 2
def baseEnd_3758997 : Nat := 428927164401985475700043

theorem tailTrace_3758997 : CollatzResearch.WordTrace tailWord_3758997 prefixEnd_3758997 428927164401985475700043 := by
  unfold tailWord_3758997
  simp only [CollatzResearch.WordTrace]
  refine ⟨137101883962803329421627245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91401255975202219614418163 137101883962803329421627245)
  ·
    refine ⟨51413206486051248533110217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137101883962803329421627245 51413206486051248533110217)
    ·
      refine ⟨38559904864538436399832663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51413206486051248533110217 38559904864538436399832663)
      ·
        refine ⟨57839857296807654599748995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38559904864538436399832663 57839857296807654599748995)
        ·
          refine ⟨86759785945211481899623493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57839857296807654599748995 86759785945211481899623493)
          ·
            refine ⟨16267459864727152856179405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86759785945211481899623493 16267459864727152856179405)
            ·
              refine ⟨6100297449272682321067277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16267459864727152856179405 6100297449272682321067277)
              ·
                refine ⟨2287611543477255870400229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100297449272682321067277 2287611543477255870400229)
                ·
                  refine ⟨428927164401985475700043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287611543477255870400229 428927164401985475700043)
                  ·
                    rfl

theorem cell22_3758997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_3758997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3758997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3758997 prefixEnd_3758997 := by exact prefixLift 3758997
  have htrace : WordTrace (prefixWord ++ tailWord_3758997) baseStart_3758997 baseEnd_3758997 := by
    simpa [prefixWord, tailWord_3758997, baseEnd_3758997] using wordTrace_append hprefix tailTrace_3758997
  have hstable : (prefixWord ++ tailWord_3758997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3758997).length < 2 ^ (prefixWord ++ tailWord_3758997).sum := by decide
  have hdescent : baseEnd_3758997 < baseStart_3758997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3758997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759008 : List Nat := [2, 1, 1, 4, 1, 1, 12]
def baseStart_3759008 : Nat := 118140960795 + 3759008 * 2 ^ 59
def prefixEnd_3759008 : Nat := 4983230072969 + 3 ^ 40 * 3759008 * 2
def baseEnd_3759008 : Nat := 47658713286324298706485

theorem tailTrace_3759008 : CollatzResearch.WordTrace tailWord_3759008 prefixEnd_3759008 47658713286324298706485 := by
  unfold tailWord_3759008
  simp only [CollatzResearch.WordTrace]
  refine ⟨68551142582881739150138839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91401523443842318866851785 68551142582881739150138839)
  ·
    refine ⟨102826713874322608725208259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68551142582881739150138839 102826713874322608725208259)
    ·
      refine ⟨154240070811483913087812389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102826713874322608725208259 154240070811483913087812389)
      ·
        refine ⟨28920013277153233703964823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154240070811483913087812389 28920013277153233703964823)
        ·
          refine ⟨43380019915729850555947235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920013277153233703964823 43380019915729850555947235)
          ·
            refine ⟨65070029873594775833920853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43380019915729850555947235 65070029873594775833920853)
            ·
              refine ⟨47658713286324298706485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 65070029873594775833920853 47658713286324298706485)
              ·
                rfl

theorem cell22_3759008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 12].length) (baseStart_3759008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759008 prefixEnd_3759008 := by exact prefixLift 3759008
  have htrace : WordTrace (prefixWord ++ tailWord_3759008) baseStart_3759008 baseEnd_3759008 := by
    simpa [prefixWord, tailWord_3759008, baseEnd_3759008] using wordTrace_append hprefix tailTrace_3759008
  have hstable : (prefixWord ++ tailWord_3759008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759008).length < 2 ^ (prefixWord ++ tailWord_3759008).sum := by decide
  have hdescent : baseEnd_3759008 < baseStart_3759008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759012 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_3759012 : Nat := 118140960795 + 3759012 * 2 ^ 59
def prefixEnd_3759012 : Nat := 4983230072969 + 3 ^ 40 * 3759012 * 2
def baseEnd_3759012 : Nat := 1286786628012501387975083

theorem tailTrace_3759012 : CollatzResearch.WordTrace tailWord_3759012 prefixEnd_3759012 1286786628012501387975083 := by
  unfold tailWord_3759012
  simp only [CollatzResearch.WordTrace]
  refine ⟨68551215528874493491711645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91401620705165991322282193 68551215528874493491711645)
  ·
    refine ⟨25706705823327935059391867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68551215528874493491711645 25706705823327935059391867)
    ·
      refine ⟨38560058734991902589087801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25706705823327935059391867 38560058734991902589087801)
      ·
        refine ⟨28920044051243926941815851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38560058734991902589087801 28920044051243926941815851)
        ·
          refine ⟨43380066076865890412723777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28920044051243926941815851 43380066076865890412723777)
          ·
            refine ⟨32535049557649417809542833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43380066076865890412723777 32535049557649417809542833)
            ·
              refine ⟨24401287168237063357157125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32535049557649417809542833 24401287168237063357157125)
              ·
                refine ⟨4575241344044449379466961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24401287168237063357157125 4575241344044449379466961)
                ·
                  refine ⟨3431431008033337034600221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575241344044449379466961 3431431008033337034600221)
                  ·
                    refine ⟨1286786628012501387975083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431431008033337034600221 1286786628012501387975083)
                    ·
                      rfl

theorem cell22_3759012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_3759012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759012 prefixEnd_3759012 := by exact prefixLift 3759012
  have htrace : WordTrace (prefixWord ++ tailWord_3759012) baseStart_3759012 baseEnd_3759012 := by
    simpa [prefixWord, tailWord_3759012, baseEnd_3759012] using wordTrace_append hprefix tailTrace_3759012
  have hstable : (prefixWord ++ tailWord_3759012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759012).length < 2 ^ (prefixWord ++ tailWord_3759012).sum := by decide
  have hdescent : baseEnd_3759012 < baseStart_3759012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_3759023 : Nat := 118140960795 + 3759023 * 2 ^ 59
def prefixEnd_3759023 : Nat := 4983230072969 + 3 ^ 40 * 3759023 * 2
def baseEnd_3759023 : Nat := 1286790393537301025950049

theorem tailTrace_3759023 : CollatzResearch.WordTrace tailWord_3759023 prefixEnd_3759023 1286790393537301025950049 := by
  unfold tailWord_3759023
  simp only [CollatzResearch.WordTrace]
  refine ⟨137102832260709135862073723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91401888173806090574715815 137102832260709135862073723)
  ·
    refine ⟨205654248391063703793110585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137102832260709135862073723 205654248391063703793110585)
    ·
      refine ⟨154240686293297777844832939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205654248391063703793110585 154240686293297777844832939)
      ·
        refine ⟨231361029439946666767249409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154240686293297777844832939 231361029439946666767249409)
        ·
          refine ⟨173520772079960000075437057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231361029439946666767249409 173520772079960000075437057)
          ·
            refine ⟨130140579059970000056577793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173520772079960000075437057 130140579059970000056577793)
            ·
              refine ⟨97605434294977500042433345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130140579059970000056577793 97605434294977500042433345)
              ·
                refine ⟨73204075721233125031825009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97605434294977500042433345 73204075721233125031825009)
                ·
                  refine ⟨54903056790924843773868757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73204075721233125031825009 54903056790924843773868757)
                  ·
                    refine ⟨1286790393537301025950049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54903056790924843773868757 1286790393537301025950049)
                    ·
                      rfl

theorem cell22_3759023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_3759023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759023 prefixEnd_3759023 := by exact prefixLift 3759023
  have htrace : WordTrace (prefixWord ++ tailWord_3759023) baseStart_3759023 baseEnd_3759023 := by
    simpa [prefixWord, tailWord_3759023, baseEnd_3759023] using wordTrace_append hprefix tailTrace_3759023
  have hstable : (prefixWord ++ tailWord_3759023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759023).length < 2 ^ (prefixWord ++ tailWord_3759023).sum := by decide
  have hdescent : baseEnd_3759023 < baseStart_3759023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759166 : List Nat := [4, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3759166 : Nat := 118140960795 + 3759166 * 2 ^ 59
def prefixEnd_3759166 : Nat := 4983230072969 + 3 ^ 40 * 3759166 * 2
def baseEnd_3759166 : Nat := 428946448453232106541537

theorem tailTrace_3759166 : CollatzResearch.WordTrace tailWord_3759166 prefixEnd_3759166 428946448453232106541537 := by
  unfold tailWord_3759166
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138505987398883910566169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91405365266127380856352901 17138505987398883910566169)
  ·
    refine ⟨12853879490549162932924627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17138505987398883910566169 12853879490549162932924627)
    ·
      refine ⟨19280819235823744399386941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853879490549162932924627 19280819235823744399386941)
      ·
        refine ⟨7230307213433904149770103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19280819235823744399386941 7230307213433904149770103)
        ·
          refine ⟨10845460820150856224655155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230307213433904149770103 10845460820150856224655155)
          ·
            refine ⟨16268191230226284336982733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845460820150856224655155 16268191230226284336982733)
            ·
              refine ⟨6100571711334856626368525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16268191230226284336982733 6100571711334856626368525)
              ·
                refine ⟨2287714391750571234888197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100571711334856626368525 2287714391750571234888197)
                ·
                  refine ⟨428946448453232106541537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287714391750571234888197 428946448453232106541537)
                  ·
                    rfl

theorem cell22_3759166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3759166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759166 prefixEnd_3759166 := by exact prefixLift 3759166
  have htrace : WordTrace (prefixWord ++ tailWord_3759166) baseStart_3759166 baseEnd_3759166 := by
    simpa [prefixWord, tailWord_3759166, baseEnd_3759166] using wordTrace_append hprefix tailTrace_3759166
  have hstable : (prefixWord ++ tailWord_3759166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759166).length < 2 ^ (prefixWord ++ tailWord_3759166).sum := by decide
  have hdescent : baseEnd_3759166 < baseStart_3759166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759299 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 2, 3]
def baseStart_3759299 : Nat := 118140960795 + 3759299 * 2 ^ 59
def prefixEnd_3759299 : Nat := 4983230072969 + 3 ^ 40 * 3759299 * 2
def baseEnd_3759299 : Nat := 1286884873977728306049203

theorem tailTrace_3759299 : CollatzResearch.WordTrace tailWord_3759299 prefixEnd_3759299 1286884873977728306049203 := by
  unfold tailWord_3759299
  simp only [CollatzResearch.WordTrace]
  refine ⟨137112898807709234999120951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91408599205139489999413967 137112898807709234999120951)
  ·
    refine ⟨205669348211563852498681427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137112898807709234999120951 205669348211563852498681427)
    ·
      refine ⟨308504022317345778748022141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205669348211563852498681427 308504022317345778748022141)
      ·
        refine ⟨115689008369004667030508303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308504022317345778748022141 115689008369004667030508303)
        ·
          refine ⟨173533512553507000545762455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115689008369004667030508303 173533512553507000545762455)
          ·
            refine ⟨260300268830260500818643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173533512553507000545762455 260300268830260500818643683)
            ·
              refine ⟨390450403245390751227965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260300268830260500818643683 390450403245390751227965525)
              ·
                refine ⟨4575590663031922865952721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 390450403245390751227965525 4575590663031922865952721)
                ·
                  refine ⟨3431692997273942149464541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575590663031922865952721 3431692997273942149464541)
                  ·
                    refine ⟨1286884873977728306049203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431692997273942149464541 1286884873977728306049203)
                    ·
                      rfl

theorem cell22_3759299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].length) (baseStart_3759299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759299 prefixEnd_3759299 := by exact prefixLift 3759299
  have htrace : WordTrace (prefixWord ++ tailWord_3759299) baseStart_3759299 baseEnd_3759299 := by
    simpa [prefixWord, tailWord_3759299, baseEnd_3759299] using wordTrace_append hprefix tailTrace_3759299
  have hstable : (prefixWord ++ tailWord_3759299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759299).length < 2 ^ (prefixWord ++ tailWord_3759299).sum := by decide
  have hdescent : baseEnd_3759299 < baseStart_3759299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759329 : List Nat := [1, 2, 3, 1, 3, 2, 4, 6]
def baseStart_3759329 : Nat := 118140960795 + 3759329 * 2 ^ 59
def prefixEnd_3759329 : Nat := 4983230072969 + 3 ^ 40 * 3759329 * 2
def baseEnd_3759329 : Nat := 142988349287868691977679

theorem tailTrace_3759329 : CollatzResearch.WordTrace tailWord_3759329 prefixEnd_3759329 142988349287868691977679 := by
  unfold tailWord_3759329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137113992997600550122713041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91409328665067033415142027 137113992997600550122713041)
  ·
    refine ⟨102835494748200412592034781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137113992997600550122713041 102835494748200412592034781)
    ·
      refine ⟨38563310530575154722013043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102835494748200412592034781 38563310530575154722013043)
      ·
        refine ⟨57844965795862732083019565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38563310530575154722013043 57844965795862732083019565)
        ·
          refine ⟨21691862173448524531132337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57844965795862732083019565 21691862173448524531132337)
          ·
            refine ⟨16268896630086393398349253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21691862173448524531132337 16268896630086393398349253)
            ·
              refine ⟨3050418118141198762190485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16268896630086393398349253 3050418118141198762190485)
              ·
                refine ⟨142988349287868691977679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3050418118141198762190485 142988349287868691977679)
                ·
                  rfl

theorem cell22_3759329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 6].length) (baseStart_3759329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759329 prefixEnd_3759329 := by exact prefixLift 3759329
  have htrace : WordTrace (prefixWord ++ tailWord_3759329) baseStart_3759329 baseEnd_3759329 := by
    simpa [prefixWord, tailWord_3759329, baseEnd_3759329] using wordTrace_append hprefix tailTrace_3759329
  have hstable : (prefixWord ++ tailWord_3759329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759329).length < 2 ^ (prefixWord ++ tailWord_3759329).sum := by decide
  have hdescent : baseEnd_3759329 < baseStart_3759329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759335 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 4]
def baseStart_3759335 : Nat := 118140960795 + 3759335 * 2 ^ 59
def prefixEnd_3759335 : Nat := 4983230072969 + 3 ^ 40 * 3759335 * 2
def baseEnd_3759335 : Nat := 428965732504478737383031

theorem tailTrace_3759335 : CollatzResearch.WordTrace tailWord_3759335 prefixEnd_3759335 428965732504478737383031 := by
  unfold tailWord_3759335
  simp only [CollatzResearch.WordTrace]
  refine ⟨137114211835578813147431459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91409474557052542098287639 137114211835578813147431459)
  ·
    refine ⟨205671317753368219721147189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137114211835578813147431459 205671317753368219721147189)
    ·
      refine ⟨19281686039378270598857549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205671317753368219721147189 19281686039378270598857549)
      ·
        refine ⟨7230632264766851474571581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19281686039378270598857549 7230632264766851474571581)
        ·
          refine ⟨2711487099287569302964343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7230632264766851474571581 2711487099287569302964343)
          ·
            refine ⟨4067230648931353954446515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711487099287569302964343 4067230648931353954446515)
            ·
              refine ⟨6100845973397030931669773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067230648931353954446515 6100845973397030931669773)
              ·
                refine ⟨2287817240023886599376165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100845973397030931669773 2287817240023886599376165)
                ·
                  refine ⟨428965732504478737383031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287817240023886599376165 428965732504478737383031)
                  ·
                    rfl

theorem cell22_3759335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 4].length) (baseStart_3759335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759335 prefixEnd_3759335 := by exact prefixLift 3759335
  have htrace : WordTrace (prefixWord ++ tailWord_3759335) baseStart_3759335 baseEnd_3759335 := by
    simpa [prefixWord, tailWord_3759335, baseEnd_3759335] using wordTrace_append hprefix tailTrace_3759335
  have hstable : (prefixWord ++ tailWord_3759335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759335).length < 2 ^ (prefixWord ++ tailWord_3759335).sum := by decide
  have hdescent : baseEnd_3759335 < baseStart_3759335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759346 : List Nat := [3, 2, 1, 3, 4, 1, 8]
def baseStart_3759346 : Nat := 118140960795 + 3759346 * 2 ^ 59
def prefixEnd_3759346 : Nat := 4983230072969 + 3 ^ 40 * 3759346 * 2
def baseEnd_3759346 : Nat := 47662998631045772226817

theorem tailTrace_3759346 : CollatzResearch.WordTrace tailWord_3759346 prefixEnd_3759346 47662998631045772226817 := by
  unfold tailWord_3759346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34278653259634740506520473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91409742025692641350721261 34278653259634740506520473)
  ·
    refine ⟨25708989944726055379890355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34278653259634740506520473 25708989944726055379890355)
    ·
      refine ⟨38563484917089083069835533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25708989944726055379890355 38563484917089083069835533)
      ·
        refine ⟨14461306843908406151188325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38563484917089083069835533 14461306843908406151188325)
        ·
          refine ⟨2711495033232826153347811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14461306843908406151188325 2711495033232826153347811)
          ·
            refine ⟨4067242549849239230021717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711495033232826153347811 4067242549849239230021717)
            ·
              refine ⟨47662998631045772226817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4067242549849239230021717 47662998631045772226817)
              ·
                rfl

theorem cell22_3759346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 8].length) (baseStart_3759346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759346 prefixEnd_3759346 := by exact prefixLift 3759346
  have htrace : WordTrace (prefixWord ++ tailWord_3759346) baseStart_3759346 baseEnd_3759346 := by
    simpa [prefixWord, tailWord_3759346, baseEnd_3759346] using wordTrace_append hprefix tailTrace_3759346
  have hstable : (prefixWord ++ tailWord_3759346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759346).length < 2 ^ (prefixWord ++ tailWord_3759346).sum := by decide
  have hdescent : baseEnd_3759346 < baseStart_3759346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759361 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_3759361 : Nat := 118140960795 + 3759361 * 2 ^ 59
def prefixEnd_3759361 : Nat := 4983230072969 + 3 ^ 40 * 3759361 * 2
def baseEnd_3759361 : Nat := 1286906097844780810999013

theorem tailTrace_3759361 : CollatzResearch.WordTrace tailWord_3759361 prefixEnd_3759361 1286906097844780810999013 := by
  unfold tailWord_3759361
  simp only [CollatzResearch.WordTrace]
  refine ⟨137115160133484619587877937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91410106755656413058585291 137115160133484619587877937)
  ·
    refine ⟨102836370100113464690908453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137115160133484619587877937 102836370100113464690908453)
    ·
      refine ⟨19281819393771274629545335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102836370100113464690908453 19281819393771274629545335)
      ·
        refine ⟨28922729090656911944318003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19281819393771274629545335 28922729090656911944318003)
        ·
          refine ⟨43384093635985367916477005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28922729090656911944318003 43384093635985367916477005)
          ·
            refine ⟨16269035113494512968678877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43384093635985367916477005 16269035113494512968678877)
            ·
              refine ⟨6100888167560442363254579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16269035113494512968678877 6100888167560442363254579)
              ·
                refine ⟨9151332251340663544881869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100888167560442363254579 9151332251340663544881869)
                ·
                  refine ⟨3431749594252748829330701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9151332251340663544881869 3431749594252748829330701)
                  ·
                    refine ⟨1286906097844780810999013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431749594252748829330701 1286906097844780810999013)
                    ·
                      rfl

theorem cell22_3759361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_3759361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759361 prefixEnd_3759361 := by exact prefixLift 3759361
  have htrace : WordTrace (prefixWord ++ tailWord_3759361) baseStart_3759361 baseEnd_3759361 := by
    simpa [prefixWord, tailWord_3759361, baseEnd_3759361] using wordTrace_append hprefix tailTrace_3759361
  have hstable : (prefixWord ++ tailWord_3759361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759361).length < 2 ^ (prefixWord ++ tailWord_3759361).sum := by decide
  have hdescent : baseEnd_3759361 < baseStart_3759361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759446 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3759446 : Nat := 118140960795 + 3759446 * 2 ^ 59
def prefixEnd_3759446 : Nat := 4983230072969 + 3 ^ 40 * 3759446 * 2
def baseEnd_3759446 : Nat := 1286935195081868922623753

theorem tailTrace_3759446 : CollatzResearch.WordTrace tailWord_3759446 prefixEnd_3759446 1286935195081868922623753 := by
  unfold tailWord_3759446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569891271136042444045137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91412173558784452736481461 8569891271136042444045137)
  ·
    refine ⟨6427418453352031833033853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8569891271136042444045137 6427418453352031833033853)
    ·
      refine ⟨2410281920007011937387695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6427418453352031833033853 2410281920007011937387695)
      ·
        refine ⟨3615422880010517906081543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410281920007011937387695 3615422880010517906081543)
        ·
          refine ⟨5423134320015776859122315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615422880010517906081543 5423134320015776859122315)
          ·
            refine ⟨8134701480023665288683473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423134320015776859122315 8134701480023665288683473)
            ·
              refine ⟨6101026110017748966512605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8134701480023665288683473 6101026110017748966512605)
              ·
                refine ⟨2287884791256655862442227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6101026110017748966512605 2287884791256655862442227)
                ·
                  refine ⟨3431827186884983793663341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287884791256655862442227 3431827186884983793663341)
                  ·
                    refine ⟨1286935195081868922623753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431827186884983793663341 1286935195081868922623753)
                    ·
                      rfl

theorem cell22_3759446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3759446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759446 prefixEnd_3759446 := by exact prefixLift 3759446
  have htrace : WordTrace (prefixWord ++ tailWord_3759446) baseStart_3759446 baseEnd_3759446 := by
    simpa [prefixWord, tailWord_3759446, baseEnd_3759446] using wordTrace_append hprefix tailTrace_3759446
  have hstable : (prefixWord ++ tailWord_3759446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759446).length < 2 ^ (prefixWord ++ tailWord_3759446).sum := by decide
  have hdescent : baseEnd_3759446 < baseStart_3759446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759468 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_3759468 : Nat := 118140960795 + 3759468 * 2 ^ 59
def prefixEnd_3759468 : Nat := 4983230072969 + 3 ^ 40 * 3759468 * 2
def baseEnd_3759468 : Nat := 1286942726131468198573685

theorem tailTrace_3759468 : CollatzResearch.WordTrace tailWord_3759468 prefixEnd_3759468 1286942726131468198573685 := by
  unfold tailWord_3759468
  simp only [CollatzResearch.WordTrace]
  refine ⟨68559531372048488431011529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91412708496064651241348705 68559531372048488431011529)
  ·
    refine ⟨51419648529036366323258647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68559531372048488431011529 51419648529036366323258647)
    ·
      refine ⟨77129472793554549484887971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51419648529036366323258647 77129472793554549484887971)
      ·
        refine ⟨115694209190331824227331957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77129472793554549484887971 115694209190331824227331957)
        ·
          refine ⟨10846332111593608521312371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115694209190331824227331957 10846332111593608521312371)
          ·
            refine ⟨16269498167390412781968557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10846332111593608521312371 16269498167390412781968557)
            ·
              refine ⟨6101061812771404793238209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16269498167390412781968557 6101061812771404793238209)
              ·
                refine ⟨4575796359578553594928657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6101061812771404793238209 4575796359578553594928657)
                ·
                  refine ⟨3431847269683915196196493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575796359578553594928657 3431847269683915196196493)
                  ·
                    refine ⟨1286942726131468198573685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431847269683915196196493 1286942726131468198573685)
                    ·
                      rfl

theorem cell22_3759468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_3759468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759468 prefixEnd_3759468 := by exact prefixLift 3759468
  have htrace : WordTrace (prefixWord ++ tailWord_3759468) baseStart_3759468 baseEnd_3759468 := by
    simpa [prefixWord, tailWord_3759468, baseEnd_3759468] using wordTrace_append hprefix tailTrace_3759468
  have hstable : (prefixWord ++ tailWord_3759468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759468).length < 2 ^ (prefixWord ++ tailWord_3759468).sum := by decide
  have hdescent : baseEnd_3759468 < baseStart_3759468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759509 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 7]
def baseStart_3759509 : Nat := 118140960795 + 3759509 * 2 ^ 59
def prefixEnd_3759509 : Nat := 4983230072969 + 3 ^ 40 * 3759509 * 2
def baseEnd_3759509 : Nat := 428985587089785919432853

theorem tailTrace_3759509 : CollatzResearch.WordTrace tailWord_3759509 prefixEnd_3759509 428985587089785919432853 := by
  unfold tailWord_3759509
  simp only [CollatzResearch.WordTrace]
  refine ⟨137120558136948440864265581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91413705424632293909510387 137120558136948440864265581)
  ·
    refine ⟨51420209301355665324099593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137120558136948440864265581 51420209301355665324099593)
    ·
      refine ⟨38565156976016748993074695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51420209301355665324099593 38565156976016748993074695)
      ·
        refine ⟨57847735464025123489612043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38565156976016748993074695 57847735464025123489612043)
        ·
          refine ⟨86771603196037685234418065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57847735464025123489612043 86771603196037685234418065)
          ·
            refine ⟨65078702397028263925813549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86771603196037685234418065 65078702397028263925813549)
            ·
              refine ⟨24404513398885598972180081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65078702397028263925813549 24404513398885598972180081)
              ·
                refine ⟨18303385049164199229135061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24404513398885598972180081 18303385049164199229135061)
                ·
                  refine ⟨428985587089785919432853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18303385049164199229135061 428985587089785919432853)
                  ·
                    rfl

theorem cell22_3759509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_3759509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759509 prefixEnd_3759509 := by exact prefixLift 3759509
  have htrace : WordTrace (prefixWord ++ tailWord_3759509) baseStart_3759509 baseEnd_3759509 := by
    simpa [prefixWord, tailWord_3759509, baseEnd_3759509] using wordTrace_append hprefix tailTrace_3759509
  have hstable : (prefixWord ++ tailWord_3759509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759509).length < 2 ^ (prefixWord ++ tailWord_3759509).sum := by decide
  have hdescent : baseEnd_3759509 < baseStart_3759509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759691 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_3759691 : Nat := 118140960795 + 3759691 * 2 ^ 59
def prefixEnd_3759691 : Nat := 4983230072969 + 3 ^ 40 * 3759691 * 2
def baseEnd_3759691 : Nat := 1287019063588769950248001

theorem tailTrace_3759691 : CollatzResearch.WordTrace tailWord_3759691 prefixEnd_3759691 1287019063588769950248001 := by
  unfold tailWord_3759691
  simp only [CollatzResearch.WordTrace]
  refine ⟨137127196222289085947390927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91418130814859390631593951 137127196222289085947390927)
  ·
    refine ⟨205690794333433628921086391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137127196222289085947390927 205690794333433628921086391)
    ·
      refine ⟨308536191500150443381629587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205690794333433628921086391 308536191500150443381629587)
      ·
        refine ⟨462804287250225665072444381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308536191500150443381629587 462804287250225665072444381)
        ·
          refine ⟨173551607718834624402166643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462804287250225665072444381 173551607718834624402166643)
          ·
            refine ⟨260327411578251936603249965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173551607718834624402166643 260327411578251936603249965)
            ·
              refine ⟨97622779341844476226218737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260327411578251936603249965 97622779341844476226218737)
              ·
                refine ⟨73217084506383357169664053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97622779341844476226218737 73217084506383357169664053)
                ·
                  refine ⟨6864101672473439734656005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73217084506383357169664053 6864101672473439734656005)
                  ·
                    refine ⟨1287019063588769950248001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864101672473439734656005 1287019063588769950248001)
                    ·
                      rfl

theorem cell22_3759691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_3759691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759691 prefixEnd_3759691 := by exact prefixLift 3759691
  have htrace : WordTrace (prefixWord ++ tailWord_3759691) baseStart_3759691 baseEnd_3759691 := by
    simpa [prefixWord, tailWord_3759691, baseEnd_3759691] using wordTrace_append hprefix tailTrace_3759691
  have hstable : (prefixWord ++ tailWord_3759691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759691).length < 2 ^ (prefixWord ++ tailWord_3759691).sum := by decide
  have hdescent : baseEnd_3759691 < baseStart_3759691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759725 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3759725 : Nat := 118140960795 + 3759725 * 2 ^ 59
def prefixEnd_3759725 : Nat := 4983230072969 + 3 ^ 40 * 3759725 * 2
def baseEnd_3759725 : Nat := 1287030702483605194897897

theorem tailTrace_3759725 : CollatzResearch.WordTrace tailWord_3759725 prefixEnd_3759725 1287030702483605194897897 := by
  unfold tailWord_3759725
  simp only [CollatzResearch.WordTrace]
  refine ⟨137128436304165909754128629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91418957536110606502752419 137128436304165909754128629)
  ·
    refine ⟨12855790903515554039449559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137128436304165909754128629 12855790903515554039449559)
    ·
      refine ⟨19283686355273331059174339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12855790903515554039449559 19283686355273331059174339)
      ·
        refine ⟨28925529532909996588761509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19283686355273331059174339 28925529532909996588761509)
        ·
          refine ⟨5423536787420624360392783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28925529532909996588761509 5423536787420624360392783)
          ·
            refine ⟨8135305181130936540589175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5423536787420624360392783 8135305181130936540589175)
            ·
              refine ⟨12202957771696404810883763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135305181130936540589175 12202957771696404810883763)
              ·
                refine ⟨18304436657544607216325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12202957771696404810883763 18304436657544607216325645)
                ·
                  refine ⟨6864163746579227706122117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18304436657544607216325645 6864163746579227706122117)
                  ·
                    refine ⟨1287030702483605194897897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864163746579227706122117 1287030702483605194897897)
                    ·
                      rfl

theorem cell22_3759725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3759725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759725 prefixEnd_3759725 := by exact prefixLift 3759725
  have htrace : WordTrace (prefixWord ++ tailWord_3759725) baseStart_3759725 baseEnd_3759725 := by
    simpa [prefixWord, tailWord_3759725, baseEnd_3759725] using wordTrace_append hprefix tailTrace_3759725
  have hstable : (prefixWord ++ tailWord_3759725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759725).length < 2 ^ (prefixWord ++ tailWord_3759725).sum := by decide
  have hdescent : baseEnd_3759725 < baseStart_3759725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759738 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 4, 3]
def baseStart_3759738 : Nat := 118140960795 + 3759738 * 2 ^ 59
def prefixEnd_3759738 : Nat := 4983230072969 + 3 ^ 40 * 3759738 * 2
def baseEnd_3759738 : Nat := 1287035152649277494322857

theorem tailTrace_3759738 : CollatzResearch.WordTrace tailWord_3759738 prefixEnd_3759738 1287035152649277494322857 := by
  unfold tailWord_3759738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34282227613279703243587967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91419273635412541982901245 34282227613279703243587967)
  ·
    refine ⟨51423341419919554865381951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34282227613279703243587967 51423341419919554865381951)
    ·
      refine ⟨77135012129879332298072927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51423341419919554865381951 77135012129879332298072927)
      ·
        refine ⟨115702518194818998447109391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77135012129879332298072927 115702518194818998447109391)
        ·
          refine ⟨173553777292228497670664087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115702518194818998447109391 173553777292228497670664087)
          ·
            refine ⟨260330665938342746505996131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173553777292228497670664087 260330665938342746505996131)
            ·
              refine ⟨390495998907514119758994197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260330665938342746505996131 390495998907514119758994197)
              ·
                refine ⟨18304499948789724363702853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390495998907514119758994197 18304499948789724363702853)
                ·
                  refine ⟨3432093740398073318194285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18304499948789724363702853 3432093740398073318194285)
                  ·
                    refine ⟨1287035152649277494322857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432093740398073318194285 1287035152649277494322857)
                    ·
                      rfl

theorem cell22_3759738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_3759738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759738 prefixEnd_3759738 := by exact prefixLift 3759738
  have htrace : WordTrace (prefixWord ++ tailWord_3759738) baseStart_3759738 baseEnd_3759738 := by
    simpa [prefixWord, tailWord_3759738, baseEnd_3759738] using wordTrace_append hprefix tailTrace_3759738
  have hstable : (prefixWord ++ tailWord_3759738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759738).length < 2 ^ (prefixWord ++ tailWord_3759738).sum := by decide
  have hdescent : baseEnd_3759738 < baseStart_3759738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759751 : List Nat := [1, 1, 4, 2, 1, 13]
def baseStart_3759751 : Nat := 118140960795 + 3759751 * 2 ^ 59
def prefixEnd_3759751 : Nat := 4983230072969 + 3 ^ 40 * 3759751 * 2
def baseEnd_3759751 : Nat := 15889377812530244367257

theorem tailTrace_3759751 : CollatzResearch.WordTrace tailWord_3759751 prefixEnd_3759751 15889377812530244367257 := by
  unfold tailWord_3759751
  simp only [CollatzResearch.WordTrace]
  refine ⟨137129384602071716194575107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91419589734714477463050071 137129384602071716194575107)
  ·
    refine ⟨205694076903107574291862661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137129384602071716194575107 205694076903107574291862661)
    ·
      refine ⟨38567639419332670179724249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205694076903107574291862661 38567639419332670179724249)
      ·
        refine ⟨28925729564499502634793187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38567639419332670179724249 28925729564499502634793187)
        ·
          refine ⟨43388594346749253952189781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28925729564499502634793187 43388594346749253952189781)
          ·
            refine ⟨15889377812530244367257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 43388594346749253952189781 15889377812530244367257)
            ·
              rfl

theorem cell22_3759751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 13].length) (baseStart_3759751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759751 prefixEnd_3759751 := by exact prefixLift 3759751
  have htrace : WordTrace (prefixWord ++ tailWord_3759751) baseStart_3759751 baseEnd_3759751 := by
    simpa [prefixWord, tailWord_3759751, baseEnd_3759751] using wordTrace_append hprefix tailTrace_3759751
  have hstable : (prefixWord ++ tailWord_3759751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759751).length < 2 ^ (prefixWord ++ tailWord_3759751).sum := by decide
  have hdescent : baseEnd_3759751 < baseStart_3759751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759753 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_3759753 : Nat := 118140960795 + 3759753 * 2 ^ 59
def prefixEnd_3759753 : Nat := 4983230072969 + 3 ^ 40 * 3759753 * 2
def baseEnd_3759753 : Nat := 1287040287455822455197811

theorem tailTrace_3759753 : CollatzResearch.WordTrace tailWord_3759753 prefixEnd_3759753 1287040287455822455197811 := by
  unfold tailWord_3759753
  simp only [CollatzResearch.WordTrace]
  refine ⟨137129457548064470536147913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91419638365376313690765275 137129457548064470536147913)
  ·
    refine ⟨102847093161048352902110935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137129457548064470536147913 102847093161048352902110935)
    ·
      refine ⟨154270639741572529353166403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102847093161048352902110935 154270639741572529353166403)
      ·
        refine ⟨231405959612358794029749605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154270639741572529353166403 231405959612358794029749605)
        ·
          refine ⟨43388617427317273880578051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231405959612358794029749605 43388617427317273880578051)
          ·
            refine ⟨65082926140975910820867077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43388617427317273880578051 65082926140975910820867077)
            ·
              refine ⟨12203048651432983278912577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65082926140975910820867077 12203048651432983278912577)
              ·
                refine ⟨9152286488574737459184433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12203048651432983278912577 9152286488574737459184433)
                ·
                  refine ⟨6864214866431053094388325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152286488574737459184433 6864214866431053094388325)
                  ·
                    refine ⟨1287040287455822455197811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864214866431053094388325 1287040287455822455197811)
                    ·
                      rfl

theorem cell22_3759753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_3759753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759753 prefixEnd_3759753 := by exact prefixLift 3759753
  have htrace : WordTrace (prefixWord ++ tailWord_3759753) baseStart_3759753 baseEnd_3759753 := by
    simpa [prefixWord, tailWord_3759753, baseEnd_3759753] using wordTrace_append hprefix tailTrace_3759753
  have hstable : (prefixWord ++ tailWord_3759753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759753).length < 2 ^ (prefixWord ++ tailWord_3759753).sum := by decide
  have hdescent : baseEnd_3759753 < baseStart_3759753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759755 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 2, 3]
def baseStart_3759755 : Nat := 118140960795 + 3759755 * 2 ^ 59
def prefixEnd_3759755 : Nat := 4983230072969 + 3 ^ 40 * 3759755 * 2
def baseEnd_3759755 : Nat := 1287040972096695116647805

theorem tailTrace_3759755 : CollatzResearch.WordTrace tailWord_3759755 prefixEnd_3759755 1287040972096695116647805 := by
  unfold tailWord_3759755
  simp only [CollatzResearch.WordTrace]
  refine ⟨137129530494057224877720719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91419686996038149918480479 137129530494057224877720719)
  ·
    refine ⟨205694295741085837316581079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137129530494057224877720719 205694295741085837316581079)
    ·
      refine ⟨308541443611628755974871619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205694295741085837316581079 308541443611628755974871619)
      ·
        refine ⟨462812165417443133962307429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308541443611628755974871619 462812165417443133962307429)
        ·
          refine ⟨86777281015770587617932643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 462812165417443133962307429 86777281015770587617932643)
          ·
            refine ⟨130165921523655881426898965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86777281015770587617932643 130165921523655881426898965)
            ·
              refine ⟨6101527571421369441885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130165921523655881426898965 6101527571421369441885889)
              ·
                refine ⟨4576145678566027081414417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6101527571421369441885889 4576145678566027081414417)
                ·
                  refine ⟨3432109258924520311060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576145678566027081414417 3432109258924520311060813)
                  ·
                    refine ⟨1287040972096695116647805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432109258924520311060813 1287040972096695116647805)
                    ·
                      rfl

theorem cell22_3759755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].length) (baseStart_3759755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759755 prefixEnd_3759755 := by exact prefixLift 3759755
  have htrace : WordTrace (prefixWord ++ tailWord_3759755) baseStart_3759755 baseEnd_3759755 := by
    simpa [prefixWord, tailWord_3759755, baseEnd_3759755] using wordTrace_append hprefix tailTrace_3759755
  have hstable : (prefixWord ++ tailWord_3759755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759755).length < 2 ^ (prefixWord ++ tailWord_3759755).sum := by decide
  have hdescent : baseEnd_3759755 < baseStart_3759755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759768 : List Nat := [2, 1, 2, 4, 1, 2, 3, 7]
def baseStart_3759768 : Nat := 118140960795 + 3759768 * 2 ^ 59
def prefixEnd_3759768 : Nat := 4983230072969 + 3 ^ 40 * 3759768 * 2
def baseEnd_3759768 : Nat := 143005046918040824008085

theorem tailTrace_3759768 : CollatzResearch.WordTrace tailWord_3759768 prefixEnd_3759768 143005046918040824008085 := by
  unfold tailWord_3759768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68565002321505064048971979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91420003095340085398629305 68565002321505064048971979)
  ·
    refine ⟨102847503482257596073457969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68565002321505064048971979 102847503482257596073457969)
    ·
      refine ⟨77135627611693197055093477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102847503482257596073457969 77135627611693197055093477)
      ·
        refine ⟨14462930177192474447830027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77135627611693197055093477 14462930177192474447830027)
        ·
          refine ⟨21694395265788711671745041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14462930177192474447830027 21694395265788711671745041)
          ·
            refine ⟨16270796449341533753808781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21694395265788711671745041 16270796449341533753808781)
            ·
              refine ⟨6101548668503075157678293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16270796449341533753808781 6101548668503075157678293)
              ·
                refine ⟨143005046918040824008085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6101548668503075157678293 143005046918040824008085)
                ·
                  rfl

theorem cell22_3759768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_3759768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759768 prefixEnd_3759768 := by exact prefixLift 3759768
  have htrace : WordTrace (prefixWord ++ tailWord_3759768) baseStart_3759768 baseEnd_3759768 := by
    simpa [prefixWord, tailWord_3759768, baseEnd_3759768] using wordTrace_append hprefix tailTrace_3759768
  have hstable : (prefixWord ++ tailWord_3759768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759768).length < 2 ^ (prefixWord ++ tailWord_3759768).sum := by decide
  have hdescent : baseEnd_3759768 < baseStart_3759768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759875 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 4]
def baseStart_3759875 : Nat := 118140960795 + 3759875 * 2 ^ 59
def prefixEnd_3759875 : Nat := 4983230072969 + 3 ^ 40 * 3759875 * 2
def baseEnd_3759875 : Nat := 429027350183018267882479

theorem tailTrace_3759875 : CollatzResearch.WordTrace tailWord_3759875 prefixEnd_3759875 429027350183018267882479 := by
  unfold tailWord_3759875
  simp only [CollatzResearch.WordTrace]
  refine ⟨137133907253622485372089079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91422604835748323581392719 137133907253622485372089079)
  ·
    refine ⟨205700860880433728058133619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137133907253622485372089079 205700860880433728058133619)
    ·
      refine ⟨308551291320650592087200429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205700860880433728058133619 308551291320650592087200429)
      ·
        refine ⟨115706734245243972032700161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308551291320650592087200429 115706734245243972032700161)
        ·
          refine ⟨86780050683932979024525121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115706734245243972032700161 86780050683932979024525121)
          ·
            refine ⟨65085038012949734268393841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86780050683932979024525121 65085038012949734268393841)
            ·
              refine ⟨48813778509712300701295381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65085038012949734268393841 48813778509712300701295381)
              ·
                refine ⟨2288145867642764095373221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48813778509712300701295381 2288145867642764095373221)
                ·
                  refine ⟨429027350183018267882479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288145867642764095373221 429027350183018267882479)
                  ·
                    rfl

theorem cell22_3759875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 4].length) (baseStart_3759875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759875 prefixEnd_3759875 := by exact prefixLift 3759875
  have htrace : WordTrace (prefixWord ++ tailWord_3759875) baseStart_3759875 baseEnd_3759875 := by
    simpa [prefixWord, tailWord_3759875, baseEnd_3759875] using wordTrace_append hprefix tailTrace_3759875
  have hstable : (prefixWord ++ tailWord_3759875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759875).length < 2 ^ (prefixWord ++ tailWord_3759875).sum := by decide
  have hdescent : baseEnd_3759875 < baseStart_3759875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759903 : List Nat := [1, 1, 2, 4, 2, 1, 1, 10]
def baseStart_3759903 : Nat := 118140960795 + 3759903 * 2 ^ 59
def prefixEnd_3759903 : Nat := 4983230072969 + 3 ^ 40 * 3759903 * 2
def baseEnd_3759903 : Nat := 143010181724585784883039

theorem tailTrace_3759903 : CollatzResearch.WordTrace tailWord_3759903 prefixEnd_3759903 143010181724585784883039 := by
  unfold tailWord_3759903
  simp only [CollatzResearch.WordTrace]
  refine ⟨137134928497521046154108363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91423285665014030769405575 137134928497521046154108363)
  ·
    refine ⟨205702392746281569231162545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137134928497521046154108363 205702392746281569231162545)
    ·
      refine ⟨154276794559711176923371909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205702392746281569231162545 154276794559711176923371909)
      ·
        refine ⟨28926898979945845673132233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154276794559711176923371909 28926898979945845673132233)
        ·
          refine ⟨21695174234959384254849175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28926898979945845673132233 21695174234959384254849175)
          ·
            refine ⟨32542761352439076382273763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21695174234959384254849175 32542761352439076382273763)
            ·
              refine ⟨48814142028658614573410645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32542761352439076382273763 48814142028658614573410645)
              ·
                refine ⟨143010181724585784883039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48814142028658614573410645 143010181724585784883039)
                ·
                  rfl

theorem cell22_3759903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 10].length) (baseStart_3759903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759903 prefixEnd_3759903 := by exact prefixLift 3759903
  have htrace : WordTrace (prefixWord ++ tailWord_3759903) baseStart_3759903 baseEnd_3759903 := by
    simpa [prefixWord, tailWord_3759903, baseEnd_3759903] using wordTrace_append hprefix tailTrace_3759903
  have hstable : (prefixWord ++ tailWord_3759903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759903).length < 2 ^ (prefixWord ++ tailWord_3759903).sum := by decide
  have hdescent : baseEnd_3759903 < baseStart_3759903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759905 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3759905 : Nat := 118140960795 + 3759905 * 2 ^ 59
def prefixEnd_3759905 : Nat := 4983230072969 + 3 ^ 40 * 3759905 * 2
def baseEnd_3759905 : Nat := 1287092320162144725397345

theorem tailTrace_3759905 : CollatzResearch.WordTrace tailWord_3759905 prefixEnd_3759905 1287092320162144725397345 := by
  unfold tailWord_3759905
  simp only [CollatzResearch.WordTrace]
  refine ⟨137135001443513800495681169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91423334295675866997120779 137135001443513800495681169)
  ·
    refine ⟨102851251082635350371760877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137135001443513800495681169 102851251082635350371760877)
    ·
      refine ⟨38569219155988256389410329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102851251082635350371760877 38569219155988256389410329)
      ·
        refine ⟨28926914366991192292057747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38569219155988256389410329 28926914366991192292057747)
        ·
          refine ⟨43390371550486788438086621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28926914366991192292057747 43390371550486788438086621)
          ·
            refine ⟨16271389331432545664282483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43390371550486788438086621 16271389331432545664282483)
            ·
              refine ⟨24407083997148818496423725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271389331432545664282483 24407083997148818496423725)
              ·
                refine ⟨9152656498930806936158897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24407083997148818496423725 9152656498930806936158897)
                ·
                  refine ⟨6864492374198105202119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9152656498930806936158897 6864492374198105202119173)
                  ·
                    refine ⟨1287092320162144725397345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6864492374198105202119173 1287092320162144725397345)
                    ·
                      rfl

theorem cell22_3759905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3759905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759905 prefixEnd_3759905 := by exact prefixLift 3759905
  have htrace : WordTrace (prefixWord ++ tailWord_3759905) baseStart_3759905 baseEnd_3759905 := by
    simpa [prefixWord, tailWord_3759905, baseEnd_3759905] using wordTrace_append hprefix tailTrace_3759905
  have hstable : (prefixWord ++ tailWord_3759905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759905).length < 2 ^ (prefixWord ++ tailWord_3759905).sum := by decide
  have hdescent : baseEnd_3759905 < baseStart_3759905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759924 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_3759924 : Nat := 118140960795 + 3759924 * 2 ^ 59
def prefixEnd_3759924 : Nat := 4983230072969 + 3 ^ 40 * 3759924 * 2
def baseEnd_3759924 : Nat := 1287098824250435009172287

theorem tailTrace_3759924 : CollatzResearch.WordTrace tailWord_3759924 prefixEnd_3759924 1287098824250435009172287 := by
  unfold tailWord_3759924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68567847215222483370311413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91423796286963311160415217 68567847215222483370311413)
  ·
    refine ⟨6428235676427107815966695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68567847215222483370311413 6428235676427107815966695)
    ·
      refine ⟨9642353514640661723950043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428235676427107815966695 9642353514640661723950043)
      ·
        refine ⟨14463530271960992585925065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9642353514640661723950043 14463530271960992585925065)
        ·
          refine ⟨10847647703970744439443799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14463530271960992585925065 10847647703970744439443799)
          ·
            refine ⟨16271471555956116659165699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847647703970744439443799 16271471555956116659165699)
            ·
              refine ⟨24407207333934174988748549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271471555956116659165699 24407207333934174988748549)
              ·
                refine ⟨4576351375112657810390353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24407207333934174988748549 4576351375112657810390353)
                ·
                  refine ⟨3432263531334493357792765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576351375112657810390353 3432263531334493357792765)
                  ·
                    refine ⟨1287098824250435009172287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432263531334493357792765 1287098824250435009172287)
                    ·
                      rfl

theorem cell22_3759924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_3759924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759924 prefixEnd_3759924 := by exact prefixLift 3759924
  have htrace : WordTrace (prefixWord ++ tailWord_3759924) baseStart_3759924 baseEnd_3759924 := by
    simpa [prefixWord, tailWord_3759924, baseEnd_3759924] using wordTrace_append hprefix tailTrace_3759924
  have hstable : (prefixWord ++ tailWord_3759924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759924).length < 2 ^ (prefixWord ++ tailWord_3759924).sum := by decide
  have hdescent : baseEnd_3759924 < baseStart_3759924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759926 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_3759926 : Nat := 118140960795 + 3759926 * 2 ^ 59
def prefixEnd_3759926 : Nat := 4983230072969 + 3 ^ 40 * 3759926 * 2
def baseEnd_3759926 : Nat := 429033169630435890207427

theorem tailTrace_3759926 : CollatzResearch.WordTrace tailWord_3759926 prefixEnd_3759926 429033169630435890207427 := by
  unfold tailWord_3759926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570985461027357567637227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91423844917625147388130421 8570985461027357567637227)
  ·
    refine ⟨12856478191541036351455841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8570985461027357567637227 12856478191541036351455841)
    ·
      refine ⟨9642358643655777263591881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12856478191541036351455841 9642358643655777263591881)
      ·
        refine ⟨7231768982741832947693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9642358643655777263591881 7231768982741832947693911)
        ·
          refine ⟨10847653474112749421540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231768982741832947693911 10847653474112749421540867)
          ·
            refine ⟨16271480211169124132311301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10847653474112749421540867 16271480211169124132311301)
            ·
              refine ⟨3050902539594210774808369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16271480211169124132311301 3050902539594210774808369)
              ·
                refine ⟨2288176904695658081106277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050902539594210774808369 2288176904695658081106277)
                ·
                  refine ⟨429033169630435890207427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288176904695658081106277 429033169630435890207427)
                  ·
                    rfl

theorem cell22_3759926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_3759926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759926 prefixEnd_3759926 := by exact prefixLift 3759926
  have htrace : WordTrace (prefixWord ++ tailWord_3759926) baseStart_3759926 baseEnd_3759926 := by
    simpa [prefixWord, tailWord_3759926, baseEnd_3759926] using wordTrace_append hprefix tailTrace_3759926
  have hstable : (prefixWord ++ tailWord_3759926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759926).length < 2 ^ (prefixWord ++ tailWord_3759926).sum := by decide
  have hdescent : baseEnd_3759926 < baseStart_3759926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759969 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_3759969 : Nat := 118140960795 + 3759969 * 2 ^ 59
def prefixEnd_3759969 : Nat := 4983230072969 + 3 ^ 40 * 3759969 * 2
def baseEnd_3759969 : Nat := 1287114228670069891797149

theorem tailTrace_3759969 : CollatzResearch.WordTrace tailWord_3759969 prefixEnd_3759969 1287114228670069891797149 := by
  unfold tailWord_3759969
  simp only [CollatzResearch.WordTrace]
  refine ⟨137137335715281939426010961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91424890476854626284007307 137137335715281939426010961)
  ·
    refine ⟨102853001786461454569508221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137137335715281939426010961 102853001786461454569508221)
    ·
      refine ⟨38569875669923045463565583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102853001786461454569508221 38569875669923045463565583)
      ·
        refine ⟨57854813504884568195348375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38569875669923045463565583 57854813504884568195348375)
        ·
          refine ⟨86782220257326852293022563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57854813504884568195348375 86782220257326852293022563)
          ·
            refine ⟨130173330385990278439533845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86782220257326852293022563 130173330385990278439533845)
            ·
              refine ⟨6101874861843294301853149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130173330385990278439533845 6101874861843294301853149)
              ·
                refine ⟨2288203073191235363194931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6101874861843294301853149 2288203073191235363194931)
                ·
                  refine ⟨3432304609786853044792397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288203073191235363194931 3432304609786853044792397)
                  ·
                    refine ⟨1287114228670069891797149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432304609786853044792397 1287114228670069891797149)
                    ·
                      rfl

theorem cell22_3759969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_3759969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759969 prefixEnd_3759969 := by exact prefixLift 3759969
  have htrace : WordTrace (prefixWord ++ tailWord_3759969) baseStart_3759969 baseEnd_3759969 := by
    simpa [prefixWord, tailWord_3759969, baseEnd_3759969] using wordTrace_append hprefix tailTrace_3759969
  have hstable : (prefixWord ++ tailWord_3759969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759969).length < 2 ^ (prefixWord ++ tailWord_3759969).sum := by decide
  have hdescent : baseEnd_3759969 < baseStart_3759969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759980 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_3759980 : Nat := 118140960795 + 3759980 * 2 ^ 59
def prefixEnd_3759980 : Nat := 4983230072969 + 3 ^ 40 * 3759980 * 2
def baseEnd_3759980 : Nat := 1287117994194869529772115

theorem tailTrace_3759980 : CollatzResearch.WordTrace tailWord_3759980 prefixEnd_3759980 1287117994194869529772115 := by
  unfold tailWord_3759980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68568868459121044152330697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91425157945494725536440929 68568868459121044152330697)
  ·
    refine ⟨51426651344340783114248023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68568868459121044152330697 51426651344340783114248023)
    ·
      refine ⟨77139977016511174671372035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51426651344340783114248023 77139977016511174671372035)
      ·
        refine ⟨115709965524766762007058053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77139977016511174671372035 115709965524766762007058053)
        ·
          refine ⟨21695618535893767876323385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115709965524766762007058053 21695618535893767876323385)
          ·
            refine ⟨16271713901920325907242539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21695618535893767876323385 16271713901920325907242539)
            ·
              refine ⟨24407570852880488860863809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16271713901920325907242539 24407570852880488860863809)
              ·
                refine ⟨18305678139660366645647857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24407570852880488860863809 18305678139660366645647857)
                ·
                  refine ⟨13729258604745274984235893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18305678139660366645647857 13729258604745274984235893)
                  ·
                    refine ⟨1287117994194869529772115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13729258604745274984235893 1287117994194869529772115)
                    ·
                      rfl

theorem cell22_3759980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_3759980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759980 prefixEnd_3759980 := by exact prefixLift 3759980
  have htrace : WordTrace (prefixWord ++ tailWord_3759980) baseStart_3759980 baseEnd_3759980 := by
    simpa [prefixWord, tailWord_3759980, baseEnd_3759980] using wordTrace_append hprefix tailTrace_3759980
  have hstable : (prefixWord ++ tailWord_3759980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759980).length < 2 ^ (prefixWord ++ tailWord_3759980).sum := by decide
  have hdescent : baseEnd_3759980 < baseStart_3759980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3759982 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3759982 : Nat := 118140960795 + 3759982 * 2 ^ 59
def prefixEnd_3759982 : Nat := 4983230072969 + 3 ^ 40 * 3759982 * 2
def baseEnd_3759982 : Nat := 429039559611914063740703

theorem tailTrace_3759982 : CollatzResearch.WordTrace tailWord_3759982 prefixEnd_3759982 429039559611914063740703 := by
  unfold tailWord_3759982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17142226233029355330779275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91425206576156561764156133 17142226233029355330779275)
  ·
    refine ⟨25713339349544032996168913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17142226233029355330779275 25713339349544032996168913)
    ·
      refine ⟨19285004512158024747126685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25713339349544032996168913 19285004512158024747126685)
      ·
        refine ⟨7231876692059259280172507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19285004512158024747126685 7231876692059259280172507)
        ·
          refine ⟨10847815038088888920258761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231876692059259280172507 10847815038088888920258761)
          ·
            refine ⟨8135861278566666690194071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10847815038088888920258761 8135861278566666690194071)
            ·
              refine ⟨12203791917850000035291107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8135861278566666690194071 12203791917850000035291107)
              ·
                refine ⟨18305687876775000052936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203791917850000035291107 18305687876775000052936661)
                ·
                  refine ⟨429039559611914063740703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18305687876775000052936661 429039559611914063740703)
                  ·
                    rfl

theorem cell22_3759982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3759982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3759982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3759982 prefixEnd_3759982 := by exact prefixLift 3759982
  have htrace : WordTrace (prefixWord ++ tailWord_3759982) baseStart_3759982 baseEnd_3759982 := by
    simpa [prefixWord, tailWord_3759982, baseEnd_3759982] using wordTrace_append hprefix tailTrace_3759982
  have hstable : (prefixWord ++ tailWord_3759982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3759982).length < 2 ^ (prefixWord ++ tailWord_3759982).sum := by decide
  have hdescent : baseEnd_3759982 < baseStart_3759982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3759982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760025 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_3760025 : Nat := 118140960795 + 3760025 * 2 ^ 59
def prefixEnd_3760025 : Nat := 4983230072969 + 3 ^ 40 * 3760025 * 2
def baseEnd_3760025 : Nat := 1287133398614504412396977

theorem tailTrace_3760025 : CollatzResearch.WordTrace tailWord_3760025 prefixEnd_3760025 1287133398614504412396977 := by
  unfold tailWord_3760025
  simp only [CollatzResearch.WordTrace]
  refine ⟨137139378203079060990049529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91426252135386040660033019 137139378203079060990049529)
  ·
    refine ⟨102854533652309295742537147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137139378203079060990049529 102854533652309295742537147)
    ·
      refine ⟨154281800478463943613805721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102854533652309295742537147 154281800478463943613805721)
      ·
        refine ⟨115711350358847957710354291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154281800478463943613805721 115711350358847957710354291)
        ·
          refine ⟨173567025538271936565531437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115711350358847957710354291 173567025538271936565531437)
          ·
            refine ⟨65087634576851976212074289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173567025538271936565531437 65087634576851976212074289)
            ·
              refine ⟨48815725932638982159055717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65087634576851976212074289 48815725932638982159055717)
              ·
                refine ⟨9152948612369809154822947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48815725932638982159055717 9152948612369809154822947)
                ·
                  refine ⟨13729422918554713732234421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9152948612369809154822947 13729422918554713732234421)
                  ·
                    refine ⟨1287133398614504412396977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13729422918554713732234421 1287133398614504412396977)
                    ·
                      rfl

theorem cell22_3760025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_3760025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760025 prefixEnd_3760025 := by exact prefixLift 3760025
  have htrace : WordTrace (prefixWord ++ tailWord_3760025) baseStart_3760025 baseEnd_3760025 := by
    simpa [prefixWord, tailWord_3760025, baseEnd_3760025] using wordTrace_append hprefix tailTrace_3760025
  have hstable : (prefixWord ++ tailWord_3760025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760025).length < 2 ^ (prefixWord ++ tailWord_3760025).sum := by decide
  have hdescent : baseEnd_3760025 < baseStart_3760025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760138 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_3760138 : Nat := 118140960795 + 3760138 * 2 ^ 59
def prefixEnd_3760138 : Nat := 4983230072969 + 3 ^ 40 * 3760138 * 2
def baseEnd_3760138 : Nat := 1287172080823809784321631

theorem tailTrace_3760138 : CollatzResearch.WordTrace tailWord_3760138 prefixEnd_3760138 1287172080823809784321631 := by
  unfold tailWord_3760138
  simp only [CollatzResearch.WordTrace]
  refine ⟨34285874912917420322228267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91428999767779787525942045 34285874912917420322228267)
  ·
    refine ⟨51428812369376130483342401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34285874912917420322228267 51428812369376130483342401)
    ·
      refine ⟨38571609277032097862506801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51428812369376130483342401 38571609277032097862506801)
      ·
        refine ⟨28928706957774073396880101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38571609277032097862506801 28928706957774073396880101)
        ·
          refine ⟨5424132554582638761915019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28928706957774073396880101 5424132554582638761915019)
          ·
            refine ⟨8136198831873958142872529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424132554582638761915019 8136198831873958142872529)
            ·
              refine ⟨6102149123905468607154397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8136198831873958142872529 6102149123905468607154397)
              ·
                refine ⟨2288305921464550727682899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6102149123905468607154397 2288305921464550727682899)
                ·
                  refine ⟨3432458882196826091524349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288305921464550727682899 3432458882196826091524349)
                  ·
                    refine ⟨1287172080823809784321631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432458882196826091524349 1287172080823809784321631)
                    ·
                      rfl

theorem cell22_3760138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_3760138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760138 prefixEnd_3760138 := by exact prefixLift 3760138
  have htrace : WordTrace (prefixWord ++ tailWord_3760138) baseStart_3760138 baseEnd_3760138 := by
    simpa [prefixWord, tailWord_3760138, baseEnd_3760138] using wordTrace_append hprefix tailTrace_3760138
  have hstable : (prefixWord ++ tailWord_3760138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760138).length < 2 ^ (prefixWord ++ tailWord_3760138).sum := by decide
  have hdescent : baseEnd_3760138 < baseStart_3760138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760151 : List Nat := [1, 1, 3, 5, 2, 2, 1, 2, 5]
def baseStart_3760151 : Nat := 118140960795 + 3760151 * 2 ^ 59
def prefixEnd_3760151 : Nat := 4983230072969 + 3 ^ 40 * 3760151 * 2
def baseEnd_3760151 : Nat := 429058843663160694582197

theorem tailTrace_3760151 : CollatzResearch.WordTrace tailWord_3760151 prefixEnd_3760151 429058843663160694582197 := by
  unfold tailWord_3760151
  simp only [CollatzResearch.WordTrace]
  refine ⟨137143973800622584509136307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91429315867081723006090871 137143973800622584509136307)
  ·
    refine ⟨205715960700933876763704461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137143973800622584509136307 205715960700933876763704461)
    ·
      refine ⟨77143485262850203786389173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205715960700933876763704461 77143485262850203786389173)
      ·
        refine ⟨7232201743392206604973985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77143485262850203786389173 7232201743392206604973985)
        ·
          refine ⟨5424151307544154953730489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232201743392206604973985 5424151307544154953730489)
          ·
            refine ⟨4068113480658116215297867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424151307544154953730489 4068113480658116215297867)
            ·
              refine ⟨6102170220987174322946801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068113480658116215297867 6102170220987174322946801)
              ·
                refine ⟨4576627665740380742210101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102170220987174322946801 4576627665740380742210101)
                ·
                  refine ⟨429058843663160694582197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4576627665740380742210101 429058843663160694582197)
                  ·
                    rfl

theorem cell22_3760151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].length) (baseStart_3760151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760151 prefixEnd_3760151 := by exact prefixLift 3760151
  have htrace : WordTrace (prefixWord ++ tailWord_3760151) baseStart_3760151 baseEnd_3760151 := by
    simpa [prefixWord, tailWord_3760151, baseEnd_3760151] using wordTrace_append hprefix tailTrace_3760151
  have hstable : (prefixWord ++ tailWord_3760151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760151).length < 2 ^ (prefixWord ++ tailWord_3760151).sum := by decide
  have hdescent : baseEnd_3760151 < baseStart_3760151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760168 : List Nat := [2, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_3760168 : Nat := 118140960795 + 3760168 * 2 ^ 59
def prefixEnd_3760168 : Nat := 4983230072969 + 3 ^ 40 * 3760168 * 2
def baseEnd_3760168 : Nat := 429060783478966568690513

theorem tailTrace_3760168 : CollatzResearch.WordTrace tailWord_3760168 prefixEnd_3760168 429060783478966568690513 := by
  unfold tailWord_3760168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68572296920780498206252579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91429729227707330941670105 68572296920780498206252579)
  ·
    refine ⟨102858445381170747309378869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68572296920780498206252579 102858445381170747309378869)
    ·
      refine ⟨9642979254484757560254269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102858445381170747309378869 9642979254484757560254269)
      ·
        refine ⟨3616117220431784085095351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9642979254484757560254269 3616117220431784085095351)
        ·
          refine ⟨5424175830647676127643027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616117220431784085095351 5424175830647676127643027)
          ·
            refine ⟨8136263745971514191464541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424175830647676127643027 8136263745971514191464541)
            ·
              refine ⟨3051098904739317821799203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8136263745971514191464541 3051098904739317821799203)
              ·
                refine ⟨4576648357108976732698805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051098904739317821799203 4576648357108976732698805)
                ·
                  refine ⟨429060783478966568690513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4576648357108976732698805 429060783478966568690513)
                  ·
                    rfl

theorem cell22_3760168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_3760168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760168 prefixEnd_3760168 := by exact prefixLift 3760168
  have htrace : WordTrace (prefixWord ++ tailWord_3760168) baseStart_3760168 baseEnd_3760168 := by
    simpa [prefixWord, tailWord_3760168, baseEnd_3760168] using wordTrace_append hprefix tailTrace_3760168
  have hstable : (prefixWord ++ tailWord_3760168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760168).length < 2 ^ (prefixWord ++ tailWord_3760168).sum := by decide
  have hdescent : baseEnd_3760168 < baseStart_3760168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760192 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_3760192 : Nat := 118140960795 + 3760192 * 2 ^ 59
def prefixEnd_3760192 : Nat := 4983230072969 + 3 ^ 40 * 3760192 * 2
def baseEnd_3760192 : Nat := 1287190566127371643471465

theorem tailTrace_3760192 : CollatzResearch.WordTrace tailWord_3760192 prefixEnd_3760192 1287190566127371643471465 := by
  unfold tailWord_3760192
  simp only [CollatzResearch.WordTrace]
  refine ⟨68572734596737024255689415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91430312795649365674252553 68572734596737024255689415)
  ·
    refine ⟨102859101895105536383534123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68572734596737024255689415 102859101895105536383534123)
    ·
      refine ⟨154288652842658304575301185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102859101895105536383534123 154288652842658304575301185)
      ·
        refine ⟨115716489631993728431475889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154288652842658304575301185 115716489631993728431475889)
        ·
          refine ⟨86787367223995296323606917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115716489631993728431475889 86787367223995296323606917)
          ·
            refine ⟨16272631354499118060676297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86787367223995296323606917 16272631354499118060676297)
            ·
              refine ⟨12204473515874338545507223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16272631354499118060676297 12204473515874338545507223)
              ·
                refine ⟨18306710273811507818260835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12204473515874338545507223 18306710273811507818260835)
                ·
                  refine ⟨27460065410717261727391253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18306710273811507818260835 27460065410717261727391253)
                  ·
                    refine ⟨1287190566127371643471465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27460065410717261727391253 1287190566127371643471465)
                    ·
                      rfl

theorem cell22_3760192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_3760192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760192 prefixEnd_3760192 := by exact prefixLift 3760192
  have htrace : WordTrace (prefixWord ++ tailWord_3760192) baseStart_3760192 baseEnd_3760192 := by
    simpa [prefixWord, tailWord_3760192, baseEnd_3760192] using wordTrace_append hprefix tailTrace_3760192
  have hstable : (prefixWord ++ tailWord_3760192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760192).length < 2 ^ (prefixWord ++ tailWord_3760192).sum := by decide
  have hdescent : baseEnd_3760192 < baseStart_3760192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760256 : List Nat := [2, 1, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_3760256 : Nat := 118140960795 + 3760256 * 2 ^ 59
def prefixEnd_3760256 : Nat := 4983230072969 + 3 ^ 40 * 3760256 * 2
def baseEnd_3760256 : Nat := 1287212474635296809871269

theorem tailTrace_3760256 : CollatzResearch.WordTrace tailWord_3760256 prefixEnd_3760256 1287212474635296809871269 := by
  unfold tailWord_3760256
  simp only [CollatzResearch.WordTrace]
  refine ⟨68573901732621093720854311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91431868976828124961139081 68573901732621093720854311)
  ·
    refine ⟨102860852598931640581281467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68573901732621093720854311 102860852598931640581281467)
    ·
      refine ⟨154291278898397460871922201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102860852598931640581281467 154291278898397460871922201)
      ·
        refine ⟨115718459173798095653941651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154291278898397460871922201 115718459173798095653941651)
        ·
          refine ⟨173577688760697143480912477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115718459173798095653941651 173577688760697143480912477)
          ·
            refine ⟨65091633285261428805342179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173577688760697143480912477 65091633285261428805342179)
            ·
              refine ⟨97637449927892143208013269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65091633285261428805342179 97637449927892143208013269)
              ·
                refine ⟨2288377732684972106437811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97637449927892143208013269 2288377732684972106437811)
                ·
                  refine ⟨3432566599027458159656717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288377732684972106437811 3432566599027458159656717)
                  ·
                    refine ⟨1287212474635296809871269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432566599027458159656717 1287212474635296809871269)
                    ·
                      rfl

theorem cell22_3760256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_3760256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760256 prefixEnd_3760256 := by exact prefixLift 3760256
  have htrace : WordTrace (prefixWord ++ tailWord_3760256) baseStart_3760256 baseEnd_3760256 := by
    simpa [prefixWord, tailWord_3760256, baseEnd_3760256] using wordTrace_append hprefix tailTrace_3760256
  have hstable : (prefixWord ++ tailWord_3760256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760256).length < 2 ^ (prefixWord ++ tailWord_3760256).sum := by decide
  have hdescent : baseEnd_3760256 < baseStart_3760256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760284 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_3760284 : Nat := 118140960795 + 3760284 * 2 ^ 59
def prefixEnd_3760284 : Nat := 4983230072969 + 3 ^ 40 * 3760284 * 2
def baseEnd_3760284 : Nat := 1287222059607514070171183

theorem tailTrace_3760284 : CollatzResearch.WordTrace tailWord_3760284 prefixEnd_3760284 1287222059607514070171183 := by
  unfold tailWord_3760284
  simp only [CollatzResearch.WordTrace]
  refine ⟨68574412354570374111863953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91432549806093832149151937 68574412354570374111863953)
  ·
    refine ⟨51430809265927780583897965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68574412354570374111863953 51430809265927780583897965)
    ·
      refine ⟨19286553474722917718961737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51430809265927780583897965 19286553474722917718961737)
      ·
        refine ⟨14464915106042188289221303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19286553474722917718961737 14464915106042188289221303)
        ·
          refine ⟨21697372659063282433831955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14464915106042188289221303 21697372659063282433831955)
          ·
            refine ⟨32546058988594923650747933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21697372659063282433831955 32546058988594923650747933)
            ·
              refine ⟨12204772120723096369030475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32546058988594923650747933 12204772120723096369030475)
              ·
                refine ⟨18307158181084644553545713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12204772120723096369030475 18307158181084644553545713)
                ·
                  refine ⟨13730368635813483415159285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18307158181084644553545713 13730368635813483415159285)
                  ·
                    refine ⟨1287222059607514070171183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13730368635813483415159285 1287222059607514070171183)
                    ·
                      rfl

theorem cell22_3760284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_3760284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760284 prefixEnd_3760284 := by exact prefixLift 3760284
  have htrace : WordTrace (prefixWord ++ tailWord_3760284) baseStart_3760284 baseEnd_3760284 := by
    simpa [prefixWord, tailWord_3760284, baseEnd_3760284] using wordTrace_append hprefix tailTrace_3760284
  have hstable : (prefixWord ++ tailWord_3760284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760284).length < 2 ^ (prefixWord ++ tailWord_3760284).sum := by decide
  have hdescent : baseEnd_3760284 < baseStart_3760284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760344 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_3760344 : Nat := 118140960795 + 3760344 * 2 ^ 59
def prefixEnd_3760344 : Nat := 4983230072969 + 3 ^ 40 * 3760344 * 2
def baseEnd_3760344 : Nat := 1287242598833693913670999

theorem tailTrace_3760344 : CollatzResearch.WordTrace tailWord_3760344 prefixEnd_3760344 1287242598833693913670999 := by
  unfold tailWord_3760344
  simp only [CollatzResearch.WordTrace]
  refine ⟨68575506544461689235456043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91434008725948918980608057 68575506544461689235456043)
  ·
    refine ⟨102863259816692533853184065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68575506544461689235456043 102863259816692533853184065)
    ·
      refine ⟨77147444862519400389888049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102863259816692533853184065 77147444862519400389888049)
      ·
        refine ⟨57860583646889550292416037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77147444862519400389888049 57860583646889550292416037)
        ·
          refine ⟨10848859433791790679828007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57860583646889550292416037 10848859433791790679828007)
          ·
            refine ⟨16273289150687686019742011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848859433791790679828007 16273289150687686019742011)
            ·
              refine ⟨24409933726031529029613017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273289150687686019742011 24409933726031529029613017)
              ·
                refine ⟨18307450294523646772209763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24409933726031529029613017 18307450294523646772209763)
                ·
                  refine ⟨27461175441785470158314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18307450294523646772209763 27461175441785470158314645)
                  ·
                    refine ⟨1287242598833693913670999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27461175441785470158314645 1287242598833693913670999)
                    ·
                      rfl

theorem cell22_3760344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_3760344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760344 prefixEnd_3760344 := by exact prefixLift 3760344
  have htrace : WordTrace (prefixWord ++ tailWord_3760344) baseStart_3760344 baseEnd_3760344 := by
    simpa [prefixWord, tailWord_3760344, baseEnd_3760344] using wordTrace_append hprefix tailTrace_3760344
  have hstable : (prefixWord ++ tailWord_3760344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760344).length < 2 ^ (prefixWord ++ tailWord_3760344).sum := by decide
  have hdescent : baseEnd_3760344 < baseStart_3760344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760346 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_3760346 : Nat := 118140960795 + 3760346 * 2 ^ 59
def prefixEnd_3760346 : Nat := 4983230072969 + 3 ^ 40 * 3760346 * 2
def baseEnd_3760346 : Nat := 1287243283474566575120993

theorem tailTrace_3760346 : CollatzResearch.WordTrace tailWord_3760346 prefixEnd_3760346 1287243283474566575120993 := by
  unfold tailWord_3760346
  simp only [CollatzResearch.WordTrace]
  refine ⟨34287771508729033203121223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91434057356610755208323261 34287771508729033203121223)
  ·
    refine ⟨51431657263093549804681835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34287771508729033203121223 51431657263093549804681835)
    ·
      refine ⟨77147485894640324707022753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51431657263093549804681835 77147485894640324707022753)
      ·
        refine ⟨57860614420980243530267065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77147485894640324707022753 57860614420980243530267065)
        ·
          refine ⟨43395460815735182647700299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57860614420980243530267065 43395460815735182647700299)
          ·
            refine ⟨65093191223602773971550449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43395460815735182647700299 65093191223602773971550449)
            ·
              refine ⟨48819893417702080478662837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65093191223602773971550449 48819893417702080478662837)
              ·
                refine ⟨4576865007909570044874641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48819893417702080478662837 4576865007909570044874641)
                ·
                  refine ⟨3432648755932177533655981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4576865007909570044874641 3432648755932177533655981)
                  ·
                    refine ⟨1287243283474566575120993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432648755932177533655981 1287243283474566575120993)
                    ·
                      rfl

theorem cell22_3760346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_3760346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760346 prefixEnd_3760346 := by exact prefixLift 3760346
  have htrace : WordTrace (prefixWord ++ tailWord_3760346) baseStart_3760346 baseEnd_3760346 := by
    simpa [prefixWord, tailWord_3760346, baseEnd_3760346] using wordTrace_append hprefix tailTrace_3760346
  have hstable : (prefixWord ++ tailWord_3760346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760346).length < 2 ^ (prefixWord ++ tailWord_3760346).sum := by decide
  have hdescent : baseEnd_3760346 < baseStart_3760346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760365 : List Nat := [1, 5, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3760365 : Nat := 118140960795 + 3760365 * 2 ^ 59
def prefixEnd_3760365 : Nat := 4983230072969 + 3 ^ 40 * 3760365 * 2
def baseEnd_3760365 : Nat := 429083262520952286298645

theorem tailTrace_3760365 : CollatzResearch.WordTrace tailWord_3760365 prefixEnd_3760365 429083262520952286298645 := by
  unfold tailWord_3760365
  simp only [CollatzResearch.WordTrace]
  refine ⟨137151779021847299057426549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91434519347898199371617699 137151779021847299057426549)
  ·
    refine ⟨12857979283298184286633739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137151779021847299057426549 12857979283298184286633739)
    ·
      refine ⟨19286968924947276429950609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12857979283298184286633739 19286968924947276429950609)
      ·
        refine ⟨14465226693710457322462957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19286968924947276429950609 14465226693710457322462957)
        ·
          refine ⟨5424460010141421495923609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14465226693710457322462957 5424460010141421495923609)
          ·
            refine ⟨4068345007606066121942707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5424460010141421495923609 4068345007606066121942707)
            ·
              refine ⟨6102517511409099182914061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068345007606066121942707 6102517511409099182914061)
              ·
                refine ⟨2288444066778412193592773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6102517511409099182914061 2288444066778412193592773)
                ·
                  refine ⟨429083262520952286298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288444066778412193592773 429083262520952286298645)
                  ·
                    rfl

theorem cell22_3760365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3760365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760365 prefixEnd_3760365 := by exact prefixLift 3760365
  have htrace : WordTrace (prefixWord ++ tailWord_3760365) baseStart_3760365 baseEnd_3760365 := by
    simpa [prefixWord, tailWord_3760365, baseEnd_3760365] using wordTrace_append hprefix tailTrace_3760365
  have hstable : (prefixWord ++ tailWord_3760365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760365).length < 2 ^ (prefixWord ++ tailWord_3760365).sum := by decide
  have hdescent : baseEnd_3760365 < baseStart_3760365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760442 : List Nat := [3, 1, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_3760442 : Nat := 118140960795 + 3760442 * 2 ^ 59
def prefixEnd_3760442 : Nat := 4983230072969 + 3 ^ 40 * 3760442 * 2
def baseEnd_3760442 : Nat := 1287276146236454324720699

theorem tailTrace_3760442 : CollatzResearch.WordTrace tailWord_3760442 prefixEnd_3760442 1287276146236454324720699 := by
  unfold tailWord_3760442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34288646860642085301994895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91436391628378894138653053 34288646860642085301994895)
  ·
    refine ⟨51432970290963127952992343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34288646860642085301994895 51432970290963127952992343)
    ·
      refine ⟨77149455436444691929488515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51432970290963127952992343 77149455436444691929488515)
      ·
        refine ⟨115724183154667037894232773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77149455436444691929488515 115724183154667037894232773)
        ·
          refine ⟨21698284341500069605168645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115724183154667037894232773 21698284341500069605168645)
          ·
            refine ⟨4068428314031263050969121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21698284341500069605168645 4068428314031263050969121)
            ·
              refine ⟨3051321235523447288226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068428314031263050969121 3051321235523447288226841)
              ·
                refine ⟨2288490926642585466170131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051321235523447288226841 2288490926642585466170131)
                ·
                  refine ⟨3432736389963878199255197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288490926642585466170131 3432736389963878199255197)
                  ·
                    refine ⟨1287276146236454324720699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432736389963878199255197 1287276146236454324720699)
                    ·
                      rfl

theorem cell22_3760442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_3760442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760442 prefixEnd_3760442 := by exact prefixLift 3760442
  have htrace : WordTrace (prefixWord ++ tailWord_3760442) baseStart_3760442 baseEnd_3760442 := by
    simpa [prefixWord, tailWord_3760442, baseEnd_3760442] using wordTrace_append hprefix tailTrace_3760442
  have hstable : (prefixWord ++ tailWord_3760442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760442).length < 2 ^ (prefixWord ++ tailWord_3760442).sum := by decide
  have hdescent : baseEnd_3760442 < baseStart_3760442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760483 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 4]
def baseStart_3760483 : Nat := 118140960795 + 3760483 * 2 ^ 59
def prefixEnd_3760483 : Nat := 4983230072969 + 3 ^ 40 * 3760483 * 2
def baseEnd_3760483 : Nat := 429096727124781294815191

theorem tailTrace_3760483 : CollatzResearch.WordTrace tailWord_3760483 prefixEnd_3760483 429096727124781294815191 := by
  unfold tailWord_3760483
  simp only [CollatzResearch.WordTrace]
  refine ⟨137156082835419805210222103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91437388556946536806814735 137156082835419805210222103)
  ·
    refine ⟨205734124253129707815333155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137156082835419805210222103 205734124253129707815333155)
    ·
      refine ⟨308601186379694561722999733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205734124253129707815333155 308601186379694561722999733)
      ·
        refine ⟨28931361223096365161531225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308601186379694561722999733 28931361223096365161531225)
        ·
          refine ⟨21698520917322273871148419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28931361223096365161531225 21698520917322273871148419)
          ·
            refine ⟨32547781375983410806722629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21698520917322273871148419 32547781375983410806722629)
            ·
              refine ⟨6102709007996889526260493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32547781375983410806722629 6102709007996889526260493)
              ·
                refine ⟨2288515877998833572347685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6102709007996889526260493 2288515877998833572347685)
                ·
                  refine ⟨429096727124781294815191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288515877998833572347685 429096727124781294815191)
                  ·
                    rfl

theorem cell22_3760483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 4].length) (baseStart_3760483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760483 prefixEnd_3760483 := by exact prefixLift 3760483
  have htrace : WordTrace (prefixWord ++ tailWord_3760483) baseStart_3760483 baseEnd_3760483 := by
    simpa [prefixWord, tailWord_3760483, baseEnd_3760483] using wordTrace_append hprefix tailTrace_3760483
  have hstable : (prefixWord ++ tailWord_3760483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760483).length < 2 ^ (prefixWord ++ tailWord_3760483).sum := by decide
  have hdescent : baseEnd_3760483 < baseStart_3760483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760485 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_3760485 : Nat := 118140960795 + 3760485 * 2 ^ 59
def prefixEnd_3760485 : Nat := 4983230072969 + 3 ^ 40 * 3760485 * 2
def baseEnd_3760485 : Nat := 1287290866015216545895567

theorem tailTrace_3760485 : CollatzResearch.WordTrace tailWord_3760485 prefixEnd_3760485 1287290866015216545895567 := by
  unfold tailWord_3760485
  simp only [CollatzResearch.WordTrace]
  refine ⟨137156155781412559551794909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91437437187608373034529939 137156155781412559551794909)
  ·
    refine ⟨51433558418029709831923091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137156155781412559551794909 51433558418029709831923091)
    ·
      refine ⟨77150337627044564747884637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51433558418029709831923091 77150337627044564747884637)
      ·
        refine ⟨28931376610141711780456739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77150337627044564747884637 28931376610141711780456739)
        ·
          refine ⟨43397064915212567670685109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28931376610141711780456739 43397064915212567670685109)
          ·
            refine ⟨4068474835801178219126729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43397064915212567670685109 4068474835801178219126729)
            ·
              refine ⟨3051356126850883664345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068474835801178219126729 3051356126850883664345047)
              ·
                refine ⟨4577034190276325496517571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051356126850883664345047 4577034190276325496517571)
                ·
                  refine ⟨6865551285414488244776357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577034190276325496517571 6865551285414488244776357)
                  ·
                    refine ⟨1287290866015216545895567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6865551285414488244776357 1287290866015216545895567)
                    ·
                      rfl

theorem cell22_3760485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_3760485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760485 prefixEnd_3760485 := by exact prefixLift 3760485
  have htrace : WordTrace (prefixWord ++ tailWord_3760485) baseStart_3760485 baseEnd_3760485 := by
    simpa [prefixWord, tailWord_3760485, baseEnd_3760485] using wordTrace_append hprefix tailTrace_3760485
  have hstable : (prefixWord ++ tailWord_3760485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760485).length < 2 ^ (prefixWord ++ tailWord_3760485).sum := by decide
  have hdescent : baseEnd_3760485 < baseStart_3760485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760498 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_3760498 : Nat := 118140960795 + 3760498 * 2 ^ 59
def prefixEnd_3760498 : Nat := 4983230072969 + 3 ^ 40 * 3760498 * 2
def baseEnd_3760498 : Nat := 1287295316180888845320527

theorem tailTrace_3760498 : CollatzResearch.WordTrace tailWord_3760498 prefixEnd_3760498 1287295316180888845320527 := by
  unfold tailWord_3760498
  simp only [CollatzResearch.WordTrace]
  refine ⟨34289157482591365693004537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91437753286910308514678765 34289157482591365693004537)
  ·
    refine ⟨25716868111943524269753403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34289157482591365693004537 25716868111943524269753403)
    ·
      refine ⟨38575302167915286404630105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25716868111943524269753403 38575302167915286404630105)
      ·
        refine ⟨28931476625936464803472579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38575302167915286404630105 28931476625936464803472579)
        ·
          refine ⟨43397214938904697205208869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28931476625936464803472579 43397214938904697205208869)
          ·
            refine ⟨8136977801044630725976663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43397214938904697205208869 8136977801044630725976663)
            ·
              refine ⟨12205466701566946088964995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8136977801044630725976663 12205466701566946088964995)
              ·
                refine ⟨18308200052350419133447493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12205466701566946088964995 18308200052350419133447493)
                ·
                  refine ⟨3432787509815703587521405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18308200052350419133447493 3432787509815703587521405)
                  ·
                    refine ⟨1287295316180888845320527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432787509815703587521405 1287295316180888845320527)
                    ·
                      rfl

theorem cell22_3760498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_3760498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760498 prefixEnd_3760498 := by exact prefixLift 3760498
  have htrace : WordTrace (prefixWord ++ tailWord_3760498) baseStart_3760498 baseEnd_3760498 := by
    simpa [prefixWord, tailWord_3760498, baseEnd_3760498] using wordTrace_append hprefix tailTrace_3760498
  have hstable : (prefixWord ++ tailWord_3760498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760498).length < 2 ^ (prefixWord ++ tailWord_3760498).sum := by decide
  have hdescent : baseEnd_3760498 < baseStart_3760498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760515 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 1, 5]
def baseStart_3760515 : Nat := 118140960795 + 3760515 * 2 ^ 59
def prefixEnd_3760515 : Nat := 4983230072969 + 3 ^ 40 * 3760515 * 2
def baseEnd_3760515 : Nat := 1287301135628306467645475

theorem tailTrace_3760515 : CollatzResearch.WordTrace tailWord_3760515 prefixEnd_3760515 1287301135628306467645475 := by
  unfold tailWord_3760515
  simp only [CollatzResearch.WordTrace]
  refine ⟨137157249971303874675386999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91438166647535916450257999 137157249971303874675386999)
  ·
    refine ⟨205735874956955812013080499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137157249971303874675386999 205735874956955812013080499)
    ·
      refine ⟨308603812435433718019620749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205735874956955812013080499 308603812435433718019620749)
      ·
        refine ⟨115726429663287644257357781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308603812435433718019620749 115726429663287644257357781)
        ·
          refine ⟨2712338195233304162281823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115726429663287644257357781 2712338195233304162281823)
          ·
            refine ⟨4068507292849956243422735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712338195233304162281823 4068507292849956243422735)
            ·
              refine ⟨6102760939274934365134103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068507292849956243422735 6102760939274934365134103)
              ·
                refine ⟨9154141408912401547701155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102760939274934365134103 9154141408912401547701155)
                ·
                  refine ⟨13731212113368602321551733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9154141408912401547701155 13731212113368602321551733)
                  ·
                    refine ⟨1287301135628306467645475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13731212113368602321551733 1287301135628306467645475)
                    ·
                      rfl

theorem cell22_3760515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 1, 5].length) (baseStart_3760515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760515 prefixEnd_3760515 := by exact prefixLift 3760515
  have htrace : WordTrace (prefixWord ++ tailWord_3760515) baseStart_3760515 baseEnd_3760515 := by
    simpa [prefixWord, tailWord_3760515, baseEnd_3760515] using wordTrace_append hprefix tailTrace_3760515
  have hstable : (prefixWord ++ tailWord_3760515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760515).length < 2 ^ (prefixWord ++ tailWord_3760515).sum := by decide
  have hdescent : baseEnd_3760515 < baseStart_3760515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760545 : List Nat := [1, 2, 3, 5, 2, 1, 8]
def baseStart_3760545 : Nat := 118140960795 + 3760545 * 2 ^ 59
def prefixEnd_3760545 : Nat := 4983230072969 + 3 ^ 40 * 3760545 * 2
def baseEnd_3760545 : Nat := 47678200194125792199829

theorem tailTrace_3760545 : CollatzResearch.WordTrace tailWord_3760545 prefixEnd_3760545 47678200194125792199829 := by
  unfold tailWord_3760545
  simp only [CollatzResearch.WordTrace]
  refine ⟨137158344161195189798979089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91438896107463459865986059 137158344161195189798979089)
  ·
    refine ⟨102868758120896392349234317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137158344161195189798979089 102868758120896392349234317)
    ·
      refine ⟨38575784295336147130962869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102868758120896392349234317 38575784295336147130962869)
      ·
        refine ⟨3616479777687763793527769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38575784295336147130962869 3616479777687763793527769)
        ·
          refine ⟨2712359833265822845145827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3616479777687763793527769 2712359833265822845145827)
          ·
            refine ⟨4068539749898734267718741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712359833265822845145827 4068539749898734267718741)
            ·
              refine ⟨47678200194125792199829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4068539749898734267718741 47678200194125792199829)
              ·
                rfl

theorem cell22_3760545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 8].length) (baseStart_3760545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760545 prefixEnd_3760545 := by exact prefixLift 3760545
  have htrace : WordTrace (prefixWord ++ tailWord_3760545) baseStart_3760545 baseEnd_3760545 := by
    simpa [prefixWord, tailWord_3760545, baseEnd_3760545] using wordTrace_append hprefix tailTrace_3760545
  have hstable : (prefixWord ++ tailWord_3760545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760545).length < 2 ^ (prefixWord ++ tailWord_3760545).sum := by decide
  have hdescent : baseEnd_3760545 < baseStart_3760545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760556 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_3760556 : Nat := 118140960795 + 3760556 * 2 ^ 59
def prefixEnd_3760556 : Nat := 4983230072969 + 3 ^ 40 * 3760556 * 2
def baseEnd_3760556 : Nat := 429105056922065342456783

theorem tailTrace_3760556 : CollatzResearch.WordTrace tailWord_3760556 prefixEnd_3760556 429105056922065342456783 := by
  unfold tailWord_3760556
  simp only [CollatzResearch.WordTrace]
  refine ⟨68579372682077669338814761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91439163576103559118419681 68579372682077669338814761)
  ·
    refine ⟨51434529511558252004111071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68579372682077669338814761 51434529511558252004111071)
    ·
      refine ⟨77151794267337378006166607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51434529511558252004111071 77151794267337378006166607)
      ·
        refine ⟨115727691401006067009249911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77151794267337378006166607 115727691401006067009249911)
        ·
          refine ⟨173591537101509100513874867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115727691401006067009249911 173591537101509100513874867)
          ·
            refine ⟨260387305652263650770812301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173591537101509100513874867 260387305652263650770812301)
            ·
              refine ⟨97645239619598869039054613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 260387305652263650770812301 97645239619598869039054613)
              ·
                refine ⟨4577120607168696986205685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97645239619598869039054613 4577120607168696986205685)
                ·
                  refine ⟨429105056922065342456783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577120607168696986205685 429105056922065342456783)
                  ·
                    rfl

theorem cell22_3760556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_3760556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760556 prefixEnd_3760556 := by exact prefixLift 3760556
  have htrace : WordTrace (prefixWord ++ tailWord_3760556) baseStart_3760556 baseEnd_3760556 := by
    simpa [prefixWord, tailWord_3760556, baseEnd_3760556] using wordTrace_append hprefix tailTrace_3760556
  have hstable : (prefixWord ++ tailWord_3760556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760556).length < 2 ^ (prefixWord ++ tailWord_3760556).sum := by decide
  have hdescent : baseEnd_3760556 < baseStart_3760556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760573 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 5]
def baseStart_3760573 : Nat := 118140960795 + 3760573 * 2 ^ 59
def prefixEnd_3760573 : Nat := 4983230072969 + 3 ^ 40 * 3760573 * 2
def baseEnd_3760573 : Nat := 429106996737871216565099

theorem tailTrace_3760573 : CollatzResearch.WordTrace tailWord_3760573 prefixEnd_3760573 429106996737871216565099 := by
  unfold tailWord_3760573
  simp only [CollatzResearch.WordTrace]
  refine ⟨137159365405093750580998373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91439576936729167053998915 137159365405093750580998373)
  ·
    refine ⟨25717381013455078233937195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137159365405093750580998373 25717381013455078233937195)
    ·
      refine ⟨38576071520182617350905793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25717381013455078233937195 38576071520182617350905793)
      ·
        refine ⟨28932053640136963013179345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38576071520182617350905793 28932053640136963013179345)
        ·
          refine ⟨21699040230102722259884509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28932053640136963013179345 21699040230102722259884509)
          ·
            refine ⟨8137140086288520847456691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21699040230102722259884509 8137140086288520847456691)
            ·
              refine ⟨12205710129432781271185037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137140086288520847456691 12205710129432781271185037)
              ·
                refine ⟨4577141298537292976694389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12205710129432781271185037 4577141298537292976694389)
                ·
                  refine ⟨429106996737871216565099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577141298537292976694389 429106996737871216565099)
                  ·
                    rfl

theorem cell22_3760573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_3760573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760573 prefixEnd_3760573 := by exact prefixLift 3760573
  have htrace : WordTrace (prefixWord ++ tailWord_3760573) baseStart_3760573 baseEnd_3760573 := by
    simpa [prefixWord, tailWord_3760573, baseEnd_3760573] using wordTrace_append hprefix tailTrace_3760573
  have hstable : (prefixWord ++ tailWord_3760573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760573).length < 2 ^ (prefixWord ++ tailWord_3760573).sum := by decide
  have hdescent : baseEnd_3760573 < baseStart_3760573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760611 : List Nat := [1, 1, 1, 6, 4, 1, 2, 2, 1, 3]
def baseStart_3760611 : Nat := 118140960795 + 3760611 * 2 ^ 59
def prefixEnd_3760611 : Nat := 4983230072969 + 3 ^ 40 * 3760611 * 2
def baseEnd_3760611 : Nat := 1287333998390194217245181

theorem tailTrace_3760611 : CollatzResearch.WordTrace tailWord_3760611 prefixEnd_3760611 1287333998390194217245181 := by
  unfold tailWord_3760611
  simp only [CollatzResearch.WordTrace]
  refine ⟨137160751378956083070881687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91440500919304055380587791 137160751378956083070881687)
  ·
    refine ⟨205741127068434124606322531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137160751378956083070881687 205741127068434124606322531)
    ·
      refine ⟨308611690602651186909483797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205741127068434124606322531 308611690602651186909483797)
      ·
        refine ⟨14466172996999274386382053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 308611690602651186909483797 14466172996999274386382053)
        ·
          refine ⟨2712407436937363947446635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14466172996999274386382053 2712407436937363947446635)
          ·
            refine ⟨4068611155406045921169953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712407436937363947446635 4068611155406045921169953)
            ·
              refine ⟨3051458366554534440877465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4068611155406045921169953 3051458366554534440877465)
              ·
                refine ⟨2288593774915900830658099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051458366554534440877465 2288593774915900830658099)
                ·
                  refine ⟨3432890662373851245987149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288593774915900830658099 3432890662373851245987149)
                  ·
                    refine ⟨1287333998390194217245181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432890662373851245987149 1287333998390194217245181)
                    ·
                      rfl

theorem cell22_3760611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 1, 3].length) (baseStart_3760611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760611 prefixEnd_3760611 := by exact prefixLift 3760611
  have htrace : WordTrace (prefixWord ++ tailWord_3760611) baseStart_3760611 baseEnd_3760611 := by
    simpa [prefixWord, tailWord_3760611, baseEnd_3760611] using wordTrace_append hprefix tailTrace_3760611
  have hstable : (prefixWord ++ tailWord_3760611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760611).length < 2 ^ (prefixWord ++ tailWord_3760611).sum := by decide
  have hdescent : baseEnd_3760611 < baseStart_3760611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760768 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_3760768 : Nat := 118140960795 + 3760768 * 2 ^ 59
def prefixEnd_3760768 : Nat := 4983230072969 + 3 ^ 40 * 3760768 * 2
def baseEnd_3760768 : Nat := 1287387742698698141069699

theorem tailTrace_3760768 : CollatzResearch.WordTrace tailWord_3760768 prefixEnd_3760768 1287387742698698141069699 := by
  unfold tailWord_3760768
  simp only [CollatzResearch.WordTrace]
  refine ⟨68583238819693649442173479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91444318426258199256231305 68583238819693649442173479)
  ·
    refine ⟨102874858229540474163260219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68583238819693649442173479 102874858229540474163260219)
    ·
      refine ⟨154312287344310711244890329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102874858229540474163260219 154312287344310711244890329)
      ·
        refine ⟨115734215508233033433667747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154312287344310711244890329 115734215508233033433667747)
        ·
          refine ⟨173601323262349550150501621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115734215508233033433667747 173601323262349550150501621)
          ·
            refine ⟨16275124055845270326609527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173601323262349550150501621 16275124055845270326609527)
            ·
              refine ⟨24412686083767905489914291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16275124055845270326609527 24412686083767905489914291)
              ·
                refine ⟨36619029125651858234871437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24412686083767905489914291 36619029125651858234871437)
                ·
                  refine ⟨13732135922119446838076789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36619029125651858234871437 13732135922119446838076789)
                  ·
                    refine ⟨1287387742698698141069699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13732135922119446838076789 1287387742698698141069699)
                    ·
                      rfl

theorem cell22_3760768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_3760768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760768 prefixEnd_3760768 := by exact prefixLift 3760768
  have htrace : WordTrace (prefixWord ++ tailWord_3760768) baseStart_3760768 baseEnd_3760768 := by
    simpa [prefixWord, tailWord_3760768, baseEnd_3760768] using wordTrace_append hprefix tailTrace_3760768
  have hstable : (prefixWord ++ tailWord_3760768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760768).length < 2 ^ (prefixWord ++ tailWord_3760768).sum := by decide
  have hdescent : baseEnd_3760768 < baseStart_3760768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760815 : List Nat := [1, 1, 2, 1, 2, 6, 3, 6]
def baseStart_3760815 : Nat := 118140960795 + 3760815 * 2 ^ 59
def prefixEnd_3760815 : Nat := 4983230072969 + 3 ^ 40 * 3760815 * 2
def baseEnd_3760815 : Nat := 143044870195467298349395

theorem tailTrace_3760815 : CollatzResearch.WordTrace tailWord_3760815 prefixEnd_3760815 143044870195467298349395 := by
  unfold tailWord_3760815
  simp only [CollatzResearch.WordTrace]
  refine ⟨137168191870217025911307899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91445461246811350607538599 137168191870217025911307899)
  ·
    refine ⟨205752287805325538866961849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137168191870217025911307899 205752287805325538866961849)
    ·
      refine ⟨154314215853994154150221387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205752287805325538866961849 154314215853994154150221387)
      ·
        refine ⟨231471323780991231225332081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154314215853994154150221387 231471323780991231225332081)
        ·
          refine ⟨173603492835743423418999061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231471323780991231225332081 173603492835743423418999061)
          ·
            refine ⟨8137663726675472972765581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 173603492835743423418999061 8137663726675472972765581)
            ·
              refine ⟨3051623897503302364787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8137663726675472972765581 3051623897503302364787093)
              ·
                refine ⟨143044870195467298349395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3051623897503302364787093 143044870195467298349395)
                ·
                  rfl

theorem cell22_3760815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 6].length) (baseStart_3760815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760815 prefixEnd_3760815 := by exact prefixLift 3760815
  have htrace : WordTrace (prefixWord ++ tailWord_3760815) baseStart_3760815 baseEnd_3760815 := by
    simpa [prefixWord, tailWord_3760815, baseEnd_3760815] using wordTrace_append hprefix tailTrace_3760815
  have hstable : (prefixWord ++ tailWord_3760815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760815).length < 2 ^ (prefixWord ++ tailWord_3760815).sum := by decide
  have hdescent : baseEnd_3760815 < baseStart_3760815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760817 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_3760817 : Nat := 118140960795 + 3760817 * 2 ^ 59
def prefixEnd_3760817 : Nat := 4983230072969 + 3 ^ 40 * 3760817 * 2
def baseEnd_3760817 : Nat := 1287404516400078346594549

theorem tailTrace_3760817 : CollatzResearch.WordTrace tailWord_3760817 prefixEnd_3760817 1287404516400078346594549 := by
  unfold tailWord_3760817
  simp only [CollatzResearch.WordTrace]
  refine ⟨137168264816209780252880705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91445509877473186835253803 137168264816209780252880705)
  ·
    refine ⟨102876198612157335189660529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137168264816209780252880705 102876198612157335189660529)
    ·
      refine ⟨77157148959118001392245397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102876198612157335189660529 77157148959118001392245397)
      ·
        refine ⟨3616741357458656315261503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77157148959118001392245397 3616741357458656315261503)
        ·
          refine ⟨5425112036187984472892255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616741357458656315261503 5425112036187984472892255)
          ·
            refine ⟨8137668054281976709338383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425112036187984472892255 8137668054281976709338383)
            ·
              refine ⟨12206502081422965064007575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137668054281976709338383 12206502081422965064007575)
              ·
                refine ⟨18309753122134447596011363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206502081422965064007575 18309753122134447596011363)
                ·
                  refine ⟨27464629683201671394017045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18309753122134447596011363 27464629683201671394017045)
                  ·
                    refine ⟨1287404516400078346594549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27464629683201671394017045 1287404516400078346594549)
                    ·
                      rfl

theorem cell22_3760817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_3760817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760817 prefixEnd_3760817 := by exact prefixLift 3760817
  have htrace : WordTrace (prefixWord ++ tailWord_3760817) baseStart_3760817 baseEnd_3760817 := by
    simpa [prefixWord, tailWord_3760817, baseEnd_3760817] using wordTrace_append hprefix tailTrace_3760817
  have hstable : (prefixWord ++ tailWord_3760817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760817).length < 2 ^ (prefixWord ++ tailWord_3760817).sum := by decide
  have hdescent : baseEnd_3760817 < baseStart_3760817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760898 : List Nat := [3, 4, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3760898 : Nat := 118140960795 + 3760898 * 2 ^ 59
def prefixEnd_3760898 : Nat := 4983230072969 + 3 ^ 40 * 3760898 * 2
def baseEnd_3760898 : Nat := 1287432244355421135319301

theorem tailTrace_3760898 : CollatzResearch.WordTrace tailWord_3760898 prefixEnd_3760898 1287432244355421135319301 := by
  unfold tailWord_3760898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292804782229082771644837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91447479419277554057719565 34292804782229082771644837)
  ·
    refine ⟨6429900896667953019683407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34292804782229082771644837 6429900896667953019683407)
    ·
      refine ⟨9644851345001929529525111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429900896667953019683407 9644851345001929529525111)
      ·
        refine ⟨14467277017502894294287667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9644851345001929529525111 14467277017502894294287667)
        ·
          refine ⟨21700915526254341441431501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14467277017502894294287667 21700915526254341441431501)
          ·
            refine ⟨8137843322345378040536813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21700915526254341441431501 8137843322345378040536813)
            ·
              refine ⟨3051691245879516765201305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8137843322345378040536813 3051691245879516765201305)
              ·
                refine ⟨2288768434409637573900979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051691245879516765201305 2288768434409637573900979)
                ·
                  refine ⟨3433152651614456360851469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288768434409637573900979 3433152651614456360851469)
                  ·
                    refine ⟨1287432244355421135319301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433152651614456360851469 1287432244355421135319301)
                    ·
                      rfl

theorem cell22_3760898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3760898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760898 prefixEnd_3760898 := by exact prefixLift 3760898
  have htrace : WordTrace (prefixWord ++ tailWord_3760898) baseStart_3760898 baseEnd_3760898 := by
    simpa [prefixWord, tailWord_3760898, baseEnd_3760898] using wordTrace_append hprefix tailTrace_3760898
  have hstable : (prefixWord ++ tailWord_3760898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760898).length < 2 ^ (prefixWord ++ tailWord_3760898).sum := by decide
  have hdescent : baseEnd_3760898 < baseStart_3760898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760905 : List Nat := [1, 2, 1, 1, 3, 2, 5, 1, 6]
def baseStart_3760905 : Nat := 118140960795 + 3760905 * 2 ^ 59
def prefixEnd_3760905 : Nat := 4983230072969 + 3 ^ 40 * 3760905 * 2
def baseEnd_3760905 : Nat := 429144880199491816798093

theorem tailTrace_3760905 : CollatzResearch.WordTrace tailWord_3760905 prefixEnd_3760905 429144880199491816798093 := by
  unfold tailWord_3760905
  simp only [CollatzResearch.WordTrace]
  refine ⟨137171474439890971282084169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91447649626593980854722779 137171474439890971282084169)
  ·
    refine ⟨102878605829918228461563127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137171474439890971282084169 102878605829918228461563127)
    ·
      refine ⟨154317908744877342692344691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102878605829918228461563127 154317908744877342692344691)
      ·
        refine ⟨231476863117316014038517037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154317908744877342692344691 231476863117316014038517037)
        ·
          refine ⟨86803823668993505264443889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231476863117316014038517037 86803823668993505264443889)
          ·
            refine ⟨65102867751745128948332917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86803823668993505264443889 65102867751745128948332917)
            ·
              refine ⟨6103393851726105838906211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65102867751745128948332917 6103393851726105838906211)
              ·
                refine ⟨9155090777589158758359317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103393851726105838906211 9155090777589158758359317)
                ·
                  refine ⟨429144880199491816798093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9155090777589158758359317 429144880199491816798093)
                  ·
                    rfl

theorem cell22_3760905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_3760905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760905 prefixEnd_3760905 := by exact prefixLift 3760905
  have htrace : WordTrace (prefixWord ++ tailWord_3760905) baseStart_3760905 baseEnd_3760905 := by
    simpa [prefixWord, tailWord_3760905, baseEnd_3760905] using wordTrace_append hprefix tailTrace_3760905
  have hstable : (prefixWord ++ tailWord_3760905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760905).length < 2 ^ (prefixWord ++ tailWord_3760905).sum := by decide
  have hdescent : baseEnd_3760905 < baseStart_3760905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760920 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_3760920 : Nat := 118140960795 + 3760920 * 2 ^ 59
def prefixEnd_3760920 : Nat := 4983230072969 + 3 ^ 40 * 3760920 * 2
def baseEnd_3760920 : Nat := 1287439775405020411269233

theorem tailTrace_3760920 : CollatzResearch.WordTrace tailWord_3760920 prefixEnd_3760920 1287439775405020411269233 := by
  unfold tailWord_3760920
  simp only [CollatzResearch.WordTrace]
  refine ⟨68586010767418314421940107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91448014356557752562586809 68586010767418314421940107)
  ·
    refine ⟨102879016151127471632910161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68586010767418314421940107 102879016151127471632910161)
    ·
      refine ⟨77159262113345603724682621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102879016151127471632910161 77159262113345603724682621)
      ·
        refine ⟨28934723292504601396755983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77159262113345603724682621 28934723292504601396755983)
        ·
          refine ⟨43402084938756902095133975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28934723292504601396755983 43402084938756902095133975)
          ·
            refine ⟨65103127408135353142700963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43402084938756902095133975 65103127408135353142700963)
            ·
              refine ⟨97654691112203029714051445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65103127408135353142700963 97654691112203029714051445)
              ·
                refine ⟨9155127291769034035692323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97654691112203029714051445 9155127291769034035692323)
                ·
                  refine ⟨13732690937653551053538485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9155127291769034035692323 13732690937653551053538485)
                  ·
                    refine ⟨1287439775405020411269233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13732690937653551053538485 1287439775405020411269233)
                    ·
                      rfl

theorem cell22_3760920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_3760920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760920 prefixEnd_3760920 := by exact prefixLift 3760920
  have htrace : WordTrace (prefixWord ++ tailWord_3760920) baseStart_3760920 baseEnd_3760920 := by
    simpa [prefixWord, tailWord_3760920, baseEnd_3760920] using wordTrace_append hprefix tailTrace_3760920
  have hstable : (prefixWord ++ tailWord_3760920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760920).length < 2 ^ (prefixWord ++ tailWord_3760920).sum := by decide
  have hdescent : baseEnd_3760920 < baseStart_3760920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3760924 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_3760924 : Nat := 118140960795 + 3760924 * 2 ^ 59
def prefixEnd_3760924 : Nat := 4983230072969 + 3 ^ 40 * 3760924 * 2
def baseEnd_3760924 : Nat := 1287441144686765734169221

theorem tailTrace_3760924 : CollatzResearch.WordTrace tailWord_3760924 prefixEnd_3760924 1287441144686765734169221 := by
  unfold tailWord_3760924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68586083713411068763512913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91448111617881425018017217 68586083713411068763512913)
  ·
    refine ⟨51439562785058301572634685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68586083713411068763512913 51439562785058301572634685)
    ·
      refine ⟨19289836044396863089738007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51439562785058301572634685 19289836044396863089738007)
      ·
        refine ⟨28934754066595294634607011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19289836044396863089738007 28934754066595294634607011)
        ·
          refine ⟨43402131099892941951910517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28934754066595294634607011 43402131099892941951910517)
          ·
            refine ⟨4068949790614963307991611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43402131099892941951910517 4068949790614963307991611)
            ·
              refine ⟨6103424685922444961987417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068949790614963307991611 6103424685922444961987417)
              ·
                refine ⟨4577568514441833721490563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6103424685922444961987417 4577568514441833721490563)
                ·
                  refine ⟨6866352771662750582235845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4577568514441833721490563 6866352771662750582235845)
                  ·
                    refine ⟨1287441144686765734169221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6866352771662750582235845 1287441144686765734169221)
                    ·
                      rfl

theorem cell22_3760924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_3760924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3760924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3760924 prefixEnd_3760924 := by exact prefixLift 3760924
  have htrace : WordTrace (prefixWord ++ tailWord_3760924) baseStart_3760924 baseEnd_3760924 := by
    simpa [prefixWord, tailWord_3760924, baseEnd_3760924] using wordTrace_append hprefix tailTrace_3760924
  have hstable : (prefixWord ++ tailWord_3760924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3760924).length < 2 ^ (prefixWord ++ tailWord_3760924).sum := by decide
  have hdescent : baseEnd_3760924 < baseStart_3760924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3760924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761029 : List Nat := [1, 3, 1, 1, 3, 4, 3, 1, 5]
def baseStart_3761029 : Nat := 118140960795 + 3761029 * 2 ^ 59
def prefixEnd_3761029 : Nat := 4983230072969 + 3 ^ 40 * 3761029 * 2
def baseEnd_3761029 : Nat := 429159029444193486764633

theorem tailTrace_3761029 : CollatzResearch.WordTrace tailWord_3761029 prefixEnd_3761029 429159029444193486764633 := by
  unfold tailWord_3761029
  simp only [CollatzResearch.WordTrace]
  refine ⟨137175997091441740459598141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91450664727627826973065427 137175997091441740459598141)
  ·
    refine ⟨51440998909290652672349303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137175997091441740459598141 51440998909290652672349303)
    ·
      refine ⟨77161498363935979008523955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51440998909290652672349303 77161498363935979008523955)
      ·
        refine ⟨115742247545903968512785933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77161498363935979008523955 115742247545903968512785933)
        ·
          refine ⟨43403342829713988192294725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115742247545903968512785933 43403342829713988192294725)
          ·
            refine ⟨8138126780571372786055261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43403342829713988192294725 8138126780571372786055261)
            ·
              refine ⟨3051797542714264794770723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8138126780571372786055261 3051797542714264794770723)
              ·
                refine ⟨4577696314071397192156085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3051797542714264794770723 4577696314071397192156085)
                ·
                  refine ⟨429159029444193486764633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4577696314071397192156085 429159029444193486764633)
                  ·
                    rfl

theorem cell22_3761029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_3761029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761029 prefixEnd_3761029 := by exact prefixLift 3761029
  have htrace : WordTrace (prefixWord ++ tailWord_3761029) baseStart_3761029 baseEnd_3761029 := by
    simpa [prefixWord, tailWord_3761029, baseEnd_3761029] using wordTrace_append hprefix tailTrace_3761029
  have hstable : (prefixWord ++ tailWord_3761029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761029).length < 2 ^ (prefixWord ++ tailWord_3761029).sum := by decide
  have hdescent : baseEnd_3761029 < baseStart_3761029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761046 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3761046 : Nat := 118140960795 + 3761046 * 2 ^ 59
def prefixEnd_3761046 : Nat := 4983230072969 + 3 ^ 40 * 3761046 * 2
def baseEnd_3761046 : Nat := 429160969259999360872949

theorem tailTrace_3761046 : CollatzResearch.WordTrace tailWord_3761046 prefixEnd_3761046 429160969259999360872949 := by
  unfold tailWord_3761046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573538570773759522685437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91451078088253434908644661 8573538570773759522685437)
  ·
    refine ⟨3215076964040159821007039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8573538570773759522685437 3215076964040159821007039)
    ·
      refine ⟨4822615446060239731510559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215076964040159821007039 4822615446060239731510559)
      ·
        refine ⟨7233923169090359597265839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822615446060239731510559 7233923169090359597265839)
        ·
          refine ⟨10850884753635539395898759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7233923169090359597265839 10850884753635539395898759)
          ·
            refine ⟨16276327130453309093848139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850884753635539395898759 16276327130453309093848139)
            ·
              refine ⟨24414490695679963640772209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16276327130453309093848139 24414490695679963640772209)
              ·
                refine ⟨18310868021759972730579157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24414490695679963640772209 18310868021759972730579157)
                ·
                  refine ⟨429160969259999360872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18310868021759972730579157 429160969259999360872949)
                  ·
                    rfl

theorem cell22_3761046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3761046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761046 prefixEnd_3761046 := by exact prefixLift 3761046
  have htrace : WordTrace (prefixWord ++ tailWord_3761046) baseStart_3761046 baseEnd_3761046 := by
    simpa [prefixWord, tailWord_3761046, baseEnd_3761046] using wordTrace_append hprefix tailTrace_3761046
  have hstable : (prefixWord ++ tailWord_3761046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761046).length < 2 ^ (prefixWord ++ tailWord_3761046).sum := by decide
  have hdescent : baseEnd_3761046 < baseStart_3761046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761050 : List Nat := [3, 1, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_3761050 : Nat := 118140960795 + 3761050 * 2 ^ 59
def prefixEnd_3761050 : Nat := 4983230072969 + 3 ^ 40 * 3761050 * 2
def baseEnd_3761050 : Nat := 1287484277061743405518835

theorem tailTrace_3761050 : CollatzResearch.WordTrace tailWord_3761050 prefixEnd_3761050 1287484277061743405518835 := by
  unfold tailWord_3761050
  simp only [CollatzResearch.WordTrace]
  refine ⟨34294190756091415261528151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91451175349577107364075069 34294190756091415261528151)
  ·
    refine ⟨51441286134137122892292227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34294190756091415261528151 51441286134137122892292227)
    ·
      refine ⟨77161929201205684338438341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51441286134137122892292227 77161929201205684338438341)
      ·
        refine ⟨14467861725226065813457189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77161929201205684338438341 14467861725226065813457189)
        ·
          refine ⟨2712724073479887340023223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14467861725226065813457189 2712724073479887340023223)
          ·
            refine ⟨4069086110219831010034835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712724073479887340023223 4069086110219831010034835)
            ·
              refine ⟨6103629165329746515052253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069086110219831010034835 6103629165329746515052253)
              ·
                refine ⟨2288860936998654943144595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6103629165329746515052253 2288860936998654943144595)
                ·
                  refine ⟨3433291405497982414716893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288860936998654943144595 3433291405497982414716893)
                  ·
                    refine ⟨1287484277061743405518835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433291405497982414716893 1287484277061743405518835)
                    ·
                      rfl

theorem cell22_3761050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_3761050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761050 prefixEnd_3761050 := by exact prefixLift 3761050
  have htrace : WordTrace (prefixWord ++ tailWord_3761050) baseStart_3761050 baseEnd_3761050 := by
    simpa [prefixWord, tailWord_3761050, baseEnd_3761050] using wordTrace_append hprefix tailTrace_3761050
  have hstable : (prefixWord ++ tailWord_3761050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761050).length < 2 ^ (prefixWord ++ tailWord_3761050).sum := by decide
  have hdescent : baseEnd_3761050 < baseStart_3761050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761102 : List Nat := [4, 1, 1, 1, 2, 3, 2, 8]
def baseStart_3761102 : Nat := 118140960795 + 3761102 * 2 ^ 59
def prefixEnd_3761102 : Nat := 4983230072969 + 3 ^ 40 * 3761102 * 2
def baseEnd_3761102 : Nat := 143055786413825844802075

theorem tailTrace_3761102 : CollatzResearch.WordTrace tailWord_3761102 prefixEnd_3761102 143055786413825844802075 := by
  unfold tailWord_3761102
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147332452522159240875695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91452439746784849284670373 17147332452522159240875695)
  ·
    refine ⟨25720998678783238861313543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147332452522159240875695 25720998678783238861313543)
    ·
      refine ⟨38581498018174858291970315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25720998678783238861313543 38581498018174858291970315)
      ·
        refine ⟨57872247027262287437955473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38581498018174858291970315 57872247027262287437955473)
        ·
          refine ⟨43404185270446715578466605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57872247027262287437955473 43404185270446715578466605)
          ·
            refine ⟨16276569476417518341924977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43404185270446715578466605 16276569476417518341924977)
            ·
              refine ⟨12207427107313138756443733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16276569476417518341924977 12207427107313138756443733)
              ·
                refine ⟨143055786413825844802075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12207427107313138756443733 143055786413825844802075)
                ·
                  rfl

theorem cell22_3761102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_3761102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761102 prefixEnd_3761102 := by exact prefixLift 3761102
  have htrace : WordTrace (prefixWord ++ tailWord_3761102) baseStart_3761102 baseEnd_3761102 := by
    simpa [prefixWord, tailWord_3761102, baseEnd_3761102] using wordTrace_append hprefix tailTrace_3761102
  have hstable : (prefixWord ++ tailWord_3761102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761102).length < 2 ^ (prefixWord ++ tailWord_3761102).sum := by decide
  have hdescent : baseEnd_3761102 < baseStart_3761102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761125 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 4]
def baseStart_3761125 : Nat := 118140960795 + 3761125 * 2 ^ 59
def prefixEnd_3761125 : Nat := 4983230072969 + 3 ^ 40 * 3761125 * 2
def baseEnd_3761125 : Nat := 429169983698156069964535

theorem tailTrace_3761125 : CollatzResearch.WordTrace tailWord_3761125 prefixEnd_3761125 429169983698156069964535 := by
  unfold tailWord_3761125
  simp only [CollatzResearch.WordTrace]
  refine ⟨137179498499093948855092829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91452998999395965903395219 137179498499093948855092829)
  ·
    refine ⟨51442311937160230820659811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137179498499093948855092829 51442311937160230820659811)
    ·
      refine ⟨77163467905740346230989717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51442311937160230820659811 77163467905740346230989717)
      ·
        refine ⟨3617037558081578729577643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77163467905740346230989717 3617037558081578729577643)
        ·
          refine ⟨5425556337122368094366465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617037558081578729577643 5425556337122368094366465)
          ·
            refine ⟨4069167252841776070774849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5425556337122368094366465 4069167252841776070774849)
            ·
              refine ⟨3051875439631332053081137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4069167252841776070774849 3051875439631332053081137)
              ·
                refine ⟨2288906579723499039810853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051875439631332053081137 2288906579723499039810853)
                ·
                  refine ⟨429169983698156069964535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288906579723499039810853 429169983698156069964535)
                  ·
                    rfl

theorem cell22_3761125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_3761125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761125 prefixEnd_3761125 := by exact prefixLift 3761125
  have htrace : WordTrace (prefixWord ++ tailWord_3761125) baseStart_3761125 baseEnd_3761125 := by
    simpa [prefixWord, tailWord_3761125, baseEnd_3761125] using wordTrace_append hprefix tailTrace_3761125
  have hstable : (prefixWord ++ tailWord_3761125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761125).length < 2 ^ (prefixWord ++ tailWord_3761125).sum := by decide
  have hdescent : baseEnd_3761125 < baseStart_3761125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761209 : List Nat := [1, 2, 1, 5, 2, 1, 2, 2, 6]
def baseStart_3761209 : Nat := 118140960795 + 3761209 * 2 ^ 59
def prefixEnd_3761209 : Nat := 4983230072969 + 3 ^ 40 * 3761209 * 2
def baseEnd_3761209 : Nat := 429179568670373330264449

theorem tailTrace_3761209 : CollatzResearch.WordTrace tailWord_3761209 prefixEnd_3761209 429179568670373330264449 := by
  unfold tailWord_3761209
  simp only [CollatzResearch.WordTrace]
  refine ⟨137182562230789631201150681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91455041487193087467433787 137182562230789631201150681)
  ·
    refine ⟨102886921673092223400863011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137182562230789631201150681 102886921673092223400863011)
    ·
      refine ⟨154330382509638335101294517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102886921673092223400863011 154330382509638335101294517)
      ·
        refine ⟨14468473360278593915746361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154330382509638335101294517 14468473360278593915746361)
        ·
          refine ⟨10851355020208945436809771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14468473360278593915746361 10851355020208945436809771)
          ·
            refine ⟨16277032530313418155214657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10851355020208945436809771 16277032530313418155214657)
            ·
              refine ⟨12207774397735063616410993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16277032530313418155214657 12207774397735063616410993)
              ·
                refine ⟨9155830798301297712308245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12207774397735063616410993 9155830798301297712308245)
                ·
                  refine ⟨429179568670373330264449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9155830798301297712308245 429179568670373330264449)
                  ·
                    rfl

theorem cell22_3761209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_3761209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761209 prefixEnd_3761209 := by exact prefixLift 3761209
  have htrace : WordTrace (prefixWord ++ tailWord_3761209) baseStart_3761209 baseEnd_3761209 := by
    simpa [prefixWord, tailWord_3761209, baseEnd_3761209] using wordTrace_append hprefix tailTrace_3761209
  have hstable : (prefixWord ++ tailWord_3761209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761209).length < 2 ^ (prefixWord ++ tailWord_3761209).sum := by decide
  have hdescent : baseEnd_3761209 < baseStart_3761209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761224 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_3761224 : Nat := 118140960795 + 3761224 * 2 ^ 59
def prefixEnd_3761224 : Nat := 4983230072969 + 3 ^ 40 * 3761224 * 2
def baseEnd_3761224 : Nat := 1287543840817664951668301

theorem tailTrace_3761224 : CollatzResearch.WordTrace tailWord_3761224 prefixEnd_3761224 1287543840817664951668301 := by
  unfold tailWord_3761224
  simp only [CollatzResearch.WordTrace]
  refine ⟨68591554662867644381473363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91455406217156859175297817 68591554662867644381473363)
  ·
    refine ⟨102887331994301466572210045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68591554662867644381473363 102887331994301466572210045)
    ·
      refine ⟨38582749497863049964578767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102887331994301466572210045 38582749497863049964578767)
      ·
        refine ⟨57874124246794574946868151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38582749497863049964578767 57874124246794574946868151)
        ·
          refine ⟨86811186370191862420302227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57874124246794574946868151 86811186370191862420302227)
          ·
            refine ⟨130216779555287793630453341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86811186370191862420302227 130216779555287793630453341)
            ·
              refine ⟨48831292333232922611420003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130216779555287793630453341 48831292333232922611420003)
              ·
                refine ⟨73246938499849383917130005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48831292333232922611420003 73246938499849383917130005)
                ·
                  refine ⟨3433450242180439871115469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73246938499849383917130005 3433450242180439871115469)
                  ·
                    refine ⟨1287543840817664951668301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433450242180439871115469 1287543840817664951668301)
                    ·
                      rfl

theorem cell22_3761224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_3761224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761224 prefixEnd_3761224 := by exact prefixLift 3761224
  have htrace : WordTrace (prefixWord ++ tailWord_3761224) baseStart_3761224 baseEnd_3761224 := by
    simpa [prefixWord, tailWord_3761224, baseEnd_3761224] using wordTrace_append hprefix tailTrace_3761224
  have hstable : (prefixWord ++ tailWord_3761224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761224).length < 2 ^ (prefixWord ++ tailWord_3761224).sum := by decide
  have hdescent : baseEnd_3761224 < baseStart_3761224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761226 : List Nat := [3, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_3761226 : Nat := 118140960795 + 3761226 * 2 ^ 59
def prefixEnd_3761226 : Nat := 4983230072969 + 3 ^ 40 * 3761226 * 2
def baseEnd_3761226 : Nat := 429181508486179204372765

theorem tailTrace_3761226 : CollatzResearch.WordTrace tailWord_3761226 prefixEnd_3761226 429181508486179204372765 := by
  unfold tailWord_3761226
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295795567932010776129883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91455454847818695403013021 34295795567932010776129883)
  ·
    refine ⟨51443693351898016164194825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34295795567932010776129883 51443693351898016164194825)
    ·
      refine ⟨38582770013923512123146119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51443693351898016164194825 38582770013923512123146119)
      ·
        refine ⟨57874155020885268184719179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38582770013923512123146119 57874155020885268184719179)
        ·
          refine ⟨86811232531327902277078769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57874155020885268184719179 86811232531327902277078769)
          ·
            refine ⟨65108424398495926707809077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86811232531327902277078769 65108424398495926707809077)
            ·
              refine ⟨6103914787358993128857101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65108424398495926707809077 6103914787358993128857101)
              ·
                refine ⟨2288968045259622423321413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6103914787358993128857101 2288968045259622423321413)
                ·
                  refine ⟨429181508486179204372765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288968045259622423321413 429181508486179204372765)
                  ·
                    rfl

theorem cell22_3761226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_3761226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761226 prefixEnd_3761226 := by exact prefixLift 3761226
  have htrace : WordTrace (prefixWord ++ tailWord_3761226) baseStart_3761226 baseEnd_3761226 := by
    simpa [prefixWord, tailWord_3761226, baseEnd_3761226] using wordTrace_append hprefix tailTrace_3761226
  have hstable : (prefixWord ++ tailWord_3761226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761226).length < 2 ^ (prefixWord ++ tailWord_3761226).sum := by decide
  have hdescent : baseEnd_3761226 < baseStart_3761226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761258 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3761258 : Nat := 118140960795 + 3761258 * 2 ^ 59
def prefixEnd_3761258 : Nat := 4983230072969 + 3 ^ 40 * 3761258 * 2
def baseEnd_3761258 : Nat := 1287555479712500196318197

theorem tailTrace_3761258 : CollatzResearch.WordTrace tailWord_3761258 prefixEnd_3761258 1287555479712500196318197 := by
  unfold tailWord_3761258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34296087351903028142421107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91456232938408075046456285 34296087351903028142421107)
  ·
    refine ⟨51444131027854542213631661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34296087351903028142421107 51444131027854542213631661)
    ·
      refine ⟨19291549135445453330111873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51444131027854542213631661 19291549135445453330111873)
      ·
        refine ⟨14468661851584089997583905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19291549135445453330111873 14468661851584089997583905)
        ·
          refine ⟨10851496388688067498187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14468661851584089997583905 10851496388688067498187929)
          ·
            refine ⟨8138622291516050623640947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851496388688067498187929 8138622291516050623640947)
            ·
              refine ⟨12207933437274075935461421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138622291516050623640947 12207933437274075935461421)
              ·
                refine ⟨4577975038977778475798033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12207933437274075935461421 4577975038977778475798033)
                ·
                  refine ⟨3433481279233333856848525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4577975038977778475798033 3433481279233333856848525)
                  ·
                    refine ⟨1287555479712500196318197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433481279233333856848525 1287555479712500196318197)
                    ·
                      rfl

theorem cell22_3761258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3761258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761258 prefixEnd_3761258 := by exact prefixLift 3761258
  have htrace : WordTrace (prefixWord ++ tailWord_3761258) baseStart_3761258 baseEnd_3761258 := by
    simpa [prefixWord, tailWord_3761258, baseEnd_3761258] using wordTrace_append hprefix tailTrace_3761258
  have hstable : (prefixWord ++ tailWord_3761258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761258).length < 2 ^ (prefixWord ++ tailWord_3761258).sum := by decide
  have hdescent : baseEnd_3761258 < baseStart_3761258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761299 : List Nat := [1, 1, 1, 2, 1, 2, 5, 4, 5]
def baseStart_3761299 : Nat := 118140960795 + 3761299 * 2 ^ 59
def prefixEnd_3761299 : Nat := 4983230072969 + 3 ^ 40 * 3761299 * 2
def baseEnd_3761299 : Nat := 429189838283463252014357

theorem tailTrace_3761299 : CollatzResearch.WordTrace tailWord_3761299 prefixEnd_3761299 429189838283463252014357 := by
  unfold tailWord_3761299
  simp only [CollatzResearch.WordTrace]
  refine ⟨137185844800463576571926951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91457229866975717714617967 137185844800463576571926951)
  ·
    refine ⟨205778767200695364857890427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137185844800463576571926951 205778767200695364857890427)
    ·
      refine ⟨308668150801043047286835641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205778767200695364857890427 308668150801043047286835641)
      ·
        refine ⟨231501113100782285465126731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308668150801043047286835641 231501113100782285465126731)
        ·
          refine ⟨347251669651173428197690097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231501113100782285465126731 347251669651173428197690097)
          ·
            refine ⟨260438752238380071148267573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347251669651173428197690097 260438752238380071148267573)
            ·
              refine ⟨24416133022348131670150085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260438752238380071148267573 24416133022348131670150085)
              ·
                refine ⟨4578024941690274688153141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24416133022348131670150085 4578024941690274688153141)
                ·
                  refine ⟨429189838283463252014357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4578024941690274688153141 429189838283463252014357)
                  ·
                    rfl

theorem cell22_3761299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].length) (baseStart_3761299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761299 prefixEnd_3761299 := by exact prefixLift 3761299
  have htrace : WordTrace (prefixWord ++ tailWord_3761299) baseStart_3761299 baseEnd_3761299 := by
    simpa [prefixWord, tailWord_3761299, baseEnd_3761299] using wordTrace_append hprefix tailTrace_3761299
  have hstable : (prefixWord ++ tailWord_3761299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761299).length < 2 ^ (prefixWord ++ tailWord_3761299).sum := by decide
  have hdescent : baseEnd_3761299 < baseStart_3761299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761316 : List Nat := [2, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3761316 : Nat := 118140960795 + 3761316 * 2 ^ 59
def prefixEnd_3761316 : Nat := 4983230072969 + 3 ^ 40 * 3761316 * 2
def baseEnd_3761316 : Nat := 429191778099269126122673

theorem tailTrace_3761316 : CollatzResearch.WordTrace tailWord_3761316 prefixEnd_3761316 429191778099269126122673 := by
  unfold tailWord_3761316
  simp only [CollatzResearch.WordTrace]
  refine ⟨68593232420700994237647901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91457643227601325650197201 68593232420700994237647901)
  ·
    refine ⟨25722462157762872839117963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68593232420700994237647901 25722462157762872839117963)
    ·
      refine ⟨38583693236644309258676945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25722462157762872839117963 38583693236644309258676945)
      ·
        refine ⟨28937769927483231944007709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38583693236644309258676945 28937769927483231944007709)
        ·
          refine ⟨10851663722806211979002891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28937769927483231944007709 10851663722806211979002891)
          ·
            refine ⟨16277495584209317968504337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10851663722806211979002891 16277495584209317968504337)
            ·
              refine ⟨12208121688156988476378253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16277495584209317968504337 12208121688156988476378253)
              ·
                refine ⟨4578045633058870678641845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12208121688156988476378253 4578045633058870678641845)
                ·
                  refine ⟨429191778099269126122673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4578045633058870678641845 429191778099269126122673)
                  ·
                    rfl

theorem cell22_3761316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3761316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761316 prefixEnd_3761316 := by exact prefixLift 3761316
  have htrace : WordTrace (prefixWord ++ tailWord_3761316) baseStart_3761316 baseEnd_3761316 := by
    simpa [prefixWord, tailWord_3761316, baseEnd_3761316] using wordTrace_append hprefix tailTrace_3761316
  have hstable : (prefixWord ++ tailWord_3761316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761316).length < 2 ^ (prefixWord ++ tailWord_3761316).sum := by decide
  have hdescent : baseEnd_3761316 < baseStart_3761316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761376 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_3761376 : Nat := 118140960795 + 3761376 * 2 ^ 59
def prefixEnd_3761376 : Nat := 4983230072969 + 3 ^ 40 * 3761376 * 2
def baseEnd_3761376 : Nat := 1287595873523987221867835

theorem tailTrace_3761376 : CollatzResearch.WordTrace tailWord_3761376 prefixEnd_3761376 1287595873523987221867835 := by
  unfold tailWord_3761376
  simp only [CollatzResearch.WordTrace]
  refine ⟨68594326610592309361239991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91459102147456412481653321 68594326610592309361239991)
  ·
    refine ⟨102891489915888464041859987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68594326610592309361239991 102891489915888464041859987)
    ·
      refine ⟨154337234873832696062789981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102891489915888464041859987 154337234873832696062789981)
      ·
        refine ⟨57876463077687261023546243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154337234873832696062789981 57876463077687261023546243)
        ·
          refine ⟨86814694616530891535319365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57876463077687261023546243 86814694616530891535319365)
          ·
            refine ⟨16277755240599542162872381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86814694616530891535319365 16277755240599542162872381)
            ·
              refine ⟨6104158215224828311077143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16277755240599542162872381 6104158215224828311077143)
              ·
                refine ⟨9156237322837242466615715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104158215224828311077143 9156237322837242466615715)
                ·
                  refine ⟨13734355984255863699923573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156237322837242466615715 13734355984255863699923573)
                  ·
                    refine ⟨1287595873523987221867835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734355984255863699923573 1287595873523987221867835)
                    ·
                      rfl

theorem cell22_3761376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_3761376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761376 prefixEnd_3761376 := by exact prefixLift 3761376
  have htrace : WordTrace (prefixWord ++ tailWord_3761376) baseStart_3761376 baseEnd_3761376 := by
    simpa [prefixWord, tailWord_3761376, baseEnd_3761376] using wordTrace_append hprefix tailTrace_3761376
  have hstable : (prefixWord ++ tailWord_3761376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761376).length < 2 ^ (prefixWord ++ tailWord_3761376).sum := by decide
  have hdescent : baseEnd_3761376 < baseStart_3761376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761406 : List Nat := [4, 2, 2, 1, 1, 2, 10]
def baseStart_3761406 : Nat := 118140960795 + 3761406 * 2 ^ 59
def prefixEnd_3761406 : Nat := 4983230072969 + 3 ^ 40 * 3761406 * 2
def baseEnd_3761406 : Nat := 47689116412484338652509

theorem tailTrace_3761406 : CollatzResearch.WordTrace tailWord_3761406 prefixEnd_3761406 47689116412484338652509 := by
  unfold tailWord_3761406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148718426384491730759009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91459831607383955897381381 17148718426384491730759009)
  ·
    refine ⟨12861538819788368798069257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17148718426384491730759009 12861538819788368798069257)
    ·
      refine ⟨9646154114841276598551943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12861538819788368798069257 9646154114841276598551943)
      ·
        refine ⟨14469231172261914897827915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9646154114841276598551943 14469231172261914897827915)
        ·
          refine ⟨21703846758392872346741873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14469231172261914897827915 21703846758392872346741873)
          ·
            refine ⟨16277885068794654260056405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21703846758392872346741873 16277885068794654260056405)
            ·
              refine ⟨47689116412484338652509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16277885068794654260056405 47689116412484338652509)
              ·
                rfl

theorem cell22_3761406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 10].length) (baseStart_3761406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761406 prefixEnd_3761406 := by exact prefixLift 3761406
  have htrace : WordTrace (prefixWord ++ tailWord_3761406) baseStart_3761406 baseEnd_3761406 := by
    simpa [prefixWord, tailWord_3761406, baseEnd_3761406] using wordTrace_append hprefix tailTrace_3761406
  have hstable : (prefixWord ++ tailWord_3761406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761406).length < 2 ^ (prefixWord ++ tailWord_3761406).sum := by decide
  have hdescent : baseEnd_3761406 < baseStart_3761406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761466 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_3761466 : Nat := 118140960795 + 3761466 * 2 ^ 59
def prefixEnd_3761466 : Nat := 4983230072969 + 3 ^ 40 * 3761466 * 2
def baseEnd_3761466 : Nat := 1287626682363256987117559

theorem tailTrace_3761466 : CollatzResearch.WordTrace tailWord_3761466 prefixEnd_3761466 1287626682363256987117559 := by
  unfold tailWord_3761466
  simp only [CollatzResearch.WordTrace]
  refine ⟨34297983947714641023314063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91461290527239042728837501 34297983947714641023314063)
  ·
    refine ⟨51446975921571961534971095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34297983947714641023314063 51446975921571961534971095)
    ·
      refine ⟨77170463882357942302456643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51446975921571961534971095 77170463882357942302456643)
      ·
        refine ⟨115755695823536913453684965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77170463882357942302456643 115755695823536913453684965)
        ·
          refine ⟨21704192966913171272565931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115755695823536913453684965 21704192966913171272565931)
          ·
            refine ⟨32556289450369756908848897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21704192966913171272565931 32556289450369756908848897)
            ·
              refine ⟨24417217087777317681636673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32556289450369756908848897 24417217087777317681636673)
              ·
                refine ⟨18312912815832988261227505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24417217087777317681636673 18312912815832988261227505)
                ·
                  refine ⟨13734684611874741195920629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18312912815832988261227505 13734684611874741195920629)
                  ·
                    refine ⟨1287626682363256987117559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734684611874741195920629 1287626682363256987117559)
                    ·
                      rfl

theorem cell22_3761466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_3761466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761466 prefixEnd_3761466 := by exact prefixLift 3761466
  have htrace : WordTrace (prefixWord ++ tailWord_3761466) baseStart_3761466 baseEnd_3761466 := by
    simpa [prefixWord, tailWord_3761466, baseEnd_3761466] using wordTrace_append hprefix tailTrace_3761466
  have hstable : (prefixWord ++ tailWord_3761466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761466).length < 2 ^ (prefixWord ++ tailWord_3761466).sum := by decide
  have hdescent : baseEnd_3761466 < baseStart_3761466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761468 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_3761468 : Nat := 118140960795 + 3761468 * 2 ^ 59
def prefixEnd_3761468 : Nat := 4983230072969 + 3 ^ 40 * 3761468 * 2
def baseEnd_3761468 : Nat := 429209122334709882855851

theorem tailTrace_3761468 : CollatzResearch.WordTrace tailWord_3761468 prefixEnd_3761468 429209122334709882855851 := by
  unfold tailWord_3761468
  simp only [CollatzResearch.WordTrace]
  refine ⟨68596004368425659217414529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91461339157900878956552705 68596004368425659217414529)
  ·
    refine ⟨51447003276319244413060897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68596004368425659217414529 51447003276319244413060897)
    ·
      refine ⟨38585252457239433309795673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51447003276319244413060897 38585252457239433309795673)
      ·
        refine ⟨28938939342929574982346755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38585252457239433309795673 28938939342929574982346755)
        ·
          refine ⟨43408409014394362473520133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28938939342929574982346755 43408409014394362473520133)
          ·
            refine ⟨8139076690198942963785025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43408409014394362473520133 8139076690198942963785025)
            ·
              refine ⟨6104307517649207222838769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8139076690198942963785025 6104307517649207222838769)
              ·
                refine ⟨4578230638236905417129077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6104307517649207222838769 4578230638236905417129077)
                ·
                  refine ⟨429209122334709882855851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4578230638236905417129077 429209122334709882855851)
                  ·
                    rfl

theorem cell22_3761468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_3761468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761468 prefixEnd_3761468 := by exact prefixLift 3761468
  have htrace : WordTrace (prefixWord ++ tailWord_3761468) baseStart_3761468 baseEnd_3761468 := by
    simpa [prefixWord, tailWord_3761468, baseEnd_3761468] using wordTrace_append hprefix tailTrace_3761468
  have hstable : (prefixWord ++ tailWord_3761468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761468).length < 2 ^ (prefixWord ++ tailWord_3761468).sum := by decide
  have hdescent : baseEnd_3761468 < baseStart_3761468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761481 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_3761481 : Nat := 118140960795 + 3761481 * 2 ^ 59
def prefixEnd_3761481 : Nat := 4983230072969 + 3 ^ 40 * 3761481 * 2
def baseEnd_3761481 : Nat := 1287631817169801947992513

theorem tailTrace_3761481 : CollatzResearch.WordTrace tailWord_3761481 prefixEnd_3761481 1287631817169801947992513 := by
  unfold tailWord_3761481
  simp only [CollatzResearch.WordTrace]
  refine ⟨137192482885804221655052297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91461655257202814436701531 137192482885804221655052297)
  ·
    refine ⟨102894362164353166241289223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137192482885804221655052297 102894362164353166241289223)
    ·
      refine ⟨154341543246529749361933835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102894362164353166241289223 154341543246529749361933835)
      ·
        refine ⟨231512314869794624042900753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154341543246529749361933835 231512314869794624042900753)
        ·
          refine ⟨173634236152345968032175565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231512314869794624042900753 173634236152345968032175565)
          ·
            refine ⟨65112838557129738012065837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173634236152345968032175565 65112838557129738012065837)
            ·
              refine ⟨24417314458923651754524689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65112838557129738012065837 24417314458923651754524689)
              ·
                refine ⟨18312985844192738815893517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24417314458923651754524689 18312985844192738815893517)
                ·
                  refine ⟨6867369691572277055960069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18312985844192738815893517 6867369691572277055960069)
                  ·
                    refine ⟨1287631817169801947992513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867369691572277055960069 1287631817169801947992513)
                    ·
                      rfl

theorem cell22_3761481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_3761481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761481 prefixEnd_3761481 := by exact prefixLift 3761481
  have htrace : WordTrace (prefixWord ++ tailWord_3761481) baseStart_3761481 baseEnd_3761481 := by
    simpa [prefixWord, tailWord_3761481, baseEnd_3761481] using wordTrace_append hprefix tailTrace_3761481
  have hstable : (prefixWord ++ tailWord_3761481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761481).length < 2 ^ (prefixWord ++ tailWord_3761481).sum := by decide
  have hdescent : baseEnd_3761481 < baseStart_3761481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761496 : List Nat := [2, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_3761496 : Nat := 118140960795 + 3761496 * 2 ^ 59
def prefixEnd_3761496 : Nat := 4983230072969 + 3 ^ 40 * 3761496 * 2
def baseEnd_3761496 : Nat := 429212317325448969622489

theorem tailTrace_3761496 : CollatzResearch.WordTrace tailWord_3761496 prefixEnd_3761496 429212317325448969622489 := by
  unfold tailWord_3761496
  simp only [CollatzResearch.WordTrace]
  refine ⟨68596514990374939608424171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91462019987166586144565561 68596514990374939608424171)
  ·
    refine ⟨102894772485562409412636257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68596514990374939608424171 102894772485562409412636257)
    ·
      refine ⟨77171079364171807059477193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102894772485562409412636257 77171079364171807059477193)
      ·
        refine ⟨57878309523128855294607895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77171079364171807059477193 57878309523128855294607895)
        ·
          refine ⟨86817464284693282941911843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57878309523128855294607895 86817464284693282941911843)
          ·
            refine ⟨130226196427039924412867765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86817464284693282941911843 130226196427039924412867765)
            ·
              refine ⟨12208705915034992913706353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130226196427039924412867765 12208705915034992913706353)
              ·
                refine ⟨9156529436276244685279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12208705915034992913706353 9156529436276244685279765)
                ·
                  refine ⟨429212317325448969622489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9156529436276244685279765 429212317325448969622489)
                  ·
                    rfl

theorem cell22_3761496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_3761496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761496 prefixEnd_3761496 := by exact prefixLift 3761496
  have htrace : WordTrace (prefixWord ++ tailWord_3761496) baseStart_3761496 baseEnd_3761496 := by
    simpa [prefixWord, tailWord_3761496, baseEnd_3761496] using wordTrace_append hprefix tailTrace_3761496
  have hstable : (prefixWord ++ tailWord_3761496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761496).length < 2 ^ (prefixWord ++ tailWord_3761496).sum := by decide
  have hdescent : baseEnd_3761496 < baseStart_3761496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761545 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_3761545 : Nat := 118140960795 + 3761545 * 2 ^ 59
def prefixEnd_3761545 : Nat := 4983230072969 + 3 ^ 40 * 3761545 * 2
def baseEnd_3761545 : Nat := 1287653725677727114392317

theorem tailTrace_3761545 : CollatzResearch.WordTrace tailWord_3761545 prefixEnd_3761545 1287653725677727114392317 := by
  unfold tailWord_3761545
  simp only [CollatzResearch.WordTrace]
  refine ⟨137194817157572360585382089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91463211438381573723588059 137194817157572360585382089)
  ·
    refine ⟨102896112868179270439036567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137194817157572360585382089 102896112868179270439036567)
    ·
      refine ⟨154344169302268905658554851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102896112868179270439036567 154344169302268905658554851)
      ·
        refine ⟨231516253953403358487832277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154344169302268905658554851 231516253953403358487832277)
        ·
          refine ⟨5426162202032891214558569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231516253953403358487832277 5426162202032891214558569)
          ·
            refine ⟨4069621651524668410918927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5426162202032891214558569 4069621651524668410918927)
            ·
              refine ⟨6104432477287002616378391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069621651524668410918927 6104432477287002616378391)
              ·
                refine ⟨9156648715930503924567587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104432477287002616378391 9156648715930503924567587)
                ·
                  refine ⟨13734973073895755886851381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9156648715930503924567587 13734973073895755886851381)
                  ·
                    refine ⟨1287653725677727114392317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13734973073895755886851381 1287653725677727114392317)
                    ·
                      rfl

theorem cell22_3761545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_3761545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761545 prefixEnd_3761545 := by exact prefixLift 3761545
  have htrace : WordTrace (prefixWord ++ tailWord_3761545) baseStart_3761545 baseEnd_3761545 := by
    simpa [prefixWord, tailWord_3761545, baseEnd_3761545] using wordTrace_append hprefix tailTrace_3761545
  have hstable : (prefixWord ++ tailWord_3761545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761545).length < 2 ^ (prefixWord ++ tailWord_3761545).sum := by decide
  have hdescent : baseEnd_3761545 < baseStart_3761545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761564 : List Nat := [2, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_3761564 : Nat := 118140960795 + 3761564 * 2 ^ 59
def prefixEnd_3761564 : Nat := 4983230072969 + 3 ^ 40 * 3761564 * 2
def baseEnd_3761564 : Nat := 429220076588672466055753

theorem tailTrace_3761564 : CollatzResearch.WordTrace tailWord_3761564 prefixEnd_3761564 429220076588672466055753 := by
  unfold tailWord_3761564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68597755072251763415161873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91463673429669017886882497 68597755072251763415161873)
  ·
    refine ⟨51448316304188822561371405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68597755072251763415161873 51448316304188822561371405)
    ·
      refine ⟨19293118614070808460514277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51448316304188822561371405 19293118614070808460514277)
      ·
        refine ⟨3617459740138276586346427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19293118614070808460514277 3617459740138276586346427)
        ·
          refine ⟨5426189610207414879519641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617459740138276586346427 5426189610207414879519641)
          ·
            refine ⟨4069642207655561159639731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5426189610207414879519641 4069642207655561159639731)
            ·
              refine ⟨6104463311483341739459597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069642207655561159639731 6104463311483341739459597)
              ·
                refine ⟨2289173741806253152297349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6104463311483341739459597 2289173741806253152297349)
                ·
                  refine ⟨429220076588672466055753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289173741806253152297349 429220076588672466055753)
                  ·
                    rfl

theorem cell22_3761564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_3761564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761564 prefixEnd_3761564 := by exact prefixLift 3761564
  have htrace : WordTrace (prefixWord ++ tailWord_3761564) baseStart_3761564 baseEnd_3761564 := by
    simpa [prefixWord, tailWord_3761564, baseEnd_3761564] using wordTrace_append hprefix tailTrace_3761564
  have hstable : (prefixWord ++ tailWord_3761564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761564).length < 2 ^ (prefixWord ++ tailWord_3761564).sum := by decide
  have hdescent : baseEnd_3761564 < baseStart_3761564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761596 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_3761596 : Nat := 118140960795 + 3761596 * 2 ^ 59
def prefixEnd_3761596 : Nat := 4983230072969 + 3 ^ 40 * 3761596 * 2
def baseEnd_3761596 : Nat := 1287671184019979981367161

theorem tailTrace_3761596 : CollatzResearch.WordTrace tailWord_3761596 prefixEnd_3761596 1287671184019979981367161 := by
  unfold tailWord_3761596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68598338640193798147744321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91464451520258397530325761 68598338640193798147744321)
  ·
    refine ⟨51448753980145348610808241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68598338640193798147744321 51448753980145348610808241)
    ·
      refine ⟨38586565485109011458106181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51448753980145348610808241 38586565485109011458106181)
      ·
        refine ⟨7234981028457939648394909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38586565485109011458106181 7234981028457939648394909)
        ·
          refine ⟨2713117885671727368148091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234981028457939648394909 2713117885671727368148091)
          ·
            refine ⟨4069676828507591052222137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713117885671727368148091 4069676828507591052222137)
            ·
              refine ⟨3052257621380693289166603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4069676828507591052222137 3052257621380693289166603)
              ·
                refine ⟨4578386432071039933749905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052257621380693289166603 4578386432071039933749905)
                ·
                  refine ⟨3433789824053279950312429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578386432071039933749905 3433789824053279950312429)
                  ·
                    refine ⟨1287671184019979981367161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433789824053279950312429 1287671184019979981367161)
                    ·
                      rfl

theorem cell22_3761596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_3761596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761596 prefixEnd_3761596 := by exact prefixLift 3761596
  have htrace : WordTrace (prefixWord ++ tailWord_3761596) baseStart_3761596 baseEnd_3761596 := by
    simpa [prefixWord, tailWord_3761596, baseEnd_3761596] using wordTrace_append hprefix tailTrace_3761596
  have hstable : (prefixWord ++ tailWord_3761596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761596).length < 2 ^ (prefixWord ++ tailWord_3761596).sum := by decide
  have hdescent : baseEnd_3761596 < baseStart_3761596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761616 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_3761616 : Nat := 118140960795 + 3761616 * 2 ^ 59
def prefixEnd_3761616 : Nat := 4983230072969 + 3 ^ 40 * 3761616 * 2
def baseEnd_3761616 : Nat := 1287678030428706595867099

theorem tailTrace_3761616 : CollatzResearch.WordTrace tailWord_3761616 prefixEnd_3761616 1287678030428706595867099 := by
  unfold tailWord_3761616
  simp only [CollatzResearch.WordTrace]
  refine ⟨68598703370157569855608351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91464937826876759807477801 68598703370157569855608351)
  ·
    refine ⟨102898055055236354783412527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68598703370157569855608351 102898055055236354783412527)
    ·
      refine ⟨154347082582854532175118791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102898055055236354783412527 154347082582854532175118791)
      ·
        refine ⟨231520623874281798262678187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154347082582854532175118791 231520623874281798262678187)
        ·
          refine ⟨347280935811422697394017281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231520623874281798262678187 347280935811422697394017281)
          ·
            refine ⟨260460701858567023045512961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347280935811422697394017281 260460701858567023045512961)
            ·
              refine ⟨195345526393925267284134721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260460701858567023045512961 195345526393925267284134721)
              ·
                refine ⟨146509144795443950463101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195345526393925267284134721 146509144795443950463101041)
                ·
                  refine ⟨109881858596582962847325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 146509144795443950463101041 109881858596582962847325781)
                  ·
                    refine ⟨1287678030428706595867099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109881858596582962847325781 1287678030428706595867099)
                    ·
                      rfl

theorem cell22_3761616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_3761616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761616 prefixEnd_3761616 := by exact prefixLift 3761616
  have htrace : WordTrace (prefixWord ++ tailWord_3761616) baseStart_3761616 baseEnd_3761616 := by
    simpa [prefixWord, tailWord_3761616, baseEnd_3761616] using wordTrace_append hprefix tailTrace_3761616
  have hstable : (prefixWord ++ tailWord_3761616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761616).length < 2 ^ (prefixWord ++ tailWord_3761616).sum := by decide
  have hdescent : baseEnd_3761616 < baseStart_3761616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761650 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3761650 : Nat := 118140960795 + 3761650 * 2 ^ 59
def prefixEnd_3761650 : Nat := 4983230072969 + 3 ^ 40 * 3761650 * 2
def baseEnd_3761650 : Nat := 1287689669323541840516995

theorem tailTrace_3761650 : CollatzResearch.WordTrace tailWord_3761650 prefixEnd_3761650 1287689669323541840516995 := by
  unfold tailWord_3761650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34299661705547990879488601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91465764548127975678636269 34299661705547990879488601)
  ·
    refine ⟨25724746279160993159616451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34299661705547990879488601 25724746279160993159616451)
    ·
      refine ⟨38587119418741489739424677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25724746279160993159616451 38587119418741489739424677)
      ·
        refine ⟨7235084891014029326142127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38587119418741489739424677 7235084891014029326142127)
        ·
          refine ⟨10852627336521043989213191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235084891014029326142127 10852627336521043989213191)
          ·
            refine ⟨16278941004781565983819787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10852627336521043989213191 16278941004781565983819787)
            ·
              refine ⟨24418411507172348975729681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16278941004781565983819787 24418411507172348975729681)
              ·
                refine ⟨18313808630379261731797261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24418411507172348975729681 18313808630379261731797261)
                ·
                  refine ⟨6867678236392223149423973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18313808630379261731797261 6867678236392223149423973)
                  ·
                    refine ⟨1287689669323541840516995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867678236392223149423973 1287689669323541840516995)
                    ·
                      rfl

theorem cell22_3761650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3761650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761650 prefixEnd_3761650 := by exact prefixLift 3761650
  have htrace : WordTrace (prefixWord ++ tailWord_3761650) baseStart_3761650 baseEnd_3761650 := by
    simpa [prefixWord, tailWord_3761650, baseEnd_3761650] using wordTrace_append hprefix tailTrace_3761650
  have hstable : (prefixWord ++ tailWord_3761650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761650).length < 2 ^ (prefixWord ++ tailWord_3761650).sum := by decide
  have hdescent : baseEnd_3761650 < baseStart_3761650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761665 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 6]
def baseStart_3761665 : Nat := 118140960795 + 3761665 * 2 ^ 59
def prefixEnd_3761665 : Nat := 4983230072969 + 3 ^ 40 * 3761665 * 2
def baseEnd_3761665 : Nat := 429231601376695600463983

theorem tailTrace_3761665 : CollatzResearch.WordTrace tailWord_3761665 prefixEnd_3761665 429231601376695600463983 := by
  unfold tailWord_3761665
  simp only [CollatzResearch.WordTrace]
  refine ⟨137199193917137621079750449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91466129278091747386500299 137199193917137621079750449)
  ·
    refine ⟨102899395437853215809812837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137199193917137621079750449 102899395437853215809812837)
    ·
      refine ⟨19293636644597477964339907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102899395437853215809812837 19293636644597477964339907)
      ·
        refine ⟨28940454966896216946509861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19293636644597477964339907 28940454966896216946509861)
        ·
          refine ⟨5426335306293040677470599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28940454966896216946509861 5426335306293040677470599)
          ·
            refine ⟨8139502959439561016205899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426335306293040677470599 8139502959439561016205899)
            ·
              refine ⟨12209254439159341524308849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139502959439561016205899 12209254439159341524308849)
              ·
                refine ⟨9156940829369506143231637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12209254439159341524308849 9156940829369506143231637)
                ·
                  refine ⟨429231601376695600463983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9156940829369506143231637 429231601376695600463983)
                  ·
                    rfl

theorem cell22_3761665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_3761665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761665 prefixEnd_3761665 := by exact prefixLift 3761665
  have htrace : WordTrace (prefixWord ++ tailWord_3761665) baseStart_3761665 baseEnd_3761665 := by
    simpa [prefixWord, tailWord_3761665, baseEnd_3761665] using wordTrace_append hprefix tailTrace_3761665
  have hstable : (prefixWord ++ tailWord_3761665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761665).length < 2 ^ (prefixWord ++ tailWord_3761665).sum := by decide
  have hdescent : baseEnd_3761665 < baseStart_3761665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761684 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3761684 : Nat := 118140960795 + 3761684 * 2 ^ 59
def prefixEnd_3761684 : Nat := 4983230072969 + 3 ^ 40 * 3761684 * 2
def baseEnd_3761684 : Nat := 1287701308218377085166891

theorem tailTrace_3761684 : CollatzResearch.WordTrace tailWord_3761684 prefixEnd_3761684 1287701308218377085166891 := by
  unfold tailWord_3761684
  simp only [CollatzResearch.WordTrace]
  refine ⟨68599943452034393662346053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91466591269379191549794737 68599943452034393662346053)
  ·
    refine ⟨12862489397256448811689885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68599943452034393662346053 12862489397256448811689885)
    ·
      refine ⟨4823433523971168304383707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12862489397256448811689885 4823433523971168304383707)
      ·
        refine ⟨7235150285956752456575561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823433523971168304383707 7235150285956752456575561)
        ·
          refine ⟨5426362714467564342431671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235150285956752456575561 5426362714467564342431671)
          ·
            refine ⟨8139544071701346513647507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426362714467564342431671 8139544071701346513647507)
            ·
              refine ⟨12209316107552019770471261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8139544071701346513647507 12209316107552019770471261)
              ·
                refine ⟨4578493540332007413926723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12209316107552019770471261 4578493540332007413926723)
                ·
                  refine ⟨6867740310498011120890085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578493540332007413926723 6867740310498011120890085)
                  ·
                    refine ⟨1287701308218377085166891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867740310498011120890085 1287701308218377085166891)
                    ·
                      rfl

theorem cell22_3761684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3761684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761684 prefixEnd_3761684 := by exact prefixLift 3761684
  have htrace : WordTrace (prefixWord ++ tailWord_3761684) baseStart_3761684 baseEnd_3761684 := by
    simpa [prefixWord, tailWord_3761684, baseEnd_3761684] using wordTrace_append hprefix tailTrace_3761684
  have hstable : (prefixWord ++ tailWord_3761684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761684).length < 2 ^ (prefixWord ++ tailWord_3761684).sum := by decide
  have hdescent : baseEnd_3761684 < baseStart_3761684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761693 : List Nat := [1, 4, 2, 2, 1, 1, 11]
def baseStart_3761693 : Nat := 118140960795 + 3761693 * 2 ^ 59
def prefixEnd_3761693 : Nat := 4983230072969 + 3 ^ 40 * 3761693 * 2
def baseEnd_3761693 : Nat := 47692755151937187470069

theorem tailTrace_3761693 : CollatzResearch.WordTrace tailWord_3761693 prefixEnd_3761693 47692755151937187470069 := by
  unfold tailWord_3761693
  simp only [CollatzResearch.WordTrace]
  refine ⟨137200215161036181861769733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91466810107357454574513155 137200215161036181861769733)
  ·
    refine ⟨25725040342694284099081825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137200215161036181861769733 25725040342694284099081825)
    ·
      refine ⟨19293780257020713074311369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25725040342694284099081825 19293780257020713074311369)
      ·
        refine ⟨14470335192765534805733527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19293780257020713074311369 14470335192765534805733527)
        ·
          refine ⟨21705502789148302208600291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14470335192765534805733527 21705502789148302208600291)
          ·
            refine ⟨32558254183722453312900437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21705502789148302208600291 32558254183722453312900437)
            ·
              refine ⟨47692755151937187470069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32558254183722453312900437 47692755151937187470069)
              ·
                rfl

theorem cell22_3761693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 11].length) (baseStart_3761693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761693 prefixEnd_3761693 := by exact prefixLift 3761693
  have htrace : WordTrace (prefixWord ++ tailWord_3761693) baseStart_3761693 baseEnd_3761693 := by
    simpa [prefixWord, tailWord_3761693, baseEnd_3761693] using wordTrace_append hprefix tailTrace_3761693
  have hstable : (prefixWord ++ tailWord_3761693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761693).length < 2 ^ (prefixWord ++ tailWord_3761693).sum := by decide
  have hdescent : baseEnd_3761693 < baseStart_3761693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761697 : List Nat := [1, 2, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_3761697 : Nat := 118140960795 + 3761697 * 2 ^ 59
def prefixEnd_3761697 : Nat := 4983230072969 + 3 ^ 40 * 3761697 * 2
def baseEnd_3761697 : Nat := 1287705758384049384591851

theorem tailTrace_3761697 : CollatzResearch.WordTrace tailWord_3761697 prefixEnd_3761697 1287705758384049384591851 := by
  unfold tailWord_3761697
  simp only [CollatzResearch.WordTrace]
  refine ⟨137200361053021690544915345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91466907368681127029943563 137200361053021690544915345)
  ·
    refine ⟨102900270789766267908686509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137200361053021690544915345 102900270789766267908686509)
    ·
      refine ⟨38587601546162350465757441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102900270789766267908686509 38587601546162350465757441)
      ·
        refine ⟨28940701159621762849318081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38587601546162350465757441 28940701159621762849318081)
        ·
          refine ⟨21705525869716322136988561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28940701159621762849318081 21705525869716322136988561)
          ·
            refine ⟨16279144402287241602741421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21705525869716322136988561 16279144402287241602741421)
            ·
              refine ⟨6104679150857715601028033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16279144402287241602741421 6104679150857715601028033)
              ·
                refine ⟨4578509363143286700771025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6104679150857715601028033 4578509363143286700771025)
                ·
                  refine ⟨3433882022357465025578269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578509363143286700771025 3433882022357465025578269)
                  ·
                    refine ⟨1287705758384049384591851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433882022357465025578269 1287705758384049384591851)
                    ·
                      rfl

theorem cell22_3761697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_3761697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761697 prefixEnd_3761697 := by exact prefixLift 3761697
  have htrace : WordTrace (prefixWord ++ tailWord_3761697) baseStart_3761697 baseEnd_3761697 := by
    simpa [prefixWord, tailWord_3761697, baseEnd_3761697] using wordTrace_append hprefix tailTrace_3761697
  have hstable : (prefixWord ++ tailWord_3761697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761697).length < 2 ^ (prefixWord ++ tailWord_3761697).sum := by decide
  have hdescent : baseEnd_3761697 < baseStart_3761697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761738 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_3761738 : Nat := 118140960795 + 3761738 * 2 ^ 59
def prefixEnd_3761738 : Nat := 4983230072969 + 3 ^ 40 * 3761738 * 2
def baseEnd_3761738 : Nat := 429239931173979648105575

theorem tailTrace_3761738 : CollatzResearch.WordTrace tailWord_3761738 prefixEnd_3761738 429239931173979648105575 := by
  unfold tailWord_3761738
  simp only [CollatzResearch.WordTrace]
  refine ⟨34300464111468288636789467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91467904297248769698105245 34300464111468288636789467)
  ·
    refine ⟨51450696167202432955184201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34300464111468288636789467 51450696167202432955184201)
    ·
      refine ⟨38588022125401824716388151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51450696167202432955184201 38588022125401824716388151)
      ·
        refine ⟨57882033188102737074582227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38588022125401824716388151 57882033188102737074582227)
        ·
          refine ⟨86823049782154105611873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57882033188102737074582227 86823049782154105611873341)
          ·
            refine ⟨32558643668307789604452503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86823049782154105611873341 32558643668307789604452503)
            ·
              refine ⟨48837965502461684406678755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32558643668307789604452503 48837965502461684406678755)
              ·
                refine ⟨73256948253692526610018133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48837965502461684406678755 73256948253692526610018133)
                ·
                  refine ⟨429239931173979648105575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73256948253692526610018133 429239931173979648105575)
                  ·
                    rfl

theorem cell22_3761738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_3761738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761738 prefixEnd_3761738 := by exact prefixLift 3761738
  have htrace : WordTrace (prefixWord ++ tailWord_3761738) baseStart_3761738 baseEnd_3761738 := by
    simpa [prefixWord, tailWord_3761738, baseEnd_3761738] using wordTrace_append hprefix tailTrace_3761738
  have hstable : (prefixWord ++ tailWord_3761738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761738).length < 2 ^ (prefixWord ++ tailWord_3761738).sum := by decide
  have hdescent : baseEnd_3761738 < baseStart_3761738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761753 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_3761753 : Nat := 118140960795 + 3761753 * 2 ^ 59
def prefixEnd_3761753 : Nat := 4983230072969 + 3 ^ 40 * 3761753 * 2
def baseEnd_3761753 : Nat := 1287724928328483905191679

theorem tailTrace_3761753 : CollatzResearch.WordTrace tailWord_3761753 prefixEnd_3761753 1287724928328483905191679 := by
  unfold tailWord_3761753
  simp only [CollatzResearch.WordTrace]
  refine ⟨137202403540818812108953913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91468269027212541405969275 137202403540818812108953913)
  ·
    refine ⟨102901802655614109081715435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137202403540818812108953913 102901802655614109081715435)
    ·
      refine ⟨154352703983421163622573153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102901802655614109081715435 154352703983421163622573153)
      ·
        refine ⟨115764527987565872716929865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154352703983421163622573153 115764527987565872716929865)
        ·
          refine ⟨86823395990674404537697399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115764527987565872716929865 86823395990674404537697399)
          ·
            refine ⟨130235093986011606806546099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86823395990674404537697399 130235093986011606806546099)
            ·
              refine ⟨195352640979017410209819149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130235093986011606806546099 195352640979017410209819149)
              ·
                refine ⟨73257240367131528828682181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195352640979017410209819149 73257240367131528828682181)
                ·
                  refine ⟨13735732568837161655377909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73257240367131528828682181 13735732568837161655377909)
                  ·
                    refine ⟨1287724928328483905191679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13735732568837161655377909 1287724928328483905191679)
                    ·
                      rfl

theorem cell22_3761753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_3761753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761753 prefixEnd_3761753 := by exact prefixLift 3761753
  have htrace : WordTrace (prefixWord ++ tailWord_3761753) baseStart_3761753 baseEnd_3761753 := by
    simpa [prefixWord, tailWord_3761753, baseEnd_3761753] using wordTrace_append hprefix tailTrace_3761753
  have hstable : (prefixWord ++ tailWord_3761753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761753).length < 2 ^ (prefixWord ++ tailWord_3761753).sum := by decide
  have hdescent : baseEnd_3761753 < baseStart_3761753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
