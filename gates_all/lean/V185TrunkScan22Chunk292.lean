import V185TrunkScan22Chunk291

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2604595 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 5]
def baseStart_2604595 : Nat := 118140960795 + 2604595 * 2 ^ 59
def prefixEnd_2604595 : Nat := 4983230072969 + 3 ^ 40 * 2604595 * 2
def baseEnd_2604595 : Nat := 297202032288298276396487

theorem tailTrace_2604595 : CollatzResearch.WordTrace tailWord_2604595 prefixEnd_2604595 297202032288298276396487 := by
  unfold tailWord_2604595
  simp only [CollatzResearch.WordTrace]
  refine ⟨94997383999004619256431239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63331589332669746170954159 94997383999004619256431239)
  ·
    refine ⟨142496075998506928884646859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94997383999004619256431239 142496075998506928884646859)
    ·
      refine ⟨213744113997760393326970289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142496075998506928884646859 213744113997760393326970289)
      ·
        refine ⟨160308085498320294995227717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213744113997760393326970289 160308085498320294995227717)
        ·
          refine ⟨30057766030935055311605197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 160308085498320294995227717 30057766030935055311605197)
          ·
            refine ⟨11271662261600645741851949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30057766030935055311605197 11271662261600645741851949)
            ·
              refine ⟨4226873348100242153194481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11271662261600645741851949 4226873348100242153194481)
              ·
                refine ⟨3170155011075181614895861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4226873348100242153194481 3170155011075181614895861)
                ·
                  refine ⟨297202032288298276396487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3170155011075181614895861 297202032288298276396487)
                  ·
                    rfl

theorem cell22_2604595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 5].length) (baseStart_2604595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604595 prefixEnd_2604595 := by exact prefixLift 2604595
  have htrace : WordTrace (prefixWord ++ tailWord_2604595) baseStart_2604595 baseEnd_2604595 := by
    simpa [prefixWord, tailWord_2604595, baseEnd_2604595] using wordTrace_append hprefix tailTrace_2604595
  have hstable : (prefixWord ++ tailWord_2604595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604595).length < 2 ^ (prefixWord ++ tailWord_2604595).sum := by decide
  have hdescent : baseEnd_2604595 < baseStart_2604595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604672 : List Nat := [2, 1, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_2604672 : Nat := 118140960795 + 2604672 * 2 ^ 59
def prefixEnd_2604672 : Nat := 4983230072969 + 3 ^ 40 * 2604672 * 2
def baseEnd_2604672 : Nat := 891632455538492295014225

theorem tailTrace_2604672 : CollatzResearch.WordTrace tailWord_2604672 prefixEnd_2604672 891632455538492295014225 := by
  unfold tailWord_2604672
  simp only [CollatzResearch.WordTrace]
  refine ⟨47500096209862830703492135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63333461613150440937989513 47500096209862830703492135)
  ·
    refine ⟨71250144314794246055238203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47500096209862830703492135 71250144314794246055238203)
    ·
      refine ⟨106875216472191369082857305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71250144314794246055238203 106875216472191369082857305)
      ·
        refine ⟨80156412354143526812142979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106875216472191369082857305 80156412354143526812142979)
        ·
          refine ⟨120234618531215290218214469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80156412354143526812142979 120234618531215290218214469)
          ·
            refine ⟨22543990974602866915915213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120234618531215290218214469 22543990974602866915915213)
            ·
              refine ⟨8453996615476075093468205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22543990974602866915915213 8453996615476075093468205)
              ·
                refine ⟨3170248730803528160050577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8453996615476075093468205 3170248730803528160050577)
                ·
                  refine ⟨2377686548102646120037933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170248730803528160050577 2377686548102646120037933)
                  ·
                    refine ⟨891632455538492295014225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377686548102646120037933 891632455538492295014225)
                    ·
                      rfl

theorem cell22_2604672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_2604672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604672 prefixEnd_2604672 := by exact prefixLift 2604672
  have htrace : WordTrace (prefixWord ++ tailWord_2604672) baseStart_2604672 baseEnd_2604672 := by
    simpa [prefixWord, tailWord_2604672, baseEnd_2604672] using wordTrace_append hprefix tailTrace_2604672
  have hstable : (prefixWord ++ tailWord_2604672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604672).length < 2 ^ (prefixWord ++ tailWord_2604672).sum := by decide
  have hdescent : baseEnd_2604672 < baseStart_2604672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604676 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2604676 : Nat := 118140960795 + 2604676 * 2 ^ 59
def prefixEnd_2604676 : Nat := 4983230072969 + 3 ^ 40 * 2604676 * 2
def baseEnd_2604676 : Nat := 891633824820237617914213

theorem tailTrace_2604676 : CollatzResearch.WordTrace tailWord_2604676 prefixEnd_2604676 891633824820237617914213 := by
  unfold tailWord_2604676
  simp only [CollatzResearch.WordTrace]
  refine ⟨47500169155855585045064941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63333558874474113393419921 47500169155855585045064941)
  ·
    refine ⟨17812563433445844391899353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47500169155855585045064941 17812563433445844391899353)
    ·
      refine ⟨13359422575084383293924515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17812563433445844391899353 13359422575084383293924515)
      ·
        refine ⟨20039133862626574940886773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359422575084383293924515 20039133862626574940886773)
        ·
          refine ⟨1878668799621241400708135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20039133862626574940886773 1878668799621241400708135)
          ·
            refine ⟨2818003199431862101062203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878668799621241400708135 2818003199431862101062203)
            ·
              refine ⟨4227004799147793151593305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2818003199431862101062203 4227004799147793151593305)
              ·
                refine ⟨3170253599360844863694979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4227004799147793151593305 3170253599360844863694979)
                ·
                  refine ⟨4755380399041267295542469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170253599360844863694979 4755380399041267295542469)
                  ·
                    refine ⟨891633824820237617914213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4755380399041267295542469 891633824820237617914213)
                    ·
                      rfl

theorem cell22_2604676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2604676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604676 prefixEnd_2604676 := by exact prefixLift 2604676
  have htrace : WordTrace (prefixWord ++ tailWord_2604676) baseStart_2604676 baseEnd_2604676 := by
    simpa [prefixWord, tailWord_2604676, baseEnd_2604676] using wordTrace_append hprefix tailTrace_2604676
  have hstable : (prefixWord ++ tailWord_2604676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604676).length < 2 ^ (prefixWord ++ tailWord_2604676).sum := by decide
  have hdescent : baseEnd_2604676 < baseStart_2604676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604734 : List Nat := [4, 2, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2604734 : Nat := 118140960795 + 2604734 * 2 ^ 59
def prefixEnd_2604734 : Nat := 4983230072969 + 3 ^ 40 * 2604734 * 2
def baseEnd_2604734 : Nat := 891653679405544799964035

theorem tailTrace_2604734 : CollatzResearch.WordTrace tailWord_2604734 prefixEnd_2604734 891653679405544799964035 := by
  unfold tailWord_2604734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11875306718187630749467657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63334969163667363997160837 11875306718187630749467657)
  ·
    refine ⟨8906480038640723062100743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11875306718187630749467657 8906480038640723062100743)
    ·
      refine ⟨13359720057961084593151115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8906480038640723062100743 13359720057961084593151115)
      ·
        refine ⟨20039580086941626889726673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13359720057961084593151115 20039580086941626889726673)
        ·
          refine ⟨15029685065206220167295005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20039580086941626889726673 15029685065206220167295005)
          ·
            refine ⟨5636131899452332562735627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15029685065206220167295005 5636131899452332562735627)
            ·
              refine ⟨8454197849178498844103441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636131899452332562735627 8454197849178498844103441)
              ·
                refine ⟨6340648386883874133077581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8454197849178498844103441 6340648386883874133077581)
                ·
                  refine ⟨2377743145081452799904093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6340648386883874133077581 2377743145081452799904093)
                  ·
                    refine ⟨891653679405544799964035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2377743145081452799904093 891653679405544799964035)
                    ·
                      rfl

theorem cell22_2604734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2604734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604734 prefixEnd_2604734 := by exact prefixLift 2604734
  have htrace : WordTrace (prefixWord ++ tailWord_2604734) baseStart_2604734 baseEnd_2604734 := by
    simpa [prefixWord, tailWord_2604734, baseEnd_2604734] using wordTrace_append hprefix tailTrace_2604734
  have hstable : (prefixWord ++ tailWord_2604734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604734).length < 2 ^ (prefixWord ++ tailWord_2604734).sum := by decide
  have hdescent : baseEnd_2604734 < baseStart_2604734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604764 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_2604764 : Nat := 118140960795 + 2604764 * 2 ^ 59
def prefixEnd_2604764 : Nat := 4983230072969 + 3 ^ 40 * 2604764 * 2
def baseEnd_2604764 : Nat := 297221316339544907237981

theorem tailTrace_2604764 : CollatzResearch.WordTrace tailWord_2604764 prefixEnd_2604764 297221316339544907237981 := by
  unfold tailWord_2604764
  simp only [CollatzResearch.WordTrace]
  refine ⟨47501773967696180559666673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63335698623594907412888897 47501773967696180559666673)
  ·
    refine ⟨35626330475772135419750005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47501773967696180559666673 35626330475772135419750005)
    ·
      refine ⟨3339968482103637695601563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35626330475772135419750005 3339968482103637695601563)
      ·
        refine ⟨5009952723155456543402345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3339968482103637695601563 5009952723155456543402345)
        ·
          refine ⟨3757464542366592407551759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009952723155456543402345 3757464542366592407551759)
          ·
            refine ⟨5636196813549888611327639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757464542366592407551759 5636196813549888611327639)
            ·
              refine ⟨8454295220324832916991459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636196813549888611327639 8454295220324832916991459)
              ·
                refine ⟨12681442830487249375487189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454295220324832916991459 12681442830487249375487189)
                ·
                  refine ⟨297221316339544907237981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12681442830487249375487189 297221316339544907237981)
                  ·
                    rfl

theorem cell22_2604764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_2604764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604764 prefixEnd_2604764 := by exact prefixLift 2604764
  have htrace : WordTrace (prefixWord ++ tailWord_2604764) baseStart_2604764 baseEnd_2604764 := by
    simpa [prefixWord, tailWord_2604764, baseEnd_2604764] using wordTrace_append hprefix tailTrace_2604764
  have hstable : (prefixWord ++ tailWord_2604764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604764).length < 2 ^ (prefixWord ++ tailWord_2604764).sum := by decide
  have hdescent : baseEnd_2604764 < baseStart_2604764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604826 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_2604826 : Nat := 118140960795 + 2604826 * 2 ^ 59
def prefixEnd_2604826 : Nat := 4983230072969 + 3 ^ 40 * 2604826 * 2
def baseEnd_2604826 : Nat := 297228390961895742221251

theorem tailTrace_2604826 : CollatzResearch.WordTrace tailWord_2604826 prefixEnd_2604826 297228390961895742221251 := by
  unfold tailWord_2604826
  simp only [CollatzResearch.WordTrace]
  refine ⟨23751452315291936427022583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63337206174111830472060221 23751452315291936427022583)
  ·
    refine ⟨35627178472937904640533875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23751452315291936427022583 35627178472937904640533875)
    ·
      refine ⟨53440767709406856960800813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35627178472937904640533875 53440767709406856960800813)
      ·
        refine ⟨20040287891027571360300305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53440767709406856960800813 20040287891027571360300305)
        ·
          refine ⟨15030215918270678520225229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20040287891027571360300305 15030215918270678520225229)
          ·
            refine ⟨5636330969351504445084461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15030215918270678520225229 5636330969351504445084461)
            ·
              refine ⟨2113624113506814166906673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5636330969351504445084461 2113624113506814166906673)
              ·
                refine ⟨1585218085130110625180005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113624113506814166906673 1585218085130110625180005)
                ·
                  refine ⟨297228390961895742221251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585218085130110625180005 297228390961895742221251)
                  ·
                    rfl

theorem cell22_2604826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_2604826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604826 prefixEnd_2604826 := by exact prefixLift 2604826
  have htrace : WordTrace (prefixWord ++ tailWord_2604826) baseStart_2604826 baseEnd_2604826 := by
    simpa [prefixWord, tailWord_2604826, baseEnd_2604826] using wordTrace_append hprefix tailTrace_2604826
  have hstable : (prefixWord ++ tailWord_2604826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604826).length < 2 ^ (prefixWord ++ tailWord_2604826).sum := by decide
  have hdescent : baseEnd_2604826 < baseStart_2604826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604837 : List Nat := [1, 3, 1, 2, 3, 3, 2, 7]
def baseStart_2604837 : Nat := 118140960795 + 2604837 * 2 ^ 59
def prefixEnd_2604837 : Nat := 4983230072969 + 3 ^ 40 * 2604837 * 2
def baseEnd_2604837 : Nat := 99076548712276318293191

theorem tailTrace_2604837 : CollatzResearch.WordTrace tailWord_2604837 prefixEnd_2604837 99076548712276318293191 := by
  unfold tailWord_2604837
  simp only [CollatzResearch.WordTrace]
  refine ⟨95006210464127894586740765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63337473642751929724493843 95006210464127894586740765)
  ·
    refine ⟨35627328924047960470027787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95006210464127894586740765 35627328924047960470027787)
    ·
      refine ⟨53440993386071940705041681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35627328924047960470027787 53440993386071940705041681)
      ·
        refine ⟨40080745039553955528781261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53440993386071940705041681 40080745039553955528781261)
        ·
          refine ⟨15030279389832733323292973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40080745039553955528781261 15030279389832733323292973)
          ·
            refine ⟨5636354771187274996234865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15030279389832733323292973 5636354771187274996234865)
            ·
              refine ⟨4227266078390456247176149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5636354771187274996234865 4227266078390456247176149)
              ·
                refine ⟨99076548712276318293191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4227266078390456247176149 99076548712276318293191)
                ·
                  rfl

theorem cell22_2604837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 7].length) (baseStart_2604837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604837 prefixEnd_2604837 := by exact prefixLift 2604837
  have htrace : WordTrace (prefixWord ++ tailWord_2604837) baseStart_2604837 baseEnd_2604837 := by
    simpa [prefixWord, tailWord_2604837, baseEnd_2604837] using wordTrace_append hprefix tailTrace_2604837
  have hstable : (prefixWord ++ tailWord_2604837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604837).length < 2 ^ (prefixWord ++ tailWord_2604837).sum := by decide
  have hdescent : baseEnd_2604837 < baseStart_2604837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604854 : List Nat := [5, 1, 2, 2, 1, 1, 2, 8]
def baseStart_2604854 : Nat := 118140960795 + 2604854 * 2 ^ 59
def prefixEnd_2604854 : Nat := 4983230072969 + 3 ^ 40 * 2604854 * 2
def baseEnd_2604854 : Nat := 99077195317544942995963

theorem tailTrace_2604854 : CollatzResearch.WordTrace tailWord_2604854 prefixEnd_2604854 99077195317544942995963 := by
  unfold tailWord_2604854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937926906566644155631851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63337887003377537660073077 5937926906566644155631851)
  ·
    refine ⟨8906890359849966233447777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5937926906566644155631851 8906890359849966233447777)
    ·
      refine ⟨6680167769887474675085833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8906890359849966233447777 6680167769887474675085833)
      ·
        refine ⟨5010125827415606006314375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6680167769887474675085833 5010125827415606006314375)
        ·
          refine ⟨7515188741123409009471563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010125827415606006314375 7515188741123409009471563)
          ·
            refine ⟨11272783111685113514207345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515188741123409009471563 11272783111685113514207345)
            ·
              refine ⟨8454587333763835135655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11272783111685113514207345 8454587333763835135655509)
              ·
                refine ⟨99077195317544942995963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8454587333763835135655509 99077195317544942995963)
                ·
                  rfl

theorem cell22_2604854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_2604854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604854 prefixEnd_2604854 := by exact prefixLift 2604854
  have htrace : WordTrace (prefixWord ++ tailWord_2604854) baseStart_2604854 baseEnd_2604854 := by
    simpa [prefixWord, tailWord_2604854, baseEnd_2604854] using wordTrace_append hprefix tailTrace_2604854
  have hstable : (prefixWord ++ tailWord_2604854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604854).length < 2 ^ (prefixWord ++ tailWord_2604854).sum := by decide
  have hdescent : baseEnd_2604854 < baseStart_2604854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604897 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2604897 : Nat := 118140960795 + 2604897 * 2 ^ 59
def prefixEnd_2604897 : Nat := 4983230072969 + 3 ^ 40 * 2604897 * 2
def baseEnd_2604897 : Nat := 891709477636666708138535

theorem tailTrace_2604897 : CollatzResearch.WordTrace tailWord_2604897 prefixEnd_2604897 891709477636666708138535 := by
  unfold tailWord_2604897
  simp only [CollatzResearch.WordTrace]
  refine ⟨95008398843910524833924945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63338932562607016555949963 95008398843910524833924945)
  ·
    refine ⟨71256299132932893625443709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95008398843910524833924945 71256299132932893625443709)
    ·
      refine ⟨26721112174849835109541391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71256299132932893625443709 26721112174849835109541391)
      ·
        refine ⟨40081668262274752664312087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26721112174849835109541391 40081668262274752664312087)
        ·
          refine ⟨60122502393412128996468131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40081668262274752664312087 60122502393412128996468131)
          ·
            refine ⟨90183753590118193494702197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60122502393412128996468131 90183753590118193494702197)
            ·
              refine ⟨8454726899073580640128331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90183753590118193494702197 8454726899073580640128331)
              ·
                refine ⟨12682090348610370960192497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8454726899073580640128331 12682090348610370960192497)
                ·
                  refine ⟨9511567761457778220144373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12682090348610370960192497 9511567761457778220144373)
                  ·
                    refine ⟨891709477636666708138535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9511567761457778220144373 891709477636666708138535)
                    ·
                      rfl

theorem cell22_2604897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2604897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604897 prefixEnd_2604897 := by exact prefixLift 2604897
  have htrace : WordTrace (prefixWord ++ tailWord_2604897) baseStart_2604897 baseEnd_2604897 := by
    simpa [prefixWord, tailWord_2604897, baseEnd_2604897] using wordTrace_append hprefix tailTrace_2604897
  have hstable : (prefixWord ++ tailWord_2604897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604897).length < 2 ^ (prefixWord ++ tailWord_2604897).sum := by decide
  have hdescent : baseEnd_2604897 < baseStart_2604897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2604989 : List Nat := [1, 4, 1, 2, 3, 3, 8]
def baseStart_2604989 : Nat := 118140960795 + 2604989 * 2 ^ 59
def prefixEnd_2604989 : Nat := 4983230072969 + 3 ^ 40 * 2604989 * 2
def baseEnd_2604989 : Nat := 33027443374696634623639

theorem tailTrace_2604989 : CollatzResearch.WordTrace tailWord_2604989 prefixEnd_2604989 33027443374696634623639 := by
  unfold tailWord_2604989
  simp only [CollatzResearch.WordTrace]
  refine ⟨95011754359577224546274021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63341169573051483030849347 95011754359577224546274021)
  ·
    refine ⟨17814703942420729602426379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95011754359577224546274021 17814703942420729602426379)
    ·
      refine ⟨26722055913631094403639569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17814703942420729602426379 26722055913631094403639569)
      ·
        refine ⟨20041541935223320802729677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26722055913631094403639569 20041541935223320802729677)
        ·
          refine ⟨7515578225708745301023629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20041541935223320802729677 7515578225708745301023629)
          ·
            refine ⟨2818341834640779487883861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7515578225708745301023629 2818341834640779487883861)
            ·
              refine ⟨33027443374696634623639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2818341834640779487883861 33027443374696634623639)
              ·
                rfl

theorem cell22_2604989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 8].length) (baseStart_2604989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2604989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2604989 prefixEnd_2604989 := by exact prefixLift 2604989
  have htrace : WordTrace (prefixWord ++ tailWord_2604989) baseStart_2604989 baseEnd_2604989 := by
    simpa [prefixWord, tailWord_2604989, baseEnd_2604989] using wordTrace_append hprefix tailTrace_2604989
  have hstable : (prefixWord ++ tailWord_2604989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2604989).length < 2 ^ (prefixWord ++ tailWord_2604989).sum := by decide
  have hdescent : baseEnd_2604989 < baseStart_2604989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2604989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605064 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2605064 : Nat := 118140960795 + 2605064 * 2 ^ 59
def prefixEnd_2605064 : Nat := 4983230072969 + 3 ^ 40 * 2605064 * 2
def baseEnd_2605064 : Nat := 891766645149533939213023

theorem tailTrace_2605064 : CollatzResearch.WordTrace tailWord_2605064 prefixEnd_2605064 891766645149533939213023 := by
  unfold tailWord_2605064
  simp only [CollatzResearch.WordTrace]
  refine ⟨47507244917152756177627123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63342993222870341570169497 47507244917152756177627123)
  ·
    refine ⟨71260867375729134266440685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47507244917152756177627123 71260867375729134266440685)
    ·
      refine ⟨26722825265898425349915257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71260867375729134266440685 26722825265898425349915257)
      ·
        refine ⟨20042118949423819012436443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26722825265898425349915257 20042118949423819012436443)
        ·
          refine ⟨30063178424135728518654665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20042118949423819012436443 30063178424135728518654665)
          ·
            refine ⟨22547383818101796388990999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30063178424135728518654665 22547383818101796388990999)
            ·
              refine ⟨33821075727152694583486499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22547383818101796388990999 33821075727152694583486499)
              ·
                refine ⟨50731613590729041875229749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33821075727152694583486499 50731613590729041875229749)
                ·
                  refine ⟨4756088774130847675802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50731613590729041875229749 4756088774130847675802789)
                  ·
                    refine ⟨891766645149533939213023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756088774130847675802789 891766645149533939213023)
                    ·
                      rfl

theorem cell22_2605064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2605064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605064 prefixEnd_2605064 := by exact prefixLift 2605064
  have htrace : WordTrace (prefixWord ++ tailWord_2605064) baseStart_2605064 baseEnd_2605064 := by
    simpa [prefixWord, tailWord_2605064, baseEnd_2605064] using wordTrace_append hprefix tailTrace_2605064
  have hstable : (prefixWord ++ tailWord_2605064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605064).length < 2 ^ (prefixWord ++ tailWord_2605064).sum := by decide
  have hdescent : baseEnd_2605064 < baseStart_2605064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605066 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2605066 : Nat := 118140960795 + 2605066 * 2 ^ 59
def prefixEnd_2605066 : Nat := 4983230072969 + 3 ^ 40 * 2605066 * 2
def baseEnd_2605066 : Nat := 891767329790406600663017

theorem tailTrace_2605066 : CollatzResearch.WordTrace tailWord_2605066 prefixEnd_2605066 891767329790406600663017 := by
  unfold tailWord_2605066
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753640695074566674206763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63343041853532177797884701 23753640695074566674206763)
  ·
    refine ⟨35630461042611850011310145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23753640695074566674206763 35630461042611850011310145)
    ·
      refine ⟨26722845781958887508482609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35630461042611850011310145 26722845781958887508482609)
      ·
        refine ⟨20042134336469165631361957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26722845781958887508482609 20042134336469165631361957)
        ·
          refine ⟨3757900188087968555880367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20042134336469165631361957 3757900188087968555880367)
          ·
            refine ⟨5636850282131952833820551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757900188087968555880367 5636850282131952833820551)
            ·
              refine ⟨8455275423197929250730827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636850282131952833820551 8455275423197929250730827)
              ·
                refine ⟨12682913134796893876096241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8455275423197929250730827 12682913134796893876096241)
                ·
                  refine ⟨9512184851097670407072181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12682913134796893876096241 9512184851097670407072181)
                  ·
                    refine ⟨891767329790406600663017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9512184851097670407072181 891767329790406600663017)
                    ·
                      rfl

theorem cell22_2605066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2605066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605066 prefixEnd_2605066 := by exact prefixLift 2605066
  have htrace : WordTrace (prefixWord ++ tailWord_2605066) baseStart_2605066 baseEnd_2605066 := by
    simpa [prefixWord, tailWord_2605066, baseEnd_2605066] using wordTrace_append hprefix tailTrace_2605066
  have hstable : (prefixWord ++ tailWord_2605066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605066).length < 2 ^ (prefixWord ++ tailWord_2605066).sum := by decide
  have hdescent : baseEnd_2605066 < baseStart_2605066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605098 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2605098 : Nat := 118140960795 + 2605098 * 2 ^ 59
def prefixEnd_2605098 : Nat := 4983230072969 + 3 ^ 40 * 2605098 * 2
def baseEnd_2605098 : Nat := 891778284044369183862919

theorem tailTrace_2605098 : CollatzResearch.WordTrace tailWord_2605098 prefixEnd_2605098 891778284044369183862919 := by
  unfold tailWord_2605098
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753932479045584040497987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63343819944121557441327965 23753932479045584040497987)
  ·
    refine ⟨35630898718568376060746981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23753932479045584040497987 35630898718568376060746981)
    ·
      refine ⟨6680793509731570511390059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35630898718568376060746981 6680793509731570511390059)
      ·
        refine ⟨10021190264597355767085089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680793509731570511390059 10021190264597355767085089)
        ·
          refine ⟨7515892698448016825313817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10021190264597355767085089 7515892698448016825313817)
          ·
            refine ⟨5636919523836012618985363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7515892698448016825313817 5636919523836012618985363)
            ·
              refine ⟨8455379285754018928478045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5636919523836012618985363 8455379285754018928478045)
              ·
                refine ⟨3170767232157757098179267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8455379285754018928478045 3170767232157757098179267)
                ·
                  refine ⟨4756150848236635647268901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3170767232157757098179267 4756150848236635647268901)
                  ·
                    refine ⟨891778284044369183862919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756150848236635647268901 891778284044369183862919)
                    ·
                      rfl

theorem cell22_2605098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2605098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605098 prefixEnd_2605098 := by exact prefixLift 2605098
  have htrace : WordTrace (prefixWord ++ tailWord_2605098) baseStart_2605098 baseEnd_2605098 := by
    simpa [prefixWord, tailWord_2605098, baseEnd_2605098] using wordTrace_append hprefix tailTrace_2605098
  have hstable : (prefixWord ++ tailWord_2605098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605098).length < 2 ^ (prefixWord ++ tailWord_2605098).sum := by decide
  have hdescent : baseEnd_2605098 < baseStart_2605098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605141 : List Nat := [1, 3, 2, 2, 1, 3, 4, 6]
def baseStart_2605141 : Nat := 118140960795 + 2605141 * 2 ^ 59
def prefixEnd_2605141 : Nat := 4983230072969 + 3 ^ 40 * 2605141 * 2
def baseEnd_2605141 : Nat := 99088111535903489448643

theorem tailTrace_2605141 : CollatzResearch.WordTrace tailWord_2605141 prefixEnd_2605141 99088111535903489448643 := by
  unfold tailWord_2605141
  simp only [CollatzResearch.WordTrace]
  refine ⟨95017298255026554505807277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63344865503351036337204851 95017298255026554505807277)
  ·
    refine ⟨35631486845634957939677729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95017298255026554505807277 35631486845634957939677729)
    ·
      refine ⟨26723615134226218454758297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35631486845634957939677729 26723615134226218454758297)
      ·
        refine ⟨20042711350669663841068723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26723615134226218454758297 20042711350669663841068723)
        ·
          refine ⟨30064067026004495761603085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20042711350669663841068723 30064067026004495761603085)
          ·
            refine ⟨11274025134751685910601157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30064067026004495761603085 11274025134751685910601157)
            ·
              refine ⟨2113879712765941108237717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11274025134751685910601157 2113879712765941108237717)
              ·
                refine ⟨99088111535903489448643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2113879712765941108237717 99088111535903489448643)
                ·
                  rfl

theorem cell22_2605141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 6].length) (baseStart_2605141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605141 prefixEnd_2605141 := by exact prefixLift 2605141
  have htrace : WordTrace (prefixWord ++ tailWord_2605141) baseStart_2605141 baseEnd_2605141 := by
    simpa [prefixWord, tailWord_2605141, baseEnd_2605141] using wordTrace_append hprefix tailTrace_2605141
  have hstable : (prefixWord ++ tailWord_2605141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605141).length < 2 ^ (prefixWord ++ tailWord_2605141).sum := by decide
  have hdescent : baseEnd_2605141 < baseStart_2605141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605156 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2605156 : Nat := 118140960795 + 2605156 * 2 ^ 59
def prefixEnd_2605156 : Nat := 4983230072969 + 3 ^ 40 * 2605156 * 2
def baseEnd_2605156 : Nat := 891798138629676365912741

theorem tailTrace_2605156 : CollatzResearch.WordTrace tailWord_2605156 prefixEnd_2605156 891798138629676365912741 := by
  unfold tailWord_2605156
  simp only [CollatzResearch.WordTrace]
  refine ⟨47508922674986106033801661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63345230233314808045068881 47508922674986106033801661)
  ·
    refine ⟨17815846003119789762675623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47508922674986106033801661 17815846003119789762675623)
    ·
      refine ⟨26723769004679684644013435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17815846003119789762675623 26723769004679684644013435)
      ·
        refine ⟨40085653507019526966020153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26723769004679684644013435 40085653507019526966020153)
        ·
          refine ⟨30064240130264645224515115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40085653507019526966020153 30064240130264645224515115)
          ·
            refine ⟨45096360195396967836772673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30064240130264645224515115 45096360195396967836772673)
            ·
              refine ⟨33822270146547725877579505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45096360195396967836772673 33822270146547725877579505)
              ·
                refine ⟨25366702609910794408184629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33822270146547725877579505 25366702609910794408184629)
                ·
                  refine ⟨2378128369679136975767309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25366702609910794408184629 2378128369679136975767309)
                  ·
                    refine ⟨891798138629676365912741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378128369679136975767309 891798138629676365912741)
                    ·
                      rfl

theorem cell22_2605156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2605156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605156 prefixEnd_2605156 := by exact prefixLift 2605156
  have htrace : WordTrace (prefixWord ++ tailWord_2605156) baseStart_2605156 baseEnd_2605156 := by
    simpa [prefixWord, tailWord_2605156, baseEnd_2605156] using wordTrace_append hprefix tailTrace_2605156
  have hstable : (prefixWord ++ tailWord_2605156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605156).length < 2 ^ (prefixWord ++ tailWord_2605156).sum := by decide
  have hdescent : baseEnd_2605156 < baseStart_2605156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605169 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 7]
def baseStart_2605169 : Nat := 118140960795 + 2605169 * 2 ^ 59
def prefixEnd_2605169 : Nat := 4983230072969 + 3 ^ 40 * 2605169 * 2
def baseEnd_2605169 : Nat := 297267529598449555112567

theorem tailTrace_2605169 : CollatzResearch.WordTrace tailWord_2605169 prefixEnd_2605169 297267529598449555112567 := by
  unfold tailWord_2605169
  simp only [CollatzResearch.WordTrace]
  refine ⟨95018319498925115287826561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63345546332616743525217707 95018319498925115287826561)
  ·
    refine ⟨71263739624193836465869921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95018319498925115287826561 71263739624193836465869921)
    ·
      refine ⟨53447804718145377349402441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71263739624193836465869921 53447804718145377349402441)
      ·
        refine ⟨40085853538609033012051831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53447804718145377349402441 40085853538609033012051831)
        ·
          refine ⟨60128780307913549518077747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40085853538609033012051831 60128780307913549518077747)
          ·
            refine ⟨90193170461870324277116621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60128780307913549518077747 90193170461870324277116621)
            ·
              refine ⟨33822438923201371603918733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90193170461870324277116621 33822438923201371603918733)
              ·
                refine ⟨12683414596200514351469525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33822438923201371603918733 12683414596200514351469525)
                ·
                  refine ⟨297267529598449555112567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12683414596200514351469525 297267529598449555112567)
                  ·
                    rfl

theorem cell22_2605169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_2605169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605169 prefixEnd_2605169 := by exact prefixLift 2605169
  have htrace : WordTrace (prefixWord ++ tailWord_2605169) baseStart_2605169 baseEnd_2605169 := by
    simpa [prefixWord, tailWord_2605169, baseEnd_2605169] using wordTrace_append hprefix tailTrace_2605169
  have hstable : (prefixWord ++ tailWord_2605169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605169).length < 2 ^ (prefixWord ++ tailWord_2605169).sum := by decide
  have hdescent : baseEnd_2605169 < baseStart_2605169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605184 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_2605184 : Nat := 118140960795 + 2605184 * 2 ^ 59
def prefixEnd_2605184 : Nat := 4983230072969 + 3 ^ 40 * 2605184 * 2
def baseEnd_2605184 : Nat := 891807723601893626212655

theorem tailTrace_2605184 : CollatzResearch.WordTrace tailWord_2605184 prefixEnd_2605184 891807723601893626212655 := by
  unfold tailWord_2605184
  simp only [CollatzResearch.WordTrace]
  refine ⟨47509433296935386424811303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63345911062580515233081737 47509433296935386424811303)
  ·
    refine ⟨71264149945403079637216955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47509433296935386424811303 71264149945403079637216955)
    ·
      refine ⟨106896224918104619455825433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71264149945403079637216955 106896224918104619455825433)
      ·
        refine ⟨80172168688578464591869075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106896224918104619455825433 80172168688578464591869075)
        ·
          refine ⟨120258253032867696887803613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80172168688578464591869075 120258253032867696887803613)
          ·
            refine ⟨45096844887325386332926355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120258253032867696887803613 45096844887325386332926355)
            ·
              refine ⟨67645267330988079499389533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45096844887325386332926355 67645267330988079499389533)
              ·
                refine ⟨25366975249120529812271075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67645267330988079499389533 25366975249120529812271075)
                ·
                  refine ⟨38050462873680794718406613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25366975249120529812271075 38050462873680794718406613)
                  ·
                    refine ⟨891807723601893626212655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38050462873680794718406613 891807723601893626212655)
                    ·
                      rfl

theorem cell22_2605184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_2605184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605184 prefixEnd_2605184 := by exact prefixLift 2605184
  have htrace : WordTrace (prefixWord ++ tailWord_2605184) baseStart_2605184 baseEnd_2605184 := by
    simpa [prefixWord, tailWord_2605184, baseEnd_2605184] using wordTrace_append hprefix tailTrace_2605184
  have hstable : (prefixWord ++ tailWord_2605184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605184).length < 2 ^ (prefixWord ++ tailWord_2605184).sum := by decide
  have hdescent : baseEnd_2605184 < baseStart_2605184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605321 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 7]
def baseStart_2605321 : Nat := 118140960795 + 2605321 * 2 ^ 59
def prefixEnd_2605321 : Nat := 4983230072969 + 3 ^ 40 * 2605321 * 2
def baseEnd_2605321 : Nat := 297284873833890311845745

theorem tailTrace_2605321 : CollatzResearch.WordTrace tailWord_2605321 prefixEnd_2605321 297284873833890311845745 := by
  unfold tailWord_2605321
  simp only [CollatzResearch.WordTrace]
  refine ⟨95023863394374445247359817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63349242262916296831573211 95023863394374445247359817)
  ·
    refine ⟨71267897545780833935519863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95023863394374445247359817 71267897545780833935519863)
    ·
      refine ⟨106901846318671250903279795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71267897545780833935519863 106901846318671250903279795)
      ·
        refine ⟨160352769478006876354919693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106901846318671250903279795 160352769478006876354919693)
        ·
          refine ⟨60132288554252578633094885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160352769478006876354919693 60132288554252578633094885)
          ·
            refine ⟨11274804103922358493705291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60132288554252578633094885 11274804103922358493705291)
            ·
              refine ⟨16912206155883537740557937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11274804103922358493705291 16912206155883537740557937)
              ·
                refine ⟨12684154616912653305418453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16912206155883537740557937 12684154616912653305418453)
                ·
                  refine ⟨297284873833890311845745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12684154616912653305418453 297284873833890311845745)
                  ·
                    rfl

theorem cell22_2605321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_2605321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605321 prefixEnd_2605321 := by exact prefixLift 2605321
  have htrace : WordTrace (prefixWord ++ tailWord_2605321) baseStart_2605321 baseEnd_2605321 := by
    simpa [prefixWord, tailWord_2605321, baseEnd_2605321] using wordTrace_append hprefix tailTrace_2605321
  have hstable : (prefixWord ++ tailWord_2605321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605321).length < 2 ^ (prefixWord ++ tailWord_2605321).sum := by decide
  have hdescent : baseEnd_2605321 < baseStart_2605321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605415 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2605415 : Nat := 118140960795 + 2605415 * 2 ^ 59
def prefixEnd_2605415 : Nat := 4983230072969 + 3 ^ 40 * 2605415 * 2
def baseEnd_2605415 : Nat := 891886799622686023686947

theorem tailTrace_2605415 : CollatzResearch.WordTrace tailWord_2605415 prefixEnd_2605415 891886799622686023686947 := by
  unfold tailWord_2605415
  simp only [CollatzResearch.WordTrace]
  refine ⟨95027291856033899301281699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63351527904022599534187799 95027291856033899301281699)
  ·
    refine ⟨142540937784050848951922549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95027291856033899301281699 142540937784050848951922549)
    ·
      refine ⟨13363212917254767089242739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142540937784050848951922549 13363212917254767089242739)
      ·
        refine ⟨20044819375882150633864109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13363212917254767089242739 20044819375882150633864109)
        ·
          refine ⟨7516807265955806487699041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20044819375882150633864109 7516807265955806487699041)
          ·
            refine ⟨5637605449466854865774281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7516807265955806487699041 5637605449466854865774281)
            ·
              refine ⟨4228204087100141149330711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637605449466854865774281 4228204087100141149330711)
              ·
                refine ⟨6342306130650211723996067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228204087100141149330711 6342306130650211723996067)
                ·
                  refine ⟨9513459195975317585994101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6342306130650211723996067 9513459195975317585994101)
                  ·
                    refine ⟨891886799622686023686947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9513459195975317585994101 891886799622686023686947)
                    ·
                      rfl

theorem cell22_2605415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2605415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605415 prefixEnd_2605415 := by exact prefixLift 2605415
  have htrace : WordTrace (prefixWord ++ tailWord_2605415) baseStart_2605415 baseEnd_2605415 := by
    simpa [prefixWord, tailWord_2605415, baseEnd_2605415] using wordTrace_append hprefix tailTrace_2605415
  have hstable : (prefixWord ++ tailWord_2605415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605415).length < 2 ^ (prefixWord ++ tailWord_2605415).sum := by decide
  have hdescent : baseEnd_2605415 < baseStart_2605415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_2605503 : Nat := 118140960795 + 2605503 * 2 ^ 59
def prefixEnd_2605503 : Nat := 4983230072969 + 3 ^ 40 * 2605503 * 2
def baseEnd_2605503 : Nat := 891916923821083127486677

theorem tailTrace_2605503 : CollatzResearch.WordTrace tailWord_2605503 prefixEnd_2605503 891916923821083127486677 := by
  unfold tailWord_2605503
  simp only [CollatzResearch.WordTrace]
  refine ⟨95030501479715090330485163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63353667653143393553656775 95030501479715090330485163)
  ·
    refine ⟨142545752219572635495727745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95030501479715090330485163 142545752219572635495727745)
    ·
      refine ⟨106909314164679476621795809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142545752219572635495727745 106909314164679476621795809)
      ·
        refine ⟨80181985623509607466346857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106909314164679476621795809 80181985623509607466346857)
        ·
          refine ⟨60136489217632205599760143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80181985623509607466346857 60136489217632205599760143)
          ·
            refine ⟨90204733826448308399640215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60136489217632205599760143 90204733826448308399640215)
            ·
              refine ⟨135307100739672462599460323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90204733826448308399640215 135307100739672462599460323)
              ·
                refine ⟨202960651109508693899190485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135307100739672462599460323 202960651109508693899190485)
                ·
                  refine ⟨4756890260379110013262277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 202960651109508693899190485 4756890260379110013262277)
                  ·
                    refine ⟨891916923821083127486677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4756890260379110013262277 891916923821083127486677)
                    ·
                      rfl

theorem cell22_2605503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_2605503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605503 prefixEnd_2605503 := by exact prefixLift 2605503
  have htrace : WordTrace (prefixWord ++ tailWord_2605503) baseStart_2605503 baseEnd_2605503 := by
    simpa [prefixWord, tailWord_2605503, baseEnd_2605503] using wordTrace_append hprefix tailTrace_2605503
  have hstable : (prefixWord ++ tailWord_2605503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605503).length < 2 ^ (prefixWord ++ tailWord_2605503).sum := by decide
  have hdescent : baseEnd_2605503 < baseStart_2605503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605524 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_2605524 : Nat := 118140960795 + 2605524 * 2 ^ 59
def prefixEnd_2605524 : Nat := 4983230072969 + 3 ^ 40 * 2605524 * 2
def baseEnd_2605524 : Nat := 297308037516748690903871

theorem tailTrace_2605524 : CollatzResearch.WordTrace tailWord_2605524 prefixEnd_2605524 297308037516748690903871 := by
  unfold tailWord_2605524
  simp only [CollatzResearch.WordTrace]
  refine ⟨47515633706319505458499813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63354178275092673944666417 47515633706319505458499813)
  ·
    refine ⟨8909181319934907273468715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47515633706319505458499813 8909181319934907273468715)
    ·
      refine ⟨13363771979902360910203073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8909181319934907273468715 13363771979902360910203073)
      ·
        refine ⟨10022828984926770682652305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13363771979902360910203073 10022828984926770682652305)
        ·
          refine ⟨7517121738695078011989229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10022828984926770682652305 7517121738695078011989229)
          ·
            refine ⟨2818920652010654254495961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7517121738695078011989229 2818920652010654254495961)
            ·
              refine ⟨2114190489007990690871971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818920652010654254495961 2114190489007990690871971)
              ·
                refine ⟨3171285733511986036307957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114190489007990690871971 3171285733511986036307957)
                ·
                  refine ⟨297308037516748690903871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3171285733511986036307957 297308037516748690903871)
                  ·
                    rfl

theorem cell22_2605524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_2605524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605524 prefixEnd_2605524 := by exact prefixLift 2605524
  have htrace : WordTrace (prefixWord ++ tailWord_2605524) baseStart_2605524 baseEnd_2605524 := by
    simpa [prefixWord, tailWord_2605524, baseEnd_2605524] using wordTrace_append hprefix tailTrace_2605524
  have hstable : (prefixWord ++ tailWord_2605524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605524).length < 2 ^ (prefixWord ++ tailWord_2605524).sum := by decide
  have hdescent : baseEnd_2605524 < baseStart_2605524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605550 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2605550 : Nat := 118140960795 + 2605550 * 2 ^ 59
def prefixEnd_2605550 : Nat := 4983230072969 + 3 ^ 40 * 2605550 * 2
def baseEnd_2605550 : Nat := 891933012881590671561533

theorem tailTrace_2605550 : CollatzResearch.WordTrace tailWord_2605550 prefixEnd_2605550 891933012881590671561533 := by
  unfold tailWord_2605550
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879026963818102169680763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63354810473696544904964069 11879026963818102169680763)
  ·
    refine ⟨17818540445727153254521145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11879026963818102169680763 17818540445727153254521145)
    ·
      refine ⟨13363905334295364940890859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17818540445727153254521145 13363905334295364940890859)
      ·
        refine ⟨20045858001443047411336289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13363905334295364940890859 20045858001443047411336289)
        ·
          refine ⟨15034393501082285558502217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20045858001443047411336289 15034393501082285558502217)
          ·
            refine ⟨11275795125811714168876663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15034393501082285558502217 11275795125811714168876663)
            ·
              refine ⟨16913692688717571253314995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11275795125811714168876663 16913692688717571253314995)
              ·
                refine ⟨25370539033076356879972493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16913692688717571253314995 25370539033076356879972493)
                ·
                  refine ⟨9513952137403633829989685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25370539033076356879972493 9513952137403633829989685)
                  ·
                    refine ⟨891933012881590671561533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9513952137403633829989685 891933012881590671561533)
                    ·
                      rfl

theorem cell22_2605550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2605550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605550 prefixEnd_2605550 := by exact prefixLift 2605550
  have htrace : WordTrace (prefixWord ++ tailWord_2605550) baseStart_2605550 baseEnd_2605550 := by
    simpa [prefixWord, tailWord_2605550, baseEnd_2605550] using wordTrace_append hprefix tailTrace_2605550
  have hstable : (prefixWord ++ tailWord_2605550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605550).length < 2 ^ (prefixWord ++ tailWord_2605550).sum := by decide
  have hdescent : baseEnd_2605550 < baseStart_2605550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605565 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2605565 : Nat := 118140960795 + 2605565 * 2 ^ 59
def prefixEnd_2605565 : Nat := 4983230072969 + 3 ^ 40 * 2605565 * 2
def baseEnd_2605565 : Nat := 891938147688135632436487

theorem tailTrace_2605565 : CollatzResearch.WordTrace tailWord_2605565 prefixEnd_2605565 891938147688135632436487 := by
  unfold tailWord_2605565
  simp only [CollatzResearch.WordTrace]
  refine ⟨95032762805490474919242149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63355175203660316612828099 95032762805490474919242149)
  ·
    refine ⟨17818643026029464047357903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95032762805490474919242149 17818643026029464047357903)
    ·
      refine ⟨26727964539044196071036855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17818643026029464047357903 26727964539044196071036855)
      ·
        refine ⟨40091946808566294106555283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26727964539044196071036855 40091946808566294106555283)
        ·
          refine ⟨60137920212849441159832925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40091946808566294106555283 60137920212849441159832925)
          ·
            refine ⟨22551720079818540434937347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60137920212849441159832925 22551720079818540434937347)
            ·
              refine ⟨33827580119727810652406021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22551720079818540434937347 33827580119727810652406021)
              ·
                refine ⟨6342671272448964497326129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33827580119727810652406021 6342671272448964497326129)
                ·
                  refine ⟨4757003454336723372994597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6342671272448964497326129 4757003454336723372994597)
                  ·
                    refine ⟨891938147688135632436487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4757003454336723372994597 891938147688135632436487)
                    ·
                      rfl

theorem cell22_2605565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2605565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605565 prefixEnd_2605565 := by exact prefixLift 2605565
  have htrace : WordTrace (prefixWord ++ tailWord_2605565) baseStart_2605565 baseEnd_2605565 := by
    simpa [prefixWord, tailWord_2605565, baseEnd_2605565] using wordTrace_append hprefix tailTrace_2605565
  have hstable : (prefixWord ++ tailWord_2605565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605565).length < 2 ^ (prefixWord ++ tailWord_2605565).sum := by decide
  have hdescent : baseEnd_2605565 < baseStart_2605565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605567 : List Nat := [1, 1, 2, 2, 1, 2, 6, 2, 2, 3]
def baseStart_2605567 : Nat := 118140960795 + 2605567 * 2 ^ 59
def prefixEnd_2605567 : Nat := 4983230072969 + 3 ^ 40 * 2605567 * 2
def baseEnd_2605567 : Nat := 891938832329008293886481

theorem tailTrace_2605567 : CollatzResearch.WordTrace tailWord_2605567 prefixEnd_2605567 891938832329008293886481 := by
  unfold tailWord_2605567
  simp only [CollatzResearch.WordTrace]
  refine ⟨95032835751483229260814955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63355223834322152840543303 95032835751483229260814955)
  ·
    refine ⟨142549253627224843891222433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95032835751483229260814955 142549253627224843891222433)
    ·
      refine ⟨106911940220418632918416825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142549253627224843891222433 106911940220418632918416825)
      ·
        refine ⟨80183955165313974688812619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106911940220418632918416825 80183955165313974688812619)
        ·
          refine ⟨120275932747970962033218929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80183955165313974688812619 120275932747970962033218929)
          ·
            refine ⟨90206949560978221524914197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120275932747970962033218929 90206949560978221524914197)
            ·
              refine ⟨4228450760670854133980353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90206949560978221524914197 4228450760670854133980353)
              ·
                refine ⟨3171338070503140600485265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228450760670854133980353 3171338070503140600485265)
                ·
                  refine ⟨2378503552877355450363949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171338070503140600485265 2378503552877355450363949)
                  ·
                    refine ⟨891938832329008293886481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378503552877355450363949 891938832329008293886481)
                    ·
                      rfl

theorem cell22_2605567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_2605567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605567 prefixEnd_2605567 := by exact prefixLift 2605567
  have htrace : WordTrace (prefixWord ++ tailWord_2605567) baseStart_2605567 baseEnd_2605567 := by
    simpa [prefixWord, tailWord_2605567, baseEnd_2605567] using wordTrace_append hprefix tailTrace_2605567
  have hstable : (prefixWord ++ tailWord_2605567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605567).length < 2 ^ (prefixWord ++ tailWord_2605567).sum := by decide
  have hdescent : baseEnd_2605567 < baseStart_2605567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605569 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 4]
def baseStart_2605569 : Nat := 118140960795 + 2605569 * 2 ^ 59
def prefixEnd_2605569 : Nat := 4983230072969 + 3 ^ 40 * 2605569 * 2
def baseEnd_2605569 : Nat := 297313172323293651778825

theorem tailTrace_2605569 : CollatzResearch.WordTrace tailWord_2605569 prefixEnd_2605569 297313172323293651778825 := by
  unfold tailWord_2605569
  simp only [CollatzResearch.WordTrace]
  refine ⟨95032908697475983602387761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63355272464983989068258507 95032908697475983602387761)
  ·
    refine ⟨71274681523106987701790821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95032908697475983602387761 71274681523106987701790821)
    ·
      refine ⟨13364002785582560194085779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71274681523106987701790821 13364002785582560194085779)
      ·
        refine ⟨20046004178373840291128669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13364002785582560194085779 20046004178373840291128669)
        ·
          refine ⟨7517251566890190109173251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20046004178373840291128669 7517251566890190109173251)
          ·
            refine ⟨11275877350335285163759877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517251566890190109173251 11275877350335285163759877)
            ·
              refine ⟨2114227003187865968204977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11275877350335285163759877 2114227003187865968204977)
              ·
                refine ⟨1585670252390899476153733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114227003187865968204977 1585670252390899476153733)
                ·
                  refine ⟨297313172323293651778825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585670252390899476153733 297313172323293651778825)
                  ·
                    rfl

theorem cell22_2605569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 4].length) (baseStart_2605569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605569 prefixEnd_2605569 := by exact prefixLift 2605569
  have htrace : WordTrace (prefixWord ++ tailWord_2605569) baseStart_2605569 baseEnd_2605569 := by
    simpa [prefixWord, tailWord_2605569, baseEnd_2605569] using wordTrace_append hprefix tailTrace_2605569
  have hstable : (prefixWord ++ tailWord_2605569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605569).length < 2 ^ (prefixWord ++ tailWord_2605569).sum := by decide
  have hdescent : baseEnd_2605569 < baseStart_2605569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605580 : List Nat := [2, 2, 1, 2, 4, 1, 3, 7]
def baseStart_2605580 : Nat := 118140960795 + 2605580 * 2 ^ 59
def prefixEnd_2605580 : Nat := 4983230072969 + 3 ^ 40 * 2605580 * 2
def baseEnd_2605580 : Nat := 99104809166075621479049

theorem tailTrace_2605580 : CollatzResearch.WordTrace tailWord_2605580 prefixEnd_2605580 99104809166075621479049 := by
  unfold tailWord_2605580
  simp only [CollatzResearch.WordTrace]
  refine ⟨47516654950218066240519097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63355539933624088320692129 47516654950218066240519097)
  ·
    refine ⟨35637491212663549680389323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47516654950218066240519097 35637491212663549680389323)
    ·
      refine ⟨53456236818995324520583985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35637491212663549680389323 53456236818995324520583985)
      ·
        refine ⟨40092177614246493390437989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53456236818995324520583985 40092177614246493390437989)
        ·
          refine ⟨7517283302671217510707123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40092177614246493390437989 7517283302671217510707123)
          ·
            refine ⟨11275924954006826266060685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7517283302671217510707123 11275924954006826266060685)
            ·
              refine ⟨4228471857752559849772757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11275924954006826266060685 4228471857752559849772757)
              ·
                refine ⟨99104809166075621479049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4228471857752559849772757 99104809166075621479049)
                ·
                  rfl

theorem cell22_2605580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_2605580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605580 prefixEnd_2605580 := by exact prefixLift 2605580
  have htrace : WordTrace (prefixWord ++ tailWord_2605580) baseStart_2605580 baseEnd_2605580 := by
    simpa [prefixWord, tailWord_2605580, baseEnd_2605580] using wordTrace_append hprefix tailTrace_2605580
  have hstable : (prefixWord ++ tailWord_2605580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605580).length < 2 ^ (prefixWord ++ tailWord_2605580).sum := by decide
  have hdescent : baseEnd_2605580 < baseStart_2605580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605597 : List Nat := [1, 4, 2, 2, 1, 3, 3, 6]
def baseStart_2605597 : Nat := 118140960795 + 2605597 * 2 ^ 59
def prefixEnd_2605597 : Nat := 4983230072969 + 3 ^ 40 * 2605597 * 2
def baseEnd_2605597 : Nat := 99105455771344246181821

theorem tailTrace_2605597 : CollatzResearch.WordTrace tailWord_2605597 prefixEnd_2605597 99105455771344246181821 := by
  unfold tailWord_2605597
  simp only [CollatzResearch.WordTrace]
  refine ⟨95033929941374544384407045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63355953294249696256271363 95033929941374544384407045)
  ·
    refine ⟨17818861864007727072076321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95033929941374544384407045 17818861864007727072076321)
    ·
      refine ⟨13364146398005795304057241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17818861864007727072076321 13364146398005795304057241)
      ·
        refine ⟨10023109798504346478042931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13364146398005795304057241 10023109798504346478042931)
        ·
          refine ⟨15034664697756519717064397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023109798504346478042931 15034664697756519717064397)
          ·
            refine ⟨5637999261658694893899149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15034664697756519717064397 5637999261658694893899149)
            ·
              refine ⟨2114249723122010585212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5637999261658694893899149 2114249723122010585212181)
              ·
                refine ⟨99105455771344246181821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2114249723122010585212181 99105455771344246181821)
                ·
                  rfl

theorem cell22_2605597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 6].length) (baseStart_2605597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605597 prefixEnd_2605597 := by exact prefixLift 2605597
  have htrace : WordTrace (prefixWord ++ tailWord_2605597) baseStart_2605597 baseEnd_2605597 := by
    simpa [prefixWord, tailWord_2605597, baseEnd_2605597] using wordTrace_append hprefix tailTrace_2605597
  have hstable : (prefixWord ++ tailWord_2605597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605597).length < 2 ^ (prefixWord ++ tailWord_2605597).sum := by decide
  have hdescent : baseEnd_2605597 < baseStart_2605597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605625 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 7]
def baseStart_2605625 : Nat := 118140960795 + 2605625 * 2 ^ 59
def prefixEnd_2605625 : Nat := 4983230072969 + 3 ^ 40 * 2605625 * 2
def baseEnd_2605625 : Nat := 297319562304771825312101

theorem tailTrace_2605625 : CollatzResearch.WordTrace tailWord_2605625 prefixEnd_2605625 297319562304771825312101 := by
  unfold tailWord_2605625
  simp only [CollatzResearch.WordTrace]
  refine ⟨95034951185273105166426329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63356634123515403444284219 95034951185273105166426329)
  ·
    refine ⟨71276213388954828874819747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95034951185273105166426329 71276213388954828874819747)
    ·
      refine ⟨106914320083432243312229621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71276213388954828874819747 106914320083432243312229621)
      ·
        refine ⟨10023217507821772810521527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106914320083432243312229621 10023217507821772810521527)
        ·
          refine ⟨15034826261732659215782291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023217507821772810521527 15034826261732659215782291)
          ·
            refine ⟨22552239392598988823673437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15034826261732659215782291 22552239392598988823673437)
            ·
              refine ⟨8457089772224620808877539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22552239392598988823673437 8457089772224620808877539)
              ·
                refine ⟨12685634658336931213316309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8457089772224620808877539 12685634658336931213316309)
                ·
                  refine ⟨297319562304771825312101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12685634658336931213316309 297319562304771825312101)
                  ·
                    rfl

theorem cell22_2605625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_2605625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605625 prefixEnd_2605625 := by exact prefixLift 2605625
  have htrace : WordTrace (prefixWord ++ tailWord_2605625) baseStart_2605625 baseEnd_2605625 := by
    simpa [prefixWord, tailWord_2605625, baseEnd_2605625] using wordTrace_append hprefix tailTrace_2605625
  have hstable : (prefixWord ++ tailWord_2605625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605625).length < 2 ^ (prefixWord ++ tailWord_2605625).sum := by decide
  have hdescent : baseEnd_2605625 < baseStart_2605625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605629 : List Nat := [1, 4, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2605629 : Nat := 118140960795 + 2605629 * 2 ^ 59
def prefixEnd_2605629 : Nat := 4983230072969 + 3 ^ 40 * 2605629 * 2
def baseEnd_2605629 : Nat := 891960056196060798836291

theorem tailTrace_2605629 : CollatzResearch.WordTrace tailWord_2605629 prefixEnd_2605629 891960056196060798836291 := by
  unfold tailWord_2605629
  simp only [CollatzResearch.WordTrace]
  refine ⟨95035097077258613849571941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63356731384839075899714627 95035097077258613849571941)
  ·
    refine ⟨17819080701985990096794739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95035097077258613849571941 17819080701985990096794739)
    ·
      refine ⟨26728621052978985145192109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17819080701985990096794739 26728621052978985145192109)
      ·
        refine ⟨10023232894867119429447041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26728621052978985145192109 10023232894867119429447041)
        ·
          refine ⟨7517424671150339572085281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10023232894867119429447041 7517424671150339572085281)
          ·
            refine ⟨5638068503362754679063961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7517424671150339572085281 5638068503362754679063961)
            ·
              refine ⟨4228551377522066009297971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5638068503362754679063961 4228551377522066009297971)
              ·
                refine ⟨6342827066283099013946957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4228551377522066009297971 6342827066283099013946957)
                ·
                  refine ⟨2378560149856162130230109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6342827066283099013946957 2378560149856162130230109)
                  ·
                    refine ⟨891960056196060798836291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378560149856162130230109 891960056196060798836291)
                    ·
                      rfl

theorem cell22_2605629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2605629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605629 prefixEnd_2605629 := by exact prefixLift 2605629
  have htrace : WordTrace (prefixWord ++ tailWord_2605629) baseStart_2605629 baseEnd_2605629 := by
    simpa [prefixWord, tailWord_2605629, baseEnd_2605629] using wordTrace_append hprefix tailTrace_2605629
  have hstable : (prefixWord ++ tailWord_2605629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605629).length < 2 ^ (prefixWord ++ tailWord_2605629).sum := by decide
  have hdescent : baseEnd_2605629 < baseStart_2605629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605687 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 4]
def baseStart_2605687 : Nat := 118140960795 + 2605687 * 2 ^ 59
def prefixEnd_2605687 : Nat := 4983230072969 + 3 ^ 40 * 2605687 * 2
def baseEnd_2605687 : Nat := 297326636927122660295371

theorem tailTrace_2605687 : CollatzResearch.WordTrace tailWord_2605687 prefixEnd_2605687 297326636927122660295371 := by
  unfold tailWord_2605687
  simp only [CollatzResearch.WordTrace]
  refine ⟨95037212511048489755183315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63358141674032326503455543 95037212511048489755183315)
  ·
    refine ⟨142555818766572734632774973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95037212511048489755183315 142555818766572734632774973)
    ·
      refine ⟨53458432037464775487290615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142555818766572734632774973 53458432037464775487290615)
      ·
        refine ⟨80187648056197163230935923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53458432037464775487290615 80187648056197163230935923)
        ·
          refine ⟨120281472084295744846403885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80187648056197163230935923 120281472084295744846403885)
          ·
            refine ⟨45105552031610904317401457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120281472084295744846403885 45105552031610904317401457)
            ·
              refine ⟨33829164023708178238051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45105552031610904317401457 33829164023708178238051093)
              ·
                refine ⟨1585742063611320854908645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33829164023708178238051093 1585742063611320854908645)
                ·
                  refine ⟨297326636927122660295371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585742063611320854908645 297326636927122660295371)
                  ·
                    rfl

theorem cell22_2605687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 4].length) (baseStart_2605687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605687 prefixEnd_2605687 := by exact prefixLift 2605687
  have htrace : WordTrace (prefixWord ++ tailWord_2605687) baseStart_2605687 baseEnd_2605687 := by
    simpa [prefixWord, tailWord_2605687, baseEnd_2605687] using wordTrace_append hprefix tailTrace_2605687
  have hstable : (prefixWord ++ tailWord_2605687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605687).length < 2 ^ (prefixWord ++ tailWord_2605687).sum := by decide
  have hdescent : baseEnd_2605687 < baseStart_2605687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605706 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_2605706 : Nat := 118140960795 + 2605706 * 2 ^ 59
def prefixEnd_2605706 : Nat := 4983230072969 + 3 ^ 40 * 2605706 * 2
def baseEnd_2605706 : Nat := 891986414869658264661055

theorem tailTrace_2605706 : CollatzResearch.WordTrace tailWord_2605706 prefixEnd_2605706 891986414869658264661055 := by
  unfold tailWord_2605706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759476374494914000031243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63358603665319770666749981 23759476374494914000031243)
  ·
    refine ⟨35639214561742371000046865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23759476374494914000031243 35639214561742371000046865)
    ·
      refine ⟨26729410921306778250035149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35639214561742371000046865 26729410921306778250035149)
      ·
        refine ⟨10023529095490041843763181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26729410921306778250035149 10023529095490041843763181)
        ·
          refine ⟨3758823410808765691411193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10023529095490041843763181 3758823410808765691411193)
          ·
            refine ⟨2819117558106574268558395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3758823410808765691411193 2819117558106574268558395)
            ·
              refine ⟨4228676337159861402837593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819117558106574268558395 4228676337159861402837593)
              ·
                refine ⟨3171507252869896052128195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4228676337159861402837593 3171507252869896052128195)
                ·
                  refine ⟨4757260879304844078192293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3171507252869896052128195 4757260879304844078192293)
                  ·
                    refine ⟨891986414869658264661055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4757260879304844078192293 891986414869658264661055)
                    ·
                      rfl

theorem cell22_2605706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_2605706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605706 prefixEnd_2605706 := by exact prefixLift 2605706
  have htrace : WordTrace (prefixWord ++ tailWord_2605706) baseStart_2605706 baseEnd_2605706 := by
    simpa [prefixWord, tailWord_2605706, baseEnd_2605706] using wordTrace_append hprefix tailTrace_2605706
  have hstable : (prefixWord ++ tailWord_2605706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605706).length < 2 ^ (prefixWord ++ tailWord_2605706).sum := by decide
  have hdescent : baseEnd_2605706 < baseStart_2605706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605738 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_2605738 : Nat := 118140960795 + 2605738 * 2 ^ 59
def prefixEnd_2605738 : Nat := 4983230072969 + 3 ^ 40 * 2605738 * 2
def baseEnd_2605738 : Nat := 297332456374540282620319

theorem tailTrace_2605738 : CollatzResearch.WordTrace tailWord_2605738 prefixEnd_2605738 297332456374540282620319 := by
  unfold tailWord_2605738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23759768158465931366322467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63359381755909150310193245 23759768158465931366322467)
  ·
    refine ⟨35639652237698897049483701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23759768158465931366322467 35639652237698897049483701)
    ·
      refine ⟨3341217397284271598389097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35639652237698897049483701 3341217397284271598389097)
      ·
        refine ⟨2505913047963203698791823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3341217397284271598389097 2505913047963203698791823)
        ·
          refine ⟨3758869571944805548187735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505913047963203698791823 3758869571944805548187735)
          ·
            refine ⟨5638304357917208322281603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758869571944805548187735 5638304357917208322281603)
            ·
              refine ⟨8457456536875812483422405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5638304357917208322281603 8457456536875812483422405)
              ·
                refine ⟨1585773100664214840641701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8457456536875812483422405 1585773100664214840641701)
                ·
                  refine ⟨297332456374540282620319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585773100664214840641701 297332456374540282620319)
                  ·
                    rfl

theorem cell22_2605738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_2605738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605738 prefixEnd_2605738 := by exact prefixLift 2605738
  have htrace : WordTrace (prefixWord ++ tailWord_2605738) baseStart_2605738 baseEnd_2605738 := by
    simpa [prefixWord, tailWord_2605738, baseEnd_2605738] using wordTrace_append hprefix tailTrace_2605738
  have hstable : (prefixWord ++ tailWord_2605738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605738).length < 2 ^ (prefixWord ++ tailWord_2605738).sum := by decide
  have hdescent : baseEnd_2605738 < baseStart_2605738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605749 : List Nat := [1, 3, 3, 3, 1, 3, 1, 7]
def baseStart_2605749 : Nat := 118140960795 + 2605749 * 2 ^ 59
def prefixEnd_2605749 : Nat := 4983230072969 + 3 ^ 40 * 2605749 * 2
def baseEnd_2605749 : Nat := 99111237183157831759547

theorem tailTrace_2605749 : CollatzResearch.WordTrace tailWord_2605749 prefixEnd_2605749 99111237183157831759547 := by
  unfold tailWord_2605749
  simp only [CollatzResearch.WordTrace]
  refine ⟨95039473836823874343940301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63359649224549249562626867 95039473836823874343940301)
  ·
    refine ⟨35639802688808952878977613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95039473836823874343940301 35639802688808952878977613)
    ·
      refine ⟨13364926008303357329616605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35639802688808952878977613 13364926008303357329616605)
      ·
        refine ⟨5011847253113758998606227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13364926008303357329616605 5011847253113758998606227)
        ·
          refine ⟨7517770879670638497909341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011847253113758998606227 7517770879670638497909341)
          ·
            refine ⟨2819164079876489436716003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7517770879670638497909341 2819164079876489436716003)
            ·
              refine ⟨4228746119814734155074005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819164079876489436716003 4228746119814734155074005)
              ·
                refine ⟨99111237183157831759547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4228746119814734155074005 99111237183157831759547)
                ·
                  rfl

theorem cell22_2605749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 7].length) (baseStart_2605749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605749 prefixEnd_2605749 := by exact prefixLift 2605749
  have htrace : WordTrace (prefixWord ++ tailWord_2605749) baseStart_2605749 baseEnd_2605749 := by
    simpa [prefixWord, tailWord_2605749, baseEnd_2605749] using wordTrace_append hprefix tailTrace_2605749
  have hstable : (prefixWord ++ tailWord_2605749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605749).length < 2 ^ (prefixWord ++ tailWord_2605749).sum := by decide
  have hdescent : baseEnd_2605749 < baseStart_2605749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605764 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2605764 : Nat := 118140960795 + 2605764 * 2 ^ 59
def prefixEnd_2605764 : Nat := 4983230072969 + 3 ^ 40 * 2605764 * 2
def baseEnd_2605764 : Nat := 892006269454965446710877

theorem tailTrace_2605764 : CollatzResearch.WordTrace tailWord_2605764 prefixEnd_2605764 892006269454965446710877 := by
  unfold tailWord_2605764
  simp only [CollatzResearch.WordTrace]
  refine ⟨47520010465884765952868173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63360013954513021270490897 47520010465884765952868173)
  ·
    refine ⟨17820003924706787232325565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47520010465884765952868173 17820003924706787232325565)
    ·
      refine ⟨6682501471765045212122087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17820003924706787232325565 6682501471765045212122087)
      ·
        refine ⟨10023752207647567818183131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6682501471765045212122087 10023752207647567818183131)
        ·
          refine ⟨15035628311471351727274697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10023752207647567818183131 15035628311471351727274697)
          ·
            refine ⟨11276721233603513795456023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15035628311471351727274697 11276721233603513795456023)
            ·
              refine ⟨16915081850405270693184035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11276721233603513795456023 16915081850405270693184035)
              ·
                refine ⟨25372622775607906039776053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16915081850405270693184035 25372622775607906039776053)
                ·
                  refine ⟨2378683385213241191229005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25372622775607906039776053 2378683385213241191229005)
                  ·
                    refine ⟨892006269454965446710877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378683385213241191229005 892006269454965446710877)
                    ·
                      rfl

theorem cell22_2605764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2605764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605764 prefixEnd_2605764 := by exact prefixLift 2605764
  have htrace : WordTrace (prefixWord ++ tailWord_2605764) baseStart_2605764 baseEnd_2605764 := by
    simpa [prefixWord, tailWord_2605764, baseEnd_2605764] using wordTrace_append hprefix tailTrace_2605764
  have hstable : (prefixWord ++ tailWord_2605764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605764).length < 2 ^ (prefixWord ++ tailWord_2605764).sum := by decide
  have hdescent : baseEnd_2605764 < baseStart_2605764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605901 : List Nat := [1, 6, 1, 2, 3, 9]
def baseStart_2605901 : Nat := 118140960795 + 2605901 * 2 ^ 59
def prefixEnd_2605901 : Nat := 4983230072969 + 3 ^ 40 * 2605901 * 2
def baseEnd_2605901 : Nat := 11013002066107935259697

theorem tailTrace_2605901 : CollatzResearch.WordTrace tailWord_2605901 prefixEnd_2605901 11013002066107935259697 := by
  unfold tailWord_2605901
  simp only [CollatzResearch.WordTrace]
  refine ⟨95045017732273204303473557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63363345154848802868982371 95045017732273204303473557)
  ·
    refine ⟨4455235206200306451725323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 95045017732273204303473557 4455235206200306451725323)
    ·
      refine ⟨6682852809300459677587985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4455235206200306451725323 6682852809300459677587985)
      ·
        refine ⟨5012139606975344758190989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6682852809300459677587985 5012139606975344758190989)
        ·
          refine ⟨1879552352615754284321621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5012139606975344758190989 1879552352615754284321621)
          ·
            refine ⟨11013002066107935259697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1879552352615754284321621 11013002066107935259697)
            ·
              rfl

theorem cell22_2605901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 9].length) (baseStart_2605901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605901 prefixEnd_2605901 := by exact prefixLift 2605901
  have htrace : WordTrace (prefixWord ++ tailWord_2605901) baseStart_2605901 baseEnd_2605901 := by
    simpa [prefixWord, tailWord_2605901, baseEnd_2605901] using wordTrace_append hprefix tailTrace_2605901
  have hstable : (prefixWord ++ tailWord_2605901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605901).length < 2 ^ (prefixWord ++ tailWord_2605901).sum := by decide
  have hdescent : baseEnd_2605901 < baseStart_2605901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2605912 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_2605912 : Nat := 118140960795 + 2605912 * 2 ^ 59
def prefixEnd_2605912 : Nat := 4983230072969 + 3 ^ 40 * 2605912 * 2
def baseEnd_2605912 : Nat := 297352310959847464670141

theorem tailTrace_2605912 : CollatzResearch.WordTrace tailWord_2605912 prefixEnd_2605912 297352310959847464670141 := by
  unfold tailWord_2605912
  simp only [CollatzResearch.WordTrace]
  refine ⟨47522709467616676591061995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63363612623488902121415993 47522709467616676591061995)
  ·
    refine ⟨71284064201425014886592993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47522709467616676591061995 71284064201425014886592993)
    ·
      refine ⟨53463048151068761164944745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71284064201425014886592993 53463048151068761164944745)
      ·
        refine ⟨40097286113301570873708559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53463048151068761164944745 40097286113301570873708559)
        ·
          refine ⟨60145929169952356310562839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40097286113301570873708559 60145929169952356310562839)
          ·
            refine ⟨90218893754928534465844259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60145929169952356310562839 90218893754928534465844259)
            ·
              refine ⟨135328340632392801698766389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90218893754928534465844259 135328340632392801698766389)
              ·
                refine ⟨12687031934286825159259349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135328340632392801698766389 12687031934286825159259349)
                ·
                  refine ⟨297352310959847464670141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12687031934286825159259349 297352310959847464670141)
                  ·
                    rfl

theorem cell22_2605912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_2605912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2605912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2605912 prefixEnd_2605912 := by exact prefixLift 2605912
  have htrace : WordTrace (prefixWord ++ tailWord_2605912) baseStart_2605912 baseEnd_2605912 := by
    simpa [prefixWord, tailWord_2605912, baseEnd_2605912] using wordTrace_append hprefix tailTrace_2605912
  have hstable : (prefixWord ++ tailWord_2605912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2605912).length < 2 ^ (prefixWord ++ tailWord_2605912).sum := by decide
  have hdescent : baseEnd_2605912 < baseStart_2605912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2605912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606008 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_2606008 : Nat := 118140960795 + 2606008 * 2 ^ 59
def prefixEnd_2606008 : Nat := 4983230072969 + 3 ^ 40 * 2606008 * 2
def baseEnd_2606008 : Nat := 297363265213810047870043

theorem tailTrace_2606008 : CollatzResearch.WordTrace tailWord_2606008 prefixEnd_2606008 297363265213810047870043 := by
  unfold tailWord_2606008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524460171442780788809339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63365946895257041051745785 47524460171442780788809339)
  ·
    refine ⟨71286690257164171183214009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47524460171442780788809339 71286690257164171183214009)
    ·
      refine ⟨53465017692873128387410507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71286690257164171183214009 53465017692873128387410507)
      ·
        refine ⟨80197526539309692581115761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53465017692873128387410507 80197526539309692581115761)
        ·
          refine ⟨60148144904482269435836821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80197526539309692581115761 60148144904482269435836821)
          ·
            refine ⟨2819444292397606379804851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60148144904482269435836821 2819444292397606379804851)
            ·
              refine ⟨4229166438596409569707277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819444292397606379804851 4229166438596409569707277)
              ·
                refine ⟨1585937414473653588640229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4229166438596409569707277 1585937414473653588640229)
                ·
                  refine ⟨297363265213810047870043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1585937414473653588640229 297363265213810047870043)
                  ·
                    rfl

theorem cell22_2606008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_2606008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606008 prefixEnd_2606008 := by exact prefixLift 2606008
  have htrace : WordTrace (prefixWord ++ tailWord_2606008) baseStart_2606008 baseEnd_2606008 := by
    simpa [prefixWord, tailWord_2606008, baseEnd_2606008] using wordTrace_append hprefix tailTrace_2606008
  have hstable : (prefixWord ++ tailWord_2606008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606008).length < 2 ^ (prefixWord ++ tailWord_2606008).sum := by decide
  have hdescent : baseEnd_2606008 < baseStart_2606008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606036 : List Nat := [2, 4, 1, 2, 1, 3, 2, 7]
def baseStart_2606036 : Nat := 118140960795 + 2606036 * 2 ^ 59
def prefixEnd_2606036 : Nat := 4983230072969 + 3 ^ 40 * 2606036 * 2
def baseEnd_2606036 : Nat := 99122153401516378212227

theorem tailTrace_2606036 : CollatzResearch.WordTrace tailWord_2606036 prefixEnd_2606036 99122153401516378212227 := by
  unfold tailWord_2606036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524970793392061179818981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63366627724522748239758641 47524970793392061179818981)
  ·
    refine ⟨8910932023761011471216059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47524970793392061179818981 8910932023761011471216059)
    ·
      refine ⟨13366398035641517206824089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8910932023761011471216059 13366398035641517206824089)
      ·
        refine ⟨10024798526731137905118067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13366398035641517206824089 10024798526731137905118067)
        ·
          refine ⟨15037197790096706857677101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10024798526731137905118067 15037197790096706857677101)
          ·
            refine ⟨5638949171286265071628913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15037197790096706857677101 5638949171286265071628913)
            ·
              refine ⟨4229211878464698803721685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5638949171286265071628913 4229211878464698803721685)
              ·
                refine ⟨99122153401516378212227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4229211878464698803721685 99122153401516378212227)
                ·
                  rfl

theorem cell22_2606036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_2606036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606036 prefixEnd_2606036 := by exact prefixLift 2606036
  have htrace : WordTrace (prefixWord ++ tailWord_2606036) baseStart_2606036 baseEnd_2606036 := by
    simpa [prefixWord, tailWord_2606036, baseEnd_2606036] using wordTrace_append hprefix tailTrace_2606036
  have hstable : (prefixWord ++ tailWord_2606036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606036).length < 2 ^ (prefixWord ++ tailWord_2606036).sum := by decide
  have hdescent : baseEnd_2606036 < baseStart_2606036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606040 : List Nat := [2, 1, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_2606040 : Nat := 118140960795 + 2606040 * 2 ^ 59
def prefixEnd_2606040 : Nat := 4983230072969 + 3 ^ 40 * 2606040 * 2
def baseEnd_2606040 : Nat := 892100749895392726810031

theorem tailTrace_2606040 : CollatzResearch.WordTrace tailWord_2606040 prefixEnd_2606040 892100749895392726810031 := by
  unfold tailWord_2606040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47525043739384815521391787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63366724985846420695189049 47525043739384815521391787)
  ·
    refine ⟨71287565609077223282087681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47525043739384815521391787 71287565609077223282087681)
    ·
      refine ⟨53465674206807917461565761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71287565609077223282087681 53465674206807917461565761)
      ·
        refine ⟨40099255655105938096174321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53465674206807917461565761 40099255655105938096174321)
        ·
          refine ⟨30074441741329453572130741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40099255655105938096174321 30074441741329453572130741)
          ·
            refine ⟨2819478913249636272387257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30074441741329453572130741 2819478913249636272387257)
            ·
              refine ⟨2114609184937227204290443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819478913249636272387257 2114609184937227204290443)
              ·
                refine ⟨3171913777405840806435665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114609184937227204290443 3171913777405840806435665)
                ·
                  refine ⟨2378935333054380604826749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3171913777405840806435665 2378935333054380604826749)
                  ·
                    refine ⟨892100749895392726810031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378935333054380604826749 892100749895392726810031)
                    ·
                      rfl

theorem cell22_2606040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_2606040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606040 prefixEnd_2606040 := by exact prefixLift 2606040
  have htrace : WordTrace (prefixWord ++ tailWord_2606040) baseStart_2606040 baseEnd_2606040 := by
    simpa [prefixWord, tailWord_2606040, baseEnd_2606040] using wordTrace_append hprefix tailTrace_2606040
  have hstable : (prefixWord ++ tailWord_2606040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606040).length < 2 ^ (prefixWord ++ tailWord_2606040).sum := by decide
  have hdescent : baseEnd_2606040 < baseStart_2606040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606051 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 5, 3]
def baseStart_2606051 : Nat := 118140960795 + 2606051 * 2 ^ 59
def prefixEnd_2606051 : Nat := 4983230072969 + 3 ^ 40 * 2606051 * 2
def baseEnd_2606051 : Nat := 892104515420192364784997

theorem tailTrace_2606051 : CollatzResearch.WordTrace tailWord_2606051 prefixEnd_2606051 892104515420192364784997 := by
  unfold tailWord_2606051
  simp only [CollatzResearch.WordTrace]
  refine ⟨95050488681729779921434007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63366992454486519947622671 95050488681729779921434007)
  ·
    refine ⟨142575733022594669882151011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95050488681729779921434007 142575733022594669882151011)
    ·
      refine ⟨213863599533892004823226517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142575733022594669882151011 213863599533892004823226517)
      ·
        refine ⟨10024856228151187726088743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 213863599533892004823226517 10024856228151187726088743)
        ·
          refine ⟨15037284342226781589133115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10024856228151187726088743 15037284342226781589133115)
          ·
            refine ⟨22555926513340172383699673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037284342226781589133115 22555926513340172383699673)
            ·
              refine ⟨16916944885005129287774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22555926513340172383699673 16916944885005129287774755)
              ·
                refine ⟨25375417327507693931662133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16916944885005129287774755 25375417327507693931662133)
                ·
                  refine ⟨2378945374453846306093325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25375417327507693931662133 2378945374453846306093325)
                  ·
                    refine ⟨892104515420192364784997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2378945374453846306093325 892104515420192364784997)
                    ·
                      rfl

theorem cell22_2606051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 3].length) (baseStart_2606051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606051 prefixEnd_2606051 := by exact prefixLift 2606051
  have htrace : WordTrace (prefixWord ++ tailWord_2606051) baseStart_2606051 baseEnd_2606051 := by
    simpa [prefixWord, tailWord_2606051, baseEnd_2606051] using wordTrace_append hprefix tailTrace_2606051
  have hstable : (prefixWord ++ tailWord_2606051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606051).length < 2 ^ (prefixWord ++ tailWord_2606051).sum := by decide
  have hdescent : baseEnd_2606051 < baseStart_2606051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606081 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 5]
def baseStart_2606081 : Nat := 118140960795 + 2606081 * 2 ^ 59
def prefixEnd_2606081 : Nat := 4983230072969 + 3 ^ 40 * 2606081 * 2
def baseEnd_2606081 : Nat := 297371595011094095511635

theorem tailTrace_2606081 : CollatzResearch.WordTrace tailWord_2606081 prefixEnd_2606081 297371595011094095511635 := by
  unfold tailWord_2606081
  simp only [CollatzResearch.WordTrace]
  refine ⟨95051582871621095045026097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63367721914414063363350731 95051582871621095045026097)
  ·
    refine ⟨71288687153715821283769573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95051582871621095045026097 71288687153715821283769573)
    ·
      refine ⟨13366628841321716490706795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71288687153715821283769573 13366628841321716490706795)
      ·
        refine ⟨20049943261982574736060193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13366628841321716490706795 20049943261982574736060193)
        ·
          refine ⟨15037457446486931052045145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20049943261982574736060193 15037457446486931052045145)
          ·
            refine ⟨11278093084865198289033859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15037457446486931052045145 11278093084865198289033859)
            ·
              refine ⟨16917139627297797433550789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278093084865198289033859 16917139627297797433550789)
              ·
                refine ⟨3171963680118337018790773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16917139627297797433550789 3171963680118337018790773)
                ·
                  refine ⟨297371595011094095511635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3171963680118337018790773 297371595011094095511635)
                  ·
                    rfl

theorem cell22_2606081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 5].length) (baseStart_2606081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606081 prefixEnd_2606081 := by exact prefixLift 2606081
  have htrace : WordTrace (prefixWord ++ tailWord_2606081) baseStart_2606081 baseEnd_2606081 := by
    simpa [prefixWord, tailWord_2606081, baseEnd_2606081] using wordTrace_append hprefix tailTrace_2606081
  have hstable : (prefixWord ++ tailWord_2606081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606081).length < 2 ^ (prefixWord ++ tailWord_2606081).sum := by decide
  have hdescent : baseEnd_2606081 < baseStart_2606081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606111 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2606111 : Nat := 118140960795 + 2606111 * 2 ^ 59
def prefixEnd_2606111 : Nat := 4983230072969 + 3 ^ 40 * 2606111 * 2
def baseEnd_2606111 : Nat := 892125054646372208284813

theorem tailTrace_2606111 : CollatzResearch.WordTrace tailWord_2606111 prefixEnd_2606111 892125054646372208284813 := by
  unfold tailWord_2606111
  simp only [CollatzResearch.WordTrace]
  refine ⟨95052677061512410168618187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63368451374341606779078791 95052677061512410168618187)
  ·
    refine ⟨142579015592268615252927281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95052677061512410168618187 142579015592268615252927281)
    ·
      refine ⟨106934261694201461439695461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142579015592268615252927281 106934261694201461439695461)
      ·
        refine ⟨20050174067662774019942899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106934261694201461439695461 20050174067662774019942899)
        ·
          refine ⟨30075261101494161029914349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20050174067662774019942899 30075261101494161029914349)
          ·
            refine ⟨11278222913060310386217881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30075261101494161029914349 11278222913060310386217881)
            ·
              refine ⟨8458667184795232789663411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11278222913060310386217881 8458667184795232789663411)
              ·
                refine ⟨12688000777192849184495117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8458667184795232789663411 12688000777192849184495117)
                ·
                  refine ⟨4758000291447318444185669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12688000777192849184495117 4758000291447318444185669)
                  ·
                    refine ⟨892125054646372208284813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758000291447318444185669 892125054646372208284813)
                    ·
                      rfl

theorem cell22_2606111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2606111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606111 prefixEnd_2606111 := by exact prefixLift 2606111
  have htrace : WordTrace (prefixWord ++ tailWord_2606111) baseStart_2606111 baseEnd_2606111 := by
    simpa [prefixWord, tailWord_2606111, baseEnd_2606111] using wordTrace_append hprefix tailTrace_2606111
  have hstable : (prefixWord ++ tailWord_2606111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606111).length < 2 ^ (prefixWord ++ tailWord_2606111).sum := by decide
  have hdescent : baseEnd_2606111 < baseStart_2606111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606126 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_2606126 : Nat := 118140960795 + 2606126 * 2 ^ 59
def prefixEnd_2606126 : Nat := 4983230072969 + 3 ^ 40 * 2606126 * 2
def baseEnd_2606126 : Nat := 297376729817639056386589

theorem tailTrace_2606126 : CollatzResearch.WordTrace tailWord_2606126 prefixEnd_2606126 297376729817639056386589 := by
  unfold tailWord_2606126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11881653019557258466301779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63368816104305378486942821 11881653019557258466301779)
  ·
    refine ⟨17822479529335887699452669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11881653019557258466301779 17822479529335887699452669)
    ·
      refine ⟨6683429823500957887294751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17822479529335887699452669 6683429823500957887294751)
      ·
        refine ⟨10025144735251436830942127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6683429823500957887294751 10025144735251436830942127)
        ·
          refine ⟨15037717102877155246413191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025144735251436830942127 15037717102877155246413191)
          ·
            refine ⟨22556575654315732869619787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15037717102877155246413191 22556575654315732869619787)
            ·
              refine ⟨33834863481473599304429681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22556575654315732869619787 33834863481473599304429681)
              ·
                refine ⟨25376147611105199478322261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33834863481473599304429681 25376147611105199478322261)
                ·
                  refine ⟨297376729817639056386589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25376147611105199478322261 297376729817639056386589)
                  ·
                    rfl

theorem cell22_2606126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_2606126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606126 prefixEnd_2606126 := by exact prefixLift 2606126
  have htrace : WordTrace (prefixWord ++ tailWord_2606126) baseStart_2606126 baseEnd_2606126 := by
    simpa [prefixWord, tailWord_2606126, baseEnd_2606126] using wordTrace_append hprefix tailTrace_2606126
  have hstable : (prefixWord ++ tailWord_2606126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606126).length < 2 ^ (prefixWord ++ tailWord_2606126).sum := by decide
  have hdescent : baseEnd_2606126 < baseStart_2606126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606139 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 5, 6]
def baseStart_2606139 : Nat := 118140960795 + 2606139 * 2 ^ 59
def prefixEnd_2606139 : Nat := 4983230072969 + 3 ^ 40 * 2606139 * 2
def baseEnd_2606139 : Nat := 892134639618589468584727

theorem tailTrace_2606139 : CollatzResearch.WordTrace tailWord_2606139 prefixEnd_2606139 892134639618589468584727 := by
  unfold tailWord_2606139
  simp only [CollatzResearch.WordTrace]
  refine ⟨95053698305410970950637471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63369132203607313967091647 95053698305410970950637471)
  ·
    refine ⟨142580547458116456425956207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95053698305410970950637471 142580547458116456425956207)
    ·
      refine ⟨213870821187174684638934311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142580547458116456425956207 213870821187174684638934311)
      ·
        refine ⟨320806231780762026958401467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213870821187174684638934311 320806231780762026958401467)
        ·
          refine ⟨481209347671143040437602201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320806231780762026958401467 481209347671143040437602201)
          ·
            refine ⟨360907010753357280328201651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481209347671143040437602201 360907010753357280328201651)
            ·
              refine ⟨541360516130035920492302477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360907010753357280328201651 541360516130035920492302477)
              ·
                refine ⟨203010193548763470184613429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 541360516130035920492302477 203010193548763470184613429)
                ·
                  refine ⟨19032205645196575329807509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203010193548763470184613429 19032205645196575329807509)
                  ·
                    refine ⟨892134639618589468584727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19032205645196575329807509 892134639618589468584727)
                    ·
                      rfl

theorem cell22_2606139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_2606139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606139 prefixEnd_2606139 := by exact prefixLift 2606139
  have htrace : WordTrace (prefixWord ++ tailWord_2606139) baseStart_2606139 baseEnd_2606139 := by
    simpa [prefixWord, tailWord_2606139, baseEnd_2606139] using wordTrace_append hprefix tailTrace_2606139
  have hstable : (prefixWord ++ tailWord_2606139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606139).length < 2 ^ (prefixWord ++ tailWord_2606139).sum := by decide
  have hdescent : baseEnd_2606139 < baseStart_2606139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606250 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_2606250 : Nat := 118140960795 + 2606250 * 2 ^ 59
def prefixEnd_2606250 : Nat := 4983230072969 + 3 ^ 40 * 2606250 * 2
def baseEnd_2606250 : Nat := 297390879062340726353129

theorem tailTrace_2606250 : CollatzResearch.WordTrace tailWord_2606250 prefixEnd_2606250 297390879062340726353129 := by
  unfold tailWord_2606250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23764436702002209226982051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63371831205339224605285469 23764436702002209226982051)
  ·
    refine ⟨35646655053003313840473077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23764436702002209226982051 35646655053003313840473077)
    ·
      refine ⟨3341873911219060672544351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35646655053003313840473077 3341873911219060672544351)
      ·
        refine ⟨5012810866828591008816527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341873911219060672544351 5012810866828591008816527)
        ·
          refine ⟨7519216300242886513224791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012810866828591008816527 7519216300242886513224791)
          ·
            refine ⟨11278824450364329769837187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519216300242886513224791 11278824450364329769837187)
            ·
              refine ⟨16918236675546494654755781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11278824450364329769837187 16918236675546494654755781)
              ·
                refine ⟨3172169376664967747766709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16918236675546494654755781 3172169376664967747766709)
                ·
                  refine ⟨297390879062340726353129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3172169376664967747766709 297390879062340726353129)
                  ·
                    rfl

theorem cell22_2606250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_2606250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606250 prefixEnd_2606250 := by exact prefixLift 2606250
  have htrace : WordTrace (prefixWord ++ tailWord_2606250) baseStart_2606250 baseEnd_2606250 := by
    simpa [prefixWord, tailWord_2606250, baseEnd_2606250] using wordTrace_append hprefix tailTrace_2606250
  have hstable : (prefixWord ++ tailWord_2606250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606250).length < 2 ^ (prefixWord ++ tailWord_2606250).sum := by decide
  have hdescent : baseEnd_2606250 < baseStart_2606250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606291 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_2606291 : Nat := 118140960795 + 2606291 * 2 ^ 59
def prefixEnd_2606291 : Nat := 4983230072969 + 3 ^ 40 * 2606291 * 2
def baseEnd_2606291 : Nat := 892186672324911738784261

theorem tailTrace_2606291 : CollatzResearch.WordTrace tailWord_2606291 prefixEnd_2606291 892186672324911738784261 := by
  unfold tailWord_2606291
  simp only [CollatzResearch.WordTrace]
  refine ⟨95059242200860300910170727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63372828133906867273447151 95059242200860300910170727)
  ·
    refine ⟨142588863301290451365256091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95059242200860300910170727 142588863301290451365256091)
    ·
      refine ⟨213883294951935677047884137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142588863301290451365256091 213883294951935677047884137)
      ·
        refine ⟨160412471213951757785913103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213883294951935677047884137 160412471213951757785913103)
        ·
          refine ⟨240618706820927636678869655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160412471213951757785913103 240618706820927636678869655)
          ·
            refine ⟨360928060231391455018304483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240618706820927636678869655 360928060231391455018304483)
            ·
              refine ⟨541392090347087182527456725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360928060231391455018304483 541392090347087182527456725)
              ·
                refine ⟨12688877117509855840487267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 541392090347087182527456725 12688877117509855840487267)
                ·
                  refine ⟨19033315676264783760730901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12688877117509855840487267 19033315676264783760730901)
                  ·
                    refine ⟨892186672324911738784261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19033315676264783760730901 892186672324911738784261)
                    ·
                      rfl

theorem cell22_2606291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_2606291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606291 prefixEnd_2606291 := by exact prefixLift 2606291
  have htrace : WordTrace (prefixWord ++ tailWord_2606291) baseStart_2606291 baseEnd_2606291 := by
    simpa [prefixWord, tailWord_2606291, baseEnd_2606291] using wordTrace_append hprefix tailTrace_2606291
  have hstable : (prefixWord ++ tailWord_2606291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606291).length < 2 ^ (prefixWord ++ tailWord_2606291).sum := by decide
  have hdescent : baseEnd_2606291 < baseStart_2606291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606308 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2606308 : Nat := 118140960795 + 2606308 * 2 ^ 59
def prefixEnd_2606308 : Nat := 4983230072969 + 3 ^ 40 * 2606308 * 2
def baseEnd_2606308 : Nat := 892192491772329361109209

theorem tailTrace_2606308 : CollatzResearch.WordTrace tailWord_2606308 prefixEnd_2606308 892192491772329361109209 := by
  unfold tailWord_2606308
  simp only [CollatzResearch.WordTrace]
  refine ⟨47529931120899356406769789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63373241494532475209026385 47529931120899356406769789)
  ·
    refine ⟨17823724170337258652538671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47529931120899356406769789 17823724170337258652538671)
    ·
      refine ⟨26735586255505887978808007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17823724170337258652538671 26735586255505887978808007)
      ·
        refine ⟨40103379383258831968212011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26735586255505887978808007 40103379383258831968212011)
        ·
          refine ⟨60155069074888247952318017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40103379383258831968212011 60155069074888247952318017)
          ·
            refine ⟨45116301806166185964238513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60155069074888247952318017 45116301806166185964238513)
            ·
              refine ⟨33837226354624639473178885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45116301806166185964238513 33837226354624639473178885)
              ·
                refine ⟨6344479941492119901221041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33837226354624639473178885 6344479941492119901221041)
                ·
                  refine ⟨4758359956119089925915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6344479941492119901221041 4758359956119089925915781)
                  ·
                    refine ⟨892192491772329361109209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758359956119089925915781 892192491772329361109209)
                    ·
                      rfl

theorem cell22_2606308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2606308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606308 prefixEnd_2606308 := by exact prefixLift 2606308
  have htrace : WordTrace (prefixWord ++ tailWord_2606308) baseStart_2606308 baseEnd_2606308 := by
    simpa [prefixWord, tailWord_2606308, baseEnd_2606308] using wordTrace_append hprefix tailTrace_2606308
  have hstable : (prefixWord ++ tailWord_2606308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606308).length < 2 ^ (prefixWord ++ tailWord_2606308).sum := by decide
  have hdescent : baseEnd_2606308 < baseStart_2606308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606340 : List Nat := [2, 3, 2, 2, 2, 1, 4, 6]
def baseStart_2606340 : Nat := 118140960795 + 2606340 * 2 ^ 59
def prefixEnd_2606340 : Nat := 4983230072969 + 3 ^ 40 * 2606340 * 2
def baseEnd_2606340 : Nat := 99133716225143549367679

theorem tailTrace_2606340 : CollatzResearch.WordTrace tailWord_2606340 prefixEnd_2606340 99133716225143549367679 := by
  unfold tailWord_2606340
  simp only [CollatzResearch.WordTrace]
  refine ⟨47530514688841391139352237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63374019585121854852469649 47530514688841391139352237)
  ·
    refine ⟨17823943008315521677257089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47530514688841391139352237 17823943008315521677257089)
    ·
      refine ⟨13367957256236641257942817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17823943008315521677257089 13367957256236641257942817)
      ·
        refine ⟨10025967942177480943457113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13367957256236641257942817 10025967942177480943457113)
        ·
          refine ⟨7519475956633110707592835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10025967942177480943457113 7519475956633110707592835)
          ·
            refine ⟨11279213934949666061389253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519475956633110707592835 11279213934949666061389253)
            ·
              refine ⟨2114852612803062386510485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11279213934949666061389253 2114852612803062386510485)
              ·
                refine ⟨99133716225143549367679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2114852612803062386510485 99133716225143549367679)
                ·
                  rfl

theorem cell22_2606340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_2606340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606340 prefixEnd_2606340 := by exact prefixLift 2606340
  have htrace : WordTrace (prefixWord ++ tailWord_2606340) baseStart_2606340 baseEnd_2606340 := by
    simpa [prefixWord, tailWord_2606340, baseEnd_2606340] using wordTrace_append hprefix tailTrace_2606340
  have hstable : (prefixWord ++ tailWord_2606340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606340).length < 2 ^ (prefixWord ++ tailWord_2606340).sum := by decide
  have hdescent : baseEnd_2606340 < baseStart_2606340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606385 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 5]
def baseStart_2606385 : Nat := 118140960795 + 2606385 * 2 ^ 59
def prefixEnd_2606385 : Nat := 4983230072969 + 3 ^ 40 * 2606385 * 2
def baseEnd_2606385 : Nat := 297406283481975608977991

theorem tailTrace_2606385 : CollatzResearch.WordTrace tailWord_2606385 prefixEnd_2606385 297406283481975608977991 := by
  unfold tailWord_2606385
  simp only [CollatzResearch.WordTrace]
  refine ⟨95062670662519754964092609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63375113775013169976061739 95062670662519754964092609)
  ·
    refine ⟨71297002996889816223069457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95062670662519754964092609 71297002996889816223069457)
    ·
      refine ⟨53472752247667362167302093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71297002996889816223069457 53472752247667362167302093)
      ·
        refine ⟨20052282092875260812738285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53472752247667362167302093 20052282092875260812738285)
        ·
          refine ⟨7519605784828222804776857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20052282092875260812738285 7519605784828222804776857)
          ·
            refine ⟨5639704338621167103582643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7519605784828222804776857 5639704338621167103582643)
            ·
              refine ⟨8459556507931750655373965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5639704338621167103582643 8459556507931750655373965)
              ·
                refine ⟨3172333690474406495765237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8459556507931750655373965 3172333690474406495765237)
                ·
                  refine ⟨297406283481975608977991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3172333690474406495765237 297406283481975608977991)
                  ·
                    rfl

theorem cell22_2606385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 5].length) (baseStart_2606385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606385 prefixEnd_2606385 := by exact prefixLift 2606385
  have htrace : WordTrace (prefixWord ++ tailWord_2606385) baseStart_2606385 baseEnd_2606385 := by
    simpa [prefixWord, tailWord_2606385, baseEnd_2606385] using wordTrace_append hprefix tailTrace_2606385
  have hstable : (prefixWord ++ tailWord_2606385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606385).length < 2 ^ (prefixWord ++ tailWord_2606385).sum := by decide
  have hdescent : baseEnd_2606385 < baseStart_2606385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606445 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_2606445 : Nat := 118140960795 + 2606445 * 2 ^ 59
def prefixEnd_2606445 : Nat := 4983230072969 + 3 ^ 40 * 2606445 * 2
def baseEnd_2606445 : Nat := 892239389672106670433789

theorem tailTrace_2606445 : CollatzResearch.WordTrace tailWord_2606445 prefixEnd_2606445 892239389672106670433789 := by
  unfold tailWord_2606445
  simp only [CollatzResearch.WordTrace]
  refine ⟨95064859042302385211276789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63376572694868256807517859 95064859042302385211276789)
  ·
    refine ⟨8912330535215848613557199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95064859042302385211276789 8912330535215848613557199)
    ·
      refine ⟨13368495802823772920335799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912330535215848613557199 13368495802823772920335799)
      ·
        refine ⟨20052743704235659380503699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368495802823772920335799 20052743704235659380503699)
        ·
          refine ⟨30079115556353489070755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20052743704235659380503699 30079115556353489070755549)
          ·
            refine ⟨11279668333632558401533331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30079115556353489070755549 11279668333632558401533331)
            ·
              refine ⟨16919502500448837602299997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11279668333632558401533331 16919502500448837602299997)
              ·
                refine ⟨6344813437668314100862499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16919502500448837602299997 6344813437668314100862499)
                ·
                  refine ⟨9517220156502471151293749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6344813437668314100862499 9517220156502471151293749)
                  ·
                    refine ⟨892239389672106670433789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9517220156502471151293749 892239389672106670433789)
                    ·
                      rfl

theorem cell22_2606445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_2606445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606445 prefixEnd_2606445 := by exact prefixLift 2606445
  have htrace : WordTrace (prefixWord ++ tailWord_2606445) baseStart_2606445 baseEnd_2606445 := by
    simpa [prefixWord, tailWord_2606445, baseEnd_2606445] using wordTrace_append hprefix tailTrace_2606445
  have hstable : (prefixWord ++ tailWord_2606445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606445).length < 2 ^ (prefixWord ++ tailWord_2606445).sum := by decide
  have hdescent : baseEnd_2606445 < baseStart_2606445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606466 : List Nat := [3, 4, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_2606466 : Nat := 118140960795 + 2606466 * 2 ^ 59
def prefixEnd_2606466 : Nat := 4983230072969 + 3 ^ 40 * 2606466 * 2
def baseEnd_2606466 : Nat := 892246578401269615658725

theorem tailTrace_2606466 : CollatzResearch.WordTrace tailWord_2606466 prefixEnd_2606466 892246578401269615658725 := by
  unfold tailWord_2606466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23766406243806576449447813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63377083316817537198527501 23766406243806576449447813)
  ·
    refine ⟨4456201170713733084271465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23766406243806576449447813 4456201170713733084271465)
    ·
      refine ⟨3342150878035299813203599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456201170713733084271465 3342150878035299813203599)
      ·
        refine ⟨5013226317052949719805399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342150878035299813203599 5013226317052949719805399)
        ·
          refine ⟨7519839475579424579708099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013226317052949719805399 7519839475579424579708099)
          ·
            refine ⟨11279759213369136869562149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519839475579424579708099 11279759213369136869562149)
            ·
              refine ⟨2114954852506713163042903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11279759213369136869562149 2114954852506713163042903)
              ·
                refine ⟨3172432278760069744564355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114954852506713163042903 3172432278760069744564355)
                ·
                  refine ⟨4758648418140104616846533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172432278760069744564355 4758648418140104616846533)
                  ·
                    refine ⟨892246578401269615658725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758648418140104616846533 892246578401269615658725)
                    ·
                      rfl

theorem cell22_2606466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_2606466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606466 prefixEnd_2606466 := by exact prefixLift 2606466
  have htrace : WordTrace (prefixWord ++ tailWord_2606466) baseStart_2606466 baseEnd_2606466 := by
    simpa [prefixWord, tailWord_2606466, baseEnd_2606466] using wordTrace_append hprefix tailTrace_2606466
  have hstable : (prefixWord ++ tailWord_2606466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606466).length < 2 ^ (prefixWord ++ tailWord_2606466).sum := by decide
  have hdescent : baseEnd_2606466 < baseStart_2606466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606509 : List Nat := [1, 5, 2, 2, 1, 3, 2, 6]
def baseStart_2606509 : Nat := 118140960795 + 2606509 * 2 ^ 59
def prefixEnd_2606509 : Nat := 4983230072969 + 3 ^ 40 * 2606509 * 2
def baseEnd_2606509 : Nat := 99140144242225759648177

theorem tailTrace_2606509 : CollatzResearch.WordTrace tailWord_2606509 prefixEnd_2606509 99140144242225759648177 := by
  unfold tailWord_2606509
  simp only [CollatzResearch.WordTrace]
  refine ⟨95067193314070524141606581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63378128876047016094404387 95067193314070524141606581)
  ·
    refine ⟨8912549373194111638275617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95067193314070524141606581 8912549373194111638275617)
    ·
      refine ⟨6684412029895583728706713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8912549373194111638275617 6684412029895583728706713)
      ·
        refine ⟨5013309022421687796530035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6684412029895583728706713 5013309022421687796530035)
        ·
          refine ⟨7519963533632531694795053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013309022421687796530035 7519963533632531694795053)
          ·
            refine ⟨2819986325112199385548145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7519963533632531694795053 2819986325112199385548145)
            ·
              refine ⟨2114989743834149539161109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2819986325112199385548145 2114989743834149539161109)
              ·
                refine ⟨99140144242225759648177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2114989743834149539161109 99140144242225759648177)
                ·
                  rfl

theorem cell22_2606509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 6].length) (baseStart_2606509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606509 prefixEnd_2606509 := by exact prefixLift 2606509
  have htrace : WordTrace (prefixWord ++ tailWord_2606509) baseStart_2606509 baseEnd_2606509 := by
    simpa [prefixWord, tailWord_2606509, baseEnd_2606509] using wordTrace_append hprefix tailTrace_2606509
  have hstable : (prefixWord ++ tailWord_2606509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606509).length < 2 ^ (prefixWord ++ tailWord_2606509).sum := by decide
  have hdescent : baseEnd_2606509 < baseStart_2606509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606554 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_2606554 : Nat := 118140960795 + 2606554 * 2 ^ 59
def prefixEnd_2606554 : Nat := 4983230072969 + 3 ^ 40 * 2606554 * 2
def baseEnd_2606554 : Nat := 297425567533222239819485

theorem tailTrace_2606554 : CollatzResearch.WordTrace tailWord_2606554 prefixEnd_2606554 297425567533222239819485 := by
  unfold tailWord_2606554
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767208649726874206748679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63379223065938331217996477 23767208649726874206748679)
  ·
    refine ⟨35650812974590311310123019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23767208649726874206748679 35650812974590311310123019)
    ·
      refine ⟨53476219461885466965184529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35650812974590311310123019 53476219461885466965184529)
      ·
        refine ⟨40107164596414100223888397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53476219461885466965184529 40107164596414100223888397)
        ·
          refine ⟨15040186723655287583958149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40107164596414100223888397 15040186723655287583958149)
          ·
            refine ⟨2820035010685366421992153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15040186723655287583958149 2820035010685366421992153)
            ·
              refine ⟨2115026258014024816494115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820035010685366421992153 2115026258014024816494115)
              ·
                refine ⟨3172539387021037224741173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115026258014024816494115 3172539387021037224741173)
                ·
                  refine ⟨297425567533222239819485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3172539387021037224741173 297425567533222239819485)
                  ·
                    rfl

theorem cell22_2606554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_2606554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606554 prefixEnd_2606554 := by exact prefixLift 2606554
  have htrace : WordTrace (prefixWord ++ tailWord_2606554) baseStart_2606554 baseEnd_2606554 := by
    simpa [prefixWord, tailWord_2606554, baseEnd_2606554] using wordTrace_append hprefix tailTrace_2606554
  have hstable : (prefixWord ++ tailWord_2606554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606554).length < 2 ^ (prefixWord ++ tailWord_2606554).sum := by decide
  have hdescent : baseEnd_2606554 < baseStart_2606554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606567 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2606567 : Nat := 118140960795 + 2606567 * 2 ^ 59
def prefixEnd_2606567 : Nat := 4983230072969 + 3 ^ 40 * 2606567 * 2
def baseEnd_2606567 : Nat := 892281152765339018883415

theorem tailTrace_2606567 : CollatzResearch.WordTrace tailWord_2606567 prefixEnd_2606567 892281152765339018883415 := by
  unfold tailWord_2606567
  simp only [CollatzResearch.WordTrace]
  refine ⟨95069308747860400047217955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63379539165240266698145303 95069308747860400047217955)
  ·
    refine ⟨142603963121790600070826933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95069308747860400047217955 142603963121790600070826933)
    ·
      refine ⟨13369121542667868756640025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142603963121790600070826933 13369121542667868756640025)
      ·
        refine ⟨10026841157000901567480019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13369121542667868756640025 10026841157000901567480019)
        ·
          refine ⟨15040261735501352351220029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10026841157000901567480019 15040261735501352351220029)
          ·
            refine ⟨5640098150813007131707511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15040261735501352351220029 5640098150813007131707511)
            ·
              refine ⟨8460147226219510697561267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640098150813007131707511 8460147226219510697561267)
              ·
                refine ⟨12690220839329266046341901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8460147226219510697561267 12690220839329266046341901)
                ·
                  refine ⟨4758832814748474767378213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12690220839329266046341901 4758832814748474767378213)
                  ·
                    refine ⟨892281152765339018883415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758832814748474767378213 892281152765339018883415)
                    ·
                      rfl

theorem cell22_2606567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2606567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606567 prefixEnd_2606567 := by exact prefixLift 2606567
  have htrace : WordTrace (prefixWord ++ tailWord_2606567) baseStart_2606567 baseEnd_2606567 := by
    simpa [prefixWord, tailWord_2606567, baseEnd_2606567] using wordTrace_append hprefix tailTrace_2606567
  have hstable : (prefixWord ++ tailWord_2606567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606567).length < 2 ^ (prefixWord ++ tailWord_2606567).sum := by decide
  have hdescent : baseEnd_2606567 < baseStart_2606567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606584 : List Nat := [2, 1, 2, 1, 1, 6, 3, 1, 1, 4]
def baseStart_2606584 : Nat := 118140960795 + 2606584 * 2 ^ 59
def prefixEnd_2606584 : Nat := 4983230072969 + 3 ^ 40 * 2606584 * 2
def baseEnd_2606584 : Nat := 892286972212756641208363

theorem tailTrace_2606584 : CollatzResearch.WordTrace tailWord_2606584 prefixEnd_2606584 892286972212756641208363 := by
  unfold tailWord_2606584
  simp only [CollatzResearch.WordTrace]
  refine ⟨47534964394399405975293403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63379952525865874633724537 47534964394399405975293403)
  ·
    refine ⟨71302446591599108962940105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47534964394399405975293403 71302446591599108962940105)
    ·
      refine ⟨53476834943699331722205079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71302446591599108962940105 53476834943699331722205079)
      ·
        refine ⟨80215252415548997583307619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53476834943699331722205079 80215252415548997583307619)
        ·
          refine ⟨120322878623323496374961429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80215252415548997583307619 120322878623323496374961429)
          ·
            refine ⟨5640134935468288892576317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120322878623323496374961429 5640134935468288892576317)
            ·
              refine ⟨2115050600800608334716119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640134935468288892576317 2115050600800608334716119)
              ·
                refine ⟨3172575901200912502074179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115050600800608334716119 3172575901200912502074179)
                ·
                  refine ⟨4758863851801368753111269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172575901200912502074179 4758863851801368753111269)
                  ·
                    refine ⟨892286972212756641208363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758863851801368753111269 892286972212756641208363)
                    ·
                      rfl

theorem cell22_2606584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_2606584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606584 prefixEnd_2606584 := by exact prefixLift 2606584
  have htrace : WordTrace (prefixWord ++ tailWord_2606584) baseStart_2606584 baseEnd_2606584 := by
    simpa [prefixWord, tailWord_2606584, baseEnd_2606584] using wordTrace_append hprefix tailTrace_2606584
  have hstable : (prefixWord ++ tailWord_2606584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606584).length < 2 ^ (prefixWord ++ tailWord_2606584).sum := by decide
  have hdescent : baseEnd_2606584 < baseStart_2606584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606595 : List Nat := [1, 1, 1, 3, 2, 1, 2, 3, 4, 4]
def baseStart_2606595 : Nat := 118140960795 + 2606595 * 2 ^ 59
def prefixEnd_2606595 : Nat := 4983230072969 + 3 ^ 40 * 2606595 * 2
def baseEnd_2606595 : Nat := 892290737737556279183329

theorem tailTrace_2606595 : CollatzResearch.WordTrace tailWord_2606595 prefixEnd_2606595 892290737737556279183329 := by
  unfold tailWord_2606595
  simp only [CollatzResearch.WordTrace]
  refine ⟨95070329991758960829237239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63380219994505973886158159 95070329991758960829237239)
  ·
    refine ⟨142605494987638441243855859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95070329991758960829237239 142605494987638441243855859)
    ·
      refine ⟨213908242481457661865783789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142605494987638441243855859 213908242481457661865783789)
      ·
        refine ⟨80215590930546623199668921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213908242481457661865783789 80215590930546623199668921)
        ·
          refine ⟨60161693197909967399751691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80215590930546623199668921 60161693197909967399751691)
          ·
            refine ⟨90242539796864951099627537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60161693197909967399751691 90242539796864951099627537)
            ·
              refine ⟨67681904847648713324720653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90242539796864951099627537 67681904847648713324720653)
              ·
                refine ⟨25380714317868267496770245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67681904847648713324720653 25380714317868267496770245)
                ·
                  refine ⟨4758883934600300155644421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25380714317868267496770245 4758883934600300155644421)
                  ·
                    refine ⟨892290737737556279183329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4758883934600300155644421 892290737737556279183329)
                    ·
                      rfl

theorem cell22_2606595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_2606595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606595 prefixEnd_2606595 := by exact prefixLift 2606595
  have htrace : WordTrace (prefixWord ++ tailWord_2606595) baseStart_2606595 baseEnd_2606595 := by
    simpa [prefixWord, tailWord_2606595, baseEnd_2606595] using wordTrace_append hprefix tailTrace_2606595
  have hstable : (prefixWord ++ tailWord_2606595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606595).length < 2 ^ (prefixWord ++ tailWord_2606595).sum := by decide
  have hdescent : baseEnd_2606595 < baseStart_2606595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606599 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 4]
def baseStart_2606599 : Nat := 118140960795 + 2606599 * 2 ^ 59
def prefixEnd_2606599 : Nat := 4983230072969 + 3 ^ 40 * 2606599 * 2
def baseEnd_2606599 : Nat := 297430702339767200694439

theorem tailTrace_2606599 : CollatzResearch.WordTrace tailWord_2606599 prefixEnd_2606599 297430702339767200694439 := by
  unfold tailWord_2606599
  simp only [CollatzResearch.WordTrace]
  refine ⟨95070475883744469512382851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63380317255829646341588567 95070475883744469512382851)
  ·
    refine ⟨142605713825616704268574277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95070475883744469512382851 142605713825616704268574277)
    ·
      refine ⟨26738571342303132050357677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142605713825616704268574277 26738571342303132050357677)
      ·
        refine ⟨10026964253363674518884129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26738571342303132050357677 10026964253363674518884129)
        ·
          refine ⟨7520223190022755889163097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10026964253363674518884129 7520223190022755889163097)
          ·
            refine ⟨5640167392517066916872323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520223190022755889163097 5640167392517066916872323)
            ·
              refine ⟨8460251088775600375308485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640167392517066916872323 8460251088775600375308485)
              ·
                refine ⟨1586297079145425070370341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8460251088775600375308485 1586297079145425070370341)
                ·
                  refine ⟨297430702339767200694439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1586297079145425070370341 297430702339767200694439)
                  ·
                    rfl

theorem cell22_2606599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 4].length) (baseStart_2606599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606599 prefixEnd_2606599 := by exact prefixLift 2606599
  have htrace : WordTrace (prefixWord ++ tailWord_2606599) baseStart_2606599 baseEnd_2606599 := by
    simpa [prefixWord, tailWord_2606599, baseEnd_2606599] using wordTrace_append hprefix tailTrace_2606599
  have hstable : (prefixWord ++ tailWord_2606599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606599).length < 2 ^ (prefixWord ++ tailWord_2606599).sum := by decide
  have hdescent : baseEnd_2606599 < baseStart_2606599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606642 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2606642 : Nat := 118140960795 + 2606642 * 2 ^ 59
def prefixEnd_2606642 : Nat := 4983230072969 + 3 ^ 40 * 2606642 * 2
def baseEnd_2606642 : Nat := 892306826798063823258185

theorem tailTrace_2606642 : CollatzResearch.WordTrace tailWord_2606642 prefixEnd_2606642 892306826798063823258185 := by
  unfold tailWord_2606642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768011055647171964049545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63381362815059125237465453 23768011055647171964049545)
  ·
    refine ⟨17826008291735378973037159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23768011055647171964049545 17826008291735378973037159)
    ·
      refine ⟨26739012437603068459555739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17826008291735378973037159 26739012437603068459555739)
      ·
        refine ⟨40108518656404602689333609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26739012437603068459555739 40108518656404602689333609)
        ·
          refine ⟨30081388992303452017000207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40108518656404602689333609 30081388992303452017000207)
          ·
            refine ⟨45122083488455178025500311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30081388992303452017000207 45122083488455178025500311)
            ·
              refine ⟨67683125232682767038250467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45122083488455178025500311 67683125232682767038250467)
              ·
                refine ⟨101524687849024150557375701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67683125232682767038250467 101524687849024150557375701)
                ·
                  refine ⟨2379484871461503528688493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101524687849024150557375701 2379484871461503528688493)
                  ·
                    refine ⟨892306826798063823258185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379484871461503528688493 892306826798063823258185)
                    ·
                      rfl

theorem cell22_2606642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2606642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606642 prefixEnd_2606642 := by exact prefixLift 2606642
  have htrace : WordTrace (prefixWord ++ tailWord_2606642) baseStart_2606642 baseEnd_2606642 := by
    simpa [prefixWord, tailWord_2606642, baseEnd_2606642] using wordTrace_append hprefix tailTrace_2606642
  have hstable : (prefixWord ++ tailWord_2606642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606642).length < 2 ^ (prefixWord ++ tailWord_2606642).sum := by decide
  have hdescent : baseEnd_2606642 < baseStart_2606642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606693 : List Nat := [1, 3, 1, 3, 3, 3, 1, 3, 1, 3]
def baseStart_2606693 : Nat := 118140960795 + 2606693 * 2 ^ 59
def prefixEnd_2606693 : Nat := 4983230072969 + 3 ^ 40 * 2606693 * 2
def baseEnd_2606693 : Nat := 892324285140316690233029

theorem tailTrace_2606693 : CollatzResearch.WordTrace tailWord_2606693 prefixEnd_2606693 892324285140316690233029 := by
  unfold tailWord_2606693
  simp only [CollatzResearch.WordTrace]
  refine ⟨95073904345403923566304733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63382602896935949044203155 95073904345403923566304733)
  ·
    refine ⟨35652714129526471337364275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95073904345403923566304733 35652714129526471337364275)
    ·
      refine ⟨53479071194289707006046413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35652714129526471337364275 53479071194289707006046413)
      ·
        refine ⟨20054651697858640127267405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53479071194289707006046413 20054651697858640127267405)
        ·
          refine ⟨7520494386696990047725277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20054651697858640127267405 7520494386696990047725277)
          ·
            refine ⟨2820185395011371267896979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7520494386696990047725277 2820185395011371267896979)
            ·
              refine ⟨4230278092517056901845469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820185395011371267896979 4230278092517056901845469)
              ·
                refine ⟨1586354284693896338192051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4230278092517056901845469 1586354284693896338192051)
                ·
                  refine ⟨2379531427040844507288077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586354284693896338192051 2379531427040844507288077)
                  ·
                    refine ⟨892324285140316690233029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379531427040844507288077 892324285140316690233029)
                    ·
                      rfl

theorem cell22_2606693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_2606693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606693 prefixEnd_2606693 := by exact prefixLift 2606693
  have htrace : WordTrace (prefixWord ++ tailWord_2606693) baseStart_2606693 baseEnd_2606693 := by
    simpa [prefixWord, tailWord_2606693, baseEnd_2606693] using wordTrace_append hprefix tailTrace_2606693
  have hstable : (prefixWord ++ tailWord_2606693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606693).length < 2 ^ (prefixWord ++ tailWord_2606693).sum := by decide
  have hdescent : baseEnd_2606693 < baseStart_2606693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606710 : List Nat := [5, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2606710 : Nat := 118140960795 + 2606710 * 2 ^ 59
def prefixEnd_2606710 : Nat := 4983230072969 + 3 ^ 40 * 2606710 * 2
def baseEnd_2606710 : Nat := 892330104587734312557977

theorem tailTrace_2606710 : CollatzResearch.WordTrace tailWord_2606710 prefixEnd_2606710 892330104587734312557977 := by
  unfold tailWord_2606710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5942157774146395966854599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63383016257561556979782389 5942157774146395966854599)
  ·
    refine ⟨8913236661219593950281899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5942157774146395966854599 8913236661219593950281899)
    ·
      refine ⟨13369854991829390925422849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8913236661219593950281899 13369854991829390925422849)
      ·
        refine ⟨10027391243872043194067137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13369854991829390925422849 10027391243872043194067137)
        ·
          refine ⟨7520543432904032395550353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10027391243872043194067137 7520543432904032395550353)
          ·
            refine ⟨5640407574678024296662765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520543432904032395550353 5640407574678024296662765)
            ·
              refine ⟨2115152840504259111248537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640407574678024296662765 2115152840504259111248537)
              ·
                refine ⟨1586364630378194333436403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115152840504259111248537 1586364630378194333436403)
                ·
                  refine ⟨2379546945567291500154605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586364630378194333436403 2379546945567291500154605)
                  ·
                    refine ⟨892330104587734312557977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379546945567291500154605 892330104587734312557977)
                    ·
                      rfl

theorem cell22_2606710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2606710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606710 prefixEnd_2606710 := by exact prefixLift 2606710
  have htrace : WordTrace (prefixWord ++ tailWord_2606710) baseStart_2606710 baseEnd_2606710 := by
    simpa [prefixWord, tailWord_2606710, baseEnd_2606710] using wordTrace_append hprefix tailTrace_2606710
  have hstable : (prefixWord ++ tailWord_2606710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606710).length < 2 ^ (prefixWord ++ tailWord_2606710).sum := by decide
  have hdescent : baseEnd_2606710 < baseStart_2606710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606732 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_2606732 : Nat := 118140960795 + 2606732 * 2 ^ 59
def prefixEnd_2606732 : Nat := 4983230072969 + 3 ^ 40 * 2606732 * 2
def baseEnd_2606732 : Nat := 892337635637333588507909

theorem tailTrace_2606732 : CollatzResearch.WordTrace tailWord_2606732 prefixEnd_2606732 892337635637333588507909 := by
  unfold tailWord_2606732
  simp only [CollatzResearch.WordTrace]
  refine ⟨47537663396131316613487225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63383551194841755484649633 47537663396131316613487225)
  ·
    refine ⟨35653247547098487460115419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47537663396131316613487225 35653247547098487460115419)
    ·
      refine ⟨53479871320647731190173129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35653247547098487460115419 53479871320647731190173129)
      ·
        refine ⟨40109903490485798392629847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53479871320647731190173129 40109903490485798392629847)
        ·
          refine ⟨60164855235728697588944771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40109903490485798392629847 60164855235728697588944771)
          ·
            refine ⟨90247282853593046383417157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60164855235728697588944771 90247282853593046383417157)
            ·
              refine ⟨16921365535048696196890717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90247282853593046383417157 16921365535048696196890717)
              ·
                refine ⟨6345512075643261073834019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16921365535048696196890717 6345512075643261073834019)
                ·
                  refine ⟨9518268113464891610751029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6345512075643261073834019 9518268113464891610751029)
                  ·
                    refine ⟨892337635637333588507909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9518268113464891610751029 892337635637333588507909)
                    ·
                      rfl

theorem cell22_2606732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_2606732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606732 prefixEnd_2606732 := by exact prefixLift 2606732
  have htrace : WordTrace (prefixWord ++ tailWord_2606732) baseStart_2606732 baseEnd_2606732 := by
    simpa [prefixWord, tailWord_2606732, baseEnd_2606732] using wordTrace_append hprefix tailTrace_2606732
  have hstable : (prefixWord ++ tailWord_2606732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606732).length < 2 ^ (prefixWord ++ tailWord_2606732).sum := by decide
  have hdescent : baseEnd_2606732 < baseStart_2606732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606762 : List Nat := [3, 1, 5, 13]
def baseStart_2606762 : Nat := 118140960795 + 2606762 * 2 ^ 59
def prefixEnd_2606762 : Nat := 4983230072969 + 3 ^ 40 * 2606762 * 2
def baseEnd_2606762 : Nat := 1224071200617864897473

theorem tailTrace_2606762 : CollatzResearch.WordTrace tailWord_2606762 prefixEnd_2606762 1224071200617864897473 := by
  unfold tailWord_2606762
  simp only [CollatzResearch.WordTrace]
  refine ⟨23769105245538487087641635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63384280654769298900377693 23769105245538487087641635)
  ·
    refine ⟨35653657868307730631462453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23769105245538487087641635 35653657868307730631462453)
    ·
      refine ⟨3342530425153849746699605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35653657868307730631462453 3342530425153849746699605)
      ·
        refine ⟨1224071200617864897473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3342530425153849746699605 1224071200617864897473)
        ·
          rfl

theorem cell22_2606762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 13].length) (baseStart_2606762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606762 prefixEnd_2606762 := by exact prefixLift 2606762
  have htrace : WordTrace (prefixWord ++ tailWord_2606762) baseStart_2606762 baseEnd_2606762 := by
    simpa [prefixWord, tailWord_2606762, baseEnd_2606762] using wordTrace_append hprefix tailTrace_2606762
  have hstable : (prefixWord ++ tailWord_2606762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606762).length < 2 ^ (prefixWord ++ tailWord_2606762).sum := by decide
  have hdescent : baseEnd_2606762 < baseStart_2606762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606792 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2606792 : Nat := 118140960795 + 2606792 * 2 ^ 59
def prefixEnd_2606792 : Nat := 4983230072969 + 3 ^ 40 * 2606792 * 2
def baseEnd_2606792 : Nat := 892358174863513432007725

theorem tailTrace_2606792 : CollatzResearch.WordTrace tailWord_2606792 prefixEnd_2606792 892358174863513432007725 := by
  unfold tailWord_2606792
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538757586022631737079315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63385010114696842316105753 47538757586022631737079315)
  ·
    refine ⟨71308136379033947605618973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47538757586022631737079315 71308136379033947605618973)
    ·
      refine ⟨26740551142137730352107115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71308136379033947605618973 26740551142137730352107115)
      ·
        refine ⟨40110826713206595528160673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26740551142137730352107115 40110826713206595528160673)
        ·
          refine ⟨30083120034904946646120505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40110826713206595528160673 30083120034904946646120505)
          ·
            refine ⟨22562340026178709984590379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30083120034904946646120505 22562340026178709984590379)
            ·
              refine ⟨33843510039268064976885569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22562340026178709984590379 33843510039268064976885569)
              ·
                refine ⟨25382632529451048732664177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33843510039268064976885569 25382632529451048732664177)
                ·
                  refine ⟨19036974397088286549498133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25382632529451048732664177 19036974397088286549498133)
                  ·
                    refine ⟨892358174863513432007725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19036974397088286549498133 892358174863513432007725)
                    ·
                      rfl

theorem cell22_2606792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2606792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606792 prefixEnd_2606792 := by exact prefixLift 2606792
  have htrace : WordTrace (prefixWord ++ tailWord_2606792) baseStart_2606792 baseEnd_2606792 := by
    simpa [prefixWord, tailWord_2606792, baseEnd_2606792] using wordTrace_append hprefix tailTrace_2606792
  have hstable : (prefixWord ++ tailWord_2606792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606792).length < 2 ^ (prefixWord ++ tailWord_2606792).sum := by decide
  have hdescent : baseEnd_2606792 < baseStart_2606792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606796 : List Nat := [2, 2, 1, 5, 2, 1, 3, 6]
def baseStart_2606796 : Nat := 118140960795 + 2606796 * 2 ^ 59
def prefixEnd_2606796 : Nat := 4983230072969 + 3 ^ 40 * 2606796 * 2
def baseEnd_2606796 : Nat := 99151060460584306100857

theorem tailTrace_2606796 : CollatzResearch.WordTrace tailWord_2606796 prefixEnd_2606796 99151060460584306100857 := by
  unfold tailWord_2606796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538830532015386078652121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63385107376020514771536161 47538830532015386078652121)
  ·
    refine ⟨35654122899011539558989091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47538830532015386078652121 35654122899011539558989091)
    ·
      refine ⟨53481184348517309338483637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35654122899011539558989091 53481184348517309338483637)
      ·
        refine ⟨5013861032673497750482841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53481184348517309338483637 5013861032673497750482841)
        ·
          refine ⟨3760395774505123312862131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5013861032673497750482841 3760395774505123312862131)
          ·
            refine ⟨5640593661757684969293197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760395774505123312862131 5640593661757684969293197)
            ·
              refine ⟨2115222623159131863484949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640593661757684969293197 2115222623159131863484949)
              ·
                refine ⟨99151060460584306100857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2115222623159131863484949 99151060460584306100857)
                ·
                  rfl

theorem cell22_2606796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_2606796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606796 prefixEnd_2606796 := by exact prefixLift 2606796
  have htrace : WordTrace (prefixWord ++ tailWord_2606796) baseStart_2606796 baseEnd_2606796 := by
    simpa [prefixWord, tailWord_2606796, baseEnd_2606796] using wordTrace_append hprefix tailTrace_2606796
  have hstable : (prefixWord ++ tailWord_2606796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606796).length < 2 ^ (prefixWord ++ tailWord_2606796).sum := by decide
  have hdescent : baseEnd_2606796 < baseStart_2606796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606807 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 7]
def baseStart_2606807 : Nat := 118140960795 + 2606807 * 2 ^ 59
def prefixEnd_2606807 : Nat := 4983230072969 + 3 ^ 40 * 2606807 * 2
def baseEnd_2606807 : Nat := 297454436556686130960893

theorem tailTrace_2606807 : CollatzResearch.WordTrace tailWord_2606807 prefixEnd_2606807 297454436556686130960893 := by
  unfold tailWord_2606807
  simp only [CollatzResearch.WordTrace]
  refine ⟨95078062266990921035954675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63385374844660614023969783 95078062266990921035954675)
  ·
    refine ⟨142617093400486381553932013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95078062266990921035954675 142617093400486381553932013)
    ·
      refine ⟨53481410025182393082724505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142617093400486381553932013 53481410025182393082724505)
      ·
        refine ⟨40111057518886794812043379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53481410025182393082724505 40111057518886794812043379)
        ·
          refine ⟨60166586278330192218065069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40111057518886794812043379 60166586278330192218065069)
          ·
            refine ⟨22562469854373822081774401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60166586278330192218065069 22562469854373822081774401)
            ·
              refine ⟨16921852390780366561330801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22562469854373822081774401 16921852390780366561330801)
              ·
                refine ⟨12691389293085274920998101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16921852390780366561330801 12691389293085274920998101)
                ·
                  refine ⟨297454436556686130960893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12691389293085274920998101 297454436556686130960893)
                  ·
                    rfl

theorem cell22_2606807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_2606807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606807 prefixEnd_2606807 := by exact prefixLift 2606807
  have htrace : WordTrace (prefixWord ++ tailWord_2606807) baseStart_2606807 baseEnd_2606807 := by
    simpa [prefixWord, tailWord_2606807, baseEnd_2606807] using wordTrace_append hprefix tailTrace_2606807
  have hstable : (prefixWord ++ tailWord_2606807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606807).length < 2 ^ (prefixWord ++ tailWord_2606807).sum := by decide
  have hdescent : baseEnd_2606807 < baseStart_2606807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606824 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_2606824 : Nat := 118140960795 + 2606824 * 2 ^ 59
def prefixEnd_2606824 : Nat := 4983230072969 + 3 ^ 40 * 2606824 * 2
def baseEnd_2606824 : Nat := 297456376372492005069209

theorem tailTrace_2606824 : CollatzResearch.WordTrace tailWord_2606824 prefixEnd_2606824 297456376372492005069209 := by
  unfold tailWord_2606824
  simp only [CollatzResearch.WordTrace]
  refine ⟨47539341153964666469661763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63385788205286221959549017 47539341153964666469661763)
  ·
    refine ⟨71309011730946999704492645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47539341153964666469661763 71309011730946999704492645)
    ·
      refine ⟨13370439699552562444592371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71309011730946999704492645 13370439699552562444592371)
      ·
        refine ⟨20055659549328843666888557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13370439699552562444592371 20055659549328843666888557)
        ·
          refine ⟨7520872330998316375083209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20055659549328843666888557 7520872330998316375083209)
          ·
            refine ⟨5640654248248737281312407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520872330998316375083209 5640654248248737281312407)
            ·
              refine ⟨8460981372373105921968611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5640654248248737281312407 8460981372373105921968611)
              ·
                refine ⟨12691472058559658882952917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8460981372373105921968611 12691472058559658882952917)
                ·
                  refine ⟨297456376372492005069209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12691472058559658882952917 297456376372492005069209)
                  ·
                    rfl

theorem cell22_2606824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_2606824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606824 prefixEnd_2606824 := by exact prefixLift 2606824
  have htrace : WordTrace (prefixWord ++ tailWord_2606824) baseStart_2606824 baseEnd_2606824 := by
    simpa [prefixWord, tailWord_2606824, baseEnd_2606824] using wordTrace_append hprefix tailTrace_2606824
  have hstable : (prefixWord ++ tailWord_2606824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606824).length < 2 ^ (prefixWord ++ tailWord_2606824).sum := by decide
  have hdescent : baseEnd_2606824 < baseStart_2606824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606871 : List Nat := [1, 1, 3, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2606871 : Nat := 118140960795 + 2606871 * 2 ^ 59
def prefixEnd_2606871 : Nat := 4983230072969 + 3 ^ 40 * 2606871 * 2
def baseEnd_2606871 : Nat := 892385218177983559282483

theorem tailTrace_2606871 : CollatzResearch.WordTrace tailWord_2606871 prefixEnd_2606871 892385218177983559282483 := by
  unfold tailWord_2606871
  simp only [CollatzResearch.WordTrace]
  refine ⟨95080396538759059966284467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63386931025839373310856311 95080396538759059966284467)
  ·
    refine ⟨142620594808138589949426701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95080396538759059966284467 142620594808138589949426701)
    ·
      refine ⟨53482723053051971231035013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142620594808138589949426701 53482723053051971231035013)
      ·
        refine ⟨10028010572447244605819065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53482723053051971231035013 10028010572447244605819065)
        ·
          refine ⟨7521007929335433454364299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10028010572447244605819065 7521007929335433454364299)
          ·
            refine ⟨11281511894003150181546449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7521007929335433454364299 11281511894003150181546449)
            ·
              refine ⟨8461133920502362636159837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11281511894003150181546449 8461133920502362636159837)
              ·
                refine ⟨3172925220188385988559939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8461133920502362636159837 3172925220188385988559939)
                ·
                  refine ⟨4759387830282578982839909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172925220188385988559939 4759387830282578982839909)
                  ·
                    refine ⟨892385218177983559282483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759387830282578982839909 892385218177983559282483)
                    ·
                      rfl

theorem cell22_2606871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2606871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606871 prefixEnd_2606871 := by exact prefixLift 2606871
  have htrace : WordTrace (prefixWord ++ tailWord_2606871) baseStart_2606871 baseEnd_2606871 := by
    simpa [prefixWord, tailWord_2606871, baseEnd_2606871] using wordTrace_append hprefix tailTrace_2606871
  have hstable : (prefixWord ++ tailWord_2606871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606871).length < 2 ^ (prefixWord ++ tailWord_2606871).sum := by decide
  have hdescent : baseEnd_2606871 < baseStart_2606871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606905 : List Nat := [1, 2, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_2606905 : Nat := 118140960795 + 2606905 * 2 ^ 59
def prefixEnd_2606905 : Nat := 4983230072969 + 3 ^ 40 * 2606905 * 2
def baseEnd_2606905 : Nat := 892396857072818803932379

theorem tailTrace_2606905 : CollatzResearch.WordTrace tailWord_2606905 prefixEnd_2606905 892396857072818803932379 := by
  unfold tailWord_2606905
  simp only [CollatzResearch.WordTrace]
  refine ⟨95081636620635883773022169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63387757747090589182014779 95081636620635883773022169)
  ·
    refine ⟨71311227465476912829766627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95081636620635883773022169 71311227465476912829766627)
    ·
      refine ⟨106966841198215369244649941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71311227465476912829766627 106966841198215369244649941)
      ·
        refine ⟨2507035340583172716671483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 106966841198215369244649941 2507035340583172716671483)
        ·
          refine ⟨3760553010874759075007225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507035340583172716671483 3760553010874759075007225)
          ·
            refine ⟨2820414758156069306255419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3760553010874759075007225 2820414758156069306255419)
            ·
              refine ⟨4230622137234103959383129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820414758156069306255419 4230622137234103959383129)
              ·
                refine ⟨3172966602925577969537347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230622137234103959383129 3172966602925577969537347)
                ·
                  refine ⟨4759449904388366954306021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172966602925577969537347 4759449904388366954306021)
                  ·
                    refine ⟨892396857072818803932379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759449904388366954306021 892396857072818803932379)
                    ·
                      rfl

theorem cell22_2606905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_2606905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606905 prefixEnd_2606905 := by exact prefixLift 2606905
  have htrace : WordTrace (prefixWord ++ tailWord_2606905) baseStart_2606905 baseEnd_2606905 := by
    simpa [prefixWord, tailWord_2606905, baseEnd_2606905] using wordTrace_append hprefix tailTrace_2606905
  have hstable : (prefixWord ++ tailWord_2606905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606905).length < 2 ^ (prefixWord ++ tailWord_2606905).sum := by decide
  have hdescent : baseEnd_2606905 < baseStart_2606905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606918 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2606918 : Nat := 118140960795 + 2606918 * 2 ^ 59
def prefixEnd_2606918 : Nat := 4983230072969 + 3 ^ 40 * 2606918 * 2
def baseEnd_2606918 : Nat := 892401307238491103357339

theorem tailTrace_2606918 : CollatzResearch.WordTrace tailWord_2606918 prefixEnd_2606918 892401307238491103357339 := by
  unfold tailWord_2606918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971315961549649593538919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63388073846392524662163605 2971315961549649593538919)
  ·
    refine ⟨4456973942324474390308379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2971315961549649593538919 4456973942324474390308379)
    ·
      refine ⟨6685460913486711585462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456973942324474390308379 6685460913486711585462569)
      ·
        refine ⟨5014095685115033689096927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6685460913486711585462569 5014095685115033689096927)
        ·
          refine ⟨7521143527672550533645391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014095685115033689096927 7521143527672550533645391)
          ·
            refine ⟨11281715291508825800468087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7521143527672550533645391 11281715291508825800468087)
            ·
              refine ⟨16922572937263238700702131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11281715291508825800468087 16922572937263238700702131)
              ·
                refine ⟨25383859405894858051053197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16922572937263238700702131 25383859405894858051053197)
                ·
                  refine ⟨9518947277210571769144949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25383859405894858051053197 9518947277210571769144949)
                  ·
                    refine ⟨892401307238491103357339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9518947277210571769144949 892401307238491103357339)
                    ·
                      rfl

theorem cell22_2606918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2606918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606918 prefixEnd_2606918 := by exact prefixLift 2606918
  have htrace : WordTrace (prefixWord ++ tailWord_2606918) baseStart_2606918 baseEnd_2606918 := by
    simpa [prefixWord, tailWord_2606918, baseEnd_2606918] using wordTrace_append hprefix tailTrace_2606918
  have hstable : (prefixWord ++ tailWord_2606918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606918).length < 2 ^ (prefixWord ++ tailWord_2606918).sum := by decide
  have hdescent : baseEnd_2606918 < baseStart_2606918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606944 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_2606944 : Nat := 118140960795 + 2606944 * 2 ^ 59
def prefixEnd_2606944 : Nat := 4983230072969 + 3 ^ 40 * 2606944 * 2
def baseEnd_2606944 : Nat := 892410207569835702207259

theorem tailTrace_2606944 : CollatzResearch.WordTrace tailWord_2606944 prefixEnd_2606944 892410207569835702207259 := by
  unfold tailWord_2606944
  simp only [CollatzResearch.WordTrace]
  refine ⟨47541529533747296716845943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63388706044996395622461257 47541529533747296716845943)
  ·
    refine ⟨71312294300620945075268915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47541529533747296716845943 71312294300620945075268915)
    ·
      refine ⟨106968441450931417612903373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71312294300620945075268915 106968441450931417612903373)
      ·
        refine ⟨40113165544099281604838765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106968441450931417612903373 40113165544099281604838765)
        ·
          refine ⟨15042437079037230601814537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40113165544099281604838765 15042437079037230601814537)
          ·
            refine ⟨11281827809277922951360903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15042437079037230601814537 11281827809277922951360903)
            ·
              refine ⟨16922741713916884427041355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11281827809277922951360903 16922741713916884427041355)
              ·
                refine ⟨25384112570875326640562033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16922741713916884427041355 25384112570875326640562033)
                ·
                  refine ⟨19038084428156494980421525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25384112570875326640562033 19038084428156494980421525)
                  ·
                    refine ⟨892410207569835702207259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19038084428156494980421525 892410207569835702207259)
                    ·
                      rfl

theorem cell22_2606944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_2606944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606944 prefixEnd_2606944 := by exact prefixLift 2606944
  have htrace : WordTrace (prefixWord ++ tailWord_2606944) baseStart_2606944 baseEnd_2606944 := by
    simpa [prefixWord, tailWord_2606944, baseEnd_2606944] using wordTrace_append hprefix tailTrace_2606944
  have hstable : (prefixWord ++ tailWord_2606944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606944).length < 2 ^ (prefixWord ++ tailWord_2606944).sum := by decide
  have hdescent : baseEnd_2606944 < baseStart_2606944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2606948 : List Nat := [2, 3, 1, 1, 6, 1, 1, 7]
def baseStart_2606948 : Nat := 118140960795 + 2606948 * 2 ^ 59
def prefixEnd_2606948 : Nat := 4983230072969 + 3 ^ 40 * 2606948 * 2
def baseEnd_2606948 : Nat := 99156841872397891678583

theorem tailTrace_2606948 : CollatzResearch.WordTrace tailWord_2606948 prefixEnd_2606948 99156841872397891678583 := by
  unfold tailWord_2606948
  simp only [CollatzResearch.WordTrace]
  refine ⟨47541602479740051058418749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63388803306320068077891665 47541602479740051058418749)
  ·
    refine ⟨17828100929902519146907031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47541602479740051058418749 17828100929902519146907031)
    ·
      refine ⟨26742151394853778720360547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17828100929902519146907031 26742151394853778720360547)
      ·
        refine ⟨40113227092280668080540821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26742151394853778720360547 40113227092280668080540821)
        ·
          refine ⟨1880307519950656316275351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40113227092280668080540821 1880307519950656316275351)
          ·
            refine ⟨2820461279925984474413027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880307519950656316275351 2820461279925984474413027)
            ·
              refine ⟨4230691919888976711619541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820461279925984474413027 4230691919888976711619541)
              ·
                refine ⟨99156841872397891678583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4230691919888976711619541 99156841872397891678583)
                ·
                  rfl

theorem cell22_2606948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_2606948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2606948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2606948 prefixEnd_2606948 := by exact prefixLift 2606948
  have htrace : WordTrace (prefixWord ++ tailWord_2606948) baseStart_2606948 baseEnd_2606948 := by
    simpa [prefixWord, tailWord_2606948, baseEnd_2606948] using wordTrace_append hprefix tailTrace_2606948
  have hstable : (prefixWord ++ tailWord_2606948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2606948).length < 2 ^ (prefixWord ++ tailWord_2606948).sum := by decide
  have hdescent : baseEnd_2606948 < baseStart_2606948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2606948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607010 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_2607010 : Nat := 118140960795 + 2607010 * 2 ^ 59
def prefixEnd_2607010 : Nat := 4983230072969 + 3 ^ 40 * 2607010 * 2
def baseEnd_2607010 : Nat := 297477600239544510019019

theorem tailTrace_2607010 : CollatzResearch.WordTrace tailWord_2607010 prefixEnd_2607010 297477600239544510019019 := by
  unfold tailWord_2607010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771366571313871676398621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63390310856836991137062989 23771366571313871676398621)
  ·
    refine ⟨8914262464242701878649483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23771366571313871676398621 8914262464242701878649483)
    ·
      refine ⟨13371393696364052817974225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914262464242701878649483 13371393696364052817974225)
      ·
        refine ⟨10028545272273039613480669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13371393696364052817974225 10028545272273039613480669)
        ·
          refine ⟨3760704477102389855055251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10028545272273039613480669 3760704477102389855055251)
          ·
            refine ⟨5641056715653584782582877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760704477102389855055251 5641056715653584782582877)
            ·
              refine ⟨2115396268370094293468579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5641056715653584782582877 2115396268370094293468579)
              ·
                refine ⟨3173094402555141440202869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115396268370094293468579 3173094402555141440202869)
                ·
                  refine ⟨297477600239544510019019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3173094402555141440202869 297477600239544510019019)
                  ·
                    rfl

theorem cell22_2607010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_2607010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607010 prefixEnd_2607010 := by exact prefixLift 2607010
  have htrace : WordTrace (prefixWord ++ tailWord_2607010) baseStart_2607010 baseEnd_2607010 := by
    simpa [prefixWord, tailWord_2607010, baseEnd_2607010] using wordTrace_append hprefix tailTrace_2607010
  have hstable : (prefixWord ++ tailWord_2607010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607010).length < 2 ^ (prefixWord ++ tailWord_2607010).sum := by decide
  have hdescent : baseEnd_2607010 < baseStart_2607010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607051 : List Nat := [1, 1, 1, 1, 3, 4, 3, 2, 2, 4]
def baseStart_2607051 : Nat := 118140960795 + 2607051 * 2 ^ 59
def prefixEnd_2607051 : Nat := 4983230072969 + 3 ^ 40 * 2607051 * 2
def baseEnd_2607051 : Nat := 892446835856523089781931

theorem tailTrace_2607051 : CollatzResearch.WordTrace tailWord_2607051 prefixEnd_2607051 892446835856523089781931 := by
  unfold tailWord_2607051
  simp only [CollatzResearch.WordTrace]
  refine ⟨95086961678106950707837007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63391307785404633805224671 95086961678106950707837007)
  ·
    refine ⟨142630442517160426061755511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95086961678106950707837007 142630442517160426061755511)
    ·
      refine ⟨213945663775740639092633267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142630442517160426061755511 213945663775740639092633267)
      ·
        refine ⟨320918495663610958638949901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213945663775740639092633267 320918495663610958638949901)
        ·
          refine ⟨120344435873854109489606213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320918495663610958638949901 120344435873854109489606213)
          ·
            refine ⟨22564581726347645529301165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120344435873854109489606213 22564581726347645529301165)
            ·
              refine ⟨8461718147380367073487937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22564581726347645529301165 8461718147380367073487937)
              ·
                refine ⟨6346288610535275305115953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8461718147380367073487937 6346288610535275305115953)
                ·
                  refine ⟨4759716457901456478836965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346288610535275305115953 4759716457901456478836965)
                  ·
                    refine ⟨892446835856523089781931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759716457901456478836965 892446835856523089781931)
                    ·
                      rfl

theorem cell22_2607051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_2607051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607051 prefixEnd_2607051 := by exact prefixLift 2607051
  have htrace : WordTrace (prefixWord ++ tailWord_2607051) baseStart_2607051 baseEnd_2607051 := by
    simpa [prefixWord, tailWord_2607051, baseEnd_2607051] using wordTrace_append hprefix tailTrace_2607051
  have hstable : (prefixWord ++ tailWord_2607051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607051).length < 2 ^ (prefixWord ++ tailWord_2607051).sum := by decide
  have hdescent : baseEnd_2607051 < baseStart_2607051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607074 : List Nat := [3, 3, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2607074 : Nat := 118140960795 + 2607074 * 2 ^ 59
def prefixEnd_2607074 : Nat := 4983230072969 + 3 ^ 40 * 2607074 * 2
def baseEnd_2607074 : Nat := 892454709226558696456861

theorem tailTrace_2607074 : CollatzResearch.WordTrace tailWord_2607074 prefixEnd_2607074 892454709226558696456861 := by
  unfold tailWord_2607074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23771950139255906408981069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63391867038015750423949517 23771950139255906408981069)
  ·
    refine ⟨8914481302220964903367901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23771950139255906408981069 8914481302220964903367901)
    ·
      refine ⟨3342930488332861838762963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8914481302220964903367901 3342930488332861838762963)
      ·
        refine ⟨5014395732499292758144445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342930488332861838762963 5014395732499292758144445)
        ·
          refine ⟨1880398399687234784304167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5014395732499292758144445 1880398399687234784304167)
          ·
            refine ⟨2820597599530852176456251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880398399687234784304167 2820597599530852176456251)
            ·
              refine ⟨4230896399296278264684377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2820597599530852176456251 4230896399296278264684377)
              ·
                refine ⟨3173172299472208698513283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230896399296278264684377 3173172299472208698513283)
                ·
                  refine ⟨4759758449208313047769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3173172299472208698513283 4759758449208313047769925)
                  ·
                    refine ⟨892454709226558696456861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4759758449208313047769925 892454709226558696456861)
                    ·
                      rfl

theorem cell22_2607074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2607074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607074 prefixEnd_2607074 := by exact prefixLift 2607074
  have htrace : WordTrace (prefixWord ++ tailWord_2607074) baseStart_2607074 baseEnd_2607074 := by
    simpa [prefixWord, tailWord_2607074, baseEnd_2607074] using wordTrace_append hprefix tailTrace_2607074
  have hstable : (prefixWord ++ tailWord_2607074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607074).length < 2 ^ (prefixWord ++ tailWord_2607074).sum := by decide
  have hdescent : baseEnd_2607074 < baseStart_2607074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607115 : List Nat := [1, 1, 1, 1, 6, 1, 3, 4, 1, 3]
def baseStart_2607115 : Nat := 118140960795 + 2607115 * 2 ^ 59
def prefixEnd_2607115 : Nat := 4983230072969 + 3 ^ 40 * 2607115 * 2
def baseEnd_2607115 : Nat := 892468744364448256181735

theorem tailTrace_2607115 : CollatzResearch.WordTrace tailWord_2607115 prefixEnd_2607115 892468744364448256181735 := by
  unfold tailWord_2607115
  simp only [CollatzResearch.WordTrace]
  refine ⟨95089295949875089638166799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63392863966583393092111199 95089295949875089638166799)
  ·
    refine ⟨142633943924812634457250199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95089295949875089638166799 142633943924812634457250199)
    ·
      refine ⟨213950915887218951685875299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142633943924812634457250199 213950915887218951685875299)
      ·
        refine ⟨320926373830828427528812949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213950915887218951685875299 320926373830828427528812949)
        ·
          refine ⟨15043423773320082540413107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 320926373830828427528812949 15043423773320082540413107)
          ·
            refine ⟨22565135659980123810619661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15043423773320082540413107 22565135659980123810619661)
            ·
              refine ⟨8461925872492546428982373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22565135659980123810619661 8461925872492546428982373)
              ·
                refine ⟨1586611101092352455434195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8461925872492546428982373 1586611101092352455434195)
                ·
                  refine ⟨2379916651638528683151293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586611101092352455434195 2379916651638528683151293)
                  ·
                    refine ⟨892468744364448256181735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2379916651638528683151293 892468744364448256181735)
                    ·
                      rfl

theorem cell22_2607115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 4, 1, 3].length) (baseStart_2607115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607115 prefixEnd_2607115 := by exact prefixLift 2607115
  have htrace : WordTrace (prefixWord ++ tailWord_2607115) baseStart_2607115 baseEnd_2607115 := by
    simpa [prefixWord, tailWord_2607115, baseEnd_2607115] using wordTrace_append hprefix tailTrace_2607115
  have hstable : (prefixWord ++ tailWord_2607115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607115).length < 2 ^ (prefixWord ++ tailWord_2607115).sum := by decide
  have hdescent : baseEnd_2607115 < baseStart_2607115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607218 : List Nat := [3, 2, 1, 2, 2, 4, 8]
def baseStart_2607218 : Nat := 118140960795 + 2607218 * 2 ^ 59
def prefixEnd_2607218 : Nat := 4983230072969 + 3 ^ 40 * 2607218 * 2
def baseEnd_2607218 : Nat := 33055703828495937809497

theorem tailTrace_2607218 : CollatzResearch.WordTrace tailWord_2607218 prefixEnd_2607218 33055703828495937809497 := by
  unfold tailWord_2607218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23773263167125484557291577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63395368445667958819444205 23773263167125484557291577)
  ·
    refine ⟨17829947375344113417968683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23773263167125484557291577 17829947375344113417968683)
    ·
      refine ⟨26744921063016170126953025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17829947375344113417968683 26744921063016170126953025)
      ·
        refine ⟨20058690797262127595214769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26744921063016170126953025 20058690797262127595214769)
        ·
          refine ⟨15044018097946595696411077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20058690797262127595214769 15044018097946595696411077)
          ·
            refine ⟨2820753393364986693077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15044018097946595696411077 2820753393364986693077077)
            ·
              refine ⟨33055703828495937809497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2820753393364986693077077 33055703828495937809497)
              ·
                rfl

theorem cell22_2607218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 8].length) (baseStart_2607218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607218 prefixEnd_2607218 := by exact prefixLift 2607218
  have htrace : WordTrace (prefixWord ++ tailWord_2607218) baseStart_2607218 baseEnd_2607218 := by
    simpa [prefixWord, tailWord_2607218, baseEnd_2607218] using wordTrace_append hprefix tailTrace_2607218
  have hstable : (prefixWord ++ tailWord_2607218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607218).length < 2 ^ (prefixWord ++ tailWord_2607218).sum := by decide
  have hdescent : baseEnd_2607218 < baseStart_2607218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607250 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2607250 : Nat := 118140960795 + 2607250 * 2 ^ 59
def prefixEnd_2607250 : Nat := 4983230072969 + 3 ^ 40 * 2607250 * 2
def baseEnd_2607250 : Nat := 892514957623352904056321

theorem tailTrace_2607250 : CollatzResearch.WordTrace tailWord_2607250 prefixEnd_2607250 892514957623352904056321 := by
  unfold tailWord_2607250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23773554951096501923582801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63396146536257338462887469 23773554951096501923582801)
  ·
    refine ⟨17830166213322376442687101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23773554951096501923582801 17830166213322376442687101)
    ·
      refine ⟨6686312329995891166007663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17830166213322376442687101 6686312329995891166007663)
      ·
        refine ⟨10029468494993836749011495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686312329995891166007663 10029468494993836749011495)
        ·
          refine ⟨15044202742490755123517243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10029468494993836749011495 15044202742490755123517243)
          ·
            refine ⟨22566304113736132685275865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15044202742490755123517243 22566304113736132685275865)
            ·
              refine ⟨16924728085302099513956899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22566304113736132685275865 16924728085302099513956899)
              ·
                refine ⟨25387092127953149270935349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16924728085302099513956899 25387092127953149270935349)
                ·
                  refine ⟨2380039886995607744150189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25387092127953149270935349 2380039886995607744150189)
                  ·
                    refine ⟨892514957623352904056321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380039886995607744150189 892514957623352904056321)
                    ·
                      rfl

theorem cell22_2607250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2607250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607250 prefixEnd_2607250 := by exact prefixLift 2607250
  have htrace : WordTrace (prefixWord ++ tailWord_2607250) baseStart_2607250 baseEnd_2607250 := by
    simpa [prefixWord, tailWord_2607250, baseEnd_2607250] using wordTrace_append hprefix tailTrace_2607250
  have hstable : (prefixWord ++ tailWord_2607250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607250).length < 2 ^ (prefixWord ++ tailWord_2607250).sum := by decide
  have hdescent : baseEnd_2607250 < baseStart_2607250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607310 : List Nat := [4, 1, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2607310 : Nat := 118140960795 + 2607310 * 2 ^ 59
def prefixEnd_2607310 : Nat := 4983230072969 + 3 ^ 40 * 2607310 * 2
def baseEnd_2607310 : Nat := 892535496849532747556137

theorem tailTrace_2607310 : CollatzResearch.WordTrace tailWord_2607310 prefixEnd_2607310 892535496849532747556137 := by
  unfold tailWord_2607310
  simp only [CollatzResearch.WordTrace]
  refine ⟨11887051023021079742689423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63397605456112425294343589 11887051023021079742689423)
  ·
    refine ⟨17830576534531619614034135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11887051023021079742689423 17830576534531619614034135)
    ·
      refine ⟨26745864801797429421051203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17830576534531619614034135 26745864801797429421051203)
      ·
        refine ⟨40118797202696144131576805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26745864801797429421051203 40118797202696144131576805)
        ·
          refine ⟨7522274475505527024670651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40118797202696144131576805 7522274475505527024670651)
          ·
            refine ⟨11283411713258290537005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7522274475505527024670651 11283411713258290537005977)
            ·
              refine ⟨8462558784943717902754483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11283411713258290537005977 8462558784943717902754483)
              ·
                refine ⟨12693838177415576854131725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462558784943717902754483 12693838177415576854131725)
                ·
                  refine ⟨4760189316530841320299397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12693838177415576854131725 4760189316530841320299397)
                  ·
                    refine ⟨892535496849532747556137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760189316530841320299397 892535496849532747556137)
                    ·
                      rfl

theorem cell22_2607310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2607310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607310 prefixEnd_2607310 := by exact prefixLift 2607310
  have htrace : WordTrace (prefixWord ++ tailWord_2607310) baseStart_2607310 baseEnd_2607310 := by
    simpa [prefixWord, tailWord_2607310, baseEnd_2607310] using wordTrace_append hprefix tailTrace_2607310
  have hstable : (prefixWord ++ tailWord_2607310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607310).length < 2 ^ (prefixWord ++ tailWord_2607310).sum := by decide
  have hdescent : baseEnd_2607310 < baseStart_2607310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607340 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_2607340 : Nat := 118140960795 + 2607340 * 2 ^ 59
def prefixEnd_2607340 : Nat := 4983230072969 + 3 ^ 40 * 2607340 * 2
def baseEnd_2607340 : Nat := 892545766462622669306045

theorem tailTrace_2607340 : CollatzResearch.WordTrace tailWord_2607340 prefixEnd_2607340 892545766462622669306045 := by
  unfold tailWord_2607340
  simp only [CollatzResearch.WordTrace]
  refine ⟨47548751187029976532553737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63398334916039968710071649 47548751187029976532553737)
  ·
    refine ⟨35661563390272482399415303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47548751187029976532553737 35661563390272482399415303)
    ·
      refine ⟨53492345085408723599122955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35661563390272482399415303 53492345085408723599122955)
      ·
        refine ⟨80238517628113085398684433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53492345085408723599122955 80238517628113085398684433)
        ·
          refine ⟨60178888221084814049013325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80238517628113085398684433 60178888221084814049013325)
          ·
            refine ⟨22567083082906805268379997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60178888221084814049013325 22567083082906805268379997)
            ·
              refine ⟨8462656156090051975642499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22567083082906805268379997 8462656156090051975642499)
              ·
                refine ⟨12693984234135077963463749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8462656156090051975642499 12693984234135077963463749)
                ·
                  refine ⟨2380122043900327118149453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12693984234135077963463749 2380122043900327118149453)
                  ·
                    refine ⟨892545766462622669306045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380122043900327118149453 892545766462622669306045)
                    ·
                      rfl

theorem cell22_2607340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_2607340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607340 prefixEnd_2607340 := by exact prefixLift 2607340
  have htrace : WordTrace (prefixWord ++ tailWord_2607340) baseStart_2607340 baseEnd_2607340 := by
    simpa [prefixWord, tailWord_2607340, baseEnd_2607340] using wordTrace_append hprefix tailTrace_2607340
  have hstable : (prefixWord ++ tailWord_2607340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607340).length < 2 ^ (prefixWord ++ tailWord_2607340).sum := by decide
  have hdescent : baseEnd_2607340 < baseStart_2607340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607370 : List Nat := [3, 1, 2, 2, 1, 1, 6, 6]
def baseStart_2607370 : Nat := 118140960795 + 2607370 * 2 ^ 59
def prefixEnd_2607370 : Nat := 4983230072969 + 3 ^ 40 * 2607370 * 2
def baseEnd_2607370 : Nat := 99172892897301399006217

theorem tailTrace_2607370 : CollatzResearch.WordTrace tailWord_2607370 prefixEnd_2607370 99172892897301399006217 := by
  unfold tailWord_2607370
  simp only [CollatzResearch.WordTrace]
  refine ⟨23774649140987817047174891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63399064375967512125799709 23774649140987817047174891)
  ·
    refine ⟨35661973711481725570762337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23774649140987817047174891 35661973711481725570762337)
    ·
      refine ⟨26746480283611294178071753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35661973711481725570762337 26746480283611294178071753)
      ·
        refine ⟨20059860212708470633553815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26746480283611294178071753 20059860212708470633553815)
        ·
          refine ⟨30089790319062705950330723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20059860212708470633553815 30089790319062705950330723)
          ·
            refine ⟨45134685478594058925496085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30089790319062705950330723 45134685478594058925496085)
            ·
              refine ⟨2115688381809096512132629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45134685478594058925496085 2115688381809096512132629)
              ·
                refine ⟨99172892897301399006217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2115688381809096512132629 99172892897301399006217)
                ·
                  rfl

theorem cell22_2607370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_2607370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607370 prefixEnd_2607370 := by exact prefixLift 2607370
  have htrace : WordTrace (prefixWord ++ tailWord_2607370) baseStart_2607370 baseEnd_2607370 := by
    simpa [prefixWord, tailWord_2607370, baseEnd_2607370] using wordTrace_append hprefix tailTrace_2607370
  have hstable : (prefixWord ++ tailWord_2607370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607370).length < 2 ^ (prefixWord ++ tailWord_2607370).sum := by decide
  have hdescent : baseEnd_2607370 < baseStart_2607370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607443 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 10]
def baseStart_2607443 : Nat := 118140960795 + 2607443 * 2 ^ 59
def prefixEnd_2607443 : Nat := 4983230072969 + 3 ^ 40 * 2607443 * 2
def baseEnd_2607443 : Nat := 297527008489188244660243

theorem tailTrace_2607443 : CollatzResearch.WordTrace tailWord_2607443 prefixEnd_2607443 297527008489188244660243 := by
  unfold tailWord_2607443
  simp only [CollatzResearch.WordTrace]
  refine ⟨95101259092686801656106983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63400839395124534437404655 95101259092686801656106983)
  ·
    refine ⟨142651888639030202484160475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95101259092686801656106983 142651888639030202484160475)
    ·
      refine ⟨213977832958545303726240713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142651888639030202484160475 213977832958545303726240713)
      ·
        refine ⟨160483374718908977794680535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213977832958545303726240713 160483374718908977794680535)
        ·
          refine ⟨240725062078363466692020803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160483374718908977794680535 240725062078363466692020803)
          ·
            refine ⟨361087593117545200038031205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240725062078363466692020803 361087593117545200038031205)
            ·
              refine ⟨67703923709539725007130851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 361087593117545200038031205 67703923709539725007130851)
              ·
                refine ⟨101555885564309587510696277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67703923709539725007130851 101555885564309587510696277)
                ·
                  refine ⟨297527008489188244660243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 101555885564309587510696277 297527008489188244660243)
                  ·
                    rfl

theorem cell22_2607443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 10].length) (baseStart_2607443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607443 prefixEnd_2607443 := by exact prefixLift 2607443
  have htrace : WordTrace (prefixWord ++ tailWord_2607443) baseStart_2607443 baseEnd_2607443 := by
    simpa [prefixWord, tailWord_2607443, baseEnd_2607443] using wordTrace_append hprefix tailTrace_2607443
  have hstable : (prefixWord ++ tailWord_2607443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607443).length < 2 ^ (prefixWord ++ tailWord_2607443).sum := by decide
  have hdescent : baseEnd_2607443 < baseStart_2607443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607460 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_2607460 : Nat := 118140960795 + 2607460 * 2 ^ 59
def prefixEnd_2607460 : Nat := 4983230072969 + 3 ^ 40 * 2607460 * 2
def baseEnd_2607460 : Nat := 297528948304994118768559

theorem tailTrace_2607460 : CollatzResearch.WordTrace tailWord_2607460 prefixEnd_2607460 297528948304994118768559 := by
  unfold tailWord_2607460
  simp only [CollatzResearch.WordTrace]
  refine ⟨47550939566812606779737917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63401252755750142372983889 47550939566812606779737917)
  ·
    refine ⟨17831602337554727542401719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47550939566812606779737917 17831602337554727542401719)
    ·
      refine ⟨26747403506332091313602579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17831602337554727542401719 26747403506332091313602579)
      ·
        refine ⟨40121105259498136970403869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26747403506332091313602579 40121105259498136970403869)
        ·
          refine ⟨15045414472311801363901451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40121105259498136970403869 15045414472311801363901451)
          ·
            refine ⟨22568121708467702045852177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15045414472311801363901451 22568121708467702045852177)
            ·
              refine ⟨16926091281350776534389133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22568121708467702045852177 16926091281350776534389133)
              ·
                refine ⟨6347284230506541200395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16926091281350776534389133 6347284230506541200395925)
                ·
                  refine ⟨297528948304994118768559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6347284230506541200395925 297528948304994118768559)
                  ·
                    rfl

theorem cell22_2607460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_2607460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607460 prefixEnd_2607460 := by exact prefixLift 2607460
  have htrace : WordTrace (prefixWord ++ tailWord_2607460) baseStart_2607460 baseEnd_2607460 := by
    simpa [prefixWord, tailWord_2607460, baseEnd_2607460] using wordTrace_append hprefix tailTrace_2607460
  have hstable : (prefixWord ++ tailWord_2607460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607460).length < 2 ^ (prefixWord ++ tailWord_2607460).sum := by decide
  have hdescent : baseEnd_2607460 < baseStart_2607460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607477 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 6]
def baseStart_2607477 : Nat := 118140960795 + 2607477 * 2 ^ 59
def prefixEnd_2607477 : Nat := 4983230072969 + 3 ^ 40 * 2607477 * 2
def baseEnd_2607477 : Nat := 297530888120799992876875

theorem tailTrace_2607477 : CollatzResearch.WordTrace tailWord_2607477 prefixEnd_2607477 297530888120799992876875 := by
  unfold tailWord_2607477
  simp only [CollatzResearch.WordTrace]
  refine ⟨95102499174563625462844685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63401666116375750308563123 95102499174563625462844685)
  ·
    refine ⟨35663437190461359548566757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95102499174563625462844685 35663437190461359548566757)
    ·
      refine ⟨6686894473211504915356267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35663437190461359548566757 6686894473211504915356267)
      ·
        refine ⟨10030341709817257373034401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6686894473211504915356267 10030341709817257373034401)
        ·
          refine ⟨7522756282362943029775801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10030341709817257373034401 7522756282362943029775801)
          ·
            refine ⟨5642067211772207272331851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522756282362943029775801 5642067211772207272331851)
            ·
              refine ⟨8463100817658310908497777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642067211772207272331851 8463100817658310908497777)
              ·
                refine ⟨6347325613243733181373333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463100817658310908497777 6347325613243733181373333)
                ·
                  refine ⟨297530888120799992876875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6347325613243733181373333 297530888120799992876875)
                  ·
                    rfl

theorem cell22_2607477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_2607477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607477 prefixEnd_2607477 := by exact prefixLift 2607477
  have htrace : WordTrace (prefixWord ++ tailWord_2607477) baseStart_2607477 baseEnd_2607477 := by
    simpa [prefixWord, tailWord_2607477, baseEnd_2607477] using wordTrace_append hprefix tailTrace_2607477
  have hstable : (prefixWord ++ tailWord_2607477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607477).length < 2 ^ (prefixWord ++ tailWord_2607477).sum := by decide
  have hdescent : baseEnd_2607477 < baseStart_2607477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607492 : List Nat := [2, 3, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2607492 : Nat := 118140960795 + 2607492 * 2 ^ 59
def prefixEnd_2607492 : Nat := 4983230072969 + 3 ^ 40 * 2607492 * 2
def baseEnd_2607492 : Nat := 892597799168944939505579

theorem tailTrace_2607492 : CollatzResearch.WordTrace tailWord_2607492 prefixEnd_2607492 892597799168944939505579 := by
  unfold tailWord_2607492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47551523134754641512320365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63402030846339522016427153 47551523134754641512320365)
  ·
    refine ⟨17831821175532990567120137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47551523134754641512320365 17831821175532990567120137)
    ·
      refine ⟨13373865881649742925340103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17831821175532990567120137 13373865881649742925340103)
      ·
        refine ⟨20060798822474614388010155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13373865881649742925340103 20060798822474614388010155)
        ·
          refine ⟨30091198233711921582015233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20060798822474614388010155 30091198233711921582015233)
          ·
            refine ⟨22568398675283941186511425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30091198233711921582015233 22568398675283941186511425)
            ·
              refine ⟨16926299006462955889883569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22568398675283941186511425 16926299006462955889883569)
              ·
                refine ⟨12694724254847216917412677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16926299006462955889883569 12694724254847216917412677)
                ·
                  refine ⟨2380260797783853172014877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12694724254847216917412677 2380260797783853172014877)
                  ·
                    refine ⟨892597799168944939505579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380260797783853172014877 892597799168944939505579)
                    ·
                      rfl

theorem cell22_2607492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2607492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607492 prefixEnd_2607492 := by exact prefixLift 2607492
  have htrace : WordTrace (prefixWord ++ tailWord_2607492) baseStart_2607492 baseEnd_2607492 := by
    simpa [prefixWord, tailWord_2607492, baseEnd_2607492] using wordTrace_append hprefix tailTrace_2607492
  have hstable : (prefixWord ++ tailWord_2607492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607492).length < 2 ^ (prefixWord ++ tailWord_2607492).sum := by decide
  have hdescent : baseEnd_2607492 < baseStart_2607492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607595 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 8]
def baseStart_2607595 : Nat := 118140960795 + 2607595 * 2 ^ 59
def prefixEnd_2607595 : Nat := 4983230072969 + 3 ^ 40 * 2607595 * 2
def baseEnd_2607595 : Nat := 297544352724629001393421

theorem tailTrace_2607595 : CollatzResearch.WordTrace tailWord_2607595 prefixEnd_2607595 297544352724629001393421 := by
  unfold tailWord_2607595
  simp only [CollatzResearch.WordTrace]
  refine ⟨95106802988136131615640239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63404535325424087743760159 95106802988136131615640239)
  ·
    refine ⟨142660204482204197423460359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95106802988136131615640239 142660204482204197423460359)
    ·
      refine ⟨213990306723306296135190539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142660204482204197423460359 213990306723306296135190539)
      ·
        refine ⟨320985460084959444202785809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213990306723306296135190539 320985460084959444202785809)
        ·
          refine ⟨240739095063719583152089357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320985460084959444202785809 240739095063719583152089357)
          ·
            refine ⟨90277160648894843682033509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240739095063719583152089357 90277160648894843682033509)
            ·
              refine ⟨16926967621667783190381283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90277160648894843682033509 16926967621667783190381283)
              ·
                refine ⟨25390451432501674785571925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16926967621667783190381283 25390451432501674785571925)
                ·
                  refine ⟨297544352724629001393421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25390451432501674785571925 297544352724629001393421)
                  ·
                    rfl

theorem cell22_2607595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 8].length) (baseStart_2607595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607595 prefixEnd_2607595 := by exact prefixLift 2607595
  have htrace : WordTrace (prefixWord ++ tailWord_2607595) baseStart_2607595 baseEnd_2607595 := by
    simpa [prefixWord, tailWord_2607595, baseEnd_2607595] using wordTrace_append hprefix tailTrace_2607595
  have hstable : (prefixWord ++ tailWord_2607595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607595).length < 2 ^ (prefixWord ++ tailWord_2607595).sum := by decide
  have hdescent : baseEnd_2607595 < baseStart_2607595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607622 : List Nat := [6, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2607622 : Nat := 118140960795 + 2607622 * 2 ^ 59
def prefixEnd_2607622 : Nat := 4983230072969 + 3 ^ 40 * 2607622 * 2
def baseEnd_2607622 : Nat := 892642300825667933755181

theorem tailTrace_2607622 : CollatzResearch.WordTrace tailWord_2607622 prefixEnd_2607622 892642300825667933755181 := by
  unfold tailWord_2607622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972118367469947350839785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63405191839358876817915413 2972118367469947350839785)
  ·
    refine ⟨2229088775602460513129839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2972118367469947350839785 2229088775602460513129839)
    ·
      refine ⟨3343633163403690769694759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229088775602460513129839 3343633163403690769694759)
      ·
        refine ⟨5015449745105536154542139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3343633163403690769694759 5015449745105536154542139)
        ·
          refine ⟨7523174617658304231813209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5015449745105536154542139 7523174617658304231813209)
          ·
            refine ⟨5642380963243728173859907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523174617658304231813209 5642380963243728173859907)
            ·
              refine ⟨8463571444865592260789861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642380963243728173859907 8463571444865592260789861)
              ·
                refine ⟨1586919645912298548898099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8463571444865592260789861 1586919645912298548898099)
                ·
                  refine ⟨2380379468868447823347149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586919645912298548898099 2380379468868447823347149)
                  ·
                    refine ⟨892642300825667933755181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380379468868447823347149 892642300825667933755181)
                    ·
                      rfl

theorem cell22_2607622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2607622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607622 prefixEnd_2607622 := by exact prefixLift 2607622
  have htrace : WordTrace (prefixWord ++ tailWord_2607622) baseStart_2607622 baseEnd_2607622 := by
    simpa [prefixWord, tailWord_2607622, baseEnd_2607622] using wordTrace_append hprefix tailTrace_2607622
  have hstable : (prefixWord ++ tailWord_2607622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607622).length < 2 ^ (prefixWord ++ tailWord_2607622).sum := by decide
  have hdescent : baseEnd_2607622 < baseStart_2607622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607642 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_2607642 : Nat := 118140960795 + 2607642 * 2 ^ 59
def prefixEnd_2607642 : Nat := 4983230072969 + 3 ^ 40 * 2607642 * 2
def baseEnd_2607642 : Nat := 892649147234394548255119

theorem tailTrace_2607642 : CollatzResearch.WordTrace tailWord_2607642 prefixEnd_2607642 892649147234394548255119 := by
  unfold tailWord_2607642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23777129304741464660650295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63405678145977239095067453 23777129304741464660650295)
  ·
    refine ⟨35665693957112196990975443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23777129304741464660650295 35665693957112196990975443)
    ·
      refine ⟨53498540935668295486463165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35665693957112196990975443 53498540935668295486463165)
      ·
        refine ⟨20061952850875610807423687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53498540935668295486463165 20061952850875610807423687)
        ·
          refine ⟨30092929276313416211135531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20061952850875610807423687 30092929276313416211135531)
          ·
            refine ⟨45139393914470124316703297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30092929276313416211135531 45139393914470124316703297)
            ·
              refine ⟨33854545435852593237527473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45139393914470124316703297 33854545435852593237527473)
              ·
                refine ⟨25390909076889444928145605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33854545435852593237527473 25390909076889444928145605)
                ·
                  refine ⟨4760795451916770924027301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25390909076889444928145605 4760795451916770924027301)
                  ·
                    refine ⟨892649147234394548255119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4760795451916770924027301 892649147234394548255119)
                    ·
                      rfl

theorem cell22_2607642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_2607642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607642 prefixEnd_2607642 := by exact prefixLift 2607642
  have htrace : WordTrace (prefixWord ++ tailWord_2607642) baseStart_2607642 baseEnd_2607642 := by
    simpa [prefixWord, tailWord_2607642, baseEnd_2607642] using wordTrace_append hprefix tailTrace_2607642
  have hstable : (prefixWord ++ tailWord_2607642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607642).length < 2 ^ (prefixWord ++ tailWord_2607642).sum := by decide
  have hdescent : baseEnd_2607642 < baseStart_2607642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607644 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2607644 : Nat := 118140960795 + 2607644 * 2 ^ 59
def prefixEnd_2607644 : Nat := 4983230072969 + 3 ^ 40 * 2607644 * 2
def baseEnd_2607644 : Nat := 892649831875267209705113

theorem tailTrace_2607644 : CollatzResearch.WordTrace tailWord_2607644 prefixEnd_2607644 892649831875267209705113 := by
  unfold tailWord_2607644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47554295082479306492086993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63405726776639075322782657 47554295082479306492086993)
  ·
    refine ⟨35665721311859479869065245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47554295082479306492086993 35665721311859479869065245)
    ·
      refine ⟨13374645491947304950899467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35665721311859479869065245 13374645491947304950899467)
      ·
        refine ⟨20061968237920957426349201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13374645491947304950899467 20061968237920957426349201)
        ·
          refine ⟨15046476178440718069761901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20061968237920957426349201 15046476178440718069761901)
          ·
            refine ⟨5642428566915269276160713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15046476178440718069761901 5642428566915269276160713)
            ·
              refine ⟨4231821425186451957120535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642428566915269276160713 4231821425186451957120535)
              ·
                refine ⟨6347732137779677935680803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231821425186451957120535 6347732137779677935680803)
                ·
                  refine ⟨9521598206669516903521205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6347732137779677935680803 9521598206669516903521205)
                  ·
                    refine ⟨892649831875267209705113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9521598206669516903521205 892649831875267209705113)
                    ·
                      rfl

theorem cell22_2607644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2607644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607644 prefixEnd_2607644 := by exact prefixLift 2607644
  have htrace : WordTrace (prefixWord ++ tailWord_2607644) baseStart_2607644 baseEnd_2607644 := by
    simpa [prefixWord, tailWord_2607644, baseEnd_2607644] using wordTrace_append hprefix tailTrace_2607644
  have hstable : (prefixWord ++ tailWord_2607644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607644).length < 2 ^ (prefixWord ++ tailWord_2607644).sum := by decide
  have hdescent : baseEnd_2607644 < baseStart_2607644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607678 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_2607678 : Nat := 118140960795 + 2607678 * 2 ^ 59
def prefixEnd_2607678 : Nat := 4983230072969 + 3 ^ 40 * 2607678 * 2
def baseEnd_2607678 : Nat := 892661470770102454355009

theorem tailTrace_2607678 : CollatzResearch.WordTrace tailWord_2607678 prefixEnd_2607678 892661470770102454355009 := by
  unfold tailWord_2607678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11888728780854429598863961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63406553497890291193941125 11888728780854429598863961)
  ·
    refine ⟨8916546585640822199147971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11888728780854429598863961 8916546585640822199147971)
    ·
      refine ⟨13374819878461233298721957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8916546585640822199147971 13374819878461233298721957)
      ·
        refine ⟨2507778727211481243510367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13374819878461233298721957 2507778727211481243510367)
        ·
          refine ⟨3761668090817221865265551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507778727211481243510367 3761668090817221865265551)
          ·
            refine ⟨5642502136225832797898327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761668090817221865265551 5642502136225832797898327)
            ·
              refine ⟨8463753204338749196847491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642502136225832797898327 8463753204338749196847491)
              ·
                refine ⟨12695629806508123795271237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8463753204338749196847491 12695629806508123795271237)
                ·
                  refine ⟨2380430588720273211613357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12695629806508123795271237 2380430588720273211613357)
                  ·
                    refine ⟨892661470770102454355009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380430588720273211613357 892661470770102454355009)
                    ·
                      rfl

theorem cell22_2607678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_2607678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607678 prefixEnd_2607678 := by exact prefixLift 2607678
  have htrace : WordTrace (prefixWord ++ tailWord_2607678) baseStart_2607678 baseEnd_2607678 := by
    simpa [prefixWord, tailWord_2607678, baseEnd_2607678] using wordTrace_append hprefix tailTrace_2607678
  have hstable : (prefixWord ++ tailWord_2607678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607678).length < 2 ^ (prefixWord ++ tailWord_2607678).sum := by decide
  have hdescent : baseEnd_2607678 < baseStart_2607678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607708 : List Nat := [2, 2, 4, 1, 4, 1, 2, 6]
def baseStart_2607708 : Nat := 118140960795 + 2607708 * 2 ^ 59
def prefixEnd_2607708 : Nat := 4983230072969 + 3 ^ 40 * 2607708 * 2
def baseEnd_2607708 : Nat := 99185748931465819567213

theorem tailTrace_2607708 : CollatzResearch.WordTrace tailWord_2607708 prefixEnd_2607708 99185748931465819567213 := by
  unfold tailWord_2607708
  simp only [CollatzResearch.WordTrace]
  refine ⟨47555462218363375957251889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63407282957817834609669185 47555462218363375957251889)
  ·
    refine ⟨35666596663772531967938917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47555462218363375957251889 35666596663772531967938917)
    ·
      refine ⟨6687486874457349743988547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35666596663772531967938917 6687486874457349743988547)
      ·
        refine ⟨10031230311686024615982821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687486874457349743988547 10031230311686024615982821)
        ·
          refine ⟨1880855683441129615496779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10031230311686024615982821 1880855683441129615496779)
          ·
            refine ⟨2821283525161694423245169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880855683441129615496779 2821283525161694423245169)
            ·
              refine ⟨2115962643871270817433877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821283525161694423245169 2115962643871270817433877)
              ·
                refine ⟨99185748931465819567213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2115962643871270817433877 99185748931465819567213)
                ·
                  rfl

theorem cell22_2607708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_2607708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607708 prefixEnd_2607708 := by exact prefixLift 2607708
  have htrace : WordTrace (prefixWord ++ tailWord_2607708) baseStart_2607708 baseEnd_2607708 := by
    simpa [prefixWord, tailWord_2607708, baseEnd_2607708] using wordTrace_append hprefix tailTrace_2607708
  have hstable : (prefixWord ++ tailWord_2607708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607708).length < 2 ^ (prefixWord ++ tailWord_2607708).sum := by decide
  have hdescent : baseEnd_2607708 < baseStart_2607708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607746 : List Nat := [3, 4, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2607746 : Nat := 118140960795 + 2607746 * 2 ^ 59
def prefixEnd_2607746 : Nat := 4983230072969 + 3 ^ 40 * 2607746 * 2
def baseEnd_2607746 : Nat := 892684748559772943654801

theorem tailTrace_2607746 : CollatzResearch.WordTrace tailWord_2607746 prefixEnd_2607746 892684748559772943654801 := by
  unfold tailWord_2607746
  simp only [CollatzResearch.WordTrace]
  refine ⟨23778077602647271101096773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63408206940392722936258061 23778077602647271101096773)
  ·
    refine ⟨4458389550496363331455645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23778077602647271101096773 4458389550496363331455645)
    ·
      refine ⟨1671896081436136249295867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4458389550496363331455645 1671896081436136249295867)
      ·
        refine ⟨2507844122154204373943801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671896081436136249295867 2507844122154204373943801)
        ·
          refine ⟨1880883091615653280457851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2507844122154204373943801 1880883091615653280457851)
          ·
            refine ⟨2821324637423479920686777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1880883091615653280457851 2821324637423479920686777)
            ·
              refine ⟨2115993478067609940515083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821324637423479920686777 2115993478067609940515083)
              ·
                refine ⟨3173990217101414910772625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115993478067609940515083 3173990217101414910772625)
                ·
                  refine ⟨2380492662826061183079469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3173990217101414910772625 2380492662826061183079469)
                  ·
                    refine ⟨892684748559772943654801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380492662826061183079469 892684748559772943654801)
                    ·
                      rfl

theorem cell22_2607746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2607746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607746 prefixEnd_2607746 := by exact prefixLift 2607746
  have htrace : WordTrace (prefixWord ++ tailWord_2607746) baseStart_2607746 baseEnd_2607746 := by
    simpa [prefixWord, tailWord_2607746, baseEnd_2607746] using wordTrace_append hprefix tailTrace_2607746
  have hstable : (prefixWord ++ tailWord_2607746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607746).length < 2 ^ (prefixWord ++ tailWord_2607746).sum := by decide
  have hdescent : baseEnd_2607746 < baseStart_2607746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607779 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 4, 3]
def baseStart_2607779 : Nat := 118140960795 + 2607779 * 2 ^ 59
def prefixEnd_2607779 : Nat := 4983230072969 + 3 ^ 40 * 2607779 * 2
def baseEnd_2607779 : Nat := 892696045134171857579699

theorem tailTrace_2607779 : CollatzResearch.WordTrace tailWord_2607779 prefixEnd_2607779 892696045134171857579699 := by
  unfold tailWord_2607779
  simp only [CollatzResearch.WordTrace]
  refine ⟨95113514019469531040338391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63409009346313020693558927 95113514019469531040338391)
  ·
    refine ⟨142670271029204296560507587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95113514019469531040338391 142670271029204296560507587)
    ·
      refine ⟨214005406543806444840761381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142670271029204296560507587 214005406543806444840761381)
      ·
        refine ⟨40126013726963708407642759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214005406543806444840761381 40126013726963708407642759)
        ·
          refine ⟨60189020590445562611464139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40126013726963708407642759 60189020590445562611464139)
          ·
            refine ⟨90283530885668343917196209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60189020590445562611464139 90283530885668343917196209)
            ·
              refine ⟨67712648164251257937897157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90283530885668343917196209 67712648164251257937897157)
              ·
                refine ⟨12696121530797110863355717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67712648164251257937897157 12696121530797110863355717)
                ·
                  refine ⟨2380522787024458286879197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12696121530797110863355717 2380522787024458286879197)
                  ·
                    refine ⟨892696045134171857579699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380522787024458286879197 892696045134171857579699)
                    ·
                      rfl

theorem cell22_2607779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 3].length) (baseStart_2607779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607779 prefixEnd_2607779 := by exact prefixLift 2607779
  have htrace : WordTrace (prefixWord ++ tailWord_2607779) baseStart_2607779 baseEnd_2607779 := by
    simpa [prefixWord, tailWord_2607779, baseEnd_2607779] using wordTrace_append hprefix tailTrace_2607779
  have hstable : (prefixWord ++ tailWord_2607779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607779).length < 2 ^ (prefixWord ++ tailWord_2607779).sum := by decide
  have hdescent : baseEnd_2607779 < baseStart_2607779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607858 : List Nat := [3, 2, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2607858 : Nat := 118140960795 + 2607858 * 2 ^ 59
def prefixEnd_2607858 : Nat := 4983230072969 + 3 ^ 40 * 2607858 * 2
def baseEnd_2607858 : Nat := 892723088448641984854457

theorem tailTrace_2607858 : CollatzResearch.WordTrace tailWord_2607858 prefixEnd_2607858 892723088448641984854457 := by
  unfold tailWord_2607858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23779098846545831883116057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63410930257455551688309485 23779098846545831883116057)
  ·
    refine ⟨17834324134909373912337043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23779098846545831883116057 17834324134909373912337043)
    ·
      refine ⟨26751486202364060868505565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17834324134909373912337043 26751486202364060868505565)
      ·
        refine ⟨10031807325886522825689587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26751486202364060868505565 10031807325886522825689587)
        ·
          refine ⟨15047710988829784238534381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10031807325886522825689587 15047710988829784238534381)
          ·
            refine ⟨5642891620811169089450393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15047710988829784238534381 5642891620811169089450393)
            ·
              refine ⟨4232168715608376817087795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5642891620811169089450393 4232168715608376817087795)
              ·
                refine ⟨6348253073412565225631693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232168715608376817087795 6348253073412565225631693)
                ·
                  refine ⟨2380594902529711959611885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6348253073412565225631693 2380594902529711959611885)
                  ·
                    refine ⟨892723088448641984854457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380594902529711959611885 892723088448641984854457)
                    ·
                      rfl

theorem cell22_2607858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2607858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607858 prefixEnd_2607858 := by exact prefixLift 2607858
  have htrace : WordTrace (prefixWord ++ tailWord_2607858) baseStart_2607858 baseEnd_2607858 := by
    simpa [prefixWord, tailWord_2607858, baseEnd_2607858] using wordTrace_append hprefix tailTrace_2607858
  have hstable : (prefixWord ++ tailWord_2607858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607858).length < 2 ^ (prefixWord ++ tailWord_2607858).sum := by decide
  have hdescent : baseEnd_2607858 < baseStart_2607858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607869 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2607869 : Nat := 118140960795 + 2607869 * 2 ^ 59
def prefixEnd_2607869 : Nat := 4983230072969 + 3 ^ 40 * 2607869 * 2
def baseEnd_2607869 : Nat := 892726853973441622829423

theorem tailTrace_2607869 : CollatzResearch.WordTrace tailWord_2607869 prefixEnd_2607869 892726853973441622829423 := by
  unfold tailWord_2607869
  simp only [CollatzResearch.WordTrace]
  refine ⟨95116796589143476411114661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63411197726095650940743107 95116796589143476411114661)
  ·
    refine ⟨17834399360464401827083999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95116796589143476411114661 17834399360464401827083999)
    ·
      refine ⟨26751599040696602740625999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17834399360464401827083999 26751599040696602740625999)
      ·
        refine ⟨40127398561044904110938999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26751599040696602740625999 40127398561044904110938999)
        ·
          refine ⟨60191097841567356166408499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40127398561044904110938999 60191097841567356166408499)
          ·
            refine ⟨90286646762351034249612749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60191097841567356166408499 90286646762351034249612749)
            ·
              refine ⟨33857492535881637843604781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90286646762351034249612749 33857492535881637843604781)
              ·
                refine ⟨12696559700955614191351793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33857492535881637843604781 12696559700955614191351793)
                ·
                  refine ⟨9522419775716710643513845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12696559700955614191351793 9522419775716710643513845)
                  ·
                    refine ⟨892726853973441622829423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9522419775716710643513845 892726853973441622829423)
                    ·
                      rfl

theorem cell22_2607869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2607869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607869 prefixEnd_2607869 := by exact prefixLift 2607869
  have htrace : WordTrace (prefixWord ++ tailWord_2607869) baseStart_2607869 baseEnd_2607869 := by
    simpa [prefixWord, tailWord_2607869, baseEnd_2607869] using wordTrace_append hprefix tailTrace_2607869
  have hstable : (prefixWord ++ tailWord_2607869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607869).length < 2 ^ (prefixWord ++ tailWord_2607869).sum := by decide
  have hdescent : baseEnd_2607869 < baseStart_2607869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607944 : List Nat := [2, 1, 3, 1, 1, 3, 1, 10]
def baseStart_2607944 : Nat := 118140960795 + 2607944 * 2 ^ 59
def prefixEnd_2607944 : Nat := 4983230072969 + 3 ^ 40 * 2607944 * 2
def baseEnd_2607944 : Nat := 99194725334018491911577

theorem tailTrace_2607944 : CollatzResearch.WordTrace tailWord_2607944 prefixEnd_2607944 99194725334018491911577 := by
  unfold tailWord_2607944
  simp only [CollatzResearch.WordTrace]
  refine ⟨47559766031935882110047443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63413021375914509480063257 47559766031935882110047443)
  ·
    refine ⟨71339649047903823165071165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47559766031935882110047443 71339649047903823165071165)
    ·
      refine ⟨26752368392963933686901687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71339649047903823165071165 26752368392963933686901687)
      ·
        refine ⟨40128552589445900530352531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26752368392963933686901687 40128552589445900530352531)
        ·
          refine ⟨60192828884168850795528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40128552589445900530352531 60192828884168850795528797)
          ·
            refine ⟨22572310831563319048323299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60192828884168850795528797 22572310831563319048323299)
            ·
              refine ⟨33858466247344978572484949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22572310831563319048323299 33858466247344978572484949)
              ·
                refine ⟨99194725334018491911577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33858466247344978572484949 99194725334018491911577)
                ·
                  rfl

theorem cell22_2607944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_2607944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607944 prefixEnd_2607944 := by exact prefixLift 2607944
  have htrace : WordTrace (prefixWord ++ tailWord_2607944) baseStart_2607944 baseEnd_2607944 := by
    simpa [prefixWord, tailWord_2607944, baseEnd_2607944] using wordTrace_append hprefix tailTrace_2607944
  have hstable : (prefixWord ++ tailWord_2607944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607944).length < 2 ^ (prefixWord ++ tailWord_2607944).sum := by decide
  have hdescent : baseEnd_2607944 < baseStart_2607944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2607993 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 3, 3]
def baseStart_2607993 : Nat := 118140960795 + 2607993 * 2 ^ 59
def prefixEnd_2607993 : Nat := 4983230072969 + 3 ^ 40 * 2607993 * 2
def baseEnd_2607993 : Nat := 892769301707546632729043

theorem tailTrace_2607993 : CollatzResearch.WordTrace tailWord_2607993 prefixEnd_2607993 892769301707546632729043 := by
  unfold tailWord_2607993
  simp only [CollatzResearch.WordTrace]
  refine ⟨95121319240694245588628633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63414212827129497059085755 95121319240694245588628633)
  ·
    refine ⟨71340989430520684191471475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95121319240694245588628633 71340989430520684191471475)
    ·
      refine ⟨107011484145781026287207213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71340989430520684191471475 107011484145781026287207213)
      ·
        refine ⟨40129306554667884857702705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107011484145781026287207213 40129306554667884857702705)
        ·
          refine ⟨30096979916000913643277029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40129306554667884857702705 30096979916000913643277029)
          ·
            refine ⟨5643183734250171308114443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30096979916000913643277029 5643183734250171308114443)
            ·
              refine ⟨8464775601375256962171665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643183734250171308114443 8464775601375256962171665)
              ·
                refine ⟨6348581701031442721628749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8464775601375256962171665 6348581701031442721628749)
                ·
                  refine ⟨2380718137886791020610781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6348581701031442721628749 2380718137886791020610781)
                  ·
                    refine ⟨892769301707546632729043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2380718137886791020610781 892769301707546632729043)
                    ·
                      rfl

theorem cell22_2607993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 3].length) (baseStart_2607993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2607993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2607993 prefixEnd_2607993 := by exact prefixLift 2607993
  have htrace : WordTrace (prefixWord ++ tailWord_2607993) baseStart_2607993 baseEnd_2607993 := by
    simpa [prefixWord, tailWord_2607993, baseEnd_2607993] using wordTrace_append hprefix tailTrace_2607993
  have hstable : (prefixWord ++ tailWord_2607993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2607993).length < 2 ^ (prefixWord ++ tailWord_2607993).sum := by decide
  have hdescent : baseEnd_2607993 < baseStart_2607993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2607993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608021 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2608021 : Nat := 118140960795 + 2608021 * 2 ^ 59
def prefixEnd_2608021 : Nat := 4983230072969 + 3 ^ 40 * 2608021 * 2
def baseEnd_2608021 : Nat := 892778886679763893028957

theorem tailTrace_2608021 : CollatzResearch.WordTrace tailWord_2608021 prefixEnd_2608021 892778886679763893028957 := by
  unfold tailWord_2608021
  simp only [CollatzResearch.WordTrace]
  refine ⟨95122340484592806370647917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63414893656395204247098611 95122340484592806370647917)
  ·
    refine ⟨35670877681722302388992969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95122340484592806370647917 35670877681722302388992969)
    ·
      refine ⟨26753158261291726791744727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35670877681722302388992969 26753158261291726791744727)
      ·
        refine ⟨40129737391937590187617091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26753158261291726791744727 40129737391937590187617091)
        ·
          refine ⟨60194606087906385281425637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40129737391937590187617091 60194606087906385281425637)
          ·
            refine ⟨11286488641482447240267307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60194606087906385281425637 11286488641482447240267307)
            ·
              refine ⟨16929732962223670860400961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11286488641482447240267307 16929732962223670860400961)
              ·
                refine ⟨12697299721667753145300721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16929732962223670860400961 12697299721667753145300721)
                ·
                  refine ⟨9522974791250814858975541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12697299721667753145300721 9522974791250814858975541)
                  ·
                    refine ⟨892778886679763893028957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9522974791250814858975541 892778886679763893028957)
                    ·
                      rfl

theorem cell22_2608021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2608021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608021 prefixEnd_2608021 := by exact prefixLift 2608021
  have htrace : WordTrace (prefixWord ++ tailWord_2608021) baseStart_2608021 baseEnd_2608021 := by
    simpa [prefixWord, tailWord_2608021, baseEnd_2608021] using wordTrace_append hprefix tailTrace_2608021
  have hstable : (prefixWord ++ tailWord_2608021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608021).length < 2 ^ (prefixWord ++ tailWord_2608021).sum := by decide
  have hdescent : baseEnd_2608021 < baseStart_2608021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608085 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 6]
def baseStart_2608085 : Nat := 118140960795 + 2608085 * 2 ^ 59
def prefixEnd_2608085 : Nat := 4983230072969 + 3 ^ 40 * 2608085 * 2
def baseEnd_2608085 : Nat := 297600265062563019809587

theorem tailTrace_2608085 : CollatzResearch.WordTrace tailWord_2608085 prefixEnd_2608085 297600265062563019809587 := by
  unfold tailWord_2608085
  simp only [CollatzResearch.WordTrace]
  refine ⟨95124674756360945300977709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63416449837573963533985139 95124674756360945300977709)
  ·
    refine ⟨35671753033635354487866641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95124674756360945300977709 35671753033635354487866641)
    ·
      refine ⟨26753814775226515865899981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35671753033635354487866641 26753814775226515865899981)
      ·
        refine ⟨10032680540709943449712493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26753814775226515865899981 10032680540709943449712493)
        ·
          refine ⟨3762255202766228793642185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10032680540709943449712493 3762255202766228793642185)
          ·
            refine ⟨2821691402074671595231639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3762255202766228793642185 2821691402074671595231639)
            ·
              refine ⟨4232537103112007392847459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821691402074671595231639 4232537103112007392847459)
              ·
                refine ⟨6348805654668011089271189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232537103112007392847459 6348805654668011089271189)
                ·
                  refine ⟨297600265062563019809587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6348805654668011089271189 297600265062563019809587)
                  ·
                    rfl

theorem cell22_2608085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_2608085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608085 prefixEnd_2608085 := by exact prefixLift 2608085
  have htrace : WordTrace (prefixWord ++ tailWord_2608085) baseStart_2608085 baseEnd_2608085 := by
    simpa [prefixWord, tailWord_2608085, baseEnd_2608085] using wordTrace_append hprefix tailTrace_2608085
  have hstable : (prefixWord ++ tailWord_2608085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608085).length < 2 ^ (prefixWord ++ tailWord_2608085).sum := by decide
  have hdescent : baseEnd_2608085 < baseStart_2608085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608117 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2608117 : Nat := 118140960795 + 2608117 * 2 ^ 59
def prefixEnd_2608117 : Nat := 4983230072969 + 3 ^ 40 * 2608117 * 2
def baseEnd_2608117 : Nat := 892811749441651642628663

theorem tailTrace_2608117 : CollatzResearch.WordTrace tailWord_2608117 prefixEnd_2608117 892811749441651642628663 := by
  unfold tailWord_2608117
  simp only [CollatzResearch.WordTrace]
  refine ⟨95125841892245014766142605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63417227928163343177428403 95125841892245014766142605)
  ·
    refine ⟨35672190709591880537303477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95125841892245014766142605 35672190709591880537303477)
    ·
      refine ⟨3344267879024238800372201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35672190709591880537303477 3344267879024238800372201)
      ·
        refine ⟨2508200909268179100279151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3344267879024238800372201 2508200909268179100279151)
        ·
          refine ⟨3762301363902268650418727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508200909268179100279151 3762301363902268650418727)
          ·
            refine ⟨5643452045853402975628091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762301363902268650418727 5643452045853402975628091)
            ·
              refine ⟨8465178068780104463442137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5643452045853402975628091 8465178068780104463442137)
              ·
                refine ⟨6348883551585078347581603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8465178068780104463442137 6348883551585078347581603)
                ·
                  refine ⟨9523325327377617521372405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6348883551585078347581603 9523325327377617521372405)
                  ·
                    refine ⟨892811749441651642628663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523325327377617521372405 892811749441651642628663)
                    ·
                      rfl

theorem cell22_2608117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2608117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608117 prefixEnd_2608117 := by exact prefixLift 2608117
  have htrace : WordTrace (prefixWord ++ tailWord_2608117) baseStart_2608117 baseEnd_2608117 := by
    simpa [prefixWord, tailWord_2608117, baseEnd_2608117] using wordTrace_append hprefix tailTrace_2608117
  have hstable : (prefixWord ++ tailWord_2608117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608117).length < 2 ^ (prefixWord ++ tailWord_2608117).sum := by decide
  have hdescent : baseEnd_2608117 < baseStart_2608117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608130 : List Nat := [3, 4, 1, 3, 1, 10]
def baseStart_2608130 : Nat := 118140960795 + 2608130 * 2 ^ 59
def prefixEnd_2608130 : Nat := 4983230072969 + 3 ^ 40 * 2608130 * 2
def baseEnd_2608130 : Nat := 11022422217374369654983

theorem tailTrace_2608130 : CollatzResearch.WordTrace tailWord_2608130 prefixEnd_2608130 11022422217374369654983 := by
  unfold tailWord_2608130
  simp only [CollatzResearch.WordTrace]
  refine ⟨23781579010299479496591461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63417544027465278657577229 23781579010299479496591461)
  ·
    refine ⟨4459046064431152405610899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23781579010299479496591461 4459046064431152405610899)
    ·
      refine ⟨6688569096646728608416349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459046064431152405610899 6688569096646728608416349)
      ·
        refine ⟨2508213411242523228156131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6688569096646728608416349 2508213411242523228156131)
        ·
          refine ⟨3762320116863784842234197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508213411242523228156131 3762320116863784842234197)
          ·
            refine ⟨11022422217374369654983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3762320116863784842234197 11022422217374369654983)
            ·
              rfl

theorem cell22_2608130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 10].length) (baseStart_2608130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608130 prefixEnd_2608130 := by exact prefixLift 2608130
  have htrace : WordTrace (prefixWord ++ tailWord_2608130) baseStart_2608130 baseEnd_2608130 := by
    simpa [prefixWord, tailWord_2608130, baseEnd_2608130] using wordTrace_append hprefix tailTrace_2608130
  have hstable : (prefixWord ++ tailWord_2608130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608130).length < 2 ^ (prefixWord ++ tailWord_2608130).sum := by decide
  have hdescent : baseEnd_2608130 < baseStart_2608130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608190 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2608190 : Nat := 118140960795 + 2608190 * 2 ^ 59
def prefixEnd_2608190 : Nat := 4983230072969 + 3 ^ 40 * 2608190 * 2
def baseEnd_2608190 : Nat := 892836738833503785553439

theorem tailTrace_2608190 : CollatzResearch.WordTrace tailWord_2608190 prefixEnd_2608190 892836738833503785553439 := by
  unfold tailWord_2608190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11891063052622568529193753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63419002947320365489033349 11891063052622568529193753)
  ·
    refine ⟨8918297289466926396895315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11891063052622568529193753 8918297289466926396895315)
    ·
      refine ⟨13377445934200389595342973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918297289466926396895315 13377445934200389595342973)
      ·
        refine ⟨5016542225325146098253615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13377445934200389595342973 5016542225325146098253615)
        ·
          refine ⟨7524813337987719147380423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016542225325146098253615 7524813337987719147380423)
          ·
            refine ⟨11287220006981578721070635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7524813337987719147380423 11287220006981578721070635)
            ·
              refine ⟨16930830010472368081605953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11287220006981578721070635 16930830010472368081605953)
              ·
                refine ⟨12698122507854276061204465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16930830010472368081605953 12698122507854276061204465)
                ·
                  refine ⟨9523591880890707045903349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12698122507854276061204465 9523591880890707045903349)
                  ·
                    refine ⟨892836738833503785553439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523591880890707045903349 892836738833503785553439)
                    ·
                      rfl

theorem cell22_2608190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2608190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608190 prefixEnd_2608190 := by exact prefixLift 2608190
  have htrace : WordTrace (prefixWord ++ tailWord_2608190) baseStart_2608190 baseEnd_2608190 := by
    simpa [prefixWord, tailWord_2608190, baseEnd_2608190] using wordTrace_append hprefix tailTrace_2608190
  have hstable : (prefixWord ++ tailWord_2608190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608190).length < 2 ^ (prefixWord ++ tailWord_2608190).sum := by decide
  have hdescent : baseEnd_2608190 < baseStart_2608190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608218 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_2608218 : Nat := 118140960795 + 2608218 * 2 ^ 59
def prefixEnd_2608218 : Nat := 4983230072969 + 3 ^ 40 * 2608218 * 2
def baseEnd_2608218 : Nat := 892846323805721045853353

theorem tailTrace_2608218 : CollatzResearch.WordTrace tailWord_2608218 prefixEnd_2608218 892846323805721045853353 := by
  unfold tailWord_2608218
  simp only [CollatzResearch.WordTrace]
  refine ⟨23782381416219777253892327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63419683776586072677046205 23782381416219777253892327)
  ·
    refine ⟨35673572124329665880838491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23782381416219777253892327 35673572124329665880838491)
    ·
      refine ⟨53510358186494498821257737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35673572124329665880838491 53510358186494498821257737)
      ·
        refine ⟨40132768639870874115943303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53510358186494498821257737 40132768639870874115943303)
        ·
          refine ⟨60199152959806311173914955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40132768639870874115943303 60199152959806311173914955)
          ·
            refine ⟨90298729439709466760872433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60199152959806311173914955 90298729439709466760872433)
            ·
              refine ⟨67724047079782100070654325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90298729439709466760872433 67724047079782100070654325)
              ·
                refine ⟨6349129413729571881623843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67724047079782100070654325 6349129413729571881623843)
                ·
                  refine ⟨9523694120594357822435765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349129413729571881623843 9523694120594357822435765)
                  ·
                    refine ⟨892846323805721045853353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9523694120594357822435765 892846323805721045853353)
                    ·
                      rfl

theorem cell22_2608218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_2608218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608218 prefixEnd_2608218 := by exact prefixLift 2608218
  have htrace : WordTrace (prefixWord ++ tailWord_2608218) baseStart_2608218 baseEnd_2608218 := by
    simpa [prefixWord, tailWord_2608218, baseEnd_2608218] using wordTrace_append hprefix tailTrace_2608218
  have hstable : (prefixWord ++ tailWord_2608218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608218).length < 2 ^ (prefixWord ++ tailWord_2608218).sum := by decide
  have hdescent : baseEnd_2608218 < baseStart_2608218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608233 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 1, 6]
def baseStart_2608233 : Nat := 118140960795 + 2608233 * 2 ^ 59
def prefixEnd_2608233 : Nat := 4983230072969 + 3 ^ 40 * 2608233 * 2
def baseEnd_2608233 : Nat := 892851458612266006728307

theorem tailTrace_2608233 : CollatzResearch.WordTrace tailWord_2608233 prefixEnd_2608233 892851458612266006728307 := by
  unfold tailWord_2608233
  simp only [CollatzResearch.WordTrace]
  refine ⟨95130072759824766577365353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63420048506549844384910235 95130072759824766577365353)
  ·
    refine ⟨71347554569868574933024015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95130072759824766577365353 71347554569868574933024015)
    ·
      refine ⟨107021331854802862399536023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71347554569868574933024015 107021331854802862399536023)
      ·
        refine ⟨160531997782204293599304035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107021331854802862399536023 160531997782204293599304035)
        ·
          refine ⟨240797996673306440398956053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160531997782204293599304035 240797996673306440398956053)
          ·
            refine ⟨11287406094061239393701065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 240797996673306440398956053 11287406094061239393701065)
            ·
              refine ⟨8465554570545929545275799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11287406094061239393701065 8465554570545929545275799)
              ·
                refine ⟨12698331855818894317913699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8465554570545929545275799 12698331855818894317913699)
                ·
                  refine ⟨19047497783728341476870549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12698331855818894317913699 19047497783728341476870549)
                  ·
                    refine ⟨892851458612266006728307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19047497783728341476870549 892851458612266006728307)
                    ·
                      rfl

theorem cell22_2608233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_2608233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608233 prefixEnd_2608233 := by exact prefixLift 2608233
  have htrace : WordTrace (prefixWord ++ tailWord_2608233) baseStart_2608233 baseEnd_2608233 := by
    simpa [prefixWord, tailWord_2608233, baseEnd_2608233] using wordTrace_append hprefix tailTrace_2608233
  have hstable : (prefixWord ++ tailWord_2608233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608233).length < 2 ^ (prefixWord ++ tailWord_2608233).sum := by decide
  have hdescent : baseEnd_2608233 < baseStart_2608233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608237 : List Nat := [1, 5, 1, 1, 2, 2, 3, 3, 4]
def baseStart_2608237 : Nat := 118140960795 + 2608237 * 2 ^ 59
def prefixEnd_2608237 : Nat := 4983230072969 + 3 ^ 40 * 2608237 * 2
def baseEnd_2608237 : Nat := 297617609298003776542765

theorem tailTrace_2608237 : CollatzResearch.WordTrace tailWord_2608237 prefixEnd_2608237 297617609298003776542765 := by
  unfold tailWord_2608237
  simp only [CollatzResearch.WordTrace]
  refine ⟨95130218651810275260510965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63420145767873516840340643 95130218651810275260510965)
  ·
    refine ⟨8918457998607213305672903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95130218651810275260510965 8918457998607213305672903)
    ·
      refine ⟨13377686997910819958509355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8918457998607213305672903 13377686997910819958509355)
      ·
        refine ⟨20066530496866229937764033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13377686997910819958509355 20066530496866229937764033)
        ·
          refine ⟨15049897872649672453323025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20066530496866229937764033 15049897872649672453323025)
          ·
            refine ⟨11287423404487254339992269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15049897872649672453323025 11287423404487254339992269)
            ·
              refine ⟨4232783776682720377497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11287423404487254339992269 4232783776682720377497101)
              ·
                refine ⟨1587293916256020141561413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232783776682720377497101 1587293916256020141561413)
                ·
                  refine ⟨297617609298003776542765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587293916256020141561413 297617609298003776542765)
                  ·
                    rfl

theorem cell22_2608237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_2608237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608237 prefixEnd_2608237 := by exact prefixLift 2608237
  have htrace : WordTrace (prefixWord ++ tailWord_2608237) baseStart_2608237 baseEnd_2608237 := by
    simpa [prefixWord, tailWord_2608237, baseEnd_2608237] using wordTrace_append hprefix tailTrace_2608237
  have hstable : (prefixWord ++ tailWord_2608237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608237).length < 2 ^ (prefixWord ++ tailWord_2608237).sum := by decide
  have hdescent : baseEnd_2608237 < baseStart_2608237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608385 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2608385 : Nat := 118140960795 + 2608385 * 2 ^ 59
def prefixEnd_2608385 : Nat := 4983230072969 + 3 ^ 40 * 2608385 * 2
def baseEnd_2608385 : Nat := 892903491318588276927841

theorem tailTrace_2608385 : CollatzResearch.WordTrace tailWord_2608385 prefixEnd_2608385 892903491318588276927841 := by
  unfold tailWord_2608385
  simp only [CollatzResearch.WordTrace]
  refine ⟨95135616655274096536898609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63423744436849397691265739 95135616655274096536898609)
  ·
    refine ⟨71351712491455572402673957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95135616655274096536898609 71351712491455572402673957)
    ·
      refine ⟨13378446092147919825501367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71351712491455572402673957 13378446092147919825501367)
      ·
        refine ⟨20067669138221879738252051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13378446092147919825501367 20067669138221879738252051)
        ·
          refine ⟨30101503707332819607378077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20067669138221879738252051 30101503707332819607378077)
          ·
            refine ⟨11288063890249807352766779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30101503707332819607378077 11288063890249807352766779)
            ·
              refine ⟨16932095835374711029150169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11288063890249807352766779 16932095835374711029150169)
              ·
                refine ⟨12699071876531033271862627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16932095835374711029150169 12699071876531033271862627)
                ·
                  refine ⟨19048607814796549907793941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12699071876531033271862627 19048607814796549907793941)
                  ·
                    refine ⟨892903491318588276927841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19048607814796549907793941 892903491318588276927841)
                    ·
                      rfl

theorem cell22_2608385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2608385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608385 prefixEnd_2608385 := by exact prefixLift 2608385
  have htrace : WordTrace (prefixWord ++ tailWord_2608385) baseStart_2608385 baseEnd_2608385 := by
    simpa [prefixWord, tailWord_2608385, baseEnd_2608385] using wordTrace_append hprefix tailTrace_2608385
  have hstable : (prefixWord ++ tailWord_2608385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608385).length < 2 ^ (prefixWord ++ tailWord_2608385).sum := by decide
  have hdescent : baseEnd_2608385 < baseStart_2608385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608387 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 1, 5]
def baseStart_2608387 : Nat := 118140960795 + 2608387 * 2 ^ 59
def prefixEnd_2608387 : Nat := 4983230072969 + 3 ^ 40 * 2608387 * 2
def baseEnd_2608387 : Nat := 892904175959460938377835

theorem tailTrace_2608387 : CollatzResearch.WordTrace tailWord_2608387 prefixEnd_2608387 892904175959460938377835 := by
  unfold tailWord_2608387
  simp only [CollatzResearch.WordTrace]
  refine ⟨95135689601266850878471415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63423793067511233918980943 95135689601266850878471415)
  ·
    refine ⟨142703534401900276317707123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95135689601266850878471415 142703534401900276317707123)
    ·
      refine ⟨214055301602850414476560685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142703534401900276317707123 214055301602850414476560685)
      ·
        refine ⟨80270738101068905428710257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214055301602850414476560685 80270738101068905428710257)
        ·
          refine ⟨60203053575801679071532693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80270738101068905428710257 60203053575801679071532693)
          ·
            refine ⟨2822018136365703706478095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60203053575801679071532693 2822018136365703706478095)
            ·
              refine ⟨4233027204548555559717143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822018136365703706478095 4233027204548555559717143)
              ·
                refine ⟨6349540806822833339575715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233027204548555559717143 6349540806822833339575715)
                ·
                  refine ⟨9524311210234250009363573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6349540806822833339575715 9524311210234250009363573)
                  ·
                    refine ⟨892904175959460938377835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9524311210234250009363573 892904175959460938377835)
                    ·
                      rfl

theorem cell22_2608387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 5].length) (baseStart_2608387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608387 prefixEnd_2608387 := by exact prefixLift 2608387
  have htrace : WordTrace (prefixWord ++ tailWord_2608387) baseStart_2608387 baseEnd_2608387 := by
    simpa [prefixWord, tailWord_2608387, baseEnd_2608387] using wordTrace_append hprefix tailTrace_2608387
  have hstable : (prefixWord ++ tailWord_2608387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608387).length < 2 ^ (prefixWord ++ tailWord_2608387).sum := by decide
  have hdescent : baseEnd_2608387 < baseStart_2608387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608438 : List Nat := [5, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2608438 : Nat := 118140960795 + 2608438 * 2 ^ 59
def prefixEnd_2608438 : Nat := 4983230072969 + 3 ^ 40 * 2608438 * 2
def baseEnd_2608438 : Nat := 892921634301713805352679

theorem tailTrace_2608438 : CollatzResearch.WordTrace tailWord_2608438 prefixEnd_2608438 892921634301713805352679 := by
  unfold tailWord_2608438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5946096857755130411786123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63425033149388057725718645 5946096857755130411786123)
  ·
    refine ⟨8919145286632695617679185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5946096857755130411786123 8919145286632695617679185)
    ·
      refine ⟨6689358964974521713259389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8919145286632695617679185 6689358964974521713259389)
      ·
        refine ⟨2508509611865445642472271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6689358964974521713259389 2508509611865445642472271)
        ·
          refine ⟨3762764417798168463708407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508509611865445642472271 3762764417798168463708407)
          ·
            refine ⟨5644146626697252695562611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762764417798168463708407 5644146626697252695562611)
            ·
              refine ⟨8466219940045879043343917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644146626697252695562611 8466219940045879043343917)
              ·
                refine ⟨3174832477517204641253969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8466219940045879043343917 3174832477517204641253969)
                ·
                  refine ⟨2381124358137903480940477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174832477517204641253969 2381124358137903480940477)
                  ·
                    refine ⟨892921634301713805352679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381124358137903480940477 892921634301713805352679)
                    ·
                      rfl

theorem cell22_2608438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2608438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608438 prefixEnd_2608438 := by exact prefixLift 2608438
  have htrace : WordTrace (prefixWord ++ tailWord_2608438) baseStart_2608438 baseEnd_2608438 := by
    simpa [prefixWord, tailWord_2608438, baseEnd_2608438] using wordTrace_append hprefix tailTrace_2608438
  have hstable : (prefixWord ++ tailWord_2608438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608438).length < 2 ^ (prefixWord ++ tailWord_2608438).sum := by decide
  have hdescent : baseEnd_2608438 < baseStart_2608438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608483 : List Nat := [1, 1, 1, 5, 2, 4, 2, 2, 1, 3]
def baseStart_2608483 : Nat := 118140960795 + 2608483 * 2 ^ 59
def prefixEnd_2608483 : Nat := 4983230072969 + 3 ^ 40 * 2608483 * 2
def baseEnd_2608483 : Nat := 892937038721348687977541

theorem tailTrace_2608483 : CollatzResearch.WordTrace tailWord_2608483 prefixEnd_2608483 892937038721348687977541 := by
  unfold tailWord_2608483
  simp only [CollatzResearch.WordTrace]
  refine ⟨95139191008919059273966103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63426127339279372849310735 95139191008919059273966103)
  ·
    refine ⟨142708786513378588910949155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95139191008919059273966103 142708786513378588910949155)
    ·
      refine ⟨214063179770067883366423733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142708786513378588910949155 214063179770067883366423733)
      ·
        refine ⟨20068423103443864065602225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214063179770067883366423733 20068423103443864065602225)
        ·
          refine ⟨15051317327582898049201669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20068423103443864065602225 15051317327582898049201669)
          ·
            refine ⟨2822121998921793384225313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15051317327582898049201669 2822121998921793384225313)
            ·
              refine ⟨2116591499191345038168985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822121998921793384225313 2116591499191345038168985)
              ·
                refine ⟨1587443624393508778626739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116591499191345038168985 1587443624393508778626739)
                ·
                  refine ⟨2381165436590263167940109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587443624393508778626739 2381165436590263167940109)
                  ·
                    refine ⟨892937038721348687977541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381165436590263167940109 892937038721348687977541)
                    ·
                      rfl

theorem cell22_2608483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 2, 1, 3].length) (baseStart_2608483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608483 prefixEnd_2608483 := by exact prefixLift 2608483
  have htrace : WordTrace (prefixWord ++ tailWord_2608483) baseStart_2608483 baseEnd_2608483 := by
    simpa [prefixWord, tailWord_2608483, baseEnd_2608483] using wordTrace_append hprefix tailTrace_2608483
  have hstable : (prefixWord ++ tailWord_2608483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608483).length < 2 ^ (prefixWord ++ tailWord_2608483).sum := by decide
  have hdescent : baseEnd_2608483 < baseStart_2608483 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608492 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_2608492 : Nat := 118140960795 + 2608492 * 2 ^ 59
def prefixEnd_2608492 : Nat := 4983230072969 + 3 ^ 40 * 2608492 * 2
def baseEnd_2608492 : Nat := 892940119605275664502513

theorem tailTrace_2608492 : CollatzResearch.WordTrace tailWord_2608492 prefixEnd_2608492 892940119605275664502513 := by
  unfold tailWord_2608492
  simp only [CollatzResearch.WordTrace]
  refine ⟨47569759632943226905521865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63426346177257635874029153 47569759632943226905521865)
  ·
    refine ⟨35677319724707420179141399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47569759632943226905521865 35677319724707420179141399)
    ·
      refine ⟨53515979587061130268712099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35677319724707420179141399 53515979587061130268712099)
      ·
        refine ⟨80273969380591695403068149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53515979587061130268712099 80273969380591695403068149)
        ·
          refine ⟨7525684629430471444037639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80273969380591695403068149 7525684629430471444037639)
          ·
            refine ⟨11288526944145707166056459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7525684629430471444037639 11288526944145707166056459)
            ·
              refine ⟨16932790416218560749084689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11288526944145707166056459 16932790416218560749084689)
              ·
                refine ⟨12699592812163920561813517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16932790416218560749084689 12699592812163920561813517)
                ·
                  refine ⟨4762347304561470210680069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12699592812163920561813517 4762347304561470210680069)
                  ·
                    refine ⟨892940119605275664502513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4762347304561470210680069 892940119605275664502513)
                    ·
                      rfl

theorem cell22_2608492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_2608492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608492 prefixEnd_2608492 := by exact prefixLift 2608492
  have htrace : WordTrace (prefixWord ++ tailWord_2608492) baseStart_2608492 baseEnd_2608492 := by
    simpa [prefixWord, tailWord_2608492, baseEnd_2608492] using wordTrace_append hprefix tailTrace_2608492
  have hstable : (prefixWord ++ tailWord_2608492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608492).length < 2 ^ (prefixWord ++ tailWord_2608492).sum := by decide
  have hdescent : baseEnd_2608492 < baseStart_2608492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608524 : List Nat := [2, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_2608524 : Nat := 118140960795 + 2608524 * 2 ^ 59
def prefixEnd_2608524 : Nat := 4983230072969 + 3 ^ 40 * 2608524 * 2
def baseEnd_2608524 : Nat := 297650357953079415900805

theorem tailTrace_2608524 : CollatzResearch.WordTrace tailWord_2608524 prefixEnd_2608524 297650357953079415900805 := by
  unfold tailWord_2608524
  simp only [CollatzResearch.WordTrace]
  refine ⟨47570343200885261638104313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63427124267847015517472417 47570343200885261638104313)
  ·
    refine ⟨35677757400663946228578235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47570343200885261638104313 35677757400663946228578235)
    ·
      refine ⟨53516636100995919342867353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35677757400663946228578235 53516636100995919342867353)
      ·
        refine ⟨40137477075746939507150515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53516636100995919342867353 40137477075746939507150515)
        ·
          refine ⟨60206215613620409260725773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40137477075746939507150515 60206215613620409260725773)
          ·
            refine ⟨22577330855107653472772165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60206215613620409260725773 22577330855107653472772165)
            ·
              refine ⟨4233249535332685026144781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22577330855107653472772165 4233249535332685026144781)
              ·
                refine ⟨1587468575749756884804293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4233249535332685026144781 1587468575749756884804293)
                ·
                  refine ⟨297650357953079415900805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587468575749756884804293 297650357953079415900805)
                  ·
                    rfl

theorem cell22_2608524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_2608524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608524 prefixEnd_2608524 := by exact prefixLift 2608524
  have htrace : WordTrace (prefixWord ++ tailWord_2608524) baseStart_2608524 baseEnd_2608524 := by
    simpa [prefixWord, tailWord_2608524, baseEnd_2608524] using wordTrace_append hprefix tailTrace_2608524
  have hstable : (prefixWord ++ tailWord_2608524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608524).length < 2 ^ (prefixWord ++ tailWord_2608524).sum := by decide
  have hdescent : baseEnd_2608524 < baseStart_2608524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608526 : List Nat := [4, 1, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2608526 : Nat := 118140960795 + 2608526 * 2 ^ 59
def prefixEnd_2608526 : Nat := 4983230072969 + 3 ^ 40 * 2608526 * 2
def baseEnd_2608526 : Nat := 892951758500110909152409

theorem tailTrace_2608526 : CollatzResearch.WordTrace tailWord_2608526 prefixEnd_2608526 892951758500110909152409 := by
  unfold tailWord_2608526
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892594918470409702222679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63427172898508851745187621 11892594918470409702222679)
  ·
    refine ⟨17838892377705614553334019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11892594918470409702222679 17838892377705614553334019)
    ·
      refine ⟨26758338566558421830001029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17838892377705614553334019 26758338566558421830001029)
      ·
        refine ⟨5017188481229704093125193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26758338566558421830001029 5017188481229704093125193)
        ·
          refine ⟨3762891360922278069843895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5017188481229704093125193 3762891360922278069843895)
          ·
            refine ⟨5644337041383417104765843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762891360922278069843895 5644337041383417104765843)
            ·
              refine ⟨8466505562075125657148765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644337041383417104765843 8466505562075125657148765)
              ·
                refine ⟨3174939585778172121430787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8466505562075125657148765 3174939585778172121430787)
                ·
                  refine ⟨4762409378667258182146181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3174939585778172121430787 4762409378667258182146181)
                  ·
                    refine ⟨892951758500110909152409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4762409378667258182146181 892951758500110909152409)
                    ·
                      rfl

theorem cell22_2608526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2608526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608526 prefixEnd_2608526 := by exact prefixLift 2608526
  have htrace : WordTrace (prefixWord ++ tailWord_2608526) baseStart_2608526 baseEnd_2608526 := by
    simpa [prefixWord, tailWord_2608526, baseEnd_2608526] using wordTrace_append hprefix tailTrace_2608526
  have hstable : (prefixWord ++ tailWord_2608526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608526).length < 2 ^ (prefixWord ++ tailWord_2608526).sum := by decide
  have hdescent : baseEnd_2608526 < baseStart_2608526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608597 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 7]
def baseStart_2608597 : Nat := 118140960795 + 2608597 * 2 ^ 59
def prefixEnd_2608597 : Nat := 4983230072969 + 3 ^ 40 * 2608597 * 2
def baseEnd_2608597 : Nat := 297658687750363463542397

theorem tailTrace_2608597 : CollatzResearch.WordTrace tailWord_2608597 prefixEnd_2608597 297658687750363463542397 := by
  unfold tailWord_2608597
  simp only [CollatzResearch.WordTrace]
  refine ⟨95143348930506056743616045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63428899287004037829077363 95143348930506056743616045)
  ·
    refine ⟨35678755848939771278856017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95143348930506056743616045 35678755848939771278856017)
    ·
      refine ⟨26759066886704828459142013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35678755848939771278856017 26759066886704828459142013)
      ·
        refine ⟨10034650082514310672178255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26759066886704828459142013 10034650082514310672178255)
        ·
          refine ⟨15051975123771466008267383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10034650082514310672178255 15051975123771466008267383)
          ·
            refine ⟨22577962685657199012401075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15051975123771466008267383 22577962685657199012401075)
            ·
              refine ⟨33866944028485798518601613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22577962685657199012401075 33866944028485798518601613)
              ·
                refine ⟨12700104010682174444475605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33866944028485798518601613 12700104010682174444475605)
                ·
                  refine ⟨297658687750363463542397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12700104010682174444475605 297658687750363463542397)
                  ·
                    rfl

theorem cell22_2608597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_2608597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608597 prefixEnd_2608597 := by exact prefixLift 2608597
  have htrace : WordTrace (prefixWord ++ tailWord_2608597) baseStart_2608597 baseEnd_2608597 := by
    simpa [prefixWord, tailWord_2608597, baseEnd_2608597] using wordTrace_append hprefix tailTrace_2608597
  have hstable : (prefixWord ++ tailWord_2608597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608597).length < 2 ^ (prefixWord ++ tailWord_2608597).sum := by decide
  have hdescent : baseEnd_2608597 < baseStart_2608597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608601 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 3, 3]
def baseStart_2608601 : Nat := 118140960795 + 2608601 * 2 ^ 59
def prefixEnd_2608601 : Nat := 4983230072969 + 3 ^ 40 * 2608601 * 2
def baseEnd_2608601 : Nat := 892977432532835713527179

theorem tailTrace_2608601 : CollatzResearch.WordTrace tailWord_2608601 prefixEnd_2608601 892977432532835713527179 := by
  unfold tailWord_2608601
  simp only [CollatzResearch.WordTrace]
  refine ⟨95143494822491565426761657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63428996548327710284507771 95143494822491565426761657)
  ·
    refine ⟨71357621116868674070071243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95143494822491565426761657 71357621116868674070071243)
    ·
      refine ⟨107036431675303011105106865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71357621116868674070071243 107036431675303011105106865)
      ·
        refine ⟨80277323756477258328830149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107036431675303011105106865 80277323756477258328830149)
        ·
          refine ⟨15051998204339485936655653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80277323756477258328830149 15051998204339485936655653)
          ·
            refine ⟨2822249663313653613122935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15051998204339485936655653 2822249663313653613122935)
            ·
              refine ⟨4233374494970480419684403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822249663313653613122935 4233374494970480419684403)
              ·
                refine ⟨6350061742455720629526605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233374494970480419684403 6350061742455720629526605)
                ·
                  refine ⟨2381273153420895236072477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6350061742455720629526605 2381273153420895236072477)
                  ·
                    refine ⟨892977432532835713527179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381273153420895236072477 892977432532835713527179)
                    ·
                      rfl

theorem cell22_2608601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 3].length) (baseStart_2608601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608601 prefixEnd_2608601 := by exact prefixLift 2608601
  have htrace : WordTrace (prefixWord ++ tailWord_2608601) baseStart_2608601 baseEnd_2608601 := by
    simpa [prefixWord, tailWord_2608601, baseEnd_2608601] using wordTrace_append hprefix tailTrace_2608601
  have hstable : (prefixWord ++ tailWord_2608601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608601).length < 2 ^ (prefixWord ++ tailWord_2608601).sum := by decide
  have hdescent : baseEnd_2608601 < baseStart_2608601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2608612 : Nat := 118140960795 + 2608612 * 2 ^ 59
def prefixEnd_2608612 : Nat := 4983230072969 + 3 ^ 40 * 2608612 * 2
def baseEnd_2608612 : Nat := 892981198057635351502145

theorem tailTrace_2608612 : CollatzResearch.WordTrace tailWord_2608612 prefixEnd_2608612 892981198057635351502145 := by
  unfold tailWord_2608612
  simp only [CollatzResearch.WordTrace]
  refine ⟨47571948012725857152706045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63429264016967809536941393 47571948012725857152706045)
  ·
    refine ⟨17839480504772196432264767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47571948012725857152706045 17839480504772196432264767)
    ·
      refine ⟨26759220757158294648397151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17839480504772196432264767 26759220757158294648397151)
      ·
        refine ⟨40138831135737441972595727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26759220757158294648397151 40138831135737441972595727)
        ·
          refine ⟨60208246703606162958893591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40138831135737441972595727 60208246703606162958893591)
          ·
            refine ⟨90312370055409244438340387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60208246703606162958893591 90312370055409244438340387)
            ·
              refine ⟨135468555083113866657510581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90312370055409244438340387 135468555083113866657510581)
              ·
                refine ⟨12700177039041924999141617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135468555083113866657510581 12700177039041924999141617)
                ·
                  refine ⟨9525132779281443749356213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12700177039041924999141617 9525132779281443749356213)
                  ·
                    refine ⟨892981198057635351502145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9525132779281443749356213 892981198057635351502145)
                    ·
                      rfl

theorem cell22_2608612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2608612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608612 prefixEnd_2608612 := by exact prefixLift 2608612
  have htrace : WordTrace (prefixWord ++ tailWord_2608612) baseStart_2608612 baseEnd_2608612 := by
    simpa [prefixWord, tailWord_2608612, baseEnd_2608612] using wordTrace_append hprefix tailTrace_2608612
  have hstable : (prefixWord ++ tailWord_2608612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608612).length < 2 ^ (prefixWord ++ tailWord_2608612).sum := by decide
  have hdescent : baseEnd_2608612 < baseStart_2608612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608652 : List Nat := [2, 2, 1, 2, 6, 1, 2, 2, 1, 3]
def baseStart_2608652 : Nat := 118140960795 + 2608652 * 2 ^ 59
def prefixEnd_2608652 : Nat := 4983230072969 + 3 ^ 40 * 2608652 * 2
def baseEnd_2608652 : Nat := 892994890875088580502023

theorem tailTrace_2608652 : CollatzResearch.WordTrace tailWord_2608652 prefixEnd_2608652 892994890875088580502023 := by
  unfold tailWord_2608652
  simp only [CollatzResearch.WordTrace]
  refine ⟨47572677472653400568434105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63430236630204534091245473 47572677472653400568434105)
  ·
    refine ⟨35679508104490050426325579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47572677472653400568434105 35679508104490050426325579)
    ·
      refine ⟨53519262156735075639488369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35679508104490050426325579 53519262156735075639488369)
      ·
        refine ⟨40139446617551306729616277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53519262156735075639488369 40139446617551306729616277)
        ·
          refine ⟨1881536560197717502950763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40139446617551306729616277 1881536560197717502950763)
          ·
            refine ⟨2822304840296576254426145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881536560197717502950763 2822304840296576254426145)
            ·
              refine ⟨2116728630222432190819609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2822304840296576254426145 2116728630222432190819609)
              ·
                refine ⟨1587546472666824143114707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2116728630222432190819609 1587546472666824143114707)
                ·
                  refine ⟨2381319709000236214672061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587546472666824143114707 2381319709000236214672061)
                  ·
                    refine ⟨892994890875088580502023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381319709000236214672061 892994890875088580502023)
                    ·
                      rfl

theorem cell22_2608652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 2, 1, 3].length) (baseStart_2608652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608652 prefixEnd_2608652 := by exact prefixLift 2608652
  have htrace : WordTrace (prefixWord ++ tailWord_2608652) baseStart_2608652 baseEnd_2608652 := by
    simpa [prefixWord, tailWord_2608652, baseEnd_2608652] using wordTrace_append hprefix tailTrace_2608652
  have hstable : (prefixWord ++ tailWord_2608652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608652).length < 2 ^ (prefixWord ++ tailWord_2608652).sum := by decide
  have hdescent : baseEnd_2608652 < baseStart_2608652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608657 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2608657 : Nat := 118140960795 + 2608657 * 2 ^ 59
def prefixEnd_2608657 : Nat := 4983230072969 + 3 ^ 40 * 2608657 * 2
def baseEnd_2608657 : Nat := 892996602477270234127007

theorem tailTrace_2608657 : CollatzResearch.WordTrace tailWord_2608657 prefixEnd_2608657 892996602477270234127007 := by
  unfold tailWord_2608657
  simp only [CollatzResearch.WordTrace]
  refine ⟨95145537310288686990800225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63430358206859124660533483 95145537310288686990800225)
  ·
    refine ⟨71359152982716515243100169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95145537310288686990800225 71359152982716515243100169)
    ·
      refine ⟨53519364737037386432325127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71359152982716515243100169 53519364737037386432325127)
      ·
        refine ⟨80279047105556079648487691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53519364737037386432325127 80279047105556079648487691)
        ·
          refine ⟨120418570658334119472731537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80279047105556079648487691 120418570658334119472731537)
          ·
            refine ⟨90313927993750589604548653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120418570658334119472731537 90313927993750589604548653)
            ·
              refine ⟨33867722997656471101705745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90313927993750589604548653 33867722997656471101705745)
              ·
                refine ⟨25400792248242353326279309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33867722997656471101705745 25400792248242353326279309)
                ·
                  refine ⟨9525297093090882497354741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25400792248242353326279309 9525297093090882497354741)
                  ·
                    refine ⟨892996602477270234127007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9525297093090882497354741 892996602477270234127007)
                    ·
                      rfl

theorem cell22_2608657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2608657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608657 prefixEnd_2608657 := by exact prefixLift 2608657
  have htrace : WordTrace (prefixWord ++ tailWord_2608657) baseStart_2608657 baseEnd_2608657 := by
    simpa [prefixWord, tailWord_2608657, baseEnd_2608657] using wordTrace_append hprefix tailTrace_2608657
  have hstable : (prefixWord ++ tailWord_2608657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608657).length < 2 ^ (prefixWord ++ tailWord_2608657).sum := by decide
  have hdescent : baseEnd_2608657 < baseStart_2608657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608674 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2608674 : Nat := 118140960795 + 2608674 * 2 ^ 59
def prefixEnd_2608674 : Nat := 4983230072969 + 3 ^ 40 * 2608674 * 2
def baseEnd_2608674 : Nat := 893002421924687856451955

theorem tailTrace_2608674 : CollatzResearch.WordTrace tailWord_2608674 prefixEnd_2608674 893002421924687856451955 := by
  unfold tailWord_2608674
  simp only [CollatzResearch.WordTrace]
  refine ⟨23786539337806774723542269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63430771567484732596112717 23786539337806774723542269)
  ·
    refine ⟨8919952251677540521328351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23786539337806774723542269 8919952251677540521328351)
    ·
      refine ⟨13379928377516310781992527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8919952251677540521328351 13379928377516310781992527)
      ·
        refine ⟨20069892566274466172988791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13379928377516310781992527 20069892566274466172988791)
        ·
          refine ⟨30104838849411699259483187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20069892566274466172988791 30104838849411699259483187)
          ·
            refine ⟨45157258274117548889224781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30104838849411699259483187 45157258274117548889224781)
            ·
              refine ⟨16933971852794080833459293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45157258274117548889224781 16933971852794080833459293)
              ·
                refine ⟨6350239444797780312547235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16933971852794080833459293 6350239444797780312547235)
                ·
                  refine ⟨9525359167196670468820853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6350239444797780312547235 9525359167196670468820853)
                  ·
                    refine ⟨893002421924687856451955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9525359167196670468820853 893002421924687856451955)
                    ·
                      rfl

theorem cell22_2608674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2608674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608674 prefixEnd_2608674 := by exact prefixLift 2608674
  have htrace : WordTrace (prefixWord ++ tailWord_2608674) baseStart_2608674 baseEnd_2608674 := by
    simpa [prefixWord, tailWord_2608674, baseEnd_2608674] using wordTrace_append hprefix tailTrace_2608674
  have hstable : (prefixWord ++ tailWord_2608674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608674).length < 2 ^ (prefixWord ++ tailWord_2608674).sum := by decide
  have hdescent : baseEnd_2608674 < baseStart_2608674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608779 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 3, 4]
def baseStart_2608779 : Nat := 118140960795 + 2608779 * 2 ^ 59
def prefixEnd_2608779 : Nat := 4983230072969 + 3 ^ 40 * 2608779 * 2
def baseEnd_2608779 : Nat := 893038365570502582576633

theorem tailTrace_2608779 : CollatzResearch.WordTrace tailWord_2608779 prefixEnd_2608779 893038365570502582576633 := by
  unfold tailWord_2608779
  simp only [CollatzResearch.WordTrace]
  refine ⟨95149987015846701826741391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63433324677231134551160927 95149987015846701826741391)
  ·
    refine ⟨142724980523770052740112087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95149987015846701826741391 142724980523770052740112087)
    ·
      refine ⟨214087470785655079110168131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142724980523770052740112087 214087470785655079110168131)
      ·
        refine ⟨321131206178482618665252197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214087470785655079110168131 321131206178482618665252197)
        ·
          refine ⟨60212101158465490999734787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321131206178482618665252197 60212101158465490999734787)
          ·
            refine ⟨90318151737698236499602181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60212101158465490999734787 90318151737698236499602181)
            ·
              refine ⟨16934653450818419343675409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90318151737698236499602181 16934653450818419343675409)
              ·
                refine ⟨12700990088113814507756557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16934653450818419343675409 12700990088113814507756557)
                ·
                  refine ⟨4762871283042680440408709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12700990088113814507756557 4762871283042680440408709)
                  ·
                    refine ⟨893038365570502582576633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4762871283042680440408709 893038365570502582576633)
                    ·
                      rfl

theorem cell22_2608779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 3, 4].length) (baseStart_2608779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608779 prefixEnd_2608779 := by exact prefixLift 2608779
  have htrace : WordTrace (prefixWord ++ tailWord_2608779) baseStart_2608779 baseEnd_2608779 := by
    simpa [prefixWord, tailWord_2608779, baseEnd_2608779] using wordTrace_append hprefix tailTrace_2608779
  have hstable : (prefixWord ++ tailWord_2608779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608779).length < 2 ^ (prefixWord ++ tailWord_2608779).sum := by decide
  have hdescent : baseEnd_2608779 < baseStart_2608779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608828 : List Nat := [2, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_2608828 : Nat := 118140960795 + 2608828 * 2 ^ 59
def prefixEnd_2608828 : Nat := 4983230072969 + 3 ^ 40 * 2608828 * 2
def baseEnd_2608828 : Nat := 297685046423960929367161

theorem tailTrace_2608828 : CollatzResearch.WordTrace tailWord_2608828 prefixEnd_2608828 297685046423960929367161 := by
  unfold tailWord_2608828
  simp only [CollatzResearch.WordTrace]
  refine ⟨47575887096334591597637569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63434516128446122130183425 47575887096334591597637569)
  ·
    refine ⟨35681915322250943698228177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47575887096334591597637569 35681915322250943698228177)
    ·
      refine ⟨26761436491688207773671133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35681915322250943698228177 26761436491688207773671133)
      ·
        refine ⟨10035538684383077915126675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26761436491688207773671133 10035538684383077915126675)
        ·
          refine ⟨15053308026574616872690013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10035538684383077915126675 15053308026574616872690013)
          ·
            refine ⟨5644990509965481327258755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15053308026574616872690013 5644990509965481327258755)
            ·
              refine ⟨8467485764948221990888133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5644990509965481327258755 8467485764948221990888133)
              ·
                refine ⟨1587653580927791623291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8467485764948221990888133 1587653580927791623291525)
                ·
                  refine ⟨297685046423960929367161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587653580927791623291525 297685046423960929367161)
                  ·
                    rfl

theorem cell22_2608828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_2608828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608828 prefixEnd_2608828 := by exact prefixLift 2608828
  have htrace : WordTrace (prefixWord ++ tailWord_2608828) baseStart_2608828 baseEnd_2608828 := by
    simpa [prefixWord, tailWord_2608828, baseEnd_2608828] using wordTrace_append hprefix tailTrace_2608828
  have hstable : (prefixWord ++ tailWord_2608828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608828).length < 2 ^ (prefixWord ++ tailWord_2608828).sum := by decide
  have hdescent : baseEnd_2608828 < baseStart_2608828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608856 : List Nat := [2, 1, 2, 2, 3, 1, 5, 6]
def baseStart_2608856 : Nat := 118140960795 + 2608856 * 2 ^ 59
def prefixEnd_2608856 : Nat := 4983230072969 + 3 ^ 40 * 2608856 * 2
def baseEnd_2608856 : Nat := 99229413804900005377933

theorem tailTrace_2608856 : CollatzResearch.WordTrace tailWord_2608856 prefixEnd_2608856 99229413804900005377933 := by
  unfold tailWord_2608856
  simp only [CollatzResearch.WordTrace]
  refine ⟨47576397718283871988647211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63435196957711829318196281 47576397718283871988647211)
  ·
    refine ⟨71364596577425807982970817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47576397718283871988647211 71364596577425807982970817)
    ·
      refine ⟨53523447433069355987228113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71364596577425807982970817 53523447433069355987228113)
      ·
        refine ⟨40142585574802016990421085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53523447433069355987228113 40142585574802016990421085)
        ·
          refine ⟨15053469590550756371407907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40142585574802016990421085 15053469590550756371407907)
          ·
            refine ⟨22580204385826134557111861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15053469590550756371407907 22580204385826134557111861)
            ·
              refine ⟨2116894161171200114729237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22580204385826134557111861 2116894161171200114729237)
              ·
                refine ⟨99229413804900005377933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2116894161171200114729237 99229413804900005377933)
                ·
                  rfl

theorem cell22_2608856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_2608856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608856 prefixEnd_2608856 := by exact prefixLift 2608856
  have htrace : WordTrace (prefixWord ++ tailWord_2608856) baseStart_2608856 baseEnd_2608856 := by
    simpa [prefixWord, tailWord_2608856, baseEnd_2608856] using wordTrace_append hprefix tailTrace_2608856
  have hstable : (prefixWord ++ tailWord_2608856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608856).length < 2 ^ (prefixWord ++ tailWord_2608856).sum := by decide
  have hdescent : baseEnd_2608856 < baseStart_2608856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608858 : List Nat := [3, 1, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_2608858 : Nat := 118140960795 + 2608858 * 2 ^ 59
def prefixEnd_2608858 : Nat := 4983230072969 + 3 ^ 40 * 2608858 * 2
def baseEnd_2608858 : Nat := 893065408884972709851391

theorem tailTrace_2608858 : CollatzResearch.WordTrace tailWord_2608858 prefixEnd_2608858 893065408884972709851391 := by
  unfold tailWord_2608858
  simp only [CollatzResearch.WordTrace]
  refine ⟨23788217095640124579716807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63435245588373665545911485 23788217095640124579716807)
  ·
    refine ⟨35682325643460186869575211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23788217095640124579716807 35682325643460186869575211)
    ·
      refine ⟨53523488465190280304362817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35682325643460186869575211 53523488465190280304362817)
      ·
        refine ⟨40142616348892710228272113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53523488465190280304362817 40142616348892710228272113)
        ·
          refine ⟨30106962261669532671204085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40142616348892710228272113 30106962261669532671204085)
          ·
            refine ⟨2822527712031518687925383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30106962261669532671204085 2822527712031518687925383)
            ·
              refine ⟨4233791568047278031888075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822527712031518687925383 4233791568047278031888075)
              ·
                refine ⟨6350687352070917047832113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233791568047278031888075 6350687352070917047832113)
                ·
                  refine ⟨4763015514053187785874085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6350687352070917047832113 4763015514053187785874085)
                  ·
                    refine ⟨893065408884972709851391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763015514053187785874085 893065408884972709851391)
                    ·
                      rfl

theorem cell22_2608858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_2608858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608858 prefixEnd_2608858 := by exact prefixLift 2608858
  have htrace : WordTrace (prefixWord ++ tailWord_2608858) baseStart_2608858 baseEnd_2608858 := by
    simpa [prefixWord, tailWord_2608858, baseEnd_2608858] using wordTrace_append hprefix tailTrace_2608858
  have hstable : (prefixWord ++ tailWord_2608858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608858).length < 2 ^ (prefixWord ++ tailWord_2608858).sum := by decide
  have hdescent : baseEnd_2608858 < baseStart_2608858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608922 : List Nat := [3, 1, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_2608922 : Nat := 118140960795 + 2608922 * 2 ^ 59
def prefixEnd_2608922 : Nat := 4983230072969 + 3 ^ 40 * 2608922 * 2
def baseEnd_2608922 : Nat := 893087317392897876251195

theorem tailTrace_2608922 : CollatzResearch.WordTrace tailWord_2608922 prefixEnd_2608922 893087317392897876251195 := by
  unfold tailWord_2608922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23788800663582159312299255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63436801769552424832798013 23788800663582159312299255)
  ·
    refine ⟨35683200995373238968448883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23788800663582159312299255 35683200995373238968448883)
    ·
      refine ⟨53524801493059858452673325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35683200995373238968448883 53524801493059858452673325)
      ·
        refine ⟨20071800559897446919752497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53524801493059858452673325 20071800559897446919752497)
        ·
          refine ⟨15053850419923085189814373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20071800559897446919752497 15053850419923085189814373)
          ·
            refine ⟨2822596953735578473090195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15053850419923085189814373 2822596953735578473090195)
            ·
              refine ⟨4233895430603367709635293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822596953735578473090195 4233895430603367709635293)
              ·
                refine ⟨1587710786476262891113235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4233895430603367709635293 1587710786476262891113235)
                ·
                  refine ⟨2381566179714394336669853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587710786476262891113235 2381566179714394336669853)
                  ·
                    refine ⟨893087317392897876251195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381566179714394336669853 893087317392897876251195)
                    ·
                      rfl

theorem cell22_2608922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_2608922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608922 prefixEnd_2608922 := by exact prefixLift 2608922
  have htrace : WordTrace (prefixWord ++ tailWord_2608922) baseStart_2608922 baseEnd_2608922 := by
    simpa [prefixWord, tailWord_2608922, baseEnd_2608922] using wordTrace_append hprefix tailTrace_2608922
  have hstable : (prefixWord ++ tailWord_2608922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608922).length < 2 ^ (prefixWord ++ tailWord_2608922).sum := by decide
  have hdescent : baseEnd_2608922 < baseStart_2608922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2608978 : List Nat := [3, 2, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2608978 : Nat := 118140960795 + 2608978 * 2 ^ 59
def prefixEnd_2608978 : Nat := 4983230072969 + 3 ^ 40 * 2608978 * 2
def baseEnd_2608978 : Nat := 893106487337332396851023

theorem tailTrace_2608978 : CollatzResearch.WordTrace tailWord_2608978 prefixEnd_2608978 893106487337332396851023 := by
  unfold tailWord_2608978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789311285531439703308897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63438163428083839208823725 23789311285531439703308897)
  ·
    refine ⟨17841983464148579777481673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23789311285531439703308897 17841983464148579777481673)
    ·
      refine ⟨13381487598111434833111255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17841983464148579777481673 13381487598111434833111255)
      ·
        refine ⟨20072231397167152249666883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13381487598111434833111255 20072231397167152249666883)
        ·
          refine ⟨30108347095750728374500325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20072231397167152249666883 30108347095750728374500325)
          ·
            refine ⟨5645315080453261570218811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30108347095750728374500325 5645315080453261570218811)
            ·
              refine ⟨8467972620679892355328217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645315080453261570218811 8467972620679892355328217)
              ·
                refine ⟨6350979465509919266496163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8467972620679892355328217 6350979465509919266496163)
                ·
                  refine ⟨9526469198264878899744245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6350979465509919266496163 9526469198264878899744245)
                  ·
                    refine ⟨893106487337332396851023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9526469198264878899744245 893106487337332396851023)
                    ·
                      rfl

theorem cell22_2608978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2608978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2608978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2608978 prefixEnd_2608978 := by exact prefixLift 2608978
  have htrace : WordTrace (prefixWord ++ tailWord_2608978) baseStart_2608978 baseEnd_2608978 := by
    simpa [prefixWord, tailWord_2608978, baseEnd_2608978] using wordTrace_append hprefix tailTrace_2608978
  have hstable : (prefixWord ++ tailWord_2608978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2608978).length < 2 ^ (prefixWord ++ tailWord_2608978).sum := by decide
  have hdescent : baseEnd_2608978 < baseStart_2608978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2608978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609021 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2609021 : Nat := 118140960795 + 2609021 * 2 ^ 59
def prefixEnd_2609021 : Nat := 4983230072969 + 3 ^ 40 * 2609021 * 2
def baseEnd_2609021 : Nat := 893121207116094618025891

theorem tailTrace_2609021 : CollatzResearch.WordTrace tailWord_2609021 prefixEnd_2609021 893121207116094618025891 := by
  unfold tailWord_2609021
  simp only [CollatzResearch.WordTrace]
  refine ⟨95158813480969977157050917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63439208987313318104700611 95158813480969977157050917)
  ·
    refine ⟨17842277527681870716947047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95158813480969977157050917 17842277527681870716947047)
    ·
      refine ⟨26763416291522806075420571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17842277527681870716947047 26763416291522806075420571)
      ·
        refine ⟨40145124437284209113130857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26763416291522806075420571 40145124437284209113130857)
        ·
          refine ⟨30108843327963156834848143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40145124437284209113130857 30108843327963156834848143)
          ·
            refine ⟨45163264991944735252272215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30108843327963156834848143 45163264991944735252272215)
            ·
              refine ⟨67744897487917102878408323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45163264991944735252272215 67744897487917102878408323)
              ·
                refine ⟨101617346231875654317612485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67744897487917102878408323 101617346231875654317612485)
                ·
                  refine ⟨19053252418476685184552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101617346231875654317612485 19053252418476685184552341)
                  ·
                    refine ⟨893121207116094618025891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19053252418476685184552341 893121207116094618025891)
                    ·
                      rfl

theorem cell22_2609021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2609021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609021 prefixEnd_2609021 := by exact prefixLift 2609021
  have htrace : WordTrace (prefixWord ++ tailWord_2609021) baseStart_2609021 baseEnd_2609021 := by
    simpa [prefixWord, tailWord_2609021, baseEnd_2609021] using wordTrace_append hprefix tailTrace_2609021
  have hstable : (prefixWord ++ tailWord_2609021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609021).length < 2 ^ (prefixWord ++ tailWord_2609021).sum := by decide
  have hdescent : baseEnd_2609021 < baseStart_2609021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609036 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_2609036 : Nat := 118140960795 + 2609036 * 2 ^ 59
def prefixEnd_2609036 : Nat := 4983230072969 + 3 ^ 40 * 2609036 * 2
def baseEnd_2609036 : Nat := 297708780640879859633615

theorem tailTrace_2609036 : CollatzResearch.WordTrace tailWord_2609036 prefixEnd_2609036 297708780640879859633615 := by
  unfold tailWord_2609036
  simp only [CollatzResearch.WordTrace]
  refine ⟨47579680287957817359423481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63439573717277089812564641 47579680287957817359423481)
  ·
    refine ⟨35684760215968363019567611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47579680287957817359423481 35684760215968363019567611)
    ·
      refine ⟨53527140323952544529351417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35684760215968363019567611 53527140323952544529351417)
      ·
        refine ⟨40145355242964408397013563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53527140323952544529351417 40145355242964408397013563)
        ·
          refine ⟨60218032864446612595520345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40145355242964408397013563 60218032864446612595520345)
          ·
            refine ⟨45163524648334959446640259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60218032864446612595520345 45163524648334959446640259)
            ·
              refine ⟨67745286972502439169960389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45163524648334959446640259 67745286972502439169960389)
              ·
                refine ⟨12702241307344207344367573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67745286972502439169960389 12702241307344207344367573)
                ·
                  refine ⟨297708780640879859633615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12702241307344207344367573 297708780640879859633615)
                  ·
                    rfl

theorem cell22_2609036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_2609036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609036 prefixEnd_2609036 := by exact prefixLift 2609036
  have htrace : WordTrace (prefixWord ++ tailWord_2609036) baseStart_2609036 baseEnd_2609036 := by
    simpa [prefixWord, tailWord_2609036, baseEnd_2609036] using wordTrace_append hprefix tailTrace_2609036
  have hstable : (prefixWord ++ tailWord_2609036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609036).length < 2 ^ (prefixWord ++ tailWord_2609036).sum := by decide
  have hdescent : baseEnd_2609036 < baseStart_2609036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609040 : List Nat := [2, 1, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_2609040 : Nat := 118140960795 + 2609040 * 2 ^ 59
def prefixEnd_2609040 : Nat := 4983230072969 + 3 ^ 40 * 2609040 * 2
def baseEnd_2609040 : Nat := 893127711204384901800833

theorem tailTrace_2609040 : CollatzResearch.WordTrace tailWord_2609040 prefixEnd_2609040 893127711204384901800833 := by
  unfold tailWord_2609040
  simp only [CollatzResearch.WordTrace]
  refine ⟨47579753233950571700996287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63439670978600762267995049 47579753233950571700996287)
  ·
    refine ⟨71369629850925857551494431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47579753233950571700996287 71369629850925857551494431)
    ·
      refine ⟨107054444776388786327241647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71369629850925857551494431 107054444776388786327241647)
      ·
        refine ⟨160581667164583179490862471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107054444776388786327241647 160581667164583179490862471)
        ·
          refine ⟨240872500746874769236293707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160581667164583179490862471 240872500746874769236293707)
          ·
            refine ⟨361308751120312153854440561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240872500746874769236293707 361308751120312153854440561)
            ·
              refine ⟨270981563340234115390830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361308751120312153854440561 270981563340234115390830421)
              ·
                refine ⟨1587782597696684269868147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 270981563340234115390830421 1587782597696684269868147)
                ·
                  refine ⟨2381673896545026404802221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587782597696684269868147 2381673896545026404802221)
                  ·
                    refine ⟨893127711204384901800833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381673896545026404802221 893127711204384901800833)
                    ·
                      rfl

theorem cell22_2609040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_2609040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609040 prefixEnd_2609040 := by exact prefixLift 2609040
  have htrace : WordTrace (prefixWord ++ tailWord_2609040) baseStart_2609040 baseEnd_2609040 := by
    simpa [prefixWord, tailWord_2609040, baseEnd_2609040] using wordTrace_append hprefix tailTrace_2609040
  have hstable : (prefixWord ++ tailWord_2609040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609040).length < 2 ^ (prefixWord ++ tailWord_2609040).sum := by decide
  have hdescent : baseEnd_2609040 < baseStart_2609040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609053 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 7]
def baseStart_2609053 : Nat := 118140960795 + 2609053 * 2 ^ 59
def prefixEnd_2609053 : Nat := 4983230072969 + 3 ^ 40 * 2609053 * 2
def baseEnd_2609053 : Nat := 297710720456685733741931

theorem tailTrace_2609053 : CollatzResearch.WordTrace tailWord_2609053 prefixEnd_2609053 297710720456685733741931 := by
  unfold tailWord_2609053
  simp only [CollatzResearch.WordTrace]
  refine ⟨95159980616854046622215813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63439987077902697748143875 95159980616854046622215813)
  ·
    refine ⟨17842496365660133741665465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95159980616854046622215813 17842496365660133741665465)
    ·
      refine ⟨13381872274245100306249099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17842496365660133741665465 13381872274245100306249099)
      ·
        refine ⟨20072808411367650459373649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13381872274245100306249099 20072808411367650459373649)
        ·
          refine ⟨15054606308525737844530237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20072808411367650459373649 15054606308525737844530237)
          ·
            refine ⟨5645477365697151691698839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15054606308525737844530237 5645477365697151691698839)
            ·
              refine ⟨8468216048545727537548259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5645477365697151691698839 8468216048545727537548259)
              ·
                refine ⟨12702324072818591306322389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468216048545727537548259 12702324072818591306322389)
                ·
                  refine ⟨297710720456685733741931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12702324072818591306322389 297710720456685733741931)
                  ·
                    rfl

theorem cell22_2609053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_2609053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609053 prefixEnd_2609053 := by exact prefixLift 2609053
  have htrace : WordTrace (prefixWord ++ tailWord_2609053) baseStart_2609053 baseEnd_2609053 := by
    simpa [prefixWord, tailWord_2609053, baseEnd_2609053] using wordTrace_append hprefix tailTrace_2609053
  have hstable : (prefixWord ++ tailWord_2609053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609053).length < 2 ^ (prefixWord ++ tailWord_2609053).sum := by decide
  have hdescent : baseEnd_2609053 < baseStart_2609053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609057 : List Nat := [1, 2, 3, 4, 2, 1, 2, 1, 3, 3]
def baseStart_2609057 : Nat := 118140960795 + 2609057 * 2 ^ 59
def prefixEnd_2609057 : Nat := 4983230072969 + 3 ^ 40 * 2609057 * 2
def baseEnd_2609057 : Nat := 893133530651802524125781

theorem tailTrace_2609057 : CollatzResearch.WordTrace tailWord_2609057 prefixEnd_2609057 893133530651802524125781 := by
  unfold tailWord_2609057
  simp only [CollatzResearch.WordTrace]
  refine ⟨95160126508839555305361425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63440084339226370203574283 95160126508839555305361425)
  ·
    refine ⟨71370094881629666479021069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95160126508839555305361425 71370094881629666479021069)
    ·
      refine ⟨26763785580611124929632901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71370094881629666479021069 26763785580611124929632901)
      ·
        refine ⟨5018209796364585924306169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26763785580611124929632901 5018209796364585924306169)
        ·
          refine ⟨3763657347273439443229627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5018209796364585924306169 3763657347273439443229627)
          ·
            refine ⟨5645486020910159164844441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3763657347273439443229627 5645486020910159164844441)
            ·
              refine ⟨4234114515682619373633331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5645486020910159164844441 4234114515682619373633331)
              ·
                refine ⟨6351171773523929060449997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234114515682619373633331 6351171773523929060449997)
                ·
                  refine ⟨2381689415071473397668749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6351171773523929060449997 2381689415071473397668749)
                  ·
                    refine ⟨893133530651802524125781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381689415071473397668749 893133530651802524125781)
                    ·
                      rfl

theorem cell22_2609057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_2609057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609057 prefixEnd_2609057 := by exact prefixLift 2609057
  have htrace : WordTrace (prefixWord ++ tailWord_2609057) baseStart_2609057 baseEnd_2609057 := by
    simpa [prefixWord, tailWord_2609057, baseEnd_2609057] using wordTrace_append hprefix tailTrace_2609057
  have hstable : (prefixWord ++ tailWord_2609057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609057).length < 2 ^ (prefixWord ++ tailWord_2609057).sum := by decide
  have hdescent : baseEnd_2609057 < baseStart_2609057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609083 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 1, 4]
def baseStart_2609083 : Nat := 118140960795 + 2609083 * 2 ^ 59
def prefixEnd_2609083 : Nat := 4983230072969 + 3 ^ 40 * 2609083 * 2
def baseEnd_2609083 : Nat := 893142430983147122975701

theorem tailTrace_2609083 : CollatzResearch.WordTrace tailWord_2609083 prefixEnd_2609083 893142430983147122975701 := by
  unfold tailWord_2609083
  simp only [CollatzResearch.WordTrace]
  refine ⟨95161074806745361745807903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63440716537830241163871935 95161074806745361745807903)
  ·
    refine ⟨142741612210118042618711855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95161074806745361745807903 142741612210118042618711855)
    ·
      refine ⟨214112418315177063928067783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142741612210118042618711855 214112418315177063928067783)
      ·
        refine ⟨321168627472765595892101675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214112418315177063928067783 321168627472765595892101675)
        ·
          refine ⟨481752941209148393838152513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321168627472765595892101675 481752941209148393838152513)
          ·
            refine ⟨361314705906861295378614385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481752941209148393838152513 361314705906861295378614385)
            ·
              refine ⟨270986029430145971533960789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361314705906861295378614385 270986029430145971533960789)
              ·
                refine ⟨3175617532384523103913603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 270986029430145971533960789 3175617532384523103913603)
                ·
                  refine ⟨4763426298576784655870405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175617532384523103913603 4763426298576784655870405)
                  ·
                    refine ⟨893142430983147122975701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763426298576784655870405 893142430983147122975701)
                    ·
                      rfl

theorem cell22_2609083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 4].length) (baseStart_2609083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609083 prefixEnd_2609083 := by exact prefixLift 2609083
  have htrace : WordTrace (prefixWord ++ tailWord_2609083) baseStart_2609083 baseEnd_2609083 := by
    simpa [prefixWord, tailWord_2609083, baseEnd_2609083] using wordTrace_append hprefix tailTrace_2609083
  have hstable : (prefixWord ++ tailWord_2609083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609083).length < 2 ^ (prefixWord ++ tailWord_2609083).sum := by decide
  have hdescent : baseEnd_2609083 < baseStart_2609083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609100 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_2609100 : Nat := 118140960795 + 2609100 * 2 ^ 59
def prefixEnd_2609100 : Nat := 4983230072969 + 3 ^ 40 * 2609100 * 2
def baseEnd_2609100 : Nat := 893148250430564745300649

theorem tailTrace_2609100 : CollatzResearch.WordTrace tailWord_2609100 prefixEnd_2609100 893148250430564745300649 := by
  unfold tailWord_2609100
  simp only [CollatzResearch.WordTrace]
  refine ⟨47580847423841886824588377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63441129898455849099451169 47580847423841886824588377)
  ·
    refine ⟨35685635567881415118441283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47580847423841886824588377 35685635567881415118441283)
    ·
      refine ⟨53528453351822122677661925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35685635567881415118441283 53528453351822122677661925)
      ·
        refine ⟨10036585003466648002061611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53528453351822122677661925 10036585003466648002061611)
        ·
          refine ⟨15054877505199972003092417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036585003466648002061611 15054877505199972003092417)
          ·
            refine ⟨11291158128899979002319313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15054877505199972003092417 11291158128899979002319313)
            ·
              refine ⟨8468368596674984251739485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11291158128899979002319313 8468368596674984251739485)
              ·
                refine ⟨3175638223753119094402307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8468368596674984251739485 3175638223753119094402307)
                ·
                  refine ⟨4763457335629678641603461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175638223753119094402307 4763457335629678641603461)
                  ·
                    refine ⟨893148250430564745300649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763457335629678641603461 893148250430564745300649)
                    ·
                      rfl

theorem cell22_2609100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_2609100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609100 prefixEnd_2609100 := by exact prefixLift 2609100
  have htrace : WordTrace (prefixWord ++ tailWord_2609100) baseStart_2609100 baseEnd_2609100 := by
    simpa [prefixWord, tailWord_2609100, baseEnd_2609100] using wordTrace_append hprefix tailTrace_2609100
  have hstable : (prefixWord ++ tailWord_2609100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609100).length < 2 ^ (prefixWord ++ tailWord_2609100).sum := by decide
  have hdescent : baseEnd_2609100 < baseStart_2609100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2609128 : Nat := 118140960795 + 2609128 * 2 ^ 59
def prefixEnd_2609128 : Nat := 4983230072969 + 3 ^ 40 * 2609128 * 2
def baseEnd_2609128 : Nat := 893157835402782005600563

theorem tailTrace_2609128 : CollatzResearch.WordTrace tailWord_2609128 prefixEnd_2609128 893157835402782005600563 := by
  unfold tailWord_2609128
  simp only [CollatzResearch.WordTrace]
  refine ⟨47581358045791167215598019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63441810727721556287464025 47581358045791167215598019)
  ·
    refine ⟨71372037068686750823397029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47581358045791167215598019 71372037068686750823397029)
    ·
      refine ⟨13382256950378765779386943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71372037068686750823397029 13382256950378765779386943)
      ·
        refine ⟨20073385425568148669080415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13382256950378765779386943 20073385425568148669080415)
        ·
          refine ⟨30110078138352223003620623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20073385425568148669080415 30110078138352223003620623)
          ·
            refine ⟨45165117207528334505430935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30110078138352223003620623 45165117207528334505430935)
            ·
              refine ⟨67747675811292501758146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45165117207528334505430935 67747675811292501758146403)
              ·
                refine ⟨101621513716938752637219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67747675811292501758146403 101621513716938752637219605)
                ·
                  refine ⟨4763508455481504029869669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 101621513716938752637219605 4763508455481504029869669)
                  ·
                    refine ⟨893157835402782005600563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763508455481504029869669 893157835402782005600563)
                    ·
                      rfl

theorem cell22_2609128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2609128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609128 prefixEnd_2609128 := by exact prefixLift 2609128
  have htrace : WordTrace (prefixWord ++ tailWord_2609128) baseStart_2609128 baseEnd_2609128 := by
    simpa [prefixWord, tailWord_2609128, baseEnd_2609128] using wordTrace_append hprefix tailTrace_2609128
  have hstable : (prefixWord ++ tailWord_2609128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609128).length < 2 ^ (prefixWord ++ tailWord_2609128).sum := by decide
  have hdescent : baseEnd_2609128 < baseStart_2609128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609145 : List Nat := [1, 2, 1, 3, 1, 5, 2, 1, 2, 4]
def baseStart_2609145 : Nat := 118140960795 + 2609145 * 2 ^ 59
def prefixEnd_2609145 : Nat := 4983230072969 + 3 ^ 40 * 2609145 * 2
def baseEnd_2609145 : Nat := 893163654850199627925511

theorem tailTrace_2609145 : CollatzResearch.WordTrace tailWord_2609145 prefixEnd_2609145 893163654850199627925511 := by
  unfold tailWord_2609145
  simp only [CollatzResearch.WordTrace]
  refine ⟨95163336132520746334564889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63442224088347164223043259 95163336132520746334564889)
  ·
    refine ⟨71372502099390559750923667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95163336132520746334564889 71372502099390559750923667)
    ·
      refine ⟨107058753149085839626385501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71372502099390559750923667 107058753149085839626385501)
      ·
        refine ⟨40147032430907189859894563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107058753149085839626385501 40147032430907189859894563)
        ·
          refine ⟨60220548646360784789841845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40147032430907189859894563 60220548646360784789841845)
          ·
            refine ⟨5645676435596323574047673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60220548646360784789841845 5645676435596323574047673)
            ·
              refine ⟨4234257326697242680535755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5645676435596323574047673 4234257326697242680535755)
              ·
                refine ⟨6351385990045864020803633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234257326697242680535755 6351385990045864020803633)
                ·
                  refine ⟨4763539492534398015602725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6351385990045864020803633 4763539492534398015602725)
                  ·
                    refine ⟨893163654850199627925511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763539492534398015602725 893163654850199627925511)
                    ·
                      rfl

theorem cell22_2609145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_2609145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609145 prefixEnd_2609145 := by exact prefixLift 2609145
  have htrace : WordTrace (prefixWord ++ tailWord_2609145) baseStart_2609145 baseEnd_2609145 := by
    simpa [prefixWord, tailWord_2609145, baseEnd_2609145] using wordTrace_append hprefix tailTrace_2609145
  have hstable : (prefixWord ++ tailWord_2609145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609145).length < 2 ^ (prefixWord ++ tailWord_2609145).sum := by decide
  have hdescent : baseEnd_2609145 < baseStart_2609145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609222 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2609222 : Nat := 118140960795 + 2609222 * 2 ^ 59
def prefixEnd_2609222 : Nat := 4983230072969 + 3 ^ 40 * 2609222 * 2
def baseEnd_2609222 : Nat := 297730004507932364583425

theorem tailTrace_2609222 : CollatzResearch.WordTrace tailWord_2609222 prefixEnd_2609222 297730004507932364583425 := by
  unfold tailWord_2609222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973942017288805890159935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63444096368827858990078613 2973942017288805890159935)
  ·
    refine ⟨4460913025933208835239903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2973942017288805890159935 4460913025933208835239903)
    ·
      refine ⟨6691369538899813252859855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4460913025933208835239903 6691369538899813252859855)
      ·
        refine ⟨10037054308349719879289783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6691369538899813252859855 10037054308349719879289783)
        ·
          refine ⟨15055581462524579818934675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10037054308349719879289783 15055581462524579818934675)
          ·
            refine ⟨22583372193786869728402013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15055581462524579818934675 22583372193786869728402013)
            ·
              refine ⟨8468764572670076148150755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22583372193786869728402013 8468764572670076148150755)
              ·
                refine ⟨12703146859005114222226133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8468764572670076148150755 12703146859005114222226133)
                ·
                  refine ⟨297730004507932364583425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12703146859005114222226133 297730004507932364583425)
                  ·
                    rfl

theorem cell22_2609222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2609222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609222 prefixEnd_2609222 := by exact prefixLift 2609222
  have htrace : WordTrace (prefixWord ++ tailWord_2609222) baseStart_2609222 baseEnd_2609222 := by
    simpa [prefixWord, tailWord_2609222, baseEnd_2609222] using wordTrace_append hprefix tailTrace_2609222
  have hstable : (prefixWord ++ tailWord_2609222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609222).length < 2 ^ (prefixWord ++ tailWord_2609222).sum := by decide
  have hdescent : baseEnd_2609222 < baseStart_2609222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609265 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 6, 3]
def baseStart_2609265 : Nat := 118140960795 + 2609265 * 2 ^ 59
def prefixEnd_2609265 : Nat := 4983230072969 + 3 ^ 40 * 2609265 * 2
def baseEnd_2609265 : Nat := 893204733302559314925143

theorem tailTrace_2609265 : CollatzResearch.WordTrace tailWord_2609265 prefixEnd_2609265 893204733302559314925143 := by
  unfold tailWord_2609265
  simp only [CollatzResearch.WordTrace]
  refine ⟨95167712892086006828933249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63445141928057337885955499 95167712892086006828933249)
  ·
    refine ⟨71375784669064505121699937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95167712892086006828933249 71375784669064505121699937)
    ·
      refine ⟨53531838501798378841274953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71375784669064505121699937 53531838501798378841274953)
      ·
        refine ⟨40148878876348784130956215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53531838501798378841274953 40148878876348784130956215)
        ·
          refine ⟨60223318314523176196434323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40148878876348784130956215 60223318314523176196434323)
          ·
            refine ⟨90334977471784764294651485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60223318314523176196434323 90334977471784764294651485)
            ·
              refine ⟨33875616551919286610494307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90334977471784764294651485 33875616551919286610494307)
              ·
                refine ⟨50813424827878929915741461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33875616551919286610494307 50813424827878929915741461)
                ·
                  refine ⟨2381879288806824839800381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50813424827878929915741461 2381879288806824839800381)
                  ·
                    refine ⟨893204733302559314925143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2381879288806824839800381 893204733302559314925143)
                    ·
                      rfl

theorem cell22_2609265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_2609265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609265 prefixEnd_2609265 := by exact prefixLift 2609265
  have htrace : WordTrace (prefixWord ++ tailWord_2609265) baseStart_2609265 baseEnd_2609265 := by
    simpa [prefixWord, tailWord_2609265, baseEnd_2609265] using wordTrace_append hprefix tailTrace_2609265
  have hstable : (prefixWord ++ tailWord_2609265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609265).length < 2 ^ (prefixWord ++ tailWord_2609265).sum := by decide
  have hdescent : baseEnd_2609265 < baseStart_2609265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609284 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_2609284 : Nat := 118140960795 + 2609284 * 2 ^ 59
def prefixEnd_2609284 : Nat := 4983230072969 + 3 ^ 40 * 2609284 * 2
def baseEnd_2609284 : Nat := 297737079130283199566695

theorem tailTrace_2609284 : CollatzResearch.WordTrace tailWord_2609284 prefixEnd_2609284 297737079130283199566695 := by
  unfold tailWord_2609284
  simp only [CollatzResearch.WordTrace]
  refine ⟨47584202939508586536937453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63445603919344782049249937 47584202939508586536937453)
  ·
    refine ⟨17844076102315719951351545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47584202939508586536937453 17844076102315719951351545)
    ·
      refine ⟨13383057076736789963513659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17844076102315719951351545 13383057076736789963513659)
      ·
        refine ⟨20074585615105184945270489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13383057076736789963513659 20074585615105184945270489)
        ·
          refine ⟨15055939211328888708952867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20074585615105184945270489 15055939211328888708952867)
          ·
            refine ⟨22583908816993333063429301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15055939211328888708952867 22583908816993333063429301)
            ·
              refine ⟨2117241451593124974696497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22583908816993333063429301 2117241451593124974696497)
              ·
                refine ⟨1587931088694843731022373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2117241451593124974696497 1587931088694843731022373)
                ·
                  refine ⟨297737079130283199566695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1587931088694843731022373 297737079130283199566695)
                  ·
                    rfl

theorem cell22_2609284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_2609284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609284 prefixEnd_2609284 := by exact prefixLift 2609284
  have htrace : WordTrace (prefixWord ++ tailWord_2609284) baseStart_2609284 baseEnd_2609284 := by
    simpa [prefixWord, tailWord_2609284, baseEnd_2609284] using wordTrace_append hprefix tailTrace_2609284
  have hstable : (prefixWord ++ tailWord_2609284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609284).length < 2 ^ (prefixWord ++ tailWord_2609284).sum := by decide
  have hdescent : baseEnd_2609284 < baseStart_2609284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609314 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2609314 : Nat := 118140960795 + 2609314 * 2 ^ 59
def prefixEnd_2609314 : Nat := 4983230072969 + 3 ^ 40 * 2609314 * 2
def baseEnd_2609314 : Nat := 893221507003939520449993

theorem tailTrace_2609314 : CollatzResearch.WordTrace tailWord_2609314 prefixEnd_2609314 893221507003939520449993 := by
  unfold tailWord_2609314
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792375017227122049366749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63446333379272325464977997 23792375017227122049366749)
  ·
    refine ⟨8922140631460170768512531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23792375017227122049366749 8922140631460170768512531)
    ·
      refine ⟨13383210947190256152768797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8922140631460170768512531 13383210947190256152768797)
      ·
        refine ⟨5018704105196346057288299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13383210947190256152768797 5018704105196346057288299)
        ·
          refine ⟨7528056157794519085932449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018704105196346057288299 7528056157794519085932449)
          ·
            refine ⟨5646042118345889314449337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7528056157794519085932449 5646042118345889314449337)
            ·
              refine ⟨4234531588759416985837003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646042118345889314449337 4234531588759416985837003)
              ·
                refine ⟨6351797383139125478755505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234531588759416985837003 6351797383139125478755505)
                ·
                  refine ⟨4763848037354344109066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6351797383139125478755505 4763848037354344109066629)
                  ·
                    refine ⟨893221507003939520449993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763848037354344109066629 893221507003939520449993)
                    ·
                      rfl

theorem cell22_2609314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2609314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609314 prefixEnd_2609314 := by exact prefixLift 2609314
  have htrace : WordTrace (prefixWord ++ tailWord_2609314) baseStart_2609314 baseEnd_2609314 := by
    simpa [prefixWord, tailWord_2609314, baseEnd_2609314] using wordTrace_append hprefix tailTrace_2609314
  have hstable : (prefixWord ++ tailWord_2609314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609314).length < 2 ^ (prefixWord ++ tailWord_2609314).sum := by decide
  have hdescent : baseEnd_2609314 < baseStart_2609314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609346 : List Nat := [3, 5, 1, 1, 1, 3, 1, 7]
def baseStart_2609346 : Nat := 118140960795 + 2609346 * 2 ^ 59
def prefixEnd_2609346 : Nat := 4983230072969 + 3 ^ 40 * 2609346 * 2
def baseEnd_2609346 : Nat := 99248051250878011516655

theorem tailTrace_2609346 : CollatzResearch.WordTrace tailWord_2609346 prefixEnd_2609346 99248051250878011516655 := by
  unfold tailWord_2609346
  simp only [CollatzResearch.WordTrace]
  refine ⟨23792666801198139415657973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63447111469861705108421261 23792666801198139415657973)
  ·
    refine ⟨2230562512612325570217935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23792666801198139415657973 2230562512612325570217935)
    ·
      refine ⟨3345843768918488355326903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230562512612325570217935 3345843768918488355326903)
      ·
        refine ⟨5018765653377732532990355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345843768918488355326903 5018765653377732532990355)
        ·
          refine ⟨7528148480066598799485533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5018765653377732532990355 7528148480066598799485533)
          ·
            refine ⟨2823055680024974549807075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7528148480066598799485533 2823055680024974549807075)
            ·
              refine ⟨4234583520037461824710613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823055680024974549807075 4234583520037461824710613)
              ·
                refine ⟨99248051250878011516655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4234583520037461824710613 99248051250878011516655)
                ·
                  rfl

theorem cell22_2609346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_2609346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609346 prefixEnd_2609346 := by exact prefixLift 2609346
  have htrace : WordTrace (prefixWord ++ tailWord_2609346) baseStart_2609346 baseEnd_2609346 := by
    simpa [prefixWord, tailWord_2609346, baseEnd_2609346] using wordTrace_append hprefix tailTrace_2609346
  have hstable : (prefixWord ++ tailWord_2609346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609346).length < 2 ^ (prefixWord ++ tailWord_2609346).sum := by decide
  have hdescent : baseEnd_2609346 < baseStart_2609346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609355 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 2, 5]
def baseStart_2609355 : Nat := 118140960795 + 2609355 * 2 ^ 59
def prefixEnd_2609355 : Nat := 4983230072969 + 3 ^ 40 * 2609355 * 2
def baseEnd_2609355 : Nat := 893235542141829080174867

theorem tailTrace_2609355 : CollatzResearch.WordTrace tailWord_2609355 prefixEnd_2609355 893235542141829080174867 := by
  unfold tailWord_2609355
  simp only [CollatzResearch.WordTrace]
  refine ⟨95170995461759952199709519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63447330307839968133139679 95170995461759952199709519)
  ·
    refine ⟨142756493192639928299564279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95170995461759952199709519 142756493192639928299564279)
    ·
      refine ⟨214134739788959892449346419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142756493192639928299564279 214134739788959892449346419)
      ·
        refine ⟨321202109683439838674019629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214134739788959892449346419 321202109683439838674019629)
        ·
          refine ⟨120450791131289939502757361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321202109683439838674019629 120450791131289939502757361)
          ·
            refine ⟨90338093348467454627068021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120450791131289939502757361 90338093348467454627068021)
            ·
              refine ⟨8469196251418823871287627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90338093348467454627068021 8469196251418823871287627)
              ·
                refine ⟨12703794377128235806931441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8469196251418823871287627 12703794377128235806931441)
                ·
                  refine ⟨9527845782846176855198581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12703794377128235806931441 9527845782846176855198581)
                  ·
                    refine ⟨893235542141829080174867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9527845782846176855198581 893235542141829080174867)
                    ·
                      rfl

theorem cell22_2609355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_2609355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609355 prefixEnd_2609355 := by exact prefixLift 2609355
  have htrace : WordTrace (prefixWord ++ tailWord_2609355) baseStart_2609355 baseEnd_2609355 := by
    simpa [prefixWord, tailWord_2609355, baseEnd_2609355] using wordTrace_append hprefix tailTrace_2609355
  have hstable : (prefixWord ++ tailWord_2609355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609355).length < 2 ^ (prefixWord ++ tailWord_2609355).sum := by decide
  have hdescent : baseEnd_2609355 < baseStart_2609355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609387 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 1, 4]
def baseStart_2609387 : Nat := 118140960795 + 2609387 * 2 ^ 59
def prefixEnd_2609387 : Nat := 4983230072969 + 3 ^ 40 * 2609387 * 2
def baseEnd_2609387 : Nat := 893246496395791663374769

theorem tailTrace_2609387 : CollatzResearch.WordTrace tailWord_2609387 prefixEnd_2609387 893246496395791663374769 := by
  unfold tailWord_2609387
  simp only [CollatzResearch.WordTrace]
  refine ⟨95172162597644021664874415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63448108398429347776582943 95172162597644021664874415)
  ·
    refine ⟨142758243896466032497311623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95172162597644021664874415 142758243896466032497311623)
    ·
      refine ⟨214137365844699048745967435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142758243896466032497311623 214137365844699048745967435)
      ·
        refine ⟨321206048767048573118951153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214137365844699048745967435 321206048767048573118951153)
        ·
          refine ⟨240904536575286429839213365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321206048767048573118951153 240904536575286429839213365)
          ·
            refine ⟨22584800303933102797426253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 240904536575286429839213365 22584800303933102797426253)
            ·
              refine ⟨8469300113974913549034845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22584800303933102797426253 8469300113974913549034845)
              ·
                refine ⟨3175987542740592580888067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8469300113974913549034845 3175987542740592580888067)
                ·
                  refine ⟨4763981314110888871332101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175987542740592580888067 4763981314110888871332101)
                  ·
                    refine ⟨893246496395791663374769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4763981314110888871332101 893246496395791663374769)
                    ·
                      rfl

theorem cell22_2609387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 1, 4].length) (baseStart_2609387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609387 prefixEnd_2609387 := by exact prefixLift 2609387
  have htrace : WordTrace (prefixWord ++ tailWord_2609387) baseStart_2609387 baseEnd_2609387 := by
    simpa [prefixWord, tailWord_2609387, baseEnd_2609387] using wordTrace_append hprefix tailTrace_2609387
  have hstable : (prefixWord ++ tailWord_2609387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609387).length < 2 ^ (prefixWord ++ tailWord_2609387).sum := by decide
  have hdescent : baseEnd_2609387 < baseStart_2609387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609400 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_2609400 : Nat := 118140960795 + 2609400 * 2 ^ 59
def prefixEnd_2609400 : Nat := 4983230072969 + 3 ^ 40 * 2609400 * 2
def baseEnd_2609400 : Nat := 893250946561463962799729

theorem tailTrace_2609400 : CollatzResearch.WordTrace tailWord_2609400 prefixEnd_2609400 893250946561463962799729 := by
  unfold tailWord_2609400
  simp only [CollatzResearch.WordTrace]
  refine ⟨47586318373298462442548827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63448424497731283256731769 47586318373298462442548827)
  ·
    refine ⟨71379477559947693663823241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47586318373298462442548827 71379477559947693663823241)
    ·
      refine ⟨53534608169960770247867431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71379477559947693663823241 53534608169960770247867431)
      ·
        refine ⟨80301912254941155371801147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53534608169960770247867431 80301912254941155371801147)
        ·
          refine ⟨120452868382411733057701721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80301912254941155371801147 120452868382411733057701721)
          ·
            refine ⟨90339651286808799793276291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120452868382411733057701721 90339651286808799793276291)
            ·
              refine ⟨135509476930213199689914437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90339651286808799793276291 135509476930213199689914437)
              ·
                refine ⟨25408026924414974941858957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135509476930213199689914437 25408026924414974941858957)
                ·
                  refine ⟨9528010096655615603197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25408026924414974941858957 9528010096655615603197109)
                  ·
                    refine ⟨893250946561463962799729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9528010096655615603197109 893250946561463962799729)
                    ·
                      rfl

theorem cell22_2609400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_2609400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609400 prefixEnd_2609400 := by exact prefixLift 2609400
  have htrace : WordTrace (prefixWord ++ tailWord_2609400) baseStart_2609400 baseEnd_2609400 := by
    simpa [prefixWord, tailWord_2609400, baseEnd_2609400] using wordTrace_append hprefix tailTrace_2609400
  have hstable : (prefixWord ++ tailWord_2609400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609400).length < 2 ^ (prefixWord ++ tailWord_2609400).sum := by decide
  have hdescent : baseEnd_2609400 < baseStart_2609400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609402 : List Nat := [3, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_2609402 : Nat := 118140960795 + 2609402 * 2 ^ 59
def prefixEnd_2609402 : Nat := 4983230072969 + 3 ^ 40 * 2609402 * 2
def baseEnd_2609402 : Nat := 297750543734112208083241

theorem tailTrace_2609402 : CollatzResearch.WordTrace tailWord_2609402 prefixEnd_2609402 297750543734112208083241 := by
  unfold tailWord_2609402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23793177423147419806667615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63448473128393119484446973 23793177423147419806667615)
  ·
    refine ⟨35689766134721129710001423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23793177423147419806667615 35689766134721129710001423)
    ·
      refine ⟨53534649202081694565002135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35689766134721129710001423 53534649202081694565002135)
      ·
        refine ⟨80301973803122541847503203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53534649202081694565002135 80301973803122541847503203)
        ·
          refine ⟨120452960704683812771254805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80301973803122541847503203 120452960704683812771254805)
          ·
            refine ⟨5646232533032053723652569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 120452960704683812771254805 5646232533032053723652569)
            ·
              refine ⟨4234674399774040292739427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646232533032053723652569 4234674399774040292739427)
              ·
                refine ⟨6352011599661060439109141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234674399774040292739427 6352011599661060439109141)
                ·
                  refine ⟨297750543734112208083241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6352011599661060439109141 297750543734112208083241)
                  ·
                    rfl

theorem cell22_2609402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_2609402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609402 prefixEnd_2609402 := by exact prefixLift 2609402
  have htrace : WordTrace (prefixWord ++ tailWord_2609402) baseStart_2609402 baseEnd_2609402 := by
    simpa [prefixWord, tailWord_2609402, baseEnd_2609402] using wordTrace_append hprefix tailTrace_2609402
  have hstable : (prefixWord ++ tailWord_2609402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609402).length < 2 ^ (prefixWord ++ tailWord_2609402).sum := by decide
  have hdescent : baseEnd_2609402 < baseStart_2609402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609417 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 1, 5]
def baseStart_2609417 : Nat := 118140960795 + 2609417 * 2 ^ 59
def prefixEnd_2609417 : Nat := 4983230072969 + 3 ^ 40 * 2609417 * 2
def baseEnd_2609417 : Nat := 893256766008881585124677

theorem tailTrace_2609417 : CollatzResearch.WordTrace tailWord_2609417 prefixEnd_2609417 893256766008881585124677 := by
  unfold tailWord_2609417
  simp only [CollatzResearch.WordTrace]
  refine ⟨95173256787535336788466505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63448837858356891192311003 95173256787535336788466505)
  ·
    refine ⟨71379942590651502591349879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95173256787535336788466505 71379942590651502591349879)
    ·
      refine ⟨107069913885977253887024819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71379942590651502591349879 107069913885977253887024819)
      ·
        refine ⟨160604870828965880830537229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107069913885977253887024819 160604870828965880830537229)
        ·
          refine ⟨60226826560862205311451461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160604870828965880830537229 60226826560862205311451461)
          ·
            refine ⟨11292529980161663495897149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60226826560862205311451461 11292529980161663495897149)
            ·
              refine ⟨4234698742560623810961431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11292529980161663495897149 4234698742560623810961431)
              ·
                refine ⟨6352048113840935716442147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234698742560623810961431 6352048113840935716442147)
                ·
                  refine ⟨9528072170761403574663221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6352048113840935716442147 9528072170761403574663221)
                  ·
                    refine ⟨893256766008881585124677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9528072170761403574663221 893256766008881585124677)
                    ·
                      rfl

theorem cell22_2609417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_2609417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609417 prefixEnd_2609417 := by exact prefixLift 2609417
  have htrace : WordTrace (prefixWord ++ tailWord_2609417) baseStart_2609417 baseEnd_2609417 := by
    simpa [prefixWord, tailWord_2609417, baseEnd_2609417] using wordTrace_append hprefix tailTrace_2609417
  have hstable : (prefixWord ++ tailWord_2609417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609417).length < 2 ^ (prefixWord ++ tailWord_2609417).sum := by decide
  have hdescent : baseEnd_2609417 < baseStart_2609417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609432 : List Nat := [2, 1, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_2609432 : Nat := 118140960795 + 2609432 * 2 ^ 59
def prefixEnd_2609432 : Nat := 4983230072969 + 3 ^ 40 * 2609432 * 2
def baseEnd_2609432 : Nat := 893261900815426545999631

theorem tailTrace_2609432 : CollatzResearch.WordTrace tailWord_2609432 prefixEnd_2609432 893261900815426545999631 := by
  unfold tailWord_2609432
  simp only [CollatzResearch.WordTrace]
  refine ⟨47586901941240497175131275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63449202588320662900175033 47586901941240497175131275)
  ·
    refine ⟨71380352911860745762696913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47586901941240497175131275 71380352911860745762696913)
    ·
      refine ⟨53535264683895559322022685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71380352911860745762696913 53535264683895559322022685)
      ·
        refine ⟨20075724256460834745758507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53535264683895559322022685 20075724256460834745758507)
        ·
          refine ⟨30113586384691252118637761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20075724256460834745758507 30113586384691252118637761)
          ·
            refine ⟨22585189788518439088978321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30113586384691252118637761 22585189788518439088978321)
            ·
              refine ⟨16938892341388829316733741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22585189788518439088978321 16938892341388829316733741)
              ·
                refine ⟨6352084628020810993775153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16938892341388829316733741 6352084628020810993775153)
                ·
                  refine ⟨4764063471015608245331365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352084628020810993775153 4764063471015608245331365)
                  ·
                    refine ⟨893261900815426545999631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764063471015608245331365 893261900815426545999631)
                    ·
                      rfl

theorem cell22_2609432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_2609432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609432 prefixEnd_2609432 := by exact prefixLift 2609432
  have htrace : WordTrace (prefixWord ++ tailWord_2609432) baseStart_2609432 baseEnd_2609432 := by
    simpa [prefixWord, tailWord_2609432, baseEnd_2609432] using wordTrace_append hprefix tailTrace_2609432
  have hstable : (prefixWord ++ tailWord_2609432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609432).length < 2 ^ (prefixWord ++ tailWord_2609432).sum := by decide
  have hdescent : baseEnd_2609432 < baseStart_2609432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609453 : List Nat := [1, 5, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2609453 : Nat := 118140960795 + 2609453 * 2 ^ 59
def prefixEnd_2609453 : Nat := 4983230072969 + 3 ^ 40 * 2609453 * 2
def baseEnd_2609453 : Nat := 297756363181529830408189

theorem tailTrace_2609453 : CollatzResearch.WordTrace tailWord_2609453 prefixEnd_2609453 297756363181529830408189 := by
  unfold tailWord_2609453
  simp only [CollatzResearch.WordTrace]
  refine ⟨95174569815404914936777013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63449713210269943291184675 95174569815404914936777013)
  ·
    refine ⟨8922615920194210775322845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95174569815404914936777013 8922615920194210775322845)
    ·
      refine ⟨3345980970072829040746067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8922615920194210775322845 3345980970072829040746067)
      ·
        refine ⟨5018971455109243561119101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3345980970072829040746067 5018971455109243561119101)
        ·
          refine ⟨1882114295665966335419663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5018971455109243561119101 1882114295665966335419663)
          ·
            refine ⟨2823171443498949503129495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882114295665966335419663 2823171443498949503129495)
            ·
              refine ⟨4234757165248424254694243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823171443498949503129495 4234757165248424254694243)
              ·
                refine ⟨6352135747872636382041365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234757165248424254694243 6352135747872636382041365)
                ·
                  refine ⟨297756363181529830408189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6352135747872636382041365 297756363181529830408189)
                  ·
                    rfl

theorem cell22_2609453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2609453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609453 prefixEnd_2609453 := by exact prefixLift 2609453
  have htrace : WordTrace (prefixWord ++ tailWord_2609453) baseStart_2609453 baseEnd_2609453 := by
    simpa [prefixWord, tailWord_2609453, baseEnd_2609453] using wordTrace_append hprefix tailTrace_2609453
  have hstable : (prefixWord ++ tailWord_2609453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609453).length < 2 ^ (prefixWord ++ tailWord_2609453).sum := by decide
  have hdescent : baseEnd_2609453 < baseStart_2609453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609507 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 2, 5]
def baseStart_2609507 : Nat := 118140960795 + 2609507 * 2 ^ 59
def prefixEnd_2609507 : Nat := 4983230072969 + 3 ^ 40 * 2609507 * 2
def baseEnd_2609507 : Nat := 893287574848151350374401

theorem tailTrace_2609507 : CollatzResearch.WordTrace tailWord_2609507 prefixEnd_2609507 893287574848151350374401 := by
  unfold tailWord_2609507
  simp only [CollatzResearch.WordTrace]
  refine ⟨95176539357209282159242775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63451026238139521439495183 95176539357209282159242775)
  ·
    refine ⟨142764809035813923238864163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95176539357209282159242775 142764809035813923238864163)
    ·
      refine ⟨214147213553720884858296245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142764809035813923238864163 214147213553720884858296245)
      ·
        refine ⟨20076301270661332955465273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214147213553720884858296245 20076301270661332955465273)
        ·
          refine ⟨15057225952995999716598955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20076301270661332955465273 15057225952995999716598955)
          ·
            refine ⟨22585838929493999574898433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057225952995999716598955 22585838929493999574898433)
            ·
              refine ⟨16939379197120499681173825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22585838929493999574898433 16939379197120499681173825)
              ·
                refine ⟨12704534397840374760880369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16939379197120499681173825 12704534397840374760880369)
                ·
                  refine ⟨9528400798380281070660277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12704534397840374760880369 9528400798380281070660277)
                  ·
                    refine ⟨893287574848151350374401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9528400798380281070660277 893287574848151350374401)
                    ·
                      rfl

theorem cell22_2609507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_2609507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609507 prefixEnd_2609507 := by exact prefixLift 2609507
  have htrace : WordTrace (prefixWord ++ tailWord_2609507) baseStart_2609507 baseEnd_2609507 := by
    simpa [prefixWord, tailWord_2609507, baseEnd_2609507] using wordTrace_append hprefix tailTrace_2609507
  have hstable : (prefixWord ++ tailWord_2609507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609507).length < 2 ^ (prefixWord ++ tailWord_2609507).sum := by decide
  have hdescent : baseEnd_2609507 < baseStart_2609507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609509 : List Nat := [1, 3, 1, 3, 1, 4, 2, 2, 5]
def baseStart_2609509 : Nat := 118140960795 + 2609509 * 2 ^ 59
def prefixEnd_2609509 : Nat := 4983230072969 + 3 ^ 40 * 2609509 * 2
def baseEnd_2609509 : Nat := 297762753163008003941465

theorem tailTrace_2609509 : CollatzResearch.WordTrace tailWord_2609509 prefixEnd_2609509 297762753163008003941465 := by
  unfold tailWord_2609509
  simp only [CollatzResearch.WordTrace]
  refine ⟨95176612303202036500815581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63451074868801357667210387 95176612303202036500815581)
  ·
    refine ⟨35691229613700763687805843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95176612303202036500815581 35691229613700763687805843)
    ·
      refine ⟨53536844420551145531708765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35691229613700763687805843 53536844420551145531708765)
      ·
        refine ⟨20076316657706679574390787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53536844420551145531708765 20076316657706679574390787)
        ·
          refine ⟨30114474986560019361586181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20076316657706679574390787 30114474986560019361586181)
          ·
            refine ⟨5646464059980003630297409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30114474986560019361586181 5646464059980003630297409)
            ·
              refine ⟨4234848044985002722723057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5646464059980003630297409 4234848044985002722723057)
              ·
                refine ⟨3176136033738752042042293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234848044985002722723057 3176136033738752042042293)
                ·
                  refine ⟨297762753163008003941465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176136033738752042042293 297762753163008003941465)
                  ·
                    rfl

theorem cell22_2609509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_2609509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609509 prefixEnd_2609509 := by exact prefixLift 2609509
  have htrace : WordTrace (prefixWord ++ tailWord_2609509) baseStart_2609509 baseEnd_2609509 := by
    simpa [prefixWord, tailWord_2609509, baseEnd_2609509] using wordTrace_append hprefix tailTrace_2609509
  have hstable : (prefixWord ++ tailWord_2609509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609509).length < 2 ^ (prefixWord ++ tailWord_2609509).sum := by decide
  have hdescent : baseEnd_2609509 < baseStart_2609509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609618 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2609618 : Nat := 118140960795 + 2609618 * 2 ^ 59
def prefixEnd_2609618 : Nat := 4983230072969 + 3 ^ 40 * 2609618 * 2
def baseEnd_2609618 : Nat := 893325572416584060849061

theorem tailTrace_2609618 : CollatzResearch.WordTrace tailWord_2609618 prefixEnd_2609618 893325572416584060849061 := by
  unfold tailWord_2609618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23795146964951787029133377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63453725239871432077689005 23795146964951787029133377)
  ·
    refine ⟨17846360223713840271850033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23795146964951787029133377 17846360223713840271850033)
    ·
      refine ⟨13384770167785380203887525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17846360223713840271850033 13384770167785380203887525)
      ·
        refine ⟨2509644406459758788228911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13384770167785380203887525 2509644406459758788228911)
        ·
          refine ⟨3764466609689638182343367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509644406459758788228911 3764466609689638182343367)
          ·
            refine ⟨5646699914534457273515051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764466609689638182343367 5646699914534457273515051)
            ·
              refine ⟨8470049871801685910272577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646699914534457273515051 8470049871801685910272577)
              ·
                refine ⟨6352537403851264432704433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470049871801685910272577 6352537403851264432704433)
                ·
                  refine ⟨4764403052888448324528325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6352537403851264432704433 4764403052888448324528325)
                  ·
                    refine ⟨893325572416584060849061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764403052888448324528325 893325572416584060849061)
                    ·
                      rfl

theorem cell22_2609618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2609618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609618 prefixEnd_2609618 := by exact prefixLift 2609618
  have htrace : WordTrace (prefixWord ++ tailWord_2609618) baseStart_2609618 baseEnd_2609618 := by
    simpa [prefixWord, tailWord_2609618, baseEnd_2609618] using wordTrace_append hprefix tailTrace_2609618
  have hstable : (prefixWord ++ tailWord_2609618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609618).length < 2 ^ (prefixWord ++ tailWord_2609618).sum := by decide
  have hdescent : baseEnd_2609618 < baseStart_2609618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609629 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2609629 : Nat := 118140960795 + 2609629 * 2 ^ 59
def prefixEnd_2609629 : Nat := 4983230072969 + 3 ^ 40 * 2609629 * 2
def baseEnd_2609629 : Nat := 893329337941383698824027

theorem tailTrace_2609629 : CollatzResearch.WordTrace tailWord_2609629 prefixEnd_2609629 893329337941383698824027 := by
  unfold tailWord_2609629
  simp only [CollatzResearch.WordTrace]
  refine ⟨95180989062767296995183941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63453992708511531330122627 95180989062767296995183941)
  ·
    refine ⟨17846435449268868186596989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95180989062767296995183941 17846435449268868186596989)
    ·
      refine ⟨6692413293475825569973871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17846435449268868186596989 6692413293475825569973871)
      ·
        refine ⟨10038619940213738354960807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692413293475825569973871 10038619940213738354960807)
        ·
          refine ⟨15057929910320607532441211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10038619940213738354960807 15057929910320607532441211)
          ·
            refine ⟨22586894865480911298661817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057929910320607532441211 22586894865480911298661817)
            ·
              refine ⟨16940171149110683473996363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22586894865480911298661817 16940171149110683473996363)
              ·
                refine ⟨25410256723666025210994545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16940171149110683473996363 25410256723666025210994545)
                ·
                  refine ⟨19057692542749518908245909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25410256723666025210994545 19057692542749518908245909)
                  ·
                    refine ⟨893329337941383698824027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19057692542749518908245909 893329337941383698824027)
                    ·
                      rfl

theorem cell22_2609629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2609629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609629 prefixEnd_2609629 := by exact prefixLift 2609629
  have htrace : WordTrace (prefixWord ++ tailWord_2609629) baseStart_2609629 baseEnd_2609629 := by
    simpa [prefixWord, tailWord_2609629, baseEnd_2609629] using wordTrace_append hprefix tailTrace_2609629
  have hstable : (prefixWord ++ tailWord_2609629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609629).length < 2 ^ (prefixWord ++ tailWord_2609629).sum := by decide
  have hdescent : baseEnd_2609629 < baseStart_2609629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609631 : List Nat := [1, 1, 2, 3, 3, 2, 3, 1, 3, 3]
def baseStart_2609631 : Nat := 118140960795 + 2609631 * 2 ^ 59
def prefixEnd_2609631 : Nat := 4983230072969 + 3 ^ 40 * 2609631 * 2
def baseEnd_2609631 : Nat := 893330022582256360274021

theorem tailTrace_2609631 : CollatzResearch.WordTrace tailWord_2609631 prefixEnd_2609631 893330022582256360274021 := by
  unfold tailWord_2609631
  simp only [CollatzResearch.WordTrace]
  refine ⟨95181062008760051336756747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63454041339173367557837831 95181062008760051336756747)
  ·
    refine ⟨142771593013140077005135121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95181062008760051336756747 142771593013140077005135121)
    ·
      refine ⟨107078694759855057753851341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142771593013140077005135121 107078694759855057753851341)
      ·
        refine ⟨40154510534945646657694253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107078694759855057753851341 40154510534945646657694253)
        ·
          refine ⟨15057941450604617496635345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40154510534945646657694253 15057941450604617496635345)
          ·
            refine ⟨11293456087953463122476509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15057941450604617496635345 11293456087953463122476509)
            ·
              refine ⟨4235046032982548670928691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11293456087953463122476509 4235046032982548670928691)
              ·
                refine ⟨6352569049473823006393037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4235046032982548670928691 6352569049473823006393037)
                ·
                  refine ⟨2382213393552683627397389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6352569049473823006393037 2382213393552683627397389)
                  ·
                    refine ⟨893330022582256360274021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382213393552683627397389 893330022582256360274021)
                    ·
                      rfl

theorem cell22_2609631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_2609631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609631 prefixEnd_2609631 := by exact prefixLift 2609631
  have htrace : WordTrace (prefixWord ++ tailWord_2609631) baseStart_2609631 baseEnd_2609631 := by
    simpa [prefixWord, tailWord_2609631, baseEnd_2609631] using wordTrace_append hprefix tailTrace_2609631
  have hstable : (prefixWord ++ tailWord_2609631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609631).length < 2 ^ (prefixWord ++ tailWord_2609631).sum := by decide
  have hdescent : baseEnd_2609631 < baseStart_2609631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609637 : List Nat := [1, 3, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_2609637 : Nat := 118140960795 + 2609637 * 2 ^ 59
def prefixEnd_2609637 : Nat := 4983230072969 + 3 ^ 40 * 2609637 * 2
def baseEnd_2609637 : Nat := 893332076504874344624003

theorem tailTrace_2609637 : CollatzResearch.WordTrace tailWord_2609637 prefixEnd_2609637 893332076504874344624003 := by
  unfold tailWord_2609637
  simp only [CollatzResearch.WordTrace]
  refine ⟨95181280846738314361475165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63454187231158876240983443 95181280846738314361475165)
  ·
    refine ⟨35692980317526867885553187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95181280846738314361475165 35692980317526867885553187)
    ·
      refine ⟨53539470476290301828329781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35692980317526867885553187 53539470476290301828329781)
      ·
        refine ⟨5019325357152215796405917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53539470476290301828329781 5019325357152215796405917)
        ·
          refine ⟨1882247008932080923652219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5019325357152215796405917 1882247008932080923652219)
          ·
            refine ⟨2823370513398121385478329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882247008932080923652219 2823370513398121385478329)
            ·
              refine ⟨2117527885048591039108747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823370513398121385478329 2117527885048591039108747)
              ·
                refine ⟨3176291827572886558663121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117527885048591039108747 3176291827572886558663121)
                ·
                  refine ⟨2382218870679664918997341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176291827572886558663121 2382218870679664918997341)
                  ·
                    refine ⟨893332076504874344624003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382218870679664918997341 893332076504874344624003)
                    ·
                      rfl

theorem cell22_2609637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_2609637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609637 prefixEnd_2609637 := by exact prefixLift 2609637
  have htrace : WordTrace (prefixWord ++ tailWord_2609637) baseStart_2609637 baseEnd_2609637 := by
    simpa [prefixWord, tailWord_2609637, baseEnd_2609637] using wordTrace_append hprefix tailTrace_2609637
  have hstable : (prefixWord ++ tailWord_2609637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609637).length < 2 ^ (prefixWord ++ tailWord_2609637).sum := by decide
  have hdescent : baseEnd_2609637 < baseStart_2609637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609644 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_2609644 : Nat := 118140960795 + 2609644 * 2 ^ 59
def prefixEnd_2609644 : Nat := 4983230072969 + 3 ^ 40 * 2609644 * 2
def baseEnd_2609644 : Nat := 297778157582642886566327

theorem tailTrace_2609644 : CollatzResearch.WordTrace tailWord_2609644 prefixEnd_2609644 297778157582642886566327 := by
  unfold tailWord_2609644
  simp only [CollatzResearch.WordTrace]
  refine ⟨47590768078856477278489993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63454357438475303037986657 47590768078856477278489993)
  ·
    refine ⟨35693076059142357958867495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47590768078856477278489993 35693076059142357958867495)
    ·
      refine ⟨53539614088713536938301243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35693076059142357958867495 53539614088713536938301243)
      ·
        refine ⟨80309421133070305407451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53539614088713536938301243 80309421133070305407451865)
        ·
          refine ⟨60232065849802729055588899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80309421133070305407451865 60232065849802729055588899)
          ·
            refine ⟨90348098774704093583383349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60232065849802729055588899 90348098774704093583383349)
            ·
              refine ⟨8470134260128508773442189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90348098774704093583383349 8470134260128508773442189)
              ·
                refine ⟨3176300347548190790040821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8470134260128508773442189 3176300347548190790040821)
                ·
                  refine ⟨297778157582642886566327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3176300347548190790040821 297778157582642886566327)
                  ·
                    rfl

theorem cell22_2609644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_2609644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609644 prefixEnd_2609644 := by exact prefixLift 2609644
  have htrace : WordTrace (prefixWord ++ tailWord_2609644) baseStart_2609644 baseEnd_2609644 := by
    simpa [prefixWord, tailWord_2609644, baseEnd_2609644] using wordTrace_append hprefix tailTrace_2609644
  have hstable : (prefixWord ++ tailWord_2609644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609644).length < 2 ^ (prefixWord ++ tailWord_2609644).sum := by decide
  have hdescent : baseEnd_2609644 < baseStart_2609644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609706 : List Nat := [3, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_2609706 : Nat := 118140960795 + 2609706 * 2 ^ 59
def prefixEnd_2609706 : Nat := 4983230072969 + 3 ^ 40 * 2609706 * 2
def baseEnd_2609706 : Nat := 297785232204993721549597

theorem tailTrace_2609706 : CollatzResearch.WordTrace tailWord_2609706 prefixEnd_2609706 297785232204993721549597 := by
  unfold tailWord_2609706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23795949370872084786434243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63455864988992226097157981 23795949370872084786434243)
  ·
    refine ⟨35693924056308127179651365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23795949370872084786434243 35693924056308127179651365)
    ·
      refine ⟨6692610760557773846184631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35693924056308127179651365 6692610760557773846184631)
      ·
        refine ⟨10038916140836660769276947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692610760557773846184631 10038916140836660769276947)
        ·
          refine ⟨15058374211254991153915421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10038916140836660769276947 15058374211254991153915421)
          ·
            refine ⟨5646890329220621682718283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15058374211254991153915421 5646890329220621682718283)
            ·
              refine ⟨8470335493830932524077425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5646890329220621682718283 8470335493830932524077425)
              ·
                refine ⟨6352751620373199393058069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8470335493830932524077425 6352751620373199393058069)
                ·
                  refine ⟨297785232204993721549597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6352751620373199393058069 297785232204993721549597)
                  ·
                    rfl

theorem cell22_2609706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_2609706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609706 prefixEnd_2609706 := by exact prefixLift 2609706
  have htrace : WordTrace (prefixWord ++ tailWord_2609706) baseStart_2609706 baseEnd_2609706 := by
    simpa [prefixWord, tailWord_2609706, baseEnd_2609706] using wordTrace_append hprefix tailTrace_2609706
  have hstable : (prefixWord ++ tailWord_2609706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609706).length < 2 ^ (prefixWord ++ tailWord_2609706).sum := by decide
  have hdescent : baseEnd_2609706 < baseStart_2609706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609719 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2609719 : Nat := 118140960795 + 2609719 * 2 ^ 59
def prefixEnd_2609719 : Nat := 4983230072969 + 3 ^ 40 * 2609719 * 2
def baseEnd_2609719 : Nat := 893360146780653464073751

theorem tailTrace_2609719 : CollatzResearch.WordTrace tailWord_2609719 prefixEnd_2609719 893360146780653464073751 := by
  unfold tailWord_2609719
  simp only [CollatzResearch.WordTrace]
  refine ⟨95184271632441242365960211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63456181088294161577306807 95184271632441242365960211)
  ·
    refine ⟨142776407448661863548940317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95184271632441242365960211 142776407448661863548940317)
    ·
      refine ⟨53541152793248198830852619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142776407448661863548940317 53541152793248198830852619)
      ·
        refine ⟨80311729189872298246278929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53541152793248198830852619 80311729189872298246278929)
        ·
          refine ⟨60233796892404223684709197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80311729189872298246278929 60233796892404223684709197)
          ·
            refine ⟨22587673834651583881765949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60233796892404223684709197 22587673834651583881765949)
            ·
              refine ⟨8470377687994343955662231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22587673834651583881765949 8470377687994343955662231)
              ·
                refine ⟨12705566531991515933493347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470377687994343955662231 12705566531991515933493347)
                ·
                  refine ⟨19058349797987273900240021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12705566531991515933493347 19058349797987273900240021)
                  ·
                    refine ⟨893360146780653464073751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19058349797987273900240021 893360146780653464073751)
                    ·
                      rfl

theorem cell22_2609719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2609719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609719 prefixEnd_2609719 := by exact prefixLift 2609719
  have htrace : WordTrace (prefixWord ++ tailWord_2609719) baseStart_2609719 baseEnd_2609719 := by
    simpa [prefixWord, tailWord_2609719, baseEnd_2609719] using wordTrace_append hprefix tailTrace_2609719
  have hstable : (prefixWord ++ tailWord_2609719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609719).length < 2 ^ (prefixWord ++ tailWord_2609719).sum := by decide
  have hdescent : baseEnd_2609719 < baseStart_2609719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609721 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 4, 3]
def baseStart_2609721 : Nat := 118140960795 + 2609721 * 2 ^ 59
def prefixEnd_2609721 : Nat := 4983230072969 + 3 ^ 40 * 2609721 * 2
def baseEnd_2609721 : Nat := 893360831421526125523745

theorem tailTrace_2609721 : CollatzResearch.WordTrace tailWord_2609721 prefixEnd_2609721 893360831421526125523745 := by
  unfold tailWord_2609721
  simp only [CollatzResearch.WordTrace]
  refine ⟨95184344578433996707533017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63456229718955997805022011 95184344578433996707533017)
  ·
    refine ⟨71388258433825497530649763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95184344578433996707533017 71388258433825497530649763)
    ·
      refine ⟨107082387650738246295974645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71388258433825497530649763 107082387650738246295974645)
      ·
        refine ⟨10038973842256710590247623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107082387650738246295974645 10038973842256710590247623)
        ·
          refine ⟨15058460763385065885371435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10038973842256710590247623 15058460763385065885371435)
          ·
            refine ⟨22587691145077598828057153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15058460763385065885371435 22587691145077598828057153)
            ·
              refine ⟨16940768358808199121042865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22587691145077598828057153 16940768358808199121042865)
              ·
                refine ⟨12705576269106149340782149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16940768358808199121042865 12705576269106149340782149)
                ·
                  refine ⟨2382295550457403001396653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12705576269106149340782149 2382295550457403001396653)
                  ·
                    refine ⟨893360831421526125523745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382295550457403001396653 893360831421526125523745)
                    ·
                      rfl

theorem cell22_2609721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4, 3].length) (baseStart_2609721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609721 prefixEnd_2609721 := by exact prefixLift 2609721
  have htrace : WordTrace (prefixWord ++ tailWord_2609721) baseStart_2609721 baseEnd_2609721 := by
    simpa [prefixWord, tailWord_2609721, baseEnd_2609721] using wordTrace_append hprefix tailTrace_2609721
  have hstable : (prefixWord ++ tailWord_2609721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609721).length < 2 ^ (prefixWord ++ tailWord_2609721).sum := by decide
  have hdescent : baseEnd_2609721 < baseStart_2609721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609725 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_2609725 : Nat := 118140960795 + 2609725 * 2 ^ 59
def prefixEnd_2609725 : Nat := 4983230072969 + 3 ^ 40 * 2609725 * 2
def baseEnd_2609725 : Nat := 893362200703271448423733

theorem tailTrace_2609725 : CollatzResearch.WordTrace tailWord_2609725 prefixEnd_2609725 893362200703271448423733 := by
  unfold tailWord_2609725
  simp only [CollatzResearch.WordTrace]
  refine ⟨95184490470419505390678629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63456326980279670260452419 95184490470419505390678629)
  ·
    refine ⟨17847091963203657260752243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95184490470419505390678629 17847091963203657260752243)
    ·
      refine ⟨26770637944805485891128365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17847091963203657260752243 26770637944805485891128365)
      ·
        refine ⟨10038989229302057209173137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26770637944805485891128365 10038989229302057209173137)
        ·
          refine ⟨7529241921976542906879853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10038989229302057209173137 7529241921976542906879853)
          ·
            refine ⟨2823465720741203590079945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7529241921976542906879853 2823465720741203590079945)
            ·
              refine ⟨2117599290555902692559959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2823465720741203590079945 2117599290555902692559959)
              ·
                refine ⟨3176398935833854038839939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117599290555902692559959 3176398935833854038839939)
                ·
                  refine ⟨4764598403750781058259909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3176398935833854038839939 4764598403750781058259909)
                  ·
                    refine ⟨893362200703271448423733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4764598403750781058259909 893362200703271448423733)
                    ·
                      rfl

theorem cell22_2609725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_2609725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609725 prefixEnd_2609725 := by exact prefixLift 2609725
  have htrace : WordTrace (prefixWord ++ tailWord_2609725) baseStart_2609725 baseEnd_2609725 := by
    simpa [prefixWord, tailWord_2609725, baseEnd_2609725] using wordTrace_append hprefix tailTrace_2609725
  have hstable : (prefixWord ++ tailWord_2609725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609725).length < 2 ^ (prefixWord ++ tailWord_2609725).sum := by decide
  have hdescent : baseEnd_2609725 < baseStart_2609725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609738 : List Nat := [3, 1, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_2609738 : Nat := 118140960795 + 2609738 * 2 ^ 59
def prefixEnd_2609738 : Nat := 4983230072969 + 3 ^ 40 * 2609738 * 2
def baseEnd_2609738 : Nat := 893366650868943747848693

theorem tailTrace_2609738 : CollatzResearch.WordTrace tailWord_2609738 prefixEnd_2609738 893366650868943747848693 := by
  unfold tailWord_2609738
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796241154843102152725467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63456643079581605740601245 23796241154843102152725467)
  ·
    refine ⟨35694361732264653229088201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23796241154843102152725467 35694361732264653229088201)
    ·
      refine ⟨26770771299198489921816151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35694361732264653229088201 26770771299198489921816151)
      ·
        refine ⟨40156156948797734882724227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26770771299198489921816151 40156156948797734882724227)
        ·
          refine ⟨60234235423196602324086341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40156156948797734882724227 60234235423196602324086341)
          ·
            refine ⟨11293919141849362935766189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60234235423196602324086341 11293919141849362935766189)
            ·
              refine ⟨4235219678193511100912321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11293919141849362935766189 4235219678193511100912321)
              ·
                refine ⟨3176414758645133325684241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235219678193511100912321 3176414758645133325684241)
                ·
                  refine ⟨2382311068983849994263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176414758645133325684241 2382311068983849994263181)
                  ·
                    refine ⟨893366650868943747848693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382311068983849994263181 893366650868943747848693)
                    ·
                      rfl

theorem cell22_2609738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_2609738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609738 prefixEnd_2609738 := by exact prefixLift 2609738
  have htrace : WordTrace (prefixWord ++ tailWord_2609738) baseStart_2609738 baseEnd_2609738 := by
    simpa [prefixWord, tailWord_2609738, baseEnd_2609738] using wordTrace_append hprefix tailTrace_2609738
  have hstable : (prefixWord ++ tailWord_2609738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609738).length < 2 ^ (prefixWord ++ tailWord_2609738).sum := by decide
  have hdescent : baseEnd_2609738 < baseStart_2609738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609796 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_2609796 : Nat := 118140960795 + 2609796 * 2 ^ 59
def prefixEnd_2609796 : Nat := 4983230072969 + 3 ^ 40 * 2609796 * 2
def baseEnd_2609796 : Nat := 297795501818083643299505

theorem tailTrace_2609796 : CollatzResearch.WordTrace tailWord_2609796 prefixEnd_2609796 297795501818083643299505 := by
  unfold tailWord_2609796
  simp only [CollatzResearch.WordTrace]
  refine ⟨47593540026581142258256621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63458053368774856344342161 47593540026581142258256621)
  ·
    refine ⟨17847577509967928346846233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47593540026581142258256621 17847577509967928346846233)
    ·
      refine ⟨13385683132475946260134675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17847577509967928346846233 13385683132475946260134675)
      ·
        refine ⟨20078524698713919390202013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385683132475946260134675 20078524698713919390202013)
        ·
          refine ⟨7529446762017719771325755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20078524698713919390202013 7529446762017719771325755)
          ·
            refine ⟨11294170143026579656988633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529446762017719771325755 11294170143026579656988633)
            ·
              refine ⟨8470627607269934742741475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11294170143026579656988633 8470627607269934742741475)
              ·
                refine ⟨12705941410904902114112213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470627607269934742741475 12705941410904902114112213)
                ·
                  refine ⟨297795501818083643299505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12705941410904902114112213 297795501818083643299505)
                  ·
                    rfl

theorem cell22_2609796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_2609796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609796 prefixEnd_2609796 := by exact prefixLift 2609796
  have htrace : WordTrace (prefixWord ++ tailWord_2609796) baseStart_2609796 baseEnd_2609796 := by
    simpa [prefixWord, tailWord_2609796, baseEnd_2609796] using wordTrace_append hprefix tailTrace_2609796
  have hstable : (prefixWord ++ tailWord_2609796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609796).length < 2 ^ (prefixWord ++ tailWord_2609796).sum := by decide
  have hdescent : baseEnd_2609796 < baseStart_2609796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609862 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2609862 : Nat := 118140960795 + 2609862 * 2 ^ 59
def prefixEnd_2609862 : Nat := 4983230072969 + 3 ^ 40 * 2609862 * 2
def baseEnd_2609862 : Nat := 893409098603048757748313

theorem tailTrace_2609862 : CollatzResearch.WordTrace tailWord_2609862 prefixEnd_2609862 893409098603048757748313 := by
  unfold tailWord_2609862
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974671477216349305887995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63459658180615451858943893 2974671477216349305887995)
  ·
    refine ⟨4462007215824523958831993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2974671477216349305887995 4462007215824523958831993)
    ·
      refine ⟨3346505411868392969123995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4462007215824523958831993 3346505411868392969123995)
      ·
        refine ⟨5019758117802589453685993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3346505411868392969123995 5019758117802589453685993)
        ·
          refine ⟨3764818588351942090264495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5019758117802589453685993 3764818588351942090264495)
          ·
            refine ⟨5647227882527913135396743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764818588351942090264495 5647227882527913135396743)
            ·
              refine ⟨8470841823791869703095115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5647227882527913135396743 8470841823791869703095115)
              ·
                refine ⟨12706262735687804554642673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470841823791869703095115 12706262735687804554642673)
                ·
                  refine ⟨9529697051765853415982005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12706262735687804554642673 9529697051765853415982005)
                  ·
                    refine ⟨893409098603048757748313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9529697051765853415982005 893409098603048757748313)
                    ·
                      rfl

theorem cell22_2609862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2609862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609862 prefixEnd_2609862 := by exact prefixLift 2609862
  have htrace : WordTrace (prefixWord ++ tailWord_2609862) baseStart_2609862 baseEnd_2609862 := by
    simpa [prefixWord, tailWord_2609862, baseEnd_2609862] using wordTrace_append hprefix tailTrace_2609862
  have hstable : (prefixWord ++ tailWord_2609862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609862).length < 2 ^ (prefixWord ++ tailWord_2609862).sum := by decide
  have hdescent : baseEnd_2609862 < baseStart_2609862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609873 : List Nat := [1, 2, 2, 1, 2, 3, 1, 5, 2, 3]
def baseStart_2609873 : Nat := 118140960795 + 2609873 * 2 ^ 59
def prefixEnd_2609873 : Nat := 4983230072969 + 3 ^ 40 * 2609873 * 2
def baseEnd_2609873 : Nat := 893412864127848395723279

theorem tailTrace_2609873 : CollatzResearch.WordTrace tailWord_2609873 prefixEnd_2609873 893412864127848395723279 := by
  unfold tailWord_2609873
  simp only [CollatzResearch.WordTrace]
  refine ⟨95189888473883326667066273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63459925649255551111377515 95189888473883326667066273)
  ·
    refine ⟨71392416355412495000299705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95189888473883326667066273 71392416355412495000299705)
    ·
      refine ⟨53544312266559371250224779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71392416355412495000299705 53544312266559371250224779)
      ·
        refine ⟨80316468399839056875337169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53544312266559371250224779 80316468399839056875337169)
        ·
          refine ⟨60237351299879292656502877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80316468399839056875337169 60237351299879292656502877)
          ·
            refine ⟨22589006737454734746188579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60237351299879292656502877 22589006737454734746188579)
            ·
              refine ⟨33883510106182102119282869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22589006737454734746188579 33883510106182102119282869)
              ·
                refine ⟨3176579072454572073682769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33883510106182102119282869 3176579072454572073682769)
                ·
                  refine ⟨2382434304340929055262077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176579072454572073682769 2382434304340929055262077)
                  ·
                    refine ⟨893412864127848395723279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382434304340929055262077 893412864127848395723279)
                    ·
                      rfl

theorem cell22_2609873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_2609873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609873 prefixEnd_2609873 := by exact prefixLift 2609873
  have htrace : WordTrace (prefixWord ++ tailWord_2609873) baseStart_2609873 baseEnd_2609873 := by
    simpa [prefixWord, tailWord_2609873, baseEnd_2609873] using wordTrace_append hprefix tailTrace_2609873
  have hstable : (prefixWord ++ tailWord_2609873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609873).length < 2 ^ (prefixWord ++ tailWord_2609873).sum := by decide
  have hdescent : baseEnd_2609873 < baseStart_2609873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2609952 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 1, 3]
def baseStart_2609952 : Nat := 118140960795 + 2609952 * 2 ^ 59
def prefixEnd_2609952 : Nat := 4983230072969 + 3 ^ 40 * 2609952 * 2
def baseEnd_2609952 : Nat := 893439907442318522998037

theorem tailTrace_2609952 : CollatzResearch.WordTrace tailWord_2609952 prefixEnd_2609952 893439907442318522998037 := by
  unfold tailWord_2609952
  simp only [CollatzResearch.WordTrace]
  refine ⟨47596384920298561579596055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63461846560398082106128073 47596384920298561579596055)
  ·
    refine ⟨71394577380447842369394083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47596384920298561579596055 71394577380447842369394083)
    ·
      refine ⟨107091866070671763554091125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71394577380447842369394083 107091866070671763554091125)
      ·
        refine ⟨10039862444125477833196043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107091866070671763554091125 10039862444125477833196043)
        ·
          refine ⟨15059793666188216749794065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10039862444125477833196043 15059793666188216749794065)
          ·
            refine ⟨11294845249641162562345549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15059793666188216749794065 11294845249641162562345549)
            ·
              refine ⟨4235566968615435960879581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11294845249641162562345549 4235566968615435960879581)
              ·
                refine ⟨1588337613230788485329843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4235566968615435960879581 1588337613230788485329843)
                ·
                  refine ⟨2382506419846182727994765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1588337613230788485329843 2382506419846182727994765)
                  ·
                    refine ⟨893439907442318522998037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382506419846182727994765 893439907442318522998037)
                    ·
                      rfl

theorem cell22_2609952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 3].length) (baseStart_2609952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2609952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2609952 prefixEnd_2609952 := by exact prefixLift 2609952
  have htrace : WordTrace (prefixWord ++ tailWord_2609952) baseStart_2609952 baseEnd_2609952 := by
    simpa [prefixWord, tailWord_2609952, baseEnd_2609952] using wordTrace_append hprefix tailTrace_2609952
  have hstable : (prefixWord ++ tailWord_2609952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2609952).length < 2 ^ (prefixWord ++ tailWord_2609952).sum := by decide
  have hdescent : baseEnd_2609952 < baseStart_2609952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2609952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610008 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_2610008 : Nat := 118140960795 + 2610008 * 2 ^ 59
def prefixEnd_2610008 : Nat := 4983230072969 + 3 ^ 40 * 2610008 * 2
def baseEnd_2610008 : Nat := 893459077386753043597865

theorem tailTrace_2610008 : CollatzResearch.WordTrace tailWord_2610008 prefixEnd_2610008 893459077386753043597865 := by
  unfold tailWord_2610008
  simp only [CollatzResearch.WordTrace]
  refine ⟨47597406164197122361615339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63463208218929496482153785 47597406164197122361615339)
  ·
    refine ⟨71396109246295683542423009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47597406164197122361615339 71396109246295683542423009)
    ·
      refine ⟨53547081934721762656817257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71396109246295683542423009 53547081934721762656817257)
      ·
        refine ⟨40160311451041321992612943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53547081934721762656817257 40160311451041321992612943)
        ·
          refine ⟨60240467176561982988919415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40160311451041321992612943 60240467176561982988919415)
          ·
            refine ⟨90360700764842974483379123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60240467176561982988919415 90360700764842974483379123)
            ·
              refine ⟨135541051147264461725068685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90360700764842974483379123 135541051147264461725068685)
              ·
                refine ⟨50827894180224173146900757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135541051147264461725068685 50827894180224173146900757)
                ·
                  refine ⟨2382557539698008116260973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50827894180224173146900757 2382557539698008116260973)
                  ·
                    refine ⟨893459077386753043597865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382557539698008116260973 893459077386753043597865)
                    ·
                      rfl

theorem cell22_2610008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_2610008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610008 prefixEnd_2610008 := by exact prefixLift 2610008
  have htrace : WordTrace (prefixWord ++ tailWord_2610008) baseStart_2610008 baseEnd_2610008 := by
    simpa [prefixWord, tailWord_2610008, baseEnd_2610008] using wordTrace_append hprefix tailTrace_2610008
  have hstable : (prefixWord ++ tailWord_2610008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610008).length < 2 ^ (prefixWord ++ tailWord_2610008).sum := by decide
  have hdescent : baseEnd_2610008 < baseStart_2610008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610055 : List Nat := [1, 1, 4, 2, 3, 2, 3, 6]
def baseStart_2610055 : Nat := 118140960795 + 2610055 * 2 ^ 59
def prefixEnd_2610055 : Nat := 4983230072969 + 3 ^ 40 * 2610055 * 2
def baseEnd_2610055 : Nat := 99275018494140065296969

theorem tailTrace_2610055 : CollatzResearch.WordTrace tailWord_2610055 prefixEnd_2610055 99275018494140065296969 := by
  unfold tailWord_2610055
  simp only [CollatzResearch.WordTrace]
  refine ⟨95196526559223971750191619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63464351039482647833461079 95196526559223971750191619)
  ·
    refine ⟨142794789838835957625287429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95196526559223971750191619 142794789838835957625287429)
    ·
      refine ⟨26774023094781742054741393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142794789838835957625287429 26774023094781742054741393)
      ·
        refine ⟨20080517321086306541056045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26774023094781742054741393 20080517321086306541056045)
        ·
          refine ⟨7530193995407364952896017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20080517321086306541056045 7530193995407364952896017)
          ·
            refine ⟨5647645496555523714672013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7530193995407364952896017 5647645496555523714672013)
            ·
              refine ⟨2117867061208321393002005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5647645496555523714672013 2117867061208321393002005)
              ·
                refine ⟨99275018494140065296969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2117867061208321393002005 99275018494140065296969)
                ·
                  rfl

theorem cell22_2610055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 6].length) (baseStart_2610055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610055 prefixEnd_2610055 := by exact prefixLift 2610055
  have htrace : WordTrace (prefixWord ++ tailWord_2610055) baseStart_2610055 baseEnd_2610055 := by
    simpa [prefixWord, tailWord_2610055, baseEnd_2610055] using wordTrace_append hprefix tailTrace_2610055
  have hstable : (prefixWord ++ tailWord_2610055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610055).length < 2 ^ (prefixWord ++ tailWord_2610055).sum := by decide
  have hdescent : baseEnd_2610055 < baseStart_2610055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610076 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 2, 3]
def baseStart_2610076 : Nat := 118140960795 + 2610076 * 2 ^ 59
def prefixEnd_2610076 : Nat := 4983230072969 + 3 ^ 40 * 2610076 * 2
def baseEnd_2610076 : Nat := 893482355176423532897657

theorem tailTrace_2610076 : CollatzResearch.WordTrace tailWord_2610076 prefixEnd_2610076 893482355176423532897657 := by
  unfold tailWord_2610076
  simp only [CollatzResearch.WordTrace]
  refine ⟨47598646246073946168353041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63464861661431928224470721 47598646246073946168353041)
  ·
    refine ⟨35698984684555459626264781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47598646246073946168353041 35698984684555459626264781)
    ·
      refine ⟨13387119256708297359849293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35698984684555459626264781 13387119256708297359849293)
      ·
        refine ⟨5020169721265611509943485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13387119256708297359849293 5020169721265611509943485)
        ·
          refine ⟨1882563645474604316228807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5020169721265611509943485 1882563645474604316228807)
          ·
            refine ⟨2823845468211906474343211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1882563645474604316228807 2823845468211906474343211)
            ·
              refine ⟨4235768202317859711514817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823845468211906474343211 4235768202317859711514817)
              ·
                refine ⟨3176826151738394783636113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4235768202317859711514817 3176826151738394783636113)
                ·
                  refine ⟨2382619613803796087727085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3176826151738394783636113 2382619613803796087727085)
                  ·
                    refine ⟨893482355176423532897657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2382619613803796087727085 893482355176423532897657)
                    ·
                      rfl

theorem cell22_2610076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_2610076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610076 prefixEnd_2610076 := by exact prefixLift 2610076
  have htrace : WordTrace (prefixWord ++ tailWord_2610076) baseStart_2610076 baseEnd_2610076 := by
    simpa [prefixWord, tailWord_2610076, baseEnd_2610076] using wordTrace_append hprefix tailTrace_2610076
  have hstable : (prefixWord ++ tailWord_2610076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610076).length < 2 ^ (prefixWord ++ tailWord_2610076).sum := by decide
  have hdescent : baseEnd_2610076 < baseStart_2610076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610250 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2610250 : Nat := 118140960795 + 2610250 * 2 ^ 59
def prefixEnd_2610250 : Nat := 4983230072969 + 3 ^ 40 * 2610250 * 2
def baseEnd_2610250 : Nat := 893541918932345079047123

theorem tailTrace_2610250 : CollatzResearch.WordTrace tailWord_2610250 prefixEnd_2610250 893541918932345079047123 := by
  unfold tailWord_2610250
  simp only [CollatzResearch.WordTrace]
  refine ⟨23800909698379380013385051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63469092529011680035693469 23800909698379380013385051)
  ·
    refine ⟨35701364547569070020077577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23800909698379380013385051 35701364547569070020077577)
    ·
      refine ⟨26776023410676802515058183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35701364547569070020077577 26776023410676802515058183)
      ·
        refine ⟨40164035116015203772587275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26776023410676802515058183 40164035116015203772587275)
        ·
          refine ⟨60246052674022805658880913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40164035116015203772587275 60246052674022805658880913)
          ·
            refine ⟨45184539505517104244160685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60246052674022805658880913 45184539505517104244160685)
            ·
              refine ⟨16944202314568914091560257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45184539505517104244160685 16944202314568914091560257)
              ·
                refine ⟨12708151735926685568670193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16944202314568914091560257 12708151735926685568670193)
                ·
                  refine ⟨9531113801945014176502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12708151735926685568670193 9531113801945014176502645)
                  ·
                    refine ⟨893541918932345079047123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9531113801945014176502645 893541918932345079047123)
                    ·
                      rfl

theorem cell22_2610250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2610250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610250 prefixEnd_2610250 := by exact prefixLift 2610250
  have htrace : WordTrace (prefixWord ++ tailWord_2610250) baseStart_2610250 baseEnd_2610250 := by
    simpa [prefixWord, tailWord_2610250, baseEnd_2610250] using wordTrace_append hprefix tailTrace_2610250
  have hstable : (prefixWord ++ tailWord_2610250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610250).length < 2 ^ (prefixWord ++ tailWord_2610250).sum := by decide
  have hdescent : baseEnd_2610250 < baseStart_2610250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610265 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 3, 4]
def baseStart_2610265 : Nat := 118140960795 + 2610265 * 2 ^ 59
def prefixEnd_2610265 : Nat := 4983230072969 + 3 ^ 40 * 2610265 * 2
def baseEnd_2610265 : Nat := 893547053738890039922077

theorem tailTrace_2610265 : CollatzResearch.WordTrace tailWord_2610265 prefixEnd_2610265 893547053738890039922077 := by
  unfold tailWord_2610265
  simp only [CollatzResearch.WordTrace]
  refine ⟨95204185888463177615336249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63469457258975451743557499 95204185888463177615336249)
  ·
    refine ⟨71403139416347383211502187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95204185888463177615336249 71403139416347383211502187)
    ·
      refine ⟨107104709124521074817253281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71403139416347383211502187 107104709124521074817253281)
      ·
        refine ⟨80328531843390806112939961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107104709124521074817253281 80328531843390806112939961)
        ·
          refine ⟨60246398882543104584704971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80328531843390806112939961 60246398882543104584704971)
          ·
            refine ⟨90369598323814656877057457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60246398882543104584704971 90369598323814656877057457)
            ·
              refine ⟨67777198742860992657793093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90369598323814656877057457 67777198742860992657793093)
              ·
                refine ⟨12708224764286436123336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67777198742860992657793093 12708224764286436123336205)
                ·
                  refine ⟨4765584286607413546251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12708224764286436123336205 4765584286607413546251077)
                  ·
                    refine ⟨893547053738890039922077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4765584286607413546251077 893547053738890039922077)
                    ·
                      rfl

theorem cell22_2610265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 4].length) (baseStart_2610265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610265 prefixEnd_2610265 := by exact prefixLift 2610265
  have htrace : WordTrace (prefixWord ++ tailWord_2610265) baseStart_2610265 baseEnd_2610265 := by
    simpa [prefixWord, tailWord_2610265, baseEnd_2610265] using wordTrace_append hprefix tailTrace_2610265
  have hstable : (prefixWord ++ tailWord_2610265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610265).length < 2 ^ (prefixWord ++ tailWord_2610265).sum := by decide
  have hdescent : baseEnd_2610265 < baseStart_2610265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610295 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2610295 : Nat := 118140960795 + 2610295 * 2 ^ 59
def prefixEnd_2610295 : Nat := 4983230072969 + 3 ^ 40 * 2610295 * 2
def baseEnd_2610295 : Nat := 893557323351979961671985

theorem tailTrace_2610295 : CollatzResearch.WordTrace tailWord_2610295 prefixEnd_2610295 893557323351979961671985 := by
  unfold tailWord_2610295
  simp only [CollatzResearch.WordTrace]
  refine ⟨95205280078354492738928339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63470186718902995159285559 95205280078354492738928339)
  ·
    refine ⟨142807920117531739108392509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95205280078354492738928339 142807920117531739108392509)
    ·
      refine ⟨53552970044074402165647191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142807920117531739108392509 53552970044074402165647191)
      ·
        refine ⟨80329455066111603248470787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53552970044074402165647191 80329455066111603248470787)
        ·
          refine ⟨120494182599167404872706181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80329455066111603248470787 120494182599167404872706181)
          ·
            refine ⟨22592659237343888413632409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120494182599167404872706181 22592659237343888413632409)
            ·
              refine ⟨16944494428007916310224307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22592659237343888413632409 16944494428007916310224307)
              ·
                refine ⟨25416741642011874465336461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16944494428007916310224307 25416741642011874465336461)
                ·
                  refine ⟨9531278115754452924501173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25416741642011874465336461 9531278115754452924501173)
                  ·
                    refine ⟨893557323351979961671985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9531278115754452924501173 893557323351979961671985)
                    ·
                      rfl

theorem cell22_2610295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2610295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610295 prefixEnd_2610295 := by exact prefixLift 2610295
  have htrace : WordTrace (prefixWord ++ tailWord_2610295) baseStart_2610295 baseEnd_2610295 := by
    simpa [prefixWord, tailWord_2610295, baseEnd_2610295] using wordTrace_append hprefix tailTrace_2610295
  have hstable : (prefixWord ++ tailWord_2610295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610295).length < 2 ^ (prefixWord ++ tailWord_2610295).sum := by decide
  have hdescent : baseEnd_2610295 < baseStart_2610295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610494 : List Nat := [4, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2610494 : Nat := 118140960795 + 2610494 * 2 ^ 59
def prefixEnd_2610494 : Nat := 4983230072969 + 3 ^ 40 * 2610494 * 2
def baseEnd_2610494 : Nat := 99291716124312197327375

theorem tailTrace_2610494 : CollatzResearch.WordTrace tailWord_2610494 prefixEnd_2610494 99291716124312197327375 := by
  unfold tailWord_2610494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11901567275579193715677817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63475025469755699816948357 11901567275579193715677817)
  ·
    refine ⟨8926175456684395286758363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11901567275579193715677817 8926175456684395286758363)
    ·
      refine ⟨13389263185026592930137545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8926175456684395286758363 13389263185026592930137545)
      ·
        refine ⟨10041947388769944697603159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13389263185026592930137545 10041947388769944697603159)
        ·
          refine ⟨15062921083154917046404739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10041947388769944697603159 15062921083154917046404739)
          ·
            refine ⟨22594381624732375569607109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15062921083154917046404739 22594381624732375569607109)
            ·
              refine ⟨4236446554637320419301333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22594381624732375569607109 4236446554637320419301333)
              ·
                refine ⟨99291716124312197327375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4236446554637320419301333 99291716124312197327375)
                ·
                  rfl

theorem cell22_2610494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2610494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610494 prefixEnd_2610494 := by exact prefixLift 2610494
  have htrace : WordTrace (prefixWord ++ tailWord_2610494) baseStart_2610494 baseEnd_2610494 := by
    simpa [prefixWord, tailWord_2610494, baseEnd_2610494] using wordTrace_append hprefix tailTrace_2610494
  have hstable : (prefixWord ++ tailWord_2610494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610494).length < 2 ^ (prefixWord ++ tailWord_2610494).sum := by decide
  have hdescent : baseEnd_2610494 < baseStart_2610494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610502 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2610502 : Nat := 118140960795 + 2610502 * 2 ^ 59
def prefixEnd_2610502 : Nat := 4983230072969 + 3 ^ 40 * 2610502 * 2
def baseEnd_2610502 : Nat := 893628183682300421746351

theorem tailTrace_2610502 : CollatzResearch.WordTrace tailWord_2610502 prefixEnd_2610502 893628183682300421746351 := by
  unfold tailWord_2610502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975400937143892721616055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63475219992403044727809173 2975400937143892721616055)
  ·
    refine ⟨4463101405715839082424083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2975400937143892721616055 4463101405715839082424083)
    ·
      refine ⟨6694652108573758623636125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463101405715839082424083 6694652108573758623636125)
      ·
        refine ⟨2510494540715159483863547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6694652108573758623636125 2510494540715159483863547)
        ·
          refine ⟨3765741811072739225795321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2510494540715159483863547 3765741811072739225795321)
          ·
            refine ⟨2824306358304554419346491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3765741811072739225795321 2824306358304554419346491)
            ·
              refine ⟨4236459537456831629019737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824306358304554419346491 4236459537456831629019737)
              ·
                refine ⟨3177344653092623721764803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236459537456831629019737 3177344653092623721764803)
                ·
                  refine ⟨4766016979638935582647205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177344653092623721764803 4766016979638935582647205)
                  ·
                    refine ⟨893628183682300421746351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766016979638935582647205 893628183682300421746351)
                    ·
                      rfl

theorem cell22_2610502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2610502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610502 prefixEnd_2610502 := by exact prefixLift 2610502
  have htrace : WordTrace (prefixWord ++ tailWord_2610502) baseStart_2610502 baseEnd_2610502 := by
    simpa [prefixWord, tailWord_2610502, baseEnd_2610502] using wordTrace_append hprefix tailTrace_2610502
  have hstable : (prefixWord ++ tailWord_2610502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610502).length < 2 ^ (prefixWord ++ tailWord_2610502).sum := by decide
  have hdescent : baseEnd_2610502 < baseStart_2610502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610522 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_2610522 : Nat := 118140960795 + 2610522 * 2 ^ 59
def prefixEnd_2610522 : Nat := 4983230072969 + 3 ^ 40 * 2610522 * 2
def baseEnd_2610522 : Nat := 297878343363675678748763

theorem tailTrace_2610522 : CollatzResearch.WordTrace tailWord_2610522 prefixEnd_2610522 297878343363675678748763 := by
  unfold tailWord_2610522
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803389862133027626860455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63475706299021407004961213 23803389862133027626860455)
  ·
    refine ⟨35705084793199541440290683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23803389862133027626860455 35705084793199541440290683)
    ·
      refine ⟨53557627189799312160436025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35705084793199541440290683 53557627189799312160436025)
      ·
        refine ⟨40168220392349484120327019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53557627189799312160436025 40168220392349484120327019)
        ·
          refine ⟨60252330588524226180490529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40168220392349484120327019 60252330588524226180490529)
          ·
            refine ⟨45189247941393169635367897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60252330588524226180490529 45189247941393169635367897)
            ·
              refine ⟨33891935956044877226525923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45189247941393169635367897 33891935956044877226525923)
              ·
                refine ⟨50837903934067315839788885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33891935956044877226525923 50837903934067315839788885)
                ·
                  refine ⟨297878343363675678748763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50837903934067315839788885 297878343363675678748763)
                  ·
                    rfl

theorem cell22_2610522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_2610522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610522 prefixEnd_2610522 := by exact prefixLift 2610522
  have htrace : WordTrace (prefixWord ++ tailWord_2610522) baseStart_2610522 baseEnd_2610522 := by
    simpa [prefixWord, tailWord_2610522, baseEnd_2610522] using wordTrace_append hprefix tailTrace_2610522
  have hstable : (prefixWord ++ tailWord_2610522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610522).length < 2 ^ (prefixWord ++ tailWord_2610522).sum := by decide
  have hdescent : baseEnd_2610522 < baseStart_2610522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610586 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_2610586 : Nat := 118140960795 + 2610586 * 2 ^ 59
def prefixEnd_2610586 : Nat := 4983230072969 + 3 ^ 40 * 2610586 * 2
def baseEnd_2610586 : Nat := 893656938598952202646093

theorem tailTrace_2610586 : CollatzResearch.WordTrace tailWord_2610586 prefixEnd_2610586 893656938598952202646093 := by
  unfold tailWord_2610586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23803973430075062359442903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63477262480200166291847741 23803973430075062359442903)
  ·
    refine ⟨35705960145112593539164355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23803973430075062359442903 35705960145112593539164355)
    ·
      refine ⟨53558940217668890308746533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35705960145112593539164355 53558940217668890308746533)
      ·
        refine ⟨10042301290812916932889975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53558940217668890308746533 10042301290812916932889975)
        ·
          refine ⟨15063451936219375399334963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042301290812916932889975 15063451936219375399334963)
          ·
            refine ⟨22595177904329063099002445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15063451936219375399334963 22595177904329063099002445)
            ·
              refine ⟨8473191714123398662125917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22595177904329063099002445 8473191714123398662125917)
              ·
                refine ⟨3177446892796274498297219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8473191714123398662125917 3177446892796274498297219)
                ·
                  refine ⟨4766170339194411747445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177446892796274498297219 4766170339194411747445829)
                  ·
                    refine ⟨893656938598952202646093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766170339194411747445829 893656938598952202646093)
                    ·
                      rfl

theorem cell22_2610586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_2610586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610586 prefixEnd_2610586 := by exact prefixLift 2610586
  have htrace : WordTrace (prefixWord ++ tailWord_2610586) baseStart_2610586 baseEnd_2610586 := by
    simpa [prefixWord, tailWord_2610586, baseEnd_2610586] using wordTrace_append hprefix tailTrace_2610586
  have hstable : (prefixWord ++ tailWord_2610586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610586).length < 2 ^ (prefixWord ++ tailWord_2610586).sum := by decide
  have hdescent : baseEnd_2610586 < baseStart_2610586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610590 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2610590 : Nat := 118140960795 + 2610590 * 2 ^ 59
def prefixEnd_2610590 : Nat := 4983230072969 + 3 ^ 40 * 2610590 * 2
def baseEnd_2610590 : Nat := 297886102626899175182027

theorem tailTrace_2610590 : CollatzResearch.WordTrace tailWord_2610590 prefixEnd_2610590 297886102626899175182027 := by
  unfold tailWord_2610590
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902004951535719765114653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63477359741523838747278149 11902004951535719765114653)
  ·
    refine ⟨4463251856825894911917995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11902004951535719765114653 4463251856825894911917995)
    ·
      refine ⟨6694877785238842367876993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463251856825894911917995 6694877785238842367876993)
      ·
        refine ⟨5021158338929131775907745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6694877785238842367876993 5021158338929131775907745)
        ·
          refine ⟨3765868754196848831930809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5021158338929131775907745 3765868754196848831930809)
          ·
            refine ⟨2824401565647636623948107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3765868754196848831930809 2824401565647636623948107)
            ·
              refine ⟨4236602348471454935922161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824401565647636623948107 4236602348471454935922161)
              ·
                refine ⟨3177451761353591201941621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4236602348471454935922161 3177451761353591201941621)
                ·
                  refine ⟨297886102626899175182027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3177451761353591201941621 297886102626899175182027)
                  ·
                    rfl

theorem cell22_2610590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2610590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610590 prefixEnd_2610590 := by exact prefixLift 2610590
  have htrace : WordTrace (prefixWord ++ tailWord_2610590) baseStart_2610590 baseEnd_2610590 := by
    simpa [prefixWord, tailWord_2610590, baseEnd_2610590] using wordTrace_append hprefix tailTrace_2610590
  have hstable : (prefixWord ++ tailWord_2610590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610590).length < 2 ^ (prefixWord ++ tailWord_2610590).sum := by decide
  have hdescent : baseEnd_2610590 < baseStart_2610590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610616 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_2610616 : Nat := 118140960795 + 2610616 * 2 ^ 59
def prefixEnd_2610616 : Nat := 4983230072969 + 3 ^ 40 * 2610616 * 2
def baseEnd_2610616 : Nat := 893667208212042124396001

theorem tailTrace_2610616 : CollatzResearch.WordTrace tailWord_2610616 prefixEnd_2610616 893667208212042124396001 := by
  unfold tailWord_2610616
  simp only [CollatzResearch.WordTrace]
  refine ⟨47608493955095782280681851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63477991940127709707575801 47608493955095782280681851)
  ·
    refine ⟨71412740932643673421022777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47608493955095782280681851 71412740932643673421022777)
    ·
      refine ⟨53559555699482755065767083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71412740932643673421022777 53559555699482755065767083)
      ·
        refine ⟨80339333549224132598650625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53559555699482755065767083 80339333549224132598650625)
        ·
          refine ⟨60254500161918099448987969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80339333549224132598650625 60254500161918099448987969)
          ·
            refine ⟨45190875121438574586740977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60254500161918099448987969 45190875121438574586740977)
            ·
              refine ⟨33893156341078930940055733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45190875121438574586740977 33893156341078930940055733)
              ·
                refine ⟨3177483406976149775630225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33893156341078930940055733 3177483406976149775630225)
                ·
                  refine ⟨2383112555232112331722669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177483406976149775630225 2383112555232112331722669)
                  ·
                    refine ⟨893667208212042124396001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383112555232112331722669 893667208212042124396001)
                    ·
                      rfl

theorem cell22_2610616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_2610616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610616 prefixEnd_2610616 := by exact prefixLift 2610616
  have htrace : WordTrace (prefixWord ++ tailWord_2610616) baseStart_2610616 baseEnd_2610616 := by
    simpa [prefixWord, tailWord_2610616, baseEnd_2610616] using wordTrace_append hprefix tailTrace_2610616
  have hstable : (prefixWord ++ tailWord_2610616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610616).length < 2 ^ (prefixWord ++ tailWord_2610616).sum := by decide
  have hdescent : baseEnd_2610616 < baseStart_2610616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610646 : List Nat := [5, 2, 1, 1, 1, 2, 10]
def baseStart_2610646 : Nat := 118140960795 + 2610646 * 2 ^ 59
def prefixEnd_2610646 : Nat := 4983230072969 + 3 ^ 40 * 2610646 * 2
def baseEnd_2610646 : Nat := 33099165845375260968367

theorem tailTrace_2610646 : CollatzResearch.WordTrace tailWord_2610646 prefixEnd_2610646 33099165845375260968367 := by
  unfold tailWord_2610646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951130131255179980309737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63478721400055253123303861 5951130131255179980309737)
  ·
    refine ⟨4463347598441384985232303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5951130131255179980309737 4463347598441384985232303)
    ·
      refine ⟨6695021397662077477848455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463347598441384985232303 6695021397662077477848455)
      ·
        refine ⟨10042532096493116216772683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695021397662077477848455 10042532096493116216772683)
        ·
          refine ⟨15063798144739674325159025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10042532096493116216772683 15063798144739674325159025)
          ·
            refine ⟨11297848608554755743869269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15063798144739674325159025 11297848608554755743869269)
            ·
              refine ⟨33099165845375260968367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11297848608554755743869269 33099165845375260968367)
              ·
                rfl

theorem cell22_2610646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 10].length) (baseStart_2610646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610646 prefixEnd_2610646 := by exact prefixLift 2610646
  have htrace : WordTrace (prefixWord ++ tailWord_2610646) baseStart_2610646 baseEnd_2610646 := by
    simpa [prefixWord, tailWord_2610646, baseEnd_2610646] using wordTrace_append hprefix tailTrace_2610646
  have hstable : (prefixWord ++ tailWord_2610646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610646).length < 2 ^ (prefixWord ++ tailWord_2610646).sum := by decide
  have hdescent : baseEnd_2610646 < baseStart_2610646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610721 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 3, 4]
def baseStart_2610721 : Nat := 118140960795 + 2610721 * 2 ^ 59
def prefixEnd_2610721 : Nat := 4983230072969 + 3 ^ 40 * 2610721 * 2
def baseEnd_2610721 : Nat := 893703151857856850520679

theorem tailTrace_2610721 : CollatzResearch.WordTrace tailWord_2610721 prefixEnd_2610721 893703151857856850520679 := by
  unfold tailWord_2610721
  simp only [CollatzResearch.WordTrace]
  refine ⟨95220817574811167493936017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63480545049874111662624011 95220817574811167493936017)
  ·
    refine ⟨71415613181108375620452013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95220817574811167493936017 71415613181108375620452013)
    ·
      refine ⟨26780854942915640857669505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71415613181108375620452013 26780854942915640857669505)
      ·
        refine ⟨20085641207186730643252129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26780854942915640857669505 20085641207186730643252129)
        ·
          refine ⟨15064230905390047982439097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20085641207186730643252129 15064230905390047982439097)
          ·
            refine ⟨11298173179042535986829323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15064230905390047982439097 11298173179042535986829323)
            ·
              refine ⟨16947259768563803980243985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11298173179042535986829323 16947259768563803980243985)
              ·
                refine ⟨12710444826422852985182989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16947259768563803980243985 12710444826422852985182989)
                ·
                  refine ⟨4766416809908569869443621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12710444826422852985182989 4766416809908569869443621)
                  ·
                    refine ⟨893703151857856850520679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766416809908569869443621 893703151857856850520679)
                    ·
                      rfl

theorem cell22_2610721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_2610721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610721 prefixEnd_2610721 := by exact prefixLift 2610721
  have htrace : WordTrace (prefixWord ++ tailWord_2610721) baseStart_2610721 baseEnd_2610721 := by
    simpa [prefixWord, tailWord_2610721, baseEnd_2610721] using wordTrace_append hprefix tailTrace_2610721
  have hstable : (prefixWord ++ tailWord_2610721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610721).length < 2 ^ (prefixWord ++ tailWord_2610721).sum := by decide
  have hdescent : baseEnd_2610721 < baseStart_2610721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610751 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2610751 : Nat := 118140960795 + 2610751 * 2 ^ 59
def prefixEnd_2610751 : Nat := 4983230072969 + 3 ^ 40 * 2610751 * 2
def baseEnd_2610751 : Nat := 893713421470946772270587

theorem tailTrace_2610751 : CollatzResearch.WordTrace tailWord_2610751 prefixEnd_2610751 893713421470946772270587 := by
  unfold tailWord_2610751
  simp only [CollatzResearch.WordTrace]
  refine ⟨95221911764702482617528107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63481274509801655078352071 95221911764702482617528107)
  ·
    refine ⟨142832867647053723926292161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95221911764702482617528107 142832867647053723926292161)
    ·
      refine ⟨107124650735290292944719121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142832867647053723926292161 107124650735290292944719121)
      ·
        refine ⟨80343488051467719708539341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107124650735290292944719121 80343488051467719708539341)
        ·
          refine ⟨30128808019300394890702253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80343488051467719708539341 30128808019300394890702253)
          ·
            refine ⟨11298303007237648084013345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30128808019300394890702253 11298303007237648084013345)
            ·
              refine ⟨8473727255428236063010009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11298303007237648084013345 8473727255428236063010009)
              ·
                refine ⟨6355295441571177047257507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8473727255428236063010009 6355295441571177047257507)
                ·
                  refine ⟨9532943162356765570886261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355295441571177047257507 9532943162356765570886261)
                  ·
                    refine ⟨893713421470946772270587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9532943162356765570886261 893713421470946772270587)
                    ·
                      rfl

theorem cell22_2610751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2610751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610751 prefixEnd_2610751 := by exact prefixLift 2610751
  have htrace : WordTrace (prefixWord ++ tailWord_2610751) baseStart_2610751 baseEnd_2610751 := by
    simpa [prefixWord, tailWord_2610751, baseEnd_2610751] using wordTrace_append hprefix tailTrace_2610751
  have hstable : (prefixWord ++ tailWord_2610751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610751).length < 2 ^ (prefixWord ++ tailWord_2610751).sum := by decide
  have hdescent : baseEnd_2610751 < baseStart_2610751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610766 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2610766 : Nat := 118140960795 + 2610766 * 2 ^ 59
def prefixEnd_2610766 : Nat := 4983230072969 + 3 ^ 40 * 2610766 * 2
def baseEnd_2610766 : Nat := 893718556277491733145541

theorem tailTrace_2610766 : CollatzResearch.WordTrace tailWord_2610766 prefixEnd_2610766 893718556277491733145541 := by
  unfold tailWord_2610766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902807357456017522415519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63481639239765426786216101 11902807357456017522415519)
  ·
    refine ⟨17854211036184026283623279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11902807357456017522415519 17854211036184026283623279)
    ·
      refine ⟨26781316554276039425434919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854211036184026283623279 26781316554276039425434919)
      ·
        refine ⟨40171974831414059138152379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26781316554276039425434919 40171974831414059138152379)
        ·
          refine ⟨60257962247121088707228569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40171974831414059138152379 60257962247121088707228569)
          ·
            refine ⟨45193471685340816530421427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60257962247121088707228569 45193471685340816530421427)
            ·
              refine ⟨67790207528011224795632141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45193471685340816530421427 67790207528011224795632141)
              ·
                refine ⟨25421327823004209298362053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67790207528011224795632141 25421327823004209298362053)
                ·
                  refine ⟨4766498966813289243442885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25421327823004209298362053 4766498966813289243442885)
                  ·
                    refine ⟨893718556277491733145541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766498966813289243442885 893718556277491733145541)
                    ·
                      rfl

theorem cell22_2610766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2610766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610766 prefixEnd_2610766 := by exact prefixLift 2610766
  have htrace : WordTrace (prefixWord ++ tailWord_2610766) baseStart_2610766 baseEnd_2610766 := by
    simpa [prefixWord, tailWord_2610766, baseEnd_2610766] using wordTrace_append hprefix tailTrace_2610766
  have hstable : (prefixWord ++ tailWord_2610766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610766).length < 2 ^ (prefixWord ++ tailWord_2610766).sum := by decide
  have hdescent : baseEnd_2610766 < baseStart_2610766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610785 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 2, 3]
def baseStart_2610785 : Nat := 118140960795 + 2610785 * 2 ^ 59
def prefixEnd_2610785 : Nat := 4983230072969 + 3 ^ 40 * 2610785 * 2
def baseEnd_2610785 : Nat := 893725060365782016920483

theorem tailTrace_2610785 : CollatzResearch.WordTrace tailWord_2610785 prefixEnd_2610785 893725060365782016920483 := by
  unfold tailWord_2610785
  simp only [CollatzResearch.WordTrace]
  refine ⟨95223151846579306424265809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63482101231052870949510539 95223151846579306424265809)
  ·
    refine ⟨71417363884934479818199357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95223151846579306424265809 71417363884934479818199357)
    ·
      refine ⟨26781511456850429931824759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71417363884934479818199357 26781511456850429931824759)
      ·
        refine ⟨40172267185275644897737139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26781511456850429931824759 40172267185275644897737139)
        ·
          refine ⟨60258400777913467346605709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40172267185275644897737139 60258400777913467346605709)
          ·
            refine ⟨22596900291717550254977141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60258400777913467346605709 22596900291717550254977141)
            ·
              refine ⟨2118459402348520336404107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22596900291717550254977141 2118459402348520336404107)
              ·
                refine ⟨3177689103522780504606161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118459402348520336404107 3177689103522780504606161)
                ·
                  refine ⟨2383266827642085378454621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177689103522780504606161 2383266827642085378454621)
                  ·
                    refine ⟨893725060365782016920483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383266827642085378454621 893725060365782016920483)
                    ·
                      rfl

theorem cell22_2610785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_2610785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610785 prefixEnd_2610785 := by exact prefixLift 2610785
  have htrace : WordTrace (prefixWord ++ tailWord_2610785) baseStart_2610785 baseEnd_2610785 := by
    simpa [prefixWord, tailWord_2610785, baseEnd_2610785] using wordTrace_append hprefix tailTrace_2610785
  have hstable : (prefixWord ++ tailWord_2610785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610785).length < 2 ^ (prefixWord ++ tailWord_2610785).sum := by decide
  have hdescent : baseEnd_2610785 < baseStart_2610785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610798 : List Nat := [4, 1, 2, 2, 3, 1, 1, 8]
def baseStart_2610798 : Nat := 118140960795 + 2610798 * 2 ^ 59
def prefixEnd_2610798 : Nat := 4983230072969 + 3 ^ 40 * 2610798 * 2
def baseEnd_2610798 : Nat := 99303278947939368482827

theorem tailTrace_2610798 : CollatzResearch.WordTrace tailWord_2610798 prefixEnd_2610798 99303278947939368482827 := by
  unfold tailWord_2610798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11902953249441526205561131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63482417330354806429659365 11902953249441526205561131)
  ·
    refine ⟨17854429874162289308341697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11902953249441526205561131 17854429874162289308341697)
    ·
      refine ⟨13390822405621716981256273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17854429874162289308341697 13390822405621716981256273)
      ·
        refine ⟨10043116804216287735942205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13390822405621716981256273 10043116804216287735942205)
        ·
          refine ⟨3766168801581107900978327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10043116804216287735942205 3766168801581107900978327)
          ·
            refine ⟨5649253202371661851467491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3766168801581107900978327 5649253202371661851467491)
            ·
              refine ⟨8473879803557492777201237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649253202371661851467491 8473879803557492777201237)
              ·
                refine ⟨99303278947939368482827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8473879803557492777201237 99303278947939368482827)
                ·
                  rfl

theorem cell22_2610798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_2610798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610798 prefixEnd_2610798 := by exact prefixLift 2610798
  have htrace : WordTrace (prefixWord ++ tailWord_2610798) baseStart_2610798 baseEnd_2610798 := by
    simpa [prefixWord, tailWord_2610798, baseEnd_2610798] using wordTrace_append hprefix tailTrace_2610798
  have hstable : (prefixWord ++ tailWord_2610798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610798).length < 2 ^ (prefixWord ++ tailWord_2610798).sum := by decide
  have hdescent : baseEnd_2610798 < baseStart_2610798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610830 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_2610830 : Nat := 118140960795 + 2610830 * 2 ^ 59
def prefixEnd_2610830 : Nat := 4983230072969 + 3 ^ 40 * 2610830 * 2
def baseEnd_2610830 : Nat := 893740464785416899545345

theorem tailTrace_2610830 : CollatzResearch.WordTrace tailWord_2610830 prefixEnd_2610830 893740464785416899545345 := by
  unfold tailWord_2610830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11903099141427034888706743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63483195420944186073102629 11903099141427034888706743)
  ·
    refine ⟨17854648712140552333060115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11903099141427034888706743 17854648712140552333060115)
    ·
      refine ⟨26781973068210828499590173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17854648712140552333060115 26781973068210828499590173)
      ·
        refine ⟨10043239900579060687346315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26781973068210828499590173 10043239900579060687346315)
        ·
          refine ⟨15064859850868591031019473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043239900579060687346315 15064859850868591031019473)
          ·
            refine ⟨11298644888151443273264605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15064859850868591031019473 11298644888151443273264605)
            ·
              refine ⟨4236991833056791227474227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11298644888151443273264605 4236991833056791227474227)
              ·
                refine ⟨6355487749585186841211341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4236991833056791227474227 6355487749585186841211341)
                ·
                  refine ⟨2383307906094445065454253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6355487749585186841211341 2383307906094445065454253)
                  ·
                    refine ⟨893740464785416899545345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383307906094445065454253 893740464785416899545345)
                    ·
                      rfl

theorem cell22_2610830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_2610830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610830 prefixEnd_2610830 := by exact prefixLift 2610830
  have htrace : WordTrace (prefixWord ++ tailWord_2610830) baseStart_2610830 baseEnd_2610830 := by
    simpa [prefixWord, tailWord_2610830, baseEnd_2610830] using wordTrace_append hprefix tailTrace_2610830
  have hstable : (prefixWord ++ tailWord_2610830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610830).length < 2 ^ (prefixWord ++ tailWord_2610830).sum := by decide
  have hdescent : baseEnd_2610830 < baseStart_2610830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610836 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2610836 : Nat := 118140960795 + 2610836 * 2 ^ 59
def prefixEnd_2610836 : Nat := 4983230072969 + 3 ^ 40 * 2610836 * 2
def baseEnd_2610836 : Nat := 893742518708034883895327

theorem tailTrace_2610836 : CollatzResearch.WordTrace tailWord_2610836 prefixEnd_2610836 893742518708034883895327 := by
  unfold tailWord_2610836
  simp only [CollatzResearch.WordTrace]
  refine ⟨47612505984697271067186181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63483341312929694756248241 47612505984697271067186181)
  ·
    refine ⟨8927344872130738325097409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47612505984697271067186181 8927344872130738325097409)
    ·
      refine ⟨6695508654098053743823057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8927344872130738325097409 6695508654098053743823057)
      ·
        refine ⟨5021631490573540307867293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6695508654098053743823057 5021631490573540307867293)
        ·
          refine ⟨1883111808965077615450235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5021631490573540307867293 1883111808965077615450235)
          ·
            refine ⟨2824667713447616423175353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883111808965077615450235 2824667713447616423175353)
            ·
              refine ⟨2118500785085712317381515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824667713447616423175353 2118500785085712317381515)
              ·
                refine ⟨3177751177628568476072273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2118500785085712317381515 3177751177628568476072273)
                ·
                  refine ⟨2383313383221426357054205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3177751177628568476072273 2383313383221426357054205)
                  ·
                    refine ⟨893742518708034883895327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383313383221426357054205 893742518708034883895327)
                    ·
                      rfl

theorem cell22_2610836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2610836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610836 prefixEnd_2610836 := by exact prefixLift 2610836
  have htrace : WordTrace (prefixWord ++ tailWord_2610836) baseStart_2610836 baseEnd_2610836 := by
    simpa [prefixWord, tailWord_2610836, baseEnd_2610836] using wordTrace_append hprefix tailTrace_2610836
  have hstable : (prefixWord ++ tailWord_2610836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610836).length < 2 ^ (prefixWord ++ tailWord_2610836).sum := by decide
  have hdescent : baseEnd_2610836 < baseStart_2610836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610873 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 1, 4]
def baseStart_2610873 : Nat := 118140960795 + 2610873 * 2 ^ 59
def prefixEnd_2610873 : Nat := 4983230072969 + 3 ^ 40 * 2610873 * 2
def baseEnd_2610873 : Nat := 893755184564179120720213

theorem tailTrace_2610873 : CollatzResearch.WordTrace tailWord_2610873 prefixEnd_2610873 893755184564179120720213 := by
  unfold tailWord_2610873
  simp only [CollatzResearch.WordTrace]
  refine ⟨95226361470260497453469273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63484240980173664968979515 95226361470260497453469273)
  ·
    refine ⟨71419771102695373090101955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95226361470260497453469273 71419771102695373090101955)
    ·
      refine ⟨107129656654043059635152933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71419771102695373090101955 107129656654043059635152933)
      ·
        refine ⟨20086810622633073681591175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107129656654043059635152933 20086810622633073681591175)
        ·
          refine ⟨30130215933949610522386763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20086810622633073681591175 30130215933949610522386763)
          ·
            refine ⟨45195323900924415783580145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30130215933949610522386763 45195323900924415783580145)
            ·
              refine ⟨33896492925693311837685109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45195323900924415783580145 33896492925693311837685109)
              ·
                refine ⟨3177796211783747984782979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33896492925693311837685109 3177796211783747984782979)
                ·
                  refine ⟨4766694317675621977174469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3177796211783747984782979 4766694317675621977174469)
                  ·
                    refine ⟨893755184564179120720213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766694317675621977174469 893755184564179120720213)
                    ·
                      rfl

theorem cell22_2610873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 4].length) (baseStart_2610873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610873 prefixEnd_2610873 := by exact prefixLift 2610873
  have htrace : WordTrace (prefixWord ++ tailWord_2610873) baseStart_2610873 baseEnd_2610873 := by
    simpa [prefixWord, tailWord_2610873, baseEnd_2610873] using wordTrace_append hprefix tailTrace_2610873
  have hstable : (prefixWord ++ tailWord_2610873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610873).length < 2 ^ (prefixWord ++ tailWord_2610873).sum := by decide
  have hdescent : baseEnd_2610873 < baseStart_2610873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610903 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2610903 : Nat := 118140960795 + 2610903 * 2 ^ 59
def prefixEnd_2610903 : Nat := 4983230072969 + 3 ^ 40 * 2610903 * 2
def baseEnd_2610903 : Nat := 893765454177269042470121

theorem tailTrace_2610903 : CollatzResearch.WordTrace tailWord_2610903 prefixEnd_2610903 893765454177269042470121 := by
  unfold tailWord_2610903
  simp only [CollatzResearch.WordTrace]
  refine ⟨95227455660151812577061363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63484970440101208384707575 95227455660151812577061363)
  ·
    refine ⟨142841183490227718865592045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95227455660151812577061363 142841183490227718865592045)
    ·
      refine ⟨53565443808835394574597017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142841183490227718865592045 53565443808835394574597017)
      ·
        refine ⟨40174082856626545930947763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53565443808835394574597017 40174082856626545930947763)
        ·
          refine ⟨60261124284939818896421645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40174082856626545930947763 60261124284939818896421645)
          ·
            refine ⟨22597921606852432086158117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60261124284939818896421645 22597921606852432086158117)
            ·
              refine ⟨4237110301284831016154647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22597921606852432086158117 4237110301284831016154647)
              ·
                refine ⟨6355665451927246524231971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237110301284831016154647 6355665451927246524231971)
                ·
                  refine ⟨9533498177890869786347957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6355665451927246524231971 9533498177890869786347957)
                  ·
                    refine ⟨893765454177269042470121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9533498177890869786347957 893765454177269042470121)
                    ·
                      rfl

theorem cell22_2610903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2610903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610903 prefixEnd_2610903 := by exact prefixLift 2610903
  have htrace : WordTrace (prefixWord ++ tailWord_2610903) baseStart_2610903 baseEnd_2610903 := by
    simpa [prefixWord, tailWord_2610903, baseEnd_2610903] using wordTrace_append hprefix tailTrace_2610903
  have hstable : (prefixWord ++ tailWord_2610903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610903).length < 2 ^ (prefixWord ++ tailWord_2610903).sum := by decide
  have hdescent : baseEnd_2610903 < baseStart_2610903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610965 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2610965 : Nat := 118140960795 + 2610965 * 2 ^ 59
def prefixEnd_2610965 : Nat := 4983230072969 + 3 ^ 40 * 2610965 * 2
def baseEnd_2610965 : Nat := 893786678044321547419931

theorem tailTrace_2610965 : CollatzResearch.WordTrace tailWord_2610965 prefixEnd_2610965 893786678044321547419931 := by
  unfold tailWord_2610965
  simp only [CollatzResearch.WordTrace]
  refine ⟨95229716985927197165818349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63486477990618131443878899 95229716985927197165818349)
  ·
    refine ⟨35711143869722698937181881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95229716985927197165818349 35711143869722698937181881)
    ·
      refine ⟨26783357902292024202886411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35711143869722698937181881 26783357902292024202886411)
      ·
        refine ⟨40175036853438036304329617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26783357902292024202886411 40175036853438036304329617)
        ·
          refine ⟨30131277640078527228247213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40175036853438036304329617 30131277640078527228247213)
          ·
            refine ⟨11299229115029447710592705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30131277640078527228247213 11299229115029447710592705)
            ·
              refine ⟨8474421836272085782944529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11299229115029447710592705 8474421836272085782944529)
              ·
                refine ⟨6355816377204064337208397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8474421836272085782944529 6355816377204064337208397)
                ·
                  refine ⟨2383431141451524126453149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6355816377204064337208397 2383431141451524126453149)
                  ·
                    refine ⟨893786678044321547419931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383431141451524126453149 893786678044321547419931)
                    ·
                      rfl

theorem cell22_2610965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2610965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610965 prefixEnd_2610965 := by exact prefixLift 2610965
  have htrace : WordTrace (prefixWord ++ tailWord_2610965) baseStart_2610965 baseEnd_2610965 := by
    simpa [prefixWord, tailWord_2610965, baseEnd_2610965] using wordTrace_append hprefix tailTrace_2610965
  have hstable : (prefixWord ++ tailWord_2610965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610965).length < 2 ^ (prefixWord ++ tailWord_2610965).sum := by decide
  have hdescent : baseEnd_2610965 < baseStart_2610965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2610978 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2610978 : Nat := 118140960795 + 2610978 * 2 ^ 59
def prefixEnd_2610978 : Nat := 4983230072969 + 3 ^ 40 * 2610978 * 2
def baseEnd_2610978 : Nat := 297930376069997948948297

theorem tailTrace_2610978 : CollatzResearch.WordTrace tailWord_2610978 prefixEnd_2610978 297930376069997948948297 := by
  unfold tailWord_2610978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23807547783720025096510397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63486794089920066924027725 23807547783720025096510397)
  ·
    refine ⟨8927830418895009411191399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23807547783720025096510397 8927830418895009411191399)
    ·
      refine ⟨13391745628342514116787099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8927830418895009411191399 13391745628342514116787099)
      ·
        refine ⟨20087618442513771175180649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13391745628342514116787099 20087618442513771175180649)
        ·
          refine ⟨15065713831885328381385487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20087618442513771175180649 15065713831885328381385487)
          ·
            refine ⟨22598570747827992572078231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15065713831885328381385487 22598570747827992572078231)
            ·
              refine ⟨33897856121741988858117347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22598570747827992572078231 33897856121741988858117347)
              ·
                refine ⟨50846784182612983287176021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33897856121741988858117347 50846784182612983287176021)
                ·
                  refine ⟨297930376069997948948297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 50846784182612983287176021 297930376069997948948297)
                  ·
                    rfl

theorem cell22_2610978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2610978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2610978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2610978 prefixEnd_2610978 := by exact prefixLift 2610978
  have htrace : WordTrace (prefixWord ++ tailWord_2610978) baseStart_2610978 baseEnd_2610978 := by
    simpa [prefixWord, tailWord_2610978, baseEnd_2610978] using wordTrace_append hprefix tailTrace_2610978
  have hstable : (prefixWord ++ tailWord_2610978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2610978).length < 2 ^ (prefixWord ++ tailWord_2610978).sum := by decide
  have hdescent : baseEnd_2610978 < baseStart_2610978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2610978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611025 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 3, 4]
def baseStart_2611025 : Nat := 118140960795 + 2611025 * 2 ^ 59
def prefixEnd_2611025 : Nat := 4983230072969 + 3 ^ 40 * 2611025 * 2
def baseEnd_2611025 : Nat := 893807217270501390919747

theorem tailTrace_2611025 : CollatzResearch.WordTrace tailWord_2611025 prefixEnd_2611025 893807217270501390919747 := by
  unfold tailWord_2611025
  simp only [CollatzResearch.WordTrace]
  refine ⟨95231905365709827413002529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63487936910473218275335019 95231905365709827413002529)
  ·
    refine ⟨71423929024282370559751897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95231905365709827413002529 71423929024282370559751897)
    ·
      refine ⟨53567946768211777919813923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71423929024282370559751897 53567946768211777919813923)
      ·
        refine ⟨80351920152317666879720885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53567946768211777919813923 80351920152317666879720885)
        ·
          refine ⟨7532992514279781269973833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80351920152317666879720885 7532992514279781269973833)
          ·
            refine ⟨5649744385709835952480375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7532992514279781269973833 5649744385709835952480375)
            ·
              refine ⟨8474616578564753928720563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5649744385709835952480375 8474616578564753928720563)
              ·
                refine ⟨12711924867847130893080845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8474616578564753928720563 12711924867847130893080845)
                ·
                  refine ⟨4766971825442674084905317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12711924867847130893080845 4766971825442674084905317)
                  ·
                    refine ⟨893807217270501390919747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4766971825442674084905317 893807217270501390919747)
                    ·
                      rfl

theorem cell22_2611025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_2611025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611025 prefixEnd_2611025 := by exact prefixLift 2611025
  have htrace : WordTrace (prefixWord ++ tailWord_2611025) baseStart_2611025 baseEnd_2611025 := by
    simpa [prefixWord, tailWord_2611025, baseEnd_2611025] using wordTrace_append hprefix tailTrace_2611025
  have hstable : (prefixWord ++ tailWord_2611025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611025).length < 2 ^ (prefixWord ++ tailWord_2611025).sum := by decide
  have hdescent : baseEnd_2611025 < baseStart_2611025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611050 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2611050 : Nat := 118140960795 + 2611050 * 2 ^ 59
def prefixEnd_2611050 : Nat := 4983230072969 + 3 ^ 40 * 2611050 * 2
def baseEnd_2611050 : Nat := 893815775281409659044671

theorem tailTrace_2611050 : CollatzResearch.WordTrace tailWord_2611050 prefixEnd_2611050 893815775281409659044671 := by
  unfold tailWord_2611050
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808204297654814170665651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63488544793746171121775069 23808204297654814170665651)
  ·
    refine ⟨35712306446482221255998477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23808204297654814170665651 35712306446482221255998477)
    ·
      refine ⟨13392114917430832970999429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35712306446482221255998477 13392114917430832970999429)
      ·
        refine ⟨2511021547018281182062393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13392114917430832970999429 2511021547018281182062393)
        ·
          refine ⟨1883266160263710886546795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2511021547018281182062393 1883266160263710886546795)
          ·
            refine ⟨2824899240395566329820193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883266160263710886546795 2824899240395566329820193)
            ·
              refine ⟨2118674430296674747365145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2824899240395566329820193 2118674430296674747365145)
              ·
                refine ⟨1589005822722506060523859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118674430296674747365145 1589005822722506060523859)
                ·
                  refine ⟨2383508734083759090785789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589005822722506060523859 2383508734083759090785789)
                  ·
                    refine ⟨893815775281409659044671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383508734083759090785789 893815775281409659044671)
                    ·
                      rfl

theorem cell22_2611050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2611050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611050 prefixEnd_2611050 := by exact prefixLift 2611050
  have htrace : WordTrace (prefixWord ++ tailWord_2611050) baseStart_2611050 baseEnd_2611050 := by
    simpa [prefixWord, tailWord_2611050, baseEnd_2611050] using wordTrace_append hprefix tailTrace_2611050
  have hstable : (prefixWord ++ tailWord_2611050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611050).length < 2 ^ (prefixWord ++ tailWord_2611050).sum := by decide
  have hdescent : baseEnd_2611050 < baseStart_2611050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611106 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2611106 : Nat := 118140960795 + 2611106 * 2 ^ 59
def prefixEnd_2611106 : Nat := 4983230072969 + 3 ^ 40 * 2611106 * 2
def baseEnd_2611106 : Nat := 893834945225844179644499

theorem tailTrace_2611106 : CollatzResearch.WordTrace tailWord_2611106 prefixEnd_2611106 893834945225844179644499 := by
  unfold tailWord_2611106
  simp only [CollatzResearch.WordTrace]
  refine ⟨23808714919604094561675293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63489906452277585497800781 23808714919604094561675293)
  ·
    refine ⟨8928268094851535460628235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23808714919604094561675293 8928268094851535460628235)
    ·
      refine ⟨13392402142277303190942353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8928268094851535460628235 13392402142277303190942353)
      ·
        refine ⟨10044301606707977393206765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13392402142277303190942353 10044301606707977393206765)
        ·
          refine ⟨3766613102515491522452537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10044301606707977393206765 3766613102515491522452537)
          ·
            refine ⟨2824959826886618641839403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3766613102515491522452537 2824959826886618641839403)
            ·
              refine ⟨4237439740329927962759105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2824959826886618641839403 4237439740329927962759105)
              ·
                refine ⟨3178079805247445972069329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4237439740329927962759105 3178079805247445972069329)
                ·
                  refine ⟨2383559853935584479051997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178079805247445972069329 2383559853935584479051997)
                  ·
                    refine ⟨893834945225844179644499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383559853935584479051997 893834945225844179644499)
                    ·
                      rfl

theorem cell22_2611106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2611106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611106 prefixEnd_2611106 := by exact prefixLift 2611106
  have htrace : WordTrace (prefixWord ++ tailWord_2611106) baseStart_2611106 baseEnd_2611106 := by
    simpa [prefixWord, tailWord_2611106, baseEnd_2611106] using wordTrace_append hprefix tailTrace_2611106
  have hstable : (prefixWord ++ tailWord_2611106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611106).length < 2 ^ (prefixWord ++ tailWord_2611106).sum := by decide
  have hdescent : baseEnd_2611106 < baseStart_2611106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611207 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2611207 : Nat := 118140960795 + 2611207 * 2 ^ 59
def prefixEnd_2611207 : Nat := 4983230072969 + 3 ^ 40 * 2611207 * 2
def baseEnd_2611207 : Nat := 893869519589913582869189

theorem tailTrace_2611207 : CollatzResearch.WordTrace tailWord_2611207 prefixEnd_2611207 893869519589913582869189 := by
  unfold tailWord_2611207
  simp only [CollatzResearch.WordTrace]
  refine ⟨95238543451050472496127875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63492362300700314997418583 95238543451050472496127875)
  ·
    refine ⟨142857815176575708744191813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95238543451050472496127875 142857815176575708744191813)
    ·
      refine ⟨26785840345607945389535965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 142857815176575708744191813 26785840345607945389535965)
      ·
        refine ⟨10044690129602979521075987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26785840345607945389535965 10044690129602979521075987)
        ·
          refine ⟨15067035194404469281613981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10044690129602979521075987 15067035194404469281613981)
          ·
            refine ⟨5650138197901675980605243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15067035194404469281613981 5650138197901675980605243)
            ·
              refine ⟨8475207296852513970907865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5650138197901675980605243 8475207296852513970907865)
              ·
                refine ⟨6356405472639385478180899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8475207296852513970907865 6356405472639385478180899)
                ·
                  refine ⟨9534608208959078217271349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6356405472639385478180899 9534608208959078217271349)
                  ·
                    refine ⟨893869519589913582869189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9534608208959078217271349 893869519589913582869189)
                    ·
                      rfl

theorem cell22_2611207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2611207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611207 prefixEnd_2611207 := by exact prefixLift 2611207
  have htrace : WordTrace (prefixWord ++ tailWord_2611207) baseStart_2611207 baseEnd_2611207 := by
    simpa [prefixWord, tailWord_2611207, baseEnd_2611207] using wordTrace_append hprefix tailTrace_2611207
  have hstable : (prefixWord ++ tailWord_2611207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611207).length < 2 ^ (prefixWord ++ tailWord_2611207).sum := by decide
  have hdescent : baseEnd_2611207 < baseStart_2611207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611224 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 2, 3]
def baseStart_2611224 : Nat := 118140960795 + 2611224 * 2 ^ 59
def prefixEnd_2611224 : Nat := 4983230072969 + 3 ^ 40 * 2611224 * 2
def baseEnd_2611224 : Nat := 893875339037331205194137

theorem tailTrace_2611224 : CollatzResearch.WordTrace tailWord_2611224 prefixEnd_2611224 893875339037331205194137 := by
  unfold tailWord_2611224
  simp only [CollatzResearch.WordTrace]
  refine ⟨47619581745994442199748363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63492775661325922932997817 47619581745994442199748363)
  ·
    refine ⟨71429372618991663299622545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47619581745994442199748363 71429372618991663299622545)
    ·
      refine ⟨53572029464243747474716909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71429372618991663299622545 53572029464243747474716909)
      ·
        refine ⟨20089511049091405303018841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53572029464243747474716909 20089511049091405303018841)
        ·
          refine ⟨15067133286818553977264131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20089511049091405303018841 15067133286818553977264131)
          ·
            refine ⟨22600699930227830965896197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15067133286818553977264131 22600699930227830965896197)
            ·
              refine ⟨4237631236917718306105537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22600699930227830965896197 4237631236917718306105537)
              ·
                refine ⟨3178223427688288729579153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4237631236917718306105537 3178223427688288729579153)
                ·
                  refine ⟨2383667570766216547184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178223427688288729579153 2383667570766216547184365)
                  ·
                    refine ⟨893875339037331205194137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383667570766216547184365 893875339037331205194137)
                    ·
                      rfl

theorem cell22_2611224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 3].length) (baseStart_2611224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611224 prefixEnd_2611224 := by exact prefixLift 2611224
  have htrace : WordTrace (prefixWord ++ tailWord_2611224) baseStart_2611224 baseEnd_2611224 := by
    simpa [prefixWord, tailWord_2611224, baseEnd_2611224] using wordTrace_append hprefix tailTrace_2611224
  have hstable : (prefixWord ++ tailWord_2611224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611224).length < 2 ^ (prefixWord ++ tailWord_2611224).sum := by decide
  have hdescent : baseEnd_2611224 < baseStart_2611224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611226 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_2611226 : Nat := 118140960795 + 2611226 * 2 ^ 59
def prefixEnd_2611226 : Nat := 4983230072969 + 3 ^ 40 * 2611226 * 2
def baseEnd_2611226 : Nat := 297958674559401288881377

theorem tailTrace_2611226 : CollatzResearch.WordTrace tailWord_2611226 prefixEnd_2611226 297958674559401288881377 := by
  unfold tailWord_2611226
  simp only [CollatzResearch.WordTrace]
  refine ⟨23809809109495409685267383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63492824291987759160713021 23809809109495409685267383)
  ·
    refine ⟨35714713664243114527901075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23809809109495409685267383 35714713664243114527901075)
    ·
      refine ⟨53572070496364671791851613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714713664243114527901075 53572070496364671791851613)
      ·
        refine ⟨20089526436136751921944355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53572070496364671791851613 20089526436136751921944355)
        ·
          refine ⟨30134289654205127882916533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20089526436136751921944355 30134289654205127882916533)
          ·
            refine ⟨2825089655081730739023425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30134289654205127882916533 2825089655081730739023425)
            ·
              refine ⟨2118817241311298054267569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825089655081730739023425 2118817241311298054267569)
              ·
                refine ⟨1589112930983473540700677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2118817241311298054267569 1589112930983473540700677)
                ·
                  refine ⟨297958674559401288881377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1589112930983473540700677 297958674559401288881377)
                  ·
                    rfl

theorem cell22_2611226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_2611226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611226 prefixEnd_2611226 := by exact prefixLift 2611226
  have htrace : WordTrace (prefixWord ++ tailWord_2611226) baseStart_2611226 baseEnd_2611226 := by
    simpa [prefixWord, tailWord_2611226, baseEnd_2611226] using wordTrace_append hprefix tailTrace_2611226
  have hstable : (prefixWord ++ tailWord_2611226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611226).length < 2 ^ (prefixWord ++ tailWord_2611226).sum := by decide
  have hdescent : baseEnd_2611226 < baseStart_2611226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611237 : List Nat := [1, 3, 1, 2, 2, 5, 1, 7]
def baseStart_2611237 : Nat := 118140960795 + 2611237 * 2 ^ 59
def prefixEnd_2611237 : Nat := 4983230072969 + 3 ^ 40 * 2611237 * 2
def baseEnd_2611237 : Nat := 99319976578111500513233

theorem tailTrace_2611237 : CollatzResearch.WordTrace tailWord_2611237 prefixEnd_2611237 99319976578111500513233 := by
  unfold tailWord_2611237
  simp only [CollatzResearch.WordTrace]
  refine ⟨95239637640941787619719965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63493091760627858413146643 95239637640941787619719965)
  ·
    refine ⟨35714864115353170357394987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95239637640941787619719965 35714864115353170357394987)
    ·
      refine ⟨53572296173029755536092481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35714864115353170357394987 53572296173029755536092481)
      ·
        refine ⟨40179222129772316652069361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53572296173029755536092481 40179222129772316652069361)
        ·
          refine ⟨30134416597329237489052021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40179222129772316652069361 30134416597329237489052021)
          ·
            refine ⟨2825101555999616014598627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30134416597329237489052021 2825101555999616014598627)
            ·
              refine ⟨4237652333999424021897941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825101555999616014598627 4237652333999424021897941)
              ·
                refine ⟨99319976578111500513233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4237652333999424021897941 99319976578111500513233)
                ·
                  rfl

theorem cell22_2611237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 7].length) (baseStart_2611237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611237 prefixEnd_2611237 := by exact prefixLift 2611237
  have htrace : WordTrace (prefixWord ++ tailWord_2611237) baseStart_2611237 baseEnd_2611237 := by
    simpa [prefixWord, tailWord_2611237, baseEnd_2611237] using wordTrace_append hprefix tailTrace_2611237
  have hstable : (prefixWord ++ tailWord_2611237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611237).length < 2 ^ (prefixWord ++ tailWord_2611237).sum := by decide
  have hdescent : baseEnd_2611237 < baseStart_2611237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611254 : List Nat := [5, 1, 2, 1, 1, 1, 5, 6]
def baseStart_2611254 : Nat := 118140960795 + 2611254 * 2 ^ 59
def prefixEnd_2611254 : Nat := 4983230072969 + 3 ^ 40 * 2611254 * 2
def baseEnd_2611254 : Nat := 99320623183380125216005

theorem tailTrace_2611254 : CollatzResearch.WordTrace tailWord_2611254 prefixEnd_2611254 99320623183380125216005 := by
  unfold tailWord_2611254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952516105117512470193051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63493505121253466348725877 5952516105117512470193051)
  ·
    refine ⟨8928774157676268705289577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952516105117512470193051 8928774157676268705289577)
    ·
      refine ⟨6696580618257201528967183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8928774157676268705289577 6696580618257201528967183)
      ·
        refine ⟨10044870927385802293450775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6696580618257201528967183 10044870927385802293450775)
        ·
          refine ⟨15067306391078703440176163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10044870927385802293450775 15067306391078703440176163)
          ·
            refine ⟨22600959586618055160264245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15067306391078703440176163 22600959586618055160264245)
            ·
              refine ⟨2118839961245442671274773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22600959586618055160264245 2118839961245442671274773)
              ·
                refine ⟨99320623183380125216005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2118839961245442671274773 99320623183380125216005)
                ·
                  rfl

theorem cell22_2611254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_2611254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611254 prefixEnd_2611254 := by exact prefixLift 2611254
  have htrace : WordTrace (prefixWord ++ tailWord_2611254) baseStart_2611254 baseEnd_2611254 := by
    simpa [prefixWord, tailWord_2611254, baseEnd_2611254] using wordTrace_append hprefix tailTrace_2611254
  have hstable : (prefixWord ++ tailWord_2611254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611254).length < 2 ^ (prefixWord ++ tailWord_2611254).sum := by decide
  have hdescent : baseEnd_2611254 < baseStart_2611254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611256 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 2, 4]
def baseStart_2611256 : Nat := 118140960795 + 2611256 * 2 ^ 59
def prefixEnd_2611256 : Nat := 4983230072969 + 3 ^ 40 * 2611256 * 2
def baseEnd_2611256 : Nat := 893886293291293788394039

theorem tailTrace_2611256 : CollatzResearch.WordTrace tailWord_2611256 prefixEnd_2611256 893886293291293788394039 := by
  unfold tailWord_2611256
  simp only [CollatzResearch.WordTrace]
  refine ⟨47620165313936476932330811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63493553751915302576441081 47620165313936476932330811)
  ·
    refine ⟨71430247970904715398496217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47620165313936476932330811 71430247970904715398496217)
    ·
      refine ⟨53572685978178536548872163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71430247970904715398496217 53572685978178536548872163)
      ·
        refine ⟨80359028967267804823308245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53572685978178536548872163 80359028967267804823308245)
        ·
          refine ⟨1883414741420339175546287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80359028967267804823308245 1883414741420339175546287)
          ·
            refine ⟨2825122112130508763319431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883414741420339175546287 2825122112130508763319431)
            ·
              refine ⟨4237683168195763144979147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825122112130508763319431 4237683168195763144979147)
              ·
                refine ⟨6356524752293644717468721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4237683168195763144979147 6356524752293644717468721)
                ·
                  refine ⟨4767393564220233538101541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6356524752293644717468721 4767393564220233538101541)
                  ·
                    refine ⟨893886293291293788394039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4767393564220233538101541 893886293291293788394039)
                    ·
                      rfl

theorem cell22_2611256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_2611256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611256 prefixEnd_2611256 := by exact prefixLift 2611256
  have htrace : WordTrace (prefixWord ++ tailWord_2611256) baseStart_2611256 baseEnd_2611256 := by
    simpa [prefixWord, tailWord_2611256, baseEnd_2611256] using wordTrace_append hprefix tailTrace_2611256
  have hstable : (prefixWord ++ tailWord_2611256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611256).length < 2 ^ (prefixWord ++ tailWord_2611256).sum := by decide
  have hdescent : baseEnd_2611256 < baseStart_2611256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611295 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2611295 : Nat := 118140960795 + 2611295 * 2 ^ 59
def prefixEnd_2611295 : Nat := 4983230072969 + 3 ^ 40 * 2611295 * 2
def baseEnd_2611295 : Nat := 893899643788310686668919

theorem tailTrace_2611295 : CollatzResearch.WordTrace tailWord_2611295 prefixEnd_2611295 893899643788310686668919 := by
  unfold tailWord_2611295
  simp only [CollatzResearch.WordTrace]
  refine ⟨95241753074731663525331339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63494502049821109016887559 95241753074731663525331339)
  ·
    refine ⟨142862629612097495287997009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95241753074731663525331339 142862629612097495287997009)
    ·
      refine ⟨107146972209073121465997757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142862629612097495287997009 107146972209073121465997757)
      ·
        refine ⟨40180114578402420549749159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107146972209073121465997757 40180114578402420549749159)
        ·
          refine ⟨60270171867603630824623739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40180114578402420549749159 60270171867603630824623739)
          ·
            refine ⟨90405257801405446236935609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60270171867603630824623739 90405257801405446236935609)
            ·
              refine ⟨67803943351054084677701707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90405257801405446236935609 67803943351054084677701707)
              ·
                refine ⟨101705915026581127016552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67803943351054084677701707 101705915026581127016552561)
                ·
                  refine ⟨76279436269935845262414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101705915026581127016552561 76279436269935845262414421)
                  ·
                    refine ⟨893899643788310686668919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76279436269935845262414421 893899643788310686668919)
                    ·
                      rfl

theorem cell22_2611295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2611295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611295 prefixEnd_2611295 := by exact prefixLift 2611295
  have htrace : WordTrace (prefixWord ++ tailWord_2611295) baseStart_2611295 baseEnd_2611295 := by
    simpa [prefixWord, tailWord_2611295, baseEnd_2611295] using wordTrace_append hprefix tailTrace_2611295
  have hstable : (prefixWord ++ tailWord_2611295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611295).length < 2 ^ (prefixWord ++ tailWord_2611295).sum := by decide
  have hdescent : baseEnd_2611295 < baseStart_2611295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611402 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2611402 : Nat := 118140960795 + 2611402 * 2 ^ 59
def prefixEnd_2611402 : Nat := 4983230072969 + 3 ^ 40 * 2611402 * 2
def baseEnd_2611402 : Nat := 893936272074998074243591

theorem tailTrace_2611402 : CollatzResearch.WordTrace tailWord_2611402 prefixEnd_2611402 893936272074998074243591 := by
  unfold tailWord_2611402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23811413921336005199869115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63497103790229347199650973 23811413921336005199869115)
  ·
    refine ⟨35717120882004007799803673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23811413921336005199869115 35717120882004007799803673)
    ·
      refine ⟨26787840661503005849852755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35717120882004007799803673 26787840661503005849852755)
      ·
        refine ⟨40181760992254508774779133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26787840661503005849852755 40181760992254508774779133)
        ·
          refine ⟨15068160372095440790542175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40181760992254508774779133 15068160372095440790542175)
          ·
            refine ⟨22602240558143161185813263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15068160372095440790542175 22602240558143161185813263)
            ·
              refine ⟨33903360837214741778719895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22602240558143161185813263 33903360837214741778719895)
              ·
                refine ⟨50855041255822112668079843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33903360837214741778719895 50855041255822112668079843)
                ·
                  refine ⟨76282561883733169002119765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50855041255822112668079843 76282561883733169002119765)
                  ·
                    refine ⟨893936272074998074243591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76282561883733169002119765 893936272074998074243591)
                    ·
                      rfl

theorem cell22_2611402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2611402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611402 prefixEnd_2611402 := by exact prefixLift 2611402
  have htrace : WordTrace (prefixWord ++ tailWord_2611402) baseStart_2611402 baseEnd_2611402 := by
    simpa [prefixWord, tailWord_2611402, baseEnd_2611402] using wordTrace_append hprefix tailTrace_2611402
  have hstable : (prefixWord ++ tailWord_2611402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611402).length < 2 ^ (prefixWord ++ tailWord_2611402).sum := by decide
  have hdescent : baseEnd_2611402 < baseStart_2611402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611421 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2611421 : Nat := 118140960795 + 2611421 * 2 ^ 59
def prefixEnd_2611421 : Nat := 4983230072969 + 3 ^ 40 * 2611421 * 2
def baseEnd_2611421 : Nat := 893942776163288358018533

theorem tailTrace_2611421 : CollatzResearch.WordTrace tailWord_2611421 prefixEnd_2611421 893942776163288358018533 := by
  unfold tailWord_2611421
  simp only [CollatzResearch.WordTrace]
  refine ⟨95246348672275187044418117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63497565781516791362945411 95246348672275187044418117)
  ·
    refine ⟨17858690376051597570828397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95246348672275187044418117 17858690376051597570828397)
    ·
      refine ⟨6697008891019349089060649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17858690376051597570828397 6697008891019349089060649)
      ·
        refine ⟨5022756668264511816795487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6697008891019349089060649 5022756668264511816795487)
        ·
          refine ⟨7534135002396767725193231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022756668264511816795487 7534135002396767725193231)
          ·
            refine ⟨11301202503595151587789847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7534135002396767725193231 11301202503595151587789847)
            ·
              refine ⟨16951803755392727381684771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11301202503595151587789847 16951803755392727381684771)
              ·
                refine ⟨25427705633089091072527157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16951803755392727381684771 25427705633089091072527157)
                ·
                  refine ⟨2383847403102102288049421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25427705633089091072527157 2383847403102102288049421)
                  ·
                    refine ⟨893942776163288358018533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383847403102102288049421 893942776163288358018533)
                    ·
                      rfl

theorem cell22_2611421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2611421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611421 prefixEnd_2611421 := by exact prefixLift 2611421
  have htrace : WordTrace (prefixWord ++ tailWord_2611421) baseStart_2611421 baseEnd_2611421 := by
    simpa [prefixWord, tailWord_2611421, baseEnd_2611421] using wordTrace_append hprefix tailTrace_2611421
  have hstable : (prefixWord ++ tailWord_2611421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611421).length < 2 ^ (prefixWord ++ tailWord_2611421).sum := by decide
  have hdescent : baseEnd_2611421 < baseStart_2611421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611479 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 6]
def baseStart_2611479 : Nat := 118140960795 + 2611479 * 2 ^ 59
def prefixEnd_2611479 : Nat := 4983230072969 + 3 ^ 40 * 2611479 * 2
def baseEnd_2611479 : Nat := 297987543582865180022785

theorem tailTrace_2611479 : CollatzResearch.WordTrace tailWord_2611479 prefixEnd_2611479 297987543582865180022785 := by
  unfold tailWord_2611479
  simp only [CollatzResearch.WordTrace]
  refine ⟨95248464106065062950029491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63498976070710041966686327 95248464106065062950029491)
  ·
    refine ⟨142872696159097594425044237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95248464106065062950029491 142872696159097594425044237)
    ·
      refine ⟨53577261059661597909391589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 142872696159097594425044237 53577261059661597909391589)
      ·
        refine ⟨10045736448686549608010923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53577261059661597909391589 10045736448686549608010923)
        ·
          refine ⟨15068604673029824412016385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10045736448686549608010923 15068604673029824412016385)
          ·
            refine ⟨11301453504772368309012289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15068604673029824412016385 11301453504772368309012289)
            ·
              refine ⟨8476090128579276231759217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11301453504772368309012289 8476090128579276231759217)
              ·
                refine ⟨6357067596434457173819413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8476090128579276231759217 6357067596434457173819413)
                ·
                  refine ⟨297987543582865180022785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6357067596434457173819413 297987543582865180022785)
                  ·
                    rfl

theorem cell22_2611479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_2611479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611479 prefixEnd_2611479 := by exact prefixLift 2611479
  have htrace : WordTrace (prefixWord ++ tailWord_2611479) baseStart_2611479 baseEnd_2611479 := by
    simpa [prefixWord, tailWord_2611479, baseEnd_2611479] using wordTrace_append hprefix tailTrace_2611479
  have hstable : (prefixWord ++ tailWord_2611479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611479).length < 2 ^ (prefixWord ++ tailWord_2611479).sum := by decide
  have hdescent : baseEnd_2611479 < baseStart_2611479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611528 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 2, 3]
def baseStart_2611528 : Nat := 118140960795 + 2611528 * 2 ^ 59
def prefixEnd_2611528 : Nat := 4983230072969 + 3 ^ 40 * 2611528 * 2
def baseEnd_2611528 : Nat := 893979404449975745593205

theorem tailTrace_2611528 : CollatzResearch.WordTrace tailWord_2611528 prefixEnd_2611528 893979404449975745593205 := by
  unfold tailWord_2611528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47625125641443772159281619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63500167521925029545708825 47625125641443772159281619)
  ·
    refine ⟨71437688462165658238922429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47625125641443772159281619 71437688462165658238922429)
    ·
      refine ⟨26789133173312121839595911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71437688462165658238922429 26789133173312121839595911)
      ·
        refine ⟨40183699759968182759393867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26789133173312121839595911 40183699759968182759393867)
        ·
          refine ⟨60275549639952274139090801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40183699759968182759393867 60275549639952274139090801)
          ·
            refine ⟨45206662229964205604318101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60275549639952274139090801 45206662229964205604318101)
            ·
              refine ⟨2119062292029572137702411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 45206662229964205604318101 2119062292029572137702411)
              ·
                refine ⟨3178593438044358206553617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119062292029572137702411 3178593438044358206553617)
                ·
                  refine ⟨2383945078533268654915213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3178593438044358206553617 2383945078533268654915213)
                  ·
                    refine ⟨893979404449975745593205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2383945078533268654915213 893979404449975745593205)
                    ·
                      rfl

theorem cell22_2611528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_2611528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611528 prefixEnd_2611528 := by exact prefixLift 2611528
  have htrace : WordTrace (prefixWord ++ tailWord_2611528) baseStart_2611528 baseEnd_2611528 := by
    simpa [prefixWord, tailWord_2611528, baseEnd_2611528] using wordTrace_append hprefix tailTrace_2611528
  have hstable : (prefixWord ++ tailWord_2611528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611528).length < 2 ^ (prefixWord ++ tailWord_2611528).sum := by decide
  have hdescent : baseEnd_2611528 < baseStart_2611528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611682 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2611682 : Nat := 118140960795 + 2611682 * 2 ^ 59
def prefixEnd_2611682 : Nat := 4983230072969 + 3 ^ 40 * 2611682 * 2
def baseEnd_2611682 : Nat := 298010707265723559080911

theorem tailTrace_2611682 : CollatzResearch.WordTrace tailWord_2611682 prefixEnd_2611682 298010707265723559080911 := by
  unfold tailWord_2611682
  simp only [CollatzResearch.WordTrace]
  refine ⟨23813967031082407154917325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63503912082886419079779533 23813967031082407154917325)
  ·
    refine ⟨8930237636655902683093997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23813967031082407154917325 8930237636655902683093997)
    ·
      refine ⟨3348839113745963506160249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8930237636655902683093997 3348839113745963506160249)
      ·
        refine ⟨2511629335309472629620187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348839113745963506160249 2511629335309472629620187)
        ·
          refine ⟨3767444002964208944430281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511629335309472629620187 3767444002964208944430281)
          ·
            refine ⟨2825583002223156708322711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767444002964208944430281 2825583002223156708322711)
            ·
              refine ⟨4238374503334735062484067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2825583002223156708322711 4238374503334735062484067)
              ·
                refine ⟨6357561755002102593726101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4238374503334735062484067 6357561755002102593726101)
                ·
                  refine ⟨298010707265723559080911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6357561755002102593726101 298010707265723559080911)
                  ·
                    rfl

theorem cell22_2611682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2611682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611682 prefixEnd_2611682 := by exact prefixLift 2611682
  have htrace : WordTrace (prefixWord ++ tailWord_2611682) baseStart_2611682 baseEnd_2611682 := by
    simpa [prefixWord, tailWord_2611682, baseEnd_2611682] using wordTrace_append hprefix tailTrace_2611682
  have hstable : (prefixWord ++ tailWord_2611682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611682).length < 2 ^ (prefixWord ++ tailWord_2611682).sum := by decide
  have hdescent : baseEnd_2611682 < baseStart_2611682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611693 : List Nat := [1, 5, 1, 3, 1, 2, 2, 7]
def baseStart_2611693 : Nat := 118140960795 + 2611693 * 2 ^ 59
def prefixEnd_2611693 : Nat := 4983230072969 + 3 ^ 40 * 2611693 * 2
def baseEnd_2611693 : Nat := 99337320813552257246411

theorem tailTrace_2611693 : CollatzResearch.WordTrace tailWord_2611693 prefixEnd_2611693 99337320813552257246411 := by
  unfold tailWord_2611693
  simp only [CollatzResearch.WordTrace]
  refine ⟨95256269327289777498319733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63504179551526518332213155 95256269327289777498319733)
  ·
    refine ⟨8930275249433416640467475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95256269327289777498319733 8930275249433416640467475)
    ·
      refine ⟨13395412874150124960701213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8930275249433416640467475 13395412874150124960701213)
      ·
        refine ⟨5023279827806296860262955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13395412874150124960701213 5023279827806296860262955)
        ·
          refine ⟨7534919741709445290394433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5023279827806296860262955 7534919741709445290394433)
          ·
            refine ⟨5651189806282083967795825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7534919741709445290394433 5651189806282083967795825)
            ·
              refine ⟨4238392354711562975846869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5651189806282083967795825 4238392354711562975846869)
              ·
                refine ⟨99337320813552257246411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4238392354711562975846869 99337320813552257246411)
                ·
                  rfl

theorem cell22_2611693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 7].length) (baseStart_2611693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611693 prefixEnd_2611693 := by exact prefixLift 2611693
  have htrace : WordTrace (prefixWord ++ tailWord_2611693) baseStart_2611693 baseEnd_2611693 := by
    simpa [prefixWord, tailWord_2611693, baseEnd_2611693] using wordTrace_append hprefix tailTrace_2611693
  have hstable : (prefixWord ++ tailWord_2611693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611693).length < 2 ^ (prefixWord ++ tailWord_2611693).sum := by decide
  have hdescent : baseEnd_2611693 < baseStart_2611693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611768 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 1, 4]
def baseStart_2611768 : Nat := 118140960795 + 2611768 * 2 ^ 59
def prefixEnd_2611768 : Nat := 4983230072969 + 3 ^ 40 * 2611768 * 2
def baseEnd_2611768 : Nat := 894061561354695119592469

theorem tailTrace_2611768 : CollatzResearch.WordTrace tailWord_2611768 prefixEnd_2611768 894061561354695119592469 := by
  unfold tailWord_2611768
  simp only [CollatzResearch.WordTrace]
  refine ⟨47629502401009032653649979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63506003201345376871533305 47629502401009032653649979)
  ·
    refine ⟨71444253601513548980474969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47629502401009032653649979 71444253601513548980474969)
    ·
      refine ⟨53583190201135161735356227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71444253601513548980474969 53583190201135161735356227)
      ·
        refine ⟨80374785301702742603034341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53583190201135161735356227 80374785301702742603034341)
        ·
          refine ⟨15070272244069264238068939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80374785301702742603034341 15070272244069264238068939)
          ·
            refine ⟨22605408366103896357103409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15070272244069264238068939 22605408366103896357103409)
            ·
              refine ⟨16954056274577922267827557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22605408366103896357103409 16954056274577922267827557)
              ·
                refine ⟨3178885551483360425217667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16954056274577922267827557 3178885551483360425217667)
                ·
                  refine ⟨4768328327225040637826501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3178885551483360425217667 4768328327225040637826501)
                  ·
                    refine ⟨894061561354695119592469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4768328327225040637826501 894061561354695119592469)
                    ·
                      rfl

theorem cell22_2611768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_2611768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611768 prefixEnd_2611768 := by exact prefixLift 2611768
  have htrace : WordTrace (prefixWord ++ tailWord_2611768) baseStart_2611768 baseEnd_2611768 := by
    simpa [prefixWord, tailWord_2611768, baseEnd_2611768] using wordTrace_append hprefix tailTrace_2611768
  have hstable : (prefixWord ++ tailWord_2611768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611768).length < 2 ^ (prefixWord ++ tailWord_2611768).sum := by decide
  have hdescent : baseEnd_2611768 < baseStart_2611768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611806 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2611806 : Nat := 118140960795 + 2611806 * 2 ^ 59
def prefixEnd_2611806 : Nat := 4983230072969 + 3 ^ 40 * 2611806 * 2
def baseEnd_2611806 : Nat := 298024856510425229047451

theorem tailTrace_2611806 : CollatzResearch.WordTrace tailWord_2611806 prefixEnd_2611806 298024856510425229047451 := by
  unfold tailWord_2611806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11907548846985049724647909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63506927183920265198122181 11907548846985049724647909)
  ·
    refine ⟨2232665408809696823371483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11907548846985049724647909 2232665408809696823371483)
    ·
      refine ⟨3348998113214545235057225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232665408809696823371483 3348998113214545235057225)
      ·
        refine ⟨2511748584910908926292919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348998113214545235057225 2511748584910908926292919)
        ·
          refine ⟨3767622877366363389439379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511748584910908926292919 3767622877366363389439379)
          ·
            refine ⟨5651434316049545084159069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767622877366363389439379 5651434316049545084159069)
            ·
              refine ⟨2119287868518579406559651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5651434316049545084159069 2119287868518579406559651)
              ·
                refine ⟨3178931802777869109839477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119287868518579406559651 3178931802777869109839477)
                ·
                  refine ⟨298024856510425229047451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3178931802777869109839477 298024856510425229047451)
                  ·
                    rfl

theorem cell22_2611806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2611806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611806 prefixEnd_2611806 := by exact prefixLift 2611806
  have htrace : WordTrace (prefixWord ++ tailWord_2611806) baseStart_2611806 baseEnd_2611806 := by
    simpa [prefixWord, tailWord_2611806, baseEnd_2611806] using wordTrace_append hprefix tailTrace_2611806
  have hstable : (prefixWord ++ tailWord_2611806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611806).length < 2 ^ (prefixWord ++ tailWord_2611806).sum := by decide
  have hdescent : baseEnd_2611806 < baseStart_2611806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611811 : List Nat := [1, 1, 1, 5, 1, 2, 2, 9]
def baseStart_2611811 : Nat := 118140960795 + 2611811 * 2 ^ 59
def prefixEnd_2611811 : Nat := 4983230072969 + 3 ^ 40 * 2611811 * 2
def baseEnd_2611811 : Nat := 99341809014828593418593

theorem tailTrace_2611811 : CollatzResearch.WordTrace tailWord_2611811 prefixEnd_2611811 99341809014828593418593 := by
  unfold tailWord_2611811
  simp only [CollatzResearch.WordTrace]
  refine ⟨95260573140862283651115287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63507048760574855767410191 95260573140862283651115287)
  ·
    refine ⟨142890859711293425476672931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95260573140862283651115287 142890859711293425476672931)
    ·
      refine ⟨214336289566940138215009397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142890859711293425476672931 214336289566940138215009397)
      ·
        refine ⟨20094027146900637957657131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214336289566940138215009397 20094027146900637957657131)
        ·
          refine ⟨30141040720350956936485697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20094027146900637957657131 30141040720350956936485697)
          ·
            refine ⟨22605780540263217702364273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30141040720350956936485697 22605780540263217702364273)
            ·
              refine ⟨16954335405197413276773205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22605780540263217702364273 16954335405197413276773205)
              ·
                refine ⟨99341809014828593418593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16954335405197413276773205 99341809014828593418593)
                ·
                  rfl

theorem cell22_2611811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_2611811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611811 prefixEnd_2611811 := by exact prefixLift 2611811
  have htrace : WordTrace (prefixWord ++ tailWord_2611811) baseStart_2611811 baseEnd_2611811 := by
    simpa [prefixWord, tailWord_2611811, baseEnd_2611811] using wordTrace_append hprefix tailTrace_2611811
  have hstable : (prefixWord ++ tailWord_2611811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611811).length < 2 ^ (prefixWord ++ tailWord_2611811).sum := by decide
  have hdescent : baseEnd_2611811 < baseStart_2611811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611843 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 5, 3]
def baseStart_2611843 : Nat := 118140960795 + 2611843 * 2 ^ 59
def prefixEnd_2611843 : Nat := 4983230072969 + 3 ^ 40 * 2611843 * 2
def baseEnd_2611843 : Nat := 894087235387419923967239

theorem tailTrace_2611843 : CollatzResearch.WordTrace tailWord_2611843 prefixEnd_2611843 894087235387419923967239 := by
  unfold tailWord_2611843
  simp only [CollatzResearch.WordTrace]
  refine ⟨95261740276746353116280183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63507826851164235410853455 95261740276746353116280183)
  ·
    refine ⟨142892610415119529674420275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95261740276746353116280183 142892610415119529674420275)
    ·
      refine ⟨214338915622679294511630413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142892610415119529674420275 214338915622679294511630413)
      ·
        refine ⟨80377093358504735441861405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214338915622679294511630413 80377093358504735441861405)
        ·
          refine ⟨30141410009439275790698027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80377093358504735441861405 30141410009439275790698027)
          ·
            refine ⟨45212115014158913686047041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30141410009439275790698027 45212115014158913686047041)
            ·
              refine ⟨33909086260619185264535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45212115014158913686047041 33909086260619185264535281)
              ·
                refine ⟨25431814695464388948401461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33909086260619185264535281 25431814695464388948401461)
                ·
                  refine ⟨2384232627699786463912637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25431814695464388948401461 2384232627699786463912637)
                  ·
                    refine ⟨894087235387419923967239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384232627699786463912637 894087235387419923967239)
                    ·
                      rfl

theorem cell22_2611843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].length) (baseStart_2611843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611843 prefixEnd_2611843 := by exact prefixLift 2611843
  have htrace : WordTrace (prefixWord ++ tailWord_2611843) baseStart_2611843 baseEnd_2611843 := by
    simpa [prefixWord, tailWord_2611843, baseEnd_2611843] using wordTrace_append hprefix tailTrace_2611843
  have hstable : (prefixWord ++ tailWord_2611843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611843).length < 2 ^ (prefixWord ++ tailWord_2611843).sum := by decide
  have hdescent : baseEnd_2611843 < baseStart_2611843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611866 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_2611866 : Nat := 118140960795 + 2611866 * 2 ^ 59
def prefixEnd_2611866 : Nat := 4983230072969 + 3 ^ 40 * 2611866 * 2
def baseEnd_2611866 : Nat := 894095108757455530642169

theorem tailTrace_2611866 : CollatzResearch.WordTrace tailWord_2611866 prefixEnd_2611866 894095108757455530642169 := by
  unfold tailWord_2611866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23815644788915757011091863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63508386103775352029578301 23815644788915757011091863)
  ·
    refine ⟨35723467183373635516637795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23815644788915757011091863 35723467183373635516637795)
    ·
      refine ⟨53585200775060453274956693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35723467183373635516637795 53585200775060453274956693)
      ·
        refine ⟨2511806286330958747263595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 53585200775060453274956693 2511806286330958747263595)
        ·
          refine ⟨3767709429496438120895393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511806286330958747263595 3767709429496438120895393)
          ·
            refine ⟨2825782072122328590671545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3767709429496438120895393 2825782072122328590671545)
            ·
              refine ⟨2119336554091746443003659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825782072122328590671545 2119336554091746443003659)
              ·
                refine ⟨3179004831137619664505489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119336554091746443003659 3179004831137619664505489)
                ·
                  refine ⟨2384253623353214748379117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179004831137619664505489 2384253623353214748379117)
                  ·
                    refine ⟨894095108757455530642169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384253623353214748379117 894095108757455530642169)
                    ·
                      rfl

theorem cell22_2611866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_2611866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611866 prefixEnd_2611866 := by exact prefixLift 2611866
  have htrace : WordTrace (prefixWord ++ tailWord_2611866) baseStart_2611866 baseEnd_2611866 := by
    simpa [prefixWord, tailWord_2611866, baseEnd_2611866] using wordTrace_append hprefix tailTrace_2611866
  have hstable : (prefixWord ++ tailWord_2611866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611866).length < 2 ^ (prefixWord ++ tailWord_2611866).sum := by decide
  have hdescent : baseEnd_2611866 < baseStart_2611866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611950 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2611950 : Nat := 118140960795 + 2611950 * 2 ^ 59
def prefixEnd_2611950 : Nat := 4983230072969 + 3 ^ 40 * 2611950 * 2
def baseEnd_2611950 : Nat := 894123863674107311541911

theorem tailTrace_2611950 : CollatzResearch.WordTrace tailWord_2611950 prefixEnd_2611950 894123863674107311541911 := by
  unfold tailWord_2611950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11908205360919838798803163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63510428591572473593616869 11908205360919838798803163)
  ·
    refine ⟨17862308041379758198204745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11908205360919838798803163 17862308041379758198204745)
    ·
      refine ⟨13396731031034818648653559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17862308041379758198204745 13396731031034818648653559)
      ·
        refine ⟨20095096546552227972980339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13396731031034818648653559 20095096546552227972980339)
        ·
          refine ⟨30142644819828341959470509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20095096546552227972980339 30142644819828341959470509)
          ·
            refine ⟨11303491807435628234801441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30142644819828341959470509 11303491807435628234801441)
            ·
              refine ⟨8477618855576721176101081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11303491807435628234801441 8477618855576721176101081)
              ·
                refine ⟨6358214141682540882075811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8477618855576721176101081 6358214141682540882075811)
                ·
                  refine ⟨9537321212523811323113717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6358214141682540882075811 9537321212523811323113717)
                  ·
                    refine ⟨894123863674107311541911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9537321212523811323113717 894123863674107311541911)
                    ·
                      rfl

theorem cell22_2611950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2611950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611950 prefixEnd_2611950 := by exact prefixLift 2611950
  have htrace : WordTrace (prefixWord ++ tailWord_2611950) baseStart_2611950 baseEnd_2611950 := by
    simpa [prefixWord, tailWord_2611950, baseEnd_2611950] using wordTrace_append hprefix tailTrace_2611950
  have hstable : (prefixWord ++ tailWord_2611950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611950).length < 2 ^ (prefixWord ++ tailWord_2611950).sum := by decide
  have hdescent : baseEnd_2611950 < baseStart_2611950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611954 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_2611954 : Nat := 118140960795 + 2611954 * 2 ^ 59
def prefixEnd_2611954 : Nat := 4983230072969 + 3 ^ 40 * 2611954 * 2
def baseEnd_2611954 : Nat := 894125232955852634441899

theorem tailTrace_2611954 : CollatzResearch.WordTrace tailWord_2611954 prefixEnd_2611954 894125232955852634441899 := by
  unfold tailWord_2611954
  simp only [CollatzResearch.WordTrace]
  refine ⟨23816447194836054768392729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63510525852896146049047277 23816447194836054768392729)
  ·
    refine ⟨17862335396127041076294547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23816447194836054768392729 17862335396127041076294547)
    ·
      refine ⟨26793503094190561614441821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17862335396127041076294547 26793503094190561614441821)
      ·
        refine ⟨10047563660321460605415683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26793503094190561614441821 10047563660321460605415683)
        ·
          refine ⟨15071345490482190908123525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10047563660321460605415683 15071345490482190908123525)
          ·
            refine ⟨2825877279465410795273161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15071345490482190908123525 2825877279465410795273161)
            ·
              refine ⟨2119407959599058096454871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2825877279465410795273161 2119407959599058096454871)
              ·
                refine ⟨3179111939398587144682307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2119407959599058096454871 3179111939398587144682307)
                ·
                  refine ⟨4768667909097880717023461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3179111939398587144682307 4768667909097880717023461)
                  ·
                    refine ⟨894125232955852634441899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4768667909097880717023461 894125232955852634441899)
                    ·
                      rfl

theorem cell22_2611954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_2611954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611954 prefixEnd_2611954 := by exact prefixLift 2611954
  have htrace : WordTrace (prefixWord ++ tailWord_2611954) baseStart_2611954 baseEnd_2611954 := by
    simpa [prefixWord, tailWord_2611954, baseEnd_2611954] using wordTrace_append hprefix tailTrace_2611954
  have hstable : (prefixWord ++ tailWord_2611954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611954).length < 2 ^ (prefixWord ++ tailWord_2611954).sum := by decide
  have hdescent : baseEnd_2611954 < baseStart_2611954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2611997 : List Nat := [1, 4, 2, 4, 1, 1, 1, 8]
def baseStart_2611997 : Nat := 118140960795 + 2611997 * 2 ^ 59
def prefixEnd_2611997 : Nat := 4983230072969 + 3 ^ 40 * 2611997 * 2
def baseEnd_2611997 : Nat := 99348883637179428401863

theorem tailTrace_2611997 : CollatzResearch.WordTrace tailWord_2611997 prefixEnd_2611997 99348883637179428401863 := by
  unfold tailWord_2611997
  simp only [CollatzResearch.WordTrace]
  refine ⟨95267357118188437417386245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63511571412125624944924163 95267357118188437417386245)
  ·
    refine ⟨17862629459660332015759921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95267357118188437417386245 17862629459660332015759921)
    ·
      refine ⟨13396972094745249011819941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17862629459660332015759921 13396972094745249011819941)
      ·
        refine ⟨2511932267764734189716239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13396972094745249011819941 2511932267764734189716239)
        ·
          refine ⟨3767898401647101284574359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2511932267764734189716239 3767898401647101284574359)
          ·
            refine ⟨5651847602470651926861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3767898401647101284574359 5651847602470651926861539)
            ·
              refine ⟨8477771403705977890292309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5651847602470651926861539 8477771403705977890292309)
              ·
                refine ⟨99348883637179428401863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8477771403705977890292309 99348883637179428401863)
                ·
                  rfl

theorem cell22_2611997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 8].length) (baseStart_2611997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2611997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2611997 prefixEnd_2611997 := by exact prefixLift 2611997
  have htrace : WordTrace (prefixWord ++ tailWord_2611997) baseStart_2611997 baseEnd_2611997 := by
    simpa [prefixWord, tailWord_2611997, baseEnd_2611997] using wordTrace_append hprefix tailTrace_2611997
  have hstable : (prefixWord ++ tailWord_2611997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2611997).length < 2 ^ (prefixWord ++ tailWord_2611997).sum := by decide
  have hdescent : baseEnd_2611997 < baseStart_2611997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2611997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612100 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_2612100 : Nat := 118140960795 + 2612100 * 2 ^ 59
def prefixEnd_2612100 : Nat := 4983230072969 + 3 ^ 40 * 2612100 * 2
def baseEnd_2612100 : Nat := 894175211739556920291451

theorem tailTrace_2612100 : CollatzResearch.WordTrace tailWord_2612100 prefixEnd_2612100 894175211739556920291451 := by
  unfold tailWord_2612100
  simp only [CollatzResearch.WordTrace]
  refine ⟨47635556918407643004192877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63514075891210190672257169 47635556918407643004192877)
  ·
    refine ⟨17863333844402866126572329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47635556918407643004192877 17863333844402866126572329)
    ·
      refine ⟨13397500383302149594929247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17863333844402866126572329 13397500383302149594929247)
      ·
        refine ⟨20096250574953224392393871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13397500383302149594929247 20096250574953224392393871)
        ·
          refine ⟨30144375862429836588590807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20096250574953224392393871 30144375862429836588590807)
          ·
            refine ⟨45216563793644754882886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30144375862429836588590807 45216563793644754882886211)
            ·
              refine ⟨67824845690467132324329317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45216563793644754882886211 67824845690467132324329317)
              ·
                refine ⟨12717158566962587310811747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67824845690467132324329317 12717158566962587310811747)
                ·
                  refine ⟨19075737850443880966217621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12717158566962587310811747 19075737850443880966217621)
                  ·
                    refine ⟨894175211739556920291451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19075737850443880966217621 894175211739556920291451)
                    ·
                      rfl

theorem cell22_2612100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_2612100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612100 prefixEnd_2612100 := by exact prefixLift 2612100
  have htrace : WordTrace (prefixWord ++ tailWord_2612100) baseStart_2612100 baseEnd_2612100 := by
    simpa [prefixWord, tailWord_2612100, baseEnd_2612100] using wordTrace_append hprefix tailTrace_2612100
  have hstable : (prefixWord ++ tailWord_2612100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612100).length < 2 ^ (prefixWord ++ tailWord_2612100).sum := by decide
  have hdescent : baseEnd_2612100 < baseStart_2612100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612117 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2612117 : Nat := 118140960795 + 2612117 * 2 ^ 59
def prefixEnd_2612117 : Nat := 4983230072969 + 3 ^ 40 * 2612117 * 2
def baseEnd_2612117 : Nat := 894181031186974542616399

theorem tailTrace_2612117 : CollatzResearch.WordTrace tailWord_2612117 prefixEnd_2612117 894181031186974542616399 := by
  unfold tailWord_2612117
  simp only [CollatzResearch.WordTrace]
  refine ⟨95271733877753697911754605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63514489251835798607836403 95271733877753697911754605)
  ·
    refine ⟨35726900204157636716907977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95271733877753697911754605 35726900204157636716907977)
    ·
      refine ⟨26795175153118227537680983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35726900204157636716907977 26795175153118227537680983)
      ·
        refine ⟨40192762729677341306521475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26795175153118227537680983 40192762729677341306521475)
        ·
          refine ⟨60289144094516011959782213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40192762729677341306521475 60289144094516011959782213)
          ·
            refine ⟨11304214517721752242459165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60289144094516011959782213 11304214517721752242459165)
            ·
              refine ⟨4239080444145657090922187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11304214517721752242459165 4239080444145657090922187)
              ·
                refine ⟨6358620666218485636383281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239080444145657090922187 6358620666218485636383281)
                ·
                  refine ⟨4768965499663864227287461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6358620666218485636383281 4768965499663864227287461)
                  ·
                    refine ⟨894181031186974542616399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4768965499663864227287461 894181031186974542616399)
                    ·
                      rfl

theorem cell22_2612117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2612117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612117 prefixEnd_2612117 := by exact prefixLift 2612117
  have htrace : WordTrace (prefixWord ++ tailWord_2612117) baseStart_2612117 baseEnd_2612117 := by
    simpa [prefixWord, tailWord_2612117, baseEnd_2612117] using wordTrace_append hprefix tailTrace_2612117
  have hstable : (prefixWord ++ tailWord_2612117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612117).length < 2 ^ (prefixWord ++ tailWord_2612117).sum := by decide
  have hdescent : baseEnd_2612117 < baseStart_2612117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612194 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2612194 : Nat := 118140960795 + 2612194 * 2 ^ 59
def prefixEnd_2612194 : Nat := 4983230072969 + 3 ^ 40 * 2612194 * 2
def baseEnd_2612194 : Nat := 298069129953524002813721

theorem tailTrace_2612194 : CollatzResearch.WordTrace tailWord_2612194 prefixEnd_2612194 298069129953524002813721 := by
  unfold tailWord_2612194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23818635574618685015576909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63516361532316493374871757 23818635574618685015576909)
  ·
    refine ⟨8931988340482006880841341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23818635574618685015576909 8931988340482006880841341)
    ·
      refine ⟨3349495627680752580315503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8931988340482006880841341 3349495627680752580315503)
      ·
        refine ⟨5024243441521128870473255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349495627680752580315503 5024243441521128870473255)
        ·
          refine ⟨7536365162281693305709883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024243441521128870473255 7536365162281693305709883)
          ·
            refine ⟨11304547743422539958564825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536365162281693305709883 11304547743422539958564825)
            ·
              refine ⟨8478410807566904968923619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11304547743422539958564825 8478410807566904968923619)
              ·
                refine ⟨12717616211350357453385429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478410807566904968923619 12717616211350357453385429)
                ·
                  refine ⟨298069129953524002813721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12717616211350357453385429 298069129953524002813721)
                  ·
                    rfl

theorem cell22_2612194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2612194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612194 prefixEnd_2612194 := by exact prefixLift 2612194
  have htrace : WordTrace (prefixWord ++ tailWord_2612194) baseStart_2612194 baseEnd_2612194 := by
    simpa [prefixWord, tailWord_2612194, baseEnd_2612194] using wordTrace_append hprefix tailTrace_2612194
  have hstable : (prefixWord ++ tailWord_2612194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612194).length < 2 ^ (prefixWord ++ tailWord_2612194).sum := by decide
  have hdescent : baseEnd_2612194 < baseStart_2612194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612284 : List Nat := [2, 2, 2, 2, 2, 3, 3, 6]
def baseStart_2612284 : Nat := 118140960795 + 2612284 * 2 ^ 59
def prefixEnd_2612284 : Nat := 4983230072969 + 3 ^ 40 * 2612284 * 2
def baseEnd_2612284 : Nat := 99359799855537974854543

theorem tailTrace_2612284 : CollatzResearch.WordTrace tailWord_2612284 prefixEnd_2612284 99359799855537974854543 := by
  unfold tailWord_2612284
  simp only [CollatzResearch.WordTrace]
  refine ⟨47638912434074342716541953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63518549912099123622055937 47638912434074342716541953)
  ·
    refine ⟨35729184325555757037406465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47638912434074342716541953 35729184325555757037406465)
    ·
      refine ⟨26796888244166817778054849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35729184325555757037406465 26796888244166817778054849)
      ·
        refine ⟨20097666183125113333541137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26796888244166817778054849 20097666183125113333541137)
        ·
          refine ⟨15073249637343835000155853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20097666183125113333541137 15073249637343835000155853)
          ·
            refine ⟨5652468614003938125058445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15073249637343835000155853 5652468614003938125058445)
            ·
              refine ⟨2119675730251476796896917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5652468614003938125058445 2119675730251476796896917)
              ·
                refine ⟨99359799855537974854543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2119675730251476796896917 99359799855537974854543)
                ·
                  rfl

theorem cell22_2612284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_2612284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612284 prefixEnd_2612284 := by exact prefixLift 2612284
  have htrace : WordTrace (prefixWord ++ tailWord_2612284) baseStart_2612284 baseEnd_2612284 := by
    simpa [prefixWord, tailWord_2612284, baseEnd_2612284] using wordTrace_append hprefix tailTrace_2612284
  have hstable : (prefixWord ++ tailWord_2612284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612284).length < 2 ^ (prefixWord ++ tailWord_2612284).sum := by decide
  have hdescent : baseEnd_2612284 < baseStart_2612284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612286 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2612286 : Nat := 118140960795 + 2612286 * 2 ^ 59
def prefixEnd_2612286 : Nat := 4983230072969 + 3 ^ 40 * 2612286 * 2
def baseEnd_2612286 : Nat := 894238883340714435140881

theorem tailTrace_2612286 : CollatzResearch.WordTrace tailWord_2612286 prefixEnd_2612286 894238883340714435140881 := by
  unfold tailWord_2612286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11909737226767679971832089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63518598542760959849771141 11909737226767679971832089)
  ·
    refine ⟨8932302920075759978874067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11909737226767679971832089 8932302920075759978874067)
    ·
      refine ⟨13398454380113639968311101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8932302920075759978874067 13398454380113639968311101)
      ·
        refine ⟨5024420392542614988116663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13398454380113639968311101 5024420392542614988116663)
        ·
          refine ⟨7536630588813922482174995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024420392542614988116663 7536630588813922482174995)
          ·
            refine ⟨11304945883220883723262493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536630588813922482174995 11304945883220883723262493)
            ·
              refine ⟨4239354706207831396223435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11304945883220883723262493 4239354706207831396223435)
              ·
                refine ⟨6359032059311747094335153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239354706207831396223435 6359032059311747094335153)
                ·
                  refine ⟨4769274044483810320751365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359032059311747094335153 4769274044483810320751365)
                  ·
                    refine ⟨894238883340714435140881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769274044483810320751365 894238883340714435140881)
                    ·
                      rfl

theorem cell22_2612286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2612286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612286 prefixEnd_2612286 := by exact prefixLift 2612286
  have htrace : WordTrace (prefixWord ++ tailWord_2612286) baseStart_2612286 baseEnd_2612286 := by
    simpa [prefixWord, tailWord_2612286, baseEnd_2612286] using wordTrace_append hprefix tailTrace_2612286
  have hstable : (prefixWord ++ tailWord_2612286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612286).length < 2 ^ (prefixWord ++ tailWord_2612286).sum := by decide
  have hdescent : baseEnd_2612286 < baseStart_2612286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612312 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_2612312 : Nat := 118140960795 + 2612312 * 2 ^ 59
def prefixEnd_2612312 : Nat := 4983230072969 + 3 ^ 40 * 2612312 * 2
def baseEnd_2612312 : Nat := 298082594557353011330267

theorem tailTrace_2612312 : CollatzResearch.WordTrace tailWord_2612312 prefixEnd_2612312 298082594557353011330267 := by
  unfold tailWord_2612312
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639423056023623107551595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63519230741364830810068793 47639423056023623107551595)
  ·
    refine ⟨71459134584035434661327393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47639423056023623107551595 71459134584035434661327393)
    ·
      refine ⟨53594350938026575995995545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71459134584035434661327393 53594350938026575995995545)
      ·
        refine ⟨40195763203519931996996659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53594350938026575995995545 40195763203519931996996659)
        ·
          refine ⟨60293644805279897995494989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40195763203519931996996659 60293644805279897995494989)
          ·
            refine ⟨22610116801979961748310621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60293644805279897995494989 22610116801979961748310621)
            ·
              refine ⟨8478793800742485655616483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22610116801979961748310621 8478793800742485655616483)
              ·
                refine ⟨12718190701113728483424725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8478793800742485655616483 12718190701113728483424725)
                ·
                  refine ⟨298082594557353011330267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12718190701113728483424725 298082594557353011330267)
                  ·
                    rfl

theorem cell22_2612312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_2612312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612312 prefixEnd_2612312 := by exact prefixLift 2612312
  have htrace : WordTrace (prefixWord ++ tailWord_2612312) baseStart_2612312 baseEnd_2612312 := by
    simpa [prefixWord, tailWord_2612312, baseEnd_2612312] using wordTrace_append hprefix tailTrace_2612312
  have hstable : (prefixWord ++ tailWord_2612312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612312).length < 2 ^ (prefixWord ++ tailWord_2612312).sum := by decide
  have hdescent : baseEnd_2612312 < baseStart_2612312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612316 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2612316 : Nat := 118140960795 + 2612316 * 2 ^ 59
def prefixEnd_2612316 : Nat := 4983230072969 + 3 ^ 40 * 2612316 * 2
def baseEnd_2612316 : Nat := 894249152953804356890789

theorem tailTrace_2612316 : CollatzResearch.WordTrace tailWord_2612316 prefixEnd_2612316 894249152953804356890789 := by
  unfold tailWord_2612316
  simp only [CollatzResearch.WordTrace]
  refine ⟨47639496002016377449124401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63519328002688503265499201 47639496002016377449124401)
  ·
    refine ⟨35729622001512283086843301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47639496002016377449124401 35729622001512283086843301)
    ·
      refine ⟨6699304125283553078783119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35729622001512283086843301 6699304125283553078783119)
      ·
        refine ⟨10048956187925329618174679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6699304125283553078783119 10048956187925329618174679)
        ·
          refine ⟨15073434281887994427262019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10048956187925329618174679 15073434281887994427262019)
          ·
            refine ⟨22610151422831991640893029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15073434281887994427262019 22610151422831991640893029)
            ·
              refine ⟨4239403391780998432667443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22610151422831991640893029 4239403391780998432667443)
              ·
                refine ⟨6359105087671497649001165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239403391780998432667443 6359105087671497649001165)
                ·
                  refine ⟨2384664407876811618375437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6359105087671497649001165 2384664407876811618375437)
                  ·
                    refine ⟨894249152953804356890789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384664407876811618375437 894249152953804356890789)
                    ·
                      rfl

theorem cell22_2612316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2612316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612316 prefixEnd_2612316 := by exact prefixLift 2612316
  have htrace : WordTrace (prefixWord ++ tailWord_2612316) baseStart_2612316 baseEnd_2612316 := by
    simpa [prefixWord, tailWord_2612316, baseEnd_2612316] using wordTrace_append hprefix tailTrace_2612316
  have hstable : (prefixWord ++ tailWord_2612316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612316).length < 2 ^ (prefixWord ++ tailWord_2612316).sum := by decide
  have hdescent : baseEnd_2612316 < baseStart_2612316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612387 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_2612387 : Nat := 118140960795 + 2612387 * 2 ^ 59
def prefixEnd_2612387 : Nat := 4983230072969 + 3 ^ 40 * 2612387 * 2
def baseEnd_2612387 : Nat := 894273457704783838365571

theorem tailTrace_2612387 : CollatzResearch.WordTrace tailWord_2612387 prefixEnd_2612387 894273457704783838365571 := by
  unfold tailWord_2612387
  simp only [CollatzResearch.WordTrace]
  refine ⟨95281581586775534024083415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63521054391183689349388943 95281581586775534024083415)
  ·
    refine ⟨142922372380163301036125123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95281581586775534024083415 142922372380163301036125123)
    ·
      refine ⟨214383558570244951554187685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142922372380163301036125123 214383558570244951554187685)
      ·
        refine ⟨40196917231920928416410191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214383558570244951554187685 40196917231920928416410191)
        ·
          refine ⟨60295375847881392624615287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40196917231920928416410191 60295375847881392624615287)
          ·
            refine ⟨90443063771822088936922931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60295375847881392624615287 90443063771822088936922931)
            ·
              refine ⟨135664595657733133405384397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90443063771822088936922931 135664595657733133405384397)
              ·
                refine ⟨50874223371649925027019149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135664595657733133405384397 50874223371649925027019149)
                ·
                  refine ⟨19077833764368721885132181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50874223371649925027019149 19077833764368721885132181)
                  ·
                    refine ⟨894273457704783838365571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19077833764368721885132181 894273457704783838365571)
                    ·
                      rfl

theorem cell22_2612387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_2612387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612387 prefixEnd_2612387 := by exact prefixLift 2612387
  have htrace : WordTrace (prefixWord ++ tailWord_2612387) baseStart_2612387 baseEnd_2612387 := by
    simpa [prefixWord, tailWord_2612387, baseEnd_2612387] using wordTrace_append hprefix tailTrace_2612387
  have hstable : (prefixWord ++ tailWord_2612387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612387).length < 2 ^ (prefixWord ++ tailWord_2612387).sum := by decide
  have hdescent : baseEnd_2612387 < baseStart_2612387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612455 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 2, 4]
def baseStart_2612455 : Nat := 118140960795 + 2612455 * 2 ^ 59
def prefixEnd_2612455 : Nat := 4983230072969 + 3 ^ 40 * 2612455 * 2
def baseEnd_2612455 : Nat := 894296735494454327665363

theorem tailTrace_2612455 : CollatzResearch.WordTrace tailWord_2612455 prefixEnd_2612455 894296735494454327665363 := by
  unfold tailWord_2612455
  simp only [CollatzResearch.WordTrace]
  refine ⟨95284061750529181637558819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63522707833686121091705879 95284061750529181637558819)
  ·
    refine ⟨142926092625793772456338229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95284061750529181637558819 142926092625793772456338229)
    ·
      refine ⟨13399321183668166167781709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 142926092625793772456338229 13399321183668166167781709)
      ·
        refine ⟨5024745443875562312918141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13399321183668166167781709 5024745443875562312918141)
        ·
          refine ⟨1884279541453335867344303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5024745443875562312918141 1884279541453335867344303)
          ·
            refine ⟨2826419312180003801016455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884279541453335867344303 2826419312180003801016455)
            ·
              refine ⟨4239628968270005701524683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2826419312180003801016455 4239628968270005701524683)
              ·
                refine ⟨6359443452405008552287025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4239628968270005701524683 6359443452405008552287025)
                ·
                  refine ⟨4769582589303756414215269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6359443452405008552287025 4769582589303756414215269)
                  ·
                    refine ⟨894296735494454327665363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4769582589303756414215269 894296735494454327665363)
                    ·
                      rfl

theorem cell22_2612455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_2612455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612455 prefixEnd_2612455 := by exact prefixLift 2612455
  have htrace : WordTrace (prefixWord ++ tailWord_2612455) baseStart_2612455 baseEnd_2612455 := by
    simpa [prefixWord, tailWord_2612455, baseEnd_2612455] using wordTrace_append hprefix tailTrace_2612455
  have hstable : (prefixWord ++ tailWord_2612455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612455).length < 2 ^ (prefixWord ++ tailWord_2612455).sum := by decide
  have hdescent : baseEnd_2612455 < baseStart_2612455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612479 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_2612479 : Nat := 118140960795 + 2612479 * 2 ^ 59
def prefixEnd_2612479 : Nat := 4983230072969 + 3 ^ 40 * 2612479 * 2
def baseEnd_2612479 : Nat := 894304951184926265065289

theorem tailTrace_2612479 : CollatzResearch.WordTrace tailWord_2612479 prefixEnd_2612479 894304951184926265065289 := by
  unfold tailWord_2612479
  simp only [CollatzResearch.WordTrace]
  refine ⟨95284937102442233736432491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63523291401628155824288327 95284937102442233736432491)
  ·
    refine ⟨142927405653663350604648737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95284937102442233736432491 142927405653663350604648737)
    ·
      refine ⟨107195554240247512953486553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142927405653663350604648737 107195554240247512953486553)
      ·
        refine ⟨80396665680185634715114915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107195554240247512953486553 80396665680185634715114915)
        ·
          refine ⟨120594998520278452072672373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80396665680185634715114915 120594998520278452072672373)
          ·
            refine ⟨11305781111276104881813035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120594998520278452072672373 11305781111276104881813035)
            ·
              refine ⟨16958671666914157322719553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11305781111276104881813035 16958671666914157322719553)
              ·
                refine ⟨12719003750185617992039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16958671666914157322719553 12719003750185617992039665)
                ·
                  refine ⟨9539252812639213494029749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12719003750185617992039665 9539252812639213494029749)
                  ·
                    refine ⟨894304951184926265065289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9539252812639213494029749 894304951184926265065289)
                    ·
                      rfl

theorem cell22_2612479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_2612479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612479 prefixEnd_2612479 := by exact prefixLift 2612479
  have htrace : WordTrace (prefixWord ++ tailWord_2612479) baseStart_2612479 baseEnd_2612479 := by
    simpa [prefixWord, tailWord_2612479, baseEnd_2612479] using wordTrace_append hprefix tailTrace_2612479
  have hstable : (prefixWord ++ tailWord_2612479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612479).length < 2 ^ (prefixWord ++ tailWord_2612479).sum := by decide
  have hdescent : baseEnd_2612479 < baseStart_2612479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612481 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 5]
def baseStart_2612481 : Nat := 118140960795 + 2612481 * 2 ^ 59
def prefixEnd_2612481 : Nat := 4983230072969 + 3 ^ 40 * 2612481 * 2
def baseEnd_2612481 : Nat := 298101878608599642171761

theorem tailTrace_2612481 : CollatzResearch.WordTrace tailWord_2612481 prefixEnd_2612481 298101878608599642171761 := by
  unfold tailWord_2612481
  simp only [CollatzResearch.WordTrace]
  refine ⟨95285010048434988078005297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63523340032289992052003531 95285010048434988078005297)
  ·
    refine ⟨71463757536326241058503973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95285010048434988078005297 71463757536326241058503973)
    ·
      refine ⟨13399454538061170198469495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71463757536326241058503973 13399454538061170198469495)
      ·
        refine ⟨20099181807091755297704243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13399454538061170198469495 20099181807091755297704243)
        ·
          refine ⟨30148772710637632946556365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20099181807091755297704243 30148772710637632946556365)
          ·
            refine ⟨11305789766489112354958637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30148772710637632946556365 11305789766489112354958637)
            ·
              refine ⟨4239671162433417133109489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11305789766489112354958637 4239671162433417133109489)
              ·
                refine ⟨3179753371825062849832117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4239671162433417133109489 3179753371825062849832117)
                ·
                  refine ⟨298101878608599642171761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3179753371825062849832117 298101878608599642171761)
                  ·
                    rfl

theorem cell22_2612481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_2612481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612481 prefixEnd_2612481 := by exact prefixLift 2612481
  have htrace : WordTrace (prefixWord ++ tailWord_2612481) baseStart_2612481 baseEnd_2612481 := by
    simpa [prefixWord, tailWord_2612481, baseEnd_2612481] using wordTrace_append hprefix tailTrace_2612481
  have hstable : (prefixWord ++ tailWord_2612481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612481).length < 2 ^ (prefixWord ++ tailWord_2612481).sum := by decide
  have hdescent : baseEnd_2612481 < baseStart_2612481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612524 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_2612524 : Nat := 118140960795 + 2612524 * 2 ^ 59
def prefixEnd_2612524 : Nat := 4983230072969 + 3 ^ 40 * 2612524 * 2
def baseEnd_2612524 : Nat := 894320355604561147690151

theorem tailTrace_2612524 : CollatzResearch.WordTrace tailWord_2612524 prefixEnd_2612524 894320355604561147690151 := by
  unfold tailWord_2612524
  simp only [CollatzResearch.WordTrace]
  refine ⟨47643289193639603210910313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63524385591519470947880417 47643289193639603210910313)
  ·
    refine ⟨35732466895229702408182735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47643289193639603210910313 35732466895229702408182735)
    ·
      refine ⟨53598700342844553612274103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35732466895229702408182735 53598700342844553612274103)
      ·
        refine ⟨80398050514266830418411155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53598700342844553612274103 80398050514266830418411155)
        ·
          refine ⟨120597075771400245627616733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80398050514266830418411155 120597075771400245627616733)
          ·
            refine ⟨45223903414275092110356275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120597075771400245627616733 45223903414275092110356275)
            ·
              refine ⟨67835855121412638165534413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45223903414275092110356275 67835855121412638165534413)
              ·
                refine ⟨25438445670529739312075405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67835855121412638165534413 25438445670529739312075405)
                ·
                  refine ⟨9539417126448652242028277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25438445670529739312075405 9539417126448652242028277)
                  ·
                    refine ⟨894320355604561147690151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9539417126448652242028277 894320355604561147690151)
                    ·
                      rfl

theorem cell22_2612524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_2612524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612524 prefixEnd_2612524 := by exact prefixLift 2612524
  have htrace : WordTrace (prefixWord ++ tailWord_2612524) baseStart_2612524 baseEnd_2612524 := by
    simpa [prefixWord, tailWord_2612524, baseEnd_2612524] using wordTrace_append hprefix tailTrace_2612524
  have hstable : (prefixWord ++ tailWord_2612524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612524).length < 2 ^ (prefixWord ++ tailWord_2612524).sum := by decide
  have hdescent : baseEnd_2612524 < baseStart_2612524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612558 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_2612558 : Nat := 118140960795 + 2612558 * 2 ^ 59
def prefixEnd_2612558 : Nat := 4983230072969 + 3 ^ 40 * 2612558 * 2
def baseEnd_2612558 : Nat := 894331994499396392340047

theorem tailTrace_2612558 : CollatzResearch.WordTrace tailWord_2612558 prefixEnd_2612558 894331994499396392340047 := by
  unfold tailWord_2612558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11910977308644503778569791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 63525212312770686819038885 11910977308644503778569791)
  ·
    refine ⟨17866465962966755667854687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11910977308644503778569791 17866465962966755667854687)
    ·
      refine ⟨26799698944450133501782031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17866465962966755667854687 26799698944450133501782031)
      ·
        refine ⟨40199548416675200252673047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26799698944450133501782031 40199548416675200252673047)
        ·
          refine ⟨60299322625012800379009571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40199548416675200252673047 60299322625012800379009571)
          ·
            refine ⟨90448983937519200568514357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60299322625012800379009571 90448983937519200568514357)
            ·
              refine ⟨8479592244142425053298221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 90448983937519200568514357 8479592244142425053298221)
              ·
                refine ⟨3179847091553409394986833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8479592244142425053298221 3179847091553409394986833)
                ·
                  refine ⟨2384885318665057046240125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3179847091553409394986833 2384885318665057046240125)
                  ·
                    refine ⟨894331994499396392340047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384885318665057046240125 894331994499396392340047)
                    ·
                      rfl

theorem cell22_2612558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_2612558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612558 prefixEnd_2612558 := by exact prefixLift 2612558
  have htrace : WordTrace (prefixWord ++ tailWord_2612558) baseStart_2612558 baseEnd_2612558 := by
    simpa [prefixWord, tailWord_2612558, baseEnd_2612558] using wordTrace_append hprefix tailTrace_2612558
  have hstable : (prefixWord ++ tailWord_2612558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612558).length < 2 ^ (prefixWord ++ tailWord_2612558).sum := by decide
  have hdescent : baseEnd_2612558 < baseStart_2612558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612569 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_2612569 : Nat := 118140960795 + 2612569 * 2 ^ 59
def prefixEnd_2612569 : Nat := 4983230072969 + 3 ^ 40 * 2612569 * 2
def baseEnd_2612569 : Nat := 894335760024196030315013

theorem tailTrace_2612569 : CollatzResearch.WordTrace tailWord_2612569 prefixEnd_2612569 894335760024196030315013 := by
  unfold tailWord_2612569
  simp only [CollatzResearch.WordTrace]
  refine ⟨95288219672116179107208761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63525479781410786071472507 95288219672116179107208761)
  ·
    refine ⟨71466164754087134330406571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95288219672116179107208761 71466164754087134330406571)
    ·
      refine ⟨107199247131130701495609857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71466164754087134330406571 107199247131130701495609857)
      ·
        refine ⟨80399435348348026121707393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107199247131130701495609857 80399435348348026121707393)
        ·
          refine ⟨60299576511261019591280545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80399435348348026121707393 60299576511261019591280545)
          ·
            refine ⟨45224682383445764693460409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60299576511261019591280545 45224682383445764693460409)
            ·
              refine ⟨33918511787584323520095307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45224682383445764693460409 33918511787584323520095307)
              ·
                refine ⟨50877767681376485280142961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33918511787584323520095307 50877767681376485280142961)
                ·
                  refine ⟨38158325761032363960107221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50877767681376485280142961 38158325761032363960107221)
                  ·
                    refine ⟨894335760024196030315013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38158325761032363960107221 894335760024196030315013)
                    ·
                      rfl

theorem cell22_2612569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_2612569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612569 prefixEnd_2612569 := by exact prefixLift 2612569
  have htrace : WordTrace (prefixWord ++ tailWord_2612569) baseStart_2612569 baseEnd_2612569 := by
    simpa [prefixWord, tailWord_2612569, baseEnd_2612569] using wordTrace_append hprefix tailTrace_2612569
  have hstable : (prefixWord ++ tailWord_2612569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612569).length < 2 ^ (prefixWord ++ tailWord_2612569).sum := by decide
  have hdescent : baseEnd_2612569 < baseStart_2612569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612637 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 1, 3]
def baseStart_2612637 : Nat := 118140960795 + 2612637 * 2 ^ 59
def prefixEnd_2612637 : Nat := 4983230072969 + 3 ^ 40 * 2612637 * 2
def baseEnd_2612637 : Nat := 894359037813866519614805

theorem tailTrace_2612637 : CollatzResearch.WordTrace tailWord_2612637 prefixEnd_2612637 894359037813866519614805 := by
  unfold tailWord_2612637
  simp only [CollatzResearch.WordTrace]
  refine ⟨95290699835869826720684165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63527133223913217813789443 95290699835869826720684165)
  ·
    refine ⟨17867006219225592510128281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 95290699835869826720684165 17867006219225592510128281)
    ·
      refine ⟨13400254664419194382596211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17867006219225592510128281 13400254664419194382596211)
      ·
        refine ⟨20100381996628791573894317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13400254664419194382596211 20100381996628791573894317)
        ·
          refine ⟨7537643248735796840210369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20100381996628791573894317 7537643248735796840210369)
          ·
            refine ⟨5653232436551847630157777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537643248735796840210369 5653232436551847630157777)
            ·
              refine ⟨4239924327413885722618333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5653232436551847630157777 4239924327413885722618333)
              ·
                refine ⟨1589971622780207145981875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4239924327413885722618333 1589971622780207145981875)
                ·
                  refine ⟨2384957434170310718972813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1589971622780207145981875 2384957434170310718972813)
                  ·
                    refine ⟨894359037813866519614805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2384957434170310718972813 894359037813866519614805)
                    ·
                      rfl

theorem cell22_2612637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_2612637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612637 prefixEnd_2612637 := by exact prefixLift 2612637
  have htrace : WordTrace (prefixWord ++ tailWord_2612637) baseStart_2612637 baseEnd_2612637 := by
    simpa [prefixWord, tailWord_2612637, baseEnd_2612637] using wordTrace_append hprefix tailTrace_2612637
  have hstable : (prefixWord ++ tailWord_2612637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612637).length < 2 ^ (prefixWord ++ tailWord_2612637).sum := by decide
  have hdescent : baseEnd_2612637 < baseStart_2612637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612693 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2612693 : Nat := 118140960795 + 2612693 * 2 ^ 59
def prefixEnd_2612693 : Nat := 4983230072969 + 3 ^ 40 * 2612693 * 2
def baseEnd_2612693 : Nat := 894378207758301040214633

theorem tailTrace_2612693 : CollatzResearch.WordTrace tailWord_2612693 prefixEnd_2612693 894378207758301040214633 := by
  unfold tailWord_2612693
  simp only [CollatzResearch.WordTrace]
  refine ⟨95292742323666948284722733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63528494882444632189815155 95292742323666948284722733)
  ·
    refine ⟨35734778371375105606771025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95292742323666948284722733 35734778371375105606771025)
    ·
      refine ⟨26801083778531329205078269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35734778371375105606771025 26801083778531329205078269)
      ·
        refine ⟨10050406416949248451904351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26801083778531329205078269 10050406416949248451904351)
        ·
          refine ⟨15075609625423872677856527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10050406416949248451904351 15075609625423872677856527)
          ·
            refine ⟨22613414438135809016784791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15075609625423872677856527 22613414438135809016784791)
            ·
              refine ⟨33920121657203713525177187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22613414438135809016784791 33920121657203713525177187)
              ·
                refine ⟨50880182485805570287765781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33920121657203713525177187 50880182485805570287765781)
                ·
                  refine ⟨2385008554022136107239021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50880182485805570287765781 2385008554022136107239021)
                  ·
                    refine ⟨894378207758301040214633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385008554022136107239021 894378207758301040214633)
                    ·
                      rfl

theorem cell22_2612693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2612693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612693 prefixEnd_2612693 := by exact prefixLift 2612693
  have htrace : WordTrace (prefixWord ++ tailWord_2612693) baseStart_2612693 baseEnd_2612693 := by
    simpa [prefixWord, tailWord_2612693, baseEnd_2612693] using wordTrace_append hprefix tailTrace_2612693
  have hstable : (prefixWord ++ tailWord_2612693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612693).length < 2 ^ (prefixWord ++ tailWord_2612693).sum := by decide
  have hdescent : baseEnd_2612693 < baseStart_2612693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612965 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 6]
def baseStart_2612965 : Nat := 118140960795 + 2612965 * 2 ^ 59
def prefixEnd_2612965 : Nat := 4983230072969 + 3 ^ 40 * 2612965 * 2
def baseEnd_2612965 : Nat := 298157106305660999137933

theorem tailTrace_2612965 : CollatzResearch.WordTrace tailWord_2612965 prefixEnd_2612965 298157106305660999137933 := by
  unfold tailWord_2612965
  simp only [CollatzResearch.WordTrace]
  refine ⟨95302662978681538738624349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63535108652454359159082899 95302662978681538738624349)
  ·
    refine ⟨35738498617005577026984131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95302662978681538738624349 35738498617005577026984131)
    ·
      refine ⟨53607747925508365540476197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35738498617005577026984131 53607747925508365540476197)
      ·
        refine ⟨10051452736032818538839287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53607747925508365540476197 10051452736032818538839287)
        ·
          refine ⟨15077179104049227808258931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10051452736032818538839287 15077179104049227808258931)
          ·
            refine ⟨22615768656073841712388397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15077179104049227808258931 22615768656073841712388397)
            ·
              refine ⟨8480913246027690642145649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22615768656073841712388397 8480913246027690642145649)
              ·
                refine ⟨6360684934520767981609237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8480913246027690642145649 6360684934520767981609237)
                ·
                  refine ⟨298157106305660999137933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6360684934520767981609237 298157106305660999137933)
                  ·
                    rfl

theorem cell22_2612965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_2612965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612965 prefixEnd_2612965 := by exact prefixLift 2612965
  have htrace : WordTrace (prefixWord ++ tailWord_2612965) baseStart_2612965 baseEnd_2612965 := by
    simpa [prefixWord, tailWord_2612965, baseEnd_2612965] using wordTrace_append hprefix tailTrace_2612965
  have hstable : (prefixWord ++ tailWord_2612965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612965).length < 2 ^ (prefixWord ++ tailWord_2612965).sum := by decide
  have hdescent : baseEnd_2612965 < baseStart_2612965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2612995 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_2612995 : Nat := 118140960795 + 2612995 * 2 ^ 59
def prefixEnd_2612995 : Nat := 4983230072969 + 3 ^ 40 * 2612995 * 2
def baseEnd_2612995 : Nat := 894481588530072919163707

theorem tailTrace_2612995 : CollatzResearch.WordTrace tailWord_2612995 prefixEnd_2612995 894481588530072919163707 := by
  unfold tailWord_2612995
  simp only [CollatzResearch.WordTrace]
  refine ⟨95303757168572853862216439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63535838112381902574810959 95303757168572853862216439)
  ·
    refine ⟨142955635752859280793324659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95303757168572853862216439 142955635752859280793324659)
    ·
      refine ⟨214433453629288921189986989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142955635752859280793324659 214433453629288921189986989)
      ·
        refine ⟨80412545110983345446245121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214433453629288921189986989 80412545110983345446245121)
        ·
          refine ⟨60309408833237509084683841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80412545110983345446245121 60309408833237509084683841)
          ·
            refine ⟨45232056624928131813512881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60309408833237509084683841 45232056624928131813512881)
            ·
              refine ⟨33924042468696098860134661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45232056624928131813512881 33924042468696098860134661)
              ·
                refine ⟨6360757962880518536275249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33924042468696098860134661 6360757962880518536275249)
                ·
                  refine ⟨4770568472160388902206437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6360757962880518536275249 4770568472160388902206437)
                  ·
                    refine ⟨894481588530072919163707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770568472160388902206437 894481588530072919163707)
                    ·
                      rfl

theorem cell22_2612995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_2612995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2612995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2612995 prefixEnd_2612995 := by exact prefixLift 2612995
  have htrace : WordTrace (prefixWord ++ tailWord_2612995) baseStart_2612995 baseEnd_2612995 := by
    simpa [prefixWord, tailWord_2612995, baseEnd_2612995] using wordTrace_append hprefix tailTrace_2612995
  have hstable : (prefixWord ++ tailWord_2612995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2612995).length < 2 ^ (prefixWord ++ tailWord_2612995).sum := by decide
  have hdescent : baseEnd_2612995 < baseStart_2612995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2612995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613005 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2613005 : Nat := 118140960795 + 2613005 * 2 ^ 59
def prefixEnd_2613005 : Nat := 4983230072969 + 3 ^ 40 * 2613005 * 2
def baseEnd_2613005 : Nat := 298161670578145408804559

theorem tailTrace_2613005 : CollatzResearch.WordTrace tailWord_2613005 prefixEnd_2613005 298161670578145408804559 := by
  unfold tailWord_2613005
  simp only [CollatzResearch.WordTrace]
  refine ⟨95304121898536625570080469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63536081265691083713386979 95304121898536625570080469)
  ·
    refine ⟨2233690356996952161798761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 95304121898536625570080469 2233690356996952161798761)
    ·
      refine ⟨1675267767747714121349071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2233690356996952161798761 1675267767747714121349071)
      ·
        refine ⟨2512901651621571182023607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675267767747714121349071 2512901651621571182023607)
        ·
          refine ⟨3769352477432356773035411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2512901651621571182023607 3769352477432356773035411)
          ·
            refine ⟨5654028716148535159553117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769352477432356773035411 5654028716148535159553117)
            ·
              refine ⟨2120260768555700684832419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5654028716148535159553117 2120260768555700684832419)
              ·
                refine ⟨3180391152833551027248629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120260768555700684832419 3180391152833551027248629)
                ·
                  refine ⟨298161670578145408804559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180391152833551027248629 298161670578145408804559)
                  ·
                    rfl

theorem cell22_2613005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2613005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613005 prefixEnd_2613005 := by exact prefixLift 2613005
  have htrace : WordTrace (prefixWord ++ tailWord_2613005) baseStart_2613005 baseEnd_2613005 := by
    simpa [prefixWord, tailWord_2613005, baseEnd_2613005] using wordTrace_append hprefix tailTrace_2613005
  have hstable : (prefixWord ++ tailWord_2613005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613005).length < 2 ^ (prefixWord ++ tailWord_2613005).sum := by decide
  have hdescent : baseEnd_2613005 < baseStart_2613005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613059 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 3, 3]
def baseStart_2613059 : Nat := 118140960795 + 2613059 * 2 ^ 59
def prefixEnd_2613059 : Nat := 4983230072969 + 3 ^ 40 * 2613059 * 2
def baseEnd_2613059 : Nat := 894503497037998085563511

theorem tailTrace_2613059 : CollatzResearch.WordTrace tailWord_2613059 prefixEnd_2613059 894503497037998085563511 := by
  unfold tailWord_2613059
  simp only [CollatzResearch.WordTrace]
  refine ⟨95306091440340992792546231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63537394293560661861697487 95306091440340992792546231)
  ·
    refine ⟨142959137160511489188819347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95306091440340992792546231 142959137160511489188819347)
    ·
      refine ⟨214438705740767233783229021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142959137160511489188819347 214438705740767233783229021)
      ·
        refine ⟨80414514652787712668710883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214438705740767233783229021 80414514652787712668710883)
        ·
          refine ⟨120621771979181569003066325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80414514652787712668710883 120621771979181569003066325)
          ·
            refine ⟨2827072780762068023509367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 120621771979181569003066325 2827072780762068023509367)
            ·
              refine ⟨4240609171143102035264051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827072780762068023509367 4240609171143102035264051)
              ·
                refine ⟨6360913756714653052896077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4240609171143102035264051 6360913756714653052896077)
                ·
                  refine ⟨2385342658767994894836029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6360913756714653052896077 2385342658767994894836029)
                  ·
                    refine ⟨894503497037998085563511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385342658767994894836029 894503497037998085563511)
                    ·
                      rfl

theorem cell22_2613059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].length) (baseStart_2613059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613059 prefixEnd_2613059 := by exact prefixLift 2613059
  have htrace : WordTrace (prefixWord ++ tailWord_2613059) baseStart_2613059 baseEnd_2613059 := by
    simpa [prefixWord, tailWord_2613059, baseEnd_2613059] using wordTrace_append hprefix tailTrace_2613059
  have hstable : (prefixWord ++ tailWord_2613059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613059).length < 2 ^ (prefixWord ++ tailWord_2613059).sum := by decide
  have hdescent : baseEnd_2613059 < baseStart_2613059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613115 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_2613115 : Nat := 118140960795 + 2613115 * 2 ^ 59
def prefixEnd_2613115 : Nat := 4983230072969 + 3 ^ 40 * 2613115 * 2
def baseEnd_2613115 : Nat := 894522666982432606163339

theorem tailTrace_2613115 : CollatzResearch.WordTrace tailWord_2613115 prefixEnd_2613115 894522666982432606163339 := by
  unfold tailWord_2613115
  simp only [CollatzResearch.WordTrace]
  refine ⟨95308133928138114356584799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63538755952092076237723199 95308133928138114356584799)
  ·
    refine ⟨142962200892207171534877199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95308133928138114356584799 142962200892207171534877199)
    ·
      refine ⟨214443301338310757302315799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142962200892207171534877199 214443301338310757302315799)
      ·
        refine ⟨321664952007466135953473699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214443301338310757302315799 321664952007466135953473699)
        ·
          refine ⟨482497428011199203930210549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321664952007466135953473699 482497428011199203930210549)
          ·
            refine ⟨45234133876049925368457239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 482497428011199203930210549 45234133876049925368457239)
            ·
              refine ⟨67851200814074888052685859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45234133876049925368457239 67851200814074888052685859)
              ·
                refine ⟨101776801221112332079028789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67851200814074888052685859 101776801221112332079028789)
                ·
                  refine ⟨9541575114479281132408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101776801221112332079028789 9541575114479281132408949)
                  ·
                    refine ⟨894522666982432606163339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9541575114479281132408949 894522666982432606163339)
                    ·
                      rfl

theorem cell22_2613115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_2613115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613115 prefixEnd_2613115 := by exact prefixLift 2613115
  have htrace : WordTrace (prefixWord ++ tailWord_2613115) baseStart_2613115 baseEnd_2613115 := by
    simpa [prefixWord, tailWord_2613115, baseEnd_2613115] using wordTrace_append hprefix tailTrace_2613115
  have hstable : (prefixWord ++ tailWord_2613115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613115).length < 2 ^ (prefixWord ++ tailWord_2613115).sum := by decide
  have hdescent : baseEnd_2613115 < baseStart_2613115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613132 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 6, 3]
def baseStart_2613132 : Nat := 118140960795 + 2613132 * 2 ^ 59
def prefixEnd_2613132 : Nat := 4983230072969 + 3 ^ 40 * 2613132 * 2
def baseEnd_2613132 : Nat := 894528486429850228488287

theorem tailTrace_2613132 : CollatzResearch.WordTrace tailWord_2613132 prefixEnd_2613132 894528486429850228488287 := by
  unfold tailWord_2613132
  simp only [CollatzResearch.WordTrace]
  refine ⟨47654376984538263129976825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63539169312717684173302433 47654376984538263129976825)
  ·
    refine ⟨35740782738403697347482619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47654376984538263129976825 35740782738403697347482619)
    ·
      refine ⟨53611174107605546021223929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35740782738403697347482619 53611174107605546021223929)
      ·
        refine ⟨40208380580704159515917947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53611174107605546021223929 40208380580704159515917947)
        ·
          refine ⟨60312570871056239273876921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40208380580704159515917947 60312570871056239273876921)
          ·
            refine ⟨45234428153292179455407691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60312570871056239273876921 45234428153292179455407691)
            ·
              refine ⟨67851642229938269183111537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45234428153292179455407691 67851642229938269183111537)
              ·
                refine ⟨50888731672453701887333653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67851642229938269183111537 50888731672453701887333653)
                ·
                  refine ⟨2385409297146267275968765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50888731672453701887333653 2385409297146267275968765)
                  ·
                    refine ⟨894528486429850228488287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385409297146267275968765 894528486429850228488287)
                    ·
                      rfl

theorem cell22_2613132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 3].length) (baseStart_2613132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613132 prefixEnd_2613132 := by exact prefixLift 2613132
  have htrace : WordTrace (prefixWord ++ tailWord_2613132) baseStart_2613132 baseEnd_2613132 := by
    simpa [prefixWord, tailWord_2613132, baseEnd_2613132] using wordTrace_append hprefix tailTrace_2613132
  have hstable : (prefixWord ++ tailWord_2613132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613132).length < 2 ^ (prefixWord ++ tailWord_2613132).sum := by decide
  have hdescent : baseEnd_2613132 < baseStart_2613132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613145 : List Nat := [1, 2, 1, 2, 1, 3, 2, 10]
def baseStart_2613145 : Nat := 118140960795 + 2613145 * 2 ^ 59
def prefixEnd_2613145 : Nat := 4983230072969 + 3 ^ 40 * 2613145 * 2
def baseEnd_2613145 : Nat := 99392548510613614212583

theorem tailTrace_2613145 : CollatzResearch.WordTrace tailWord_2613145 prefixEnd_2613145 99392548510613614212583 := by
  unfold tailWord_2613145
  simp only [CollatzResearch.WordTrace]
  refine ⟨95309228118029429480176889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63539485412019619653451259 95309228118029429480176889)
  ·
    refine ⟨71481921088522072110132667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95309228118029429480176889 71481921088522072110132667)
    ·
      refine ⟨107222881632783108165199001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71481921088522072110132667 107222881632783108165199001)
      ·
        refine ⟨80417161224587331123899251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107222881632783108165199001 80417161224587331123899251)
        ·
          refine ⟨120625741836880996685848877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80417161224587331123899251 120625741836880996685848877)
          ·
            refine ⟨45234653188830373757193329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 120625741836880996685848877 45234653188830373757193329)
            ·
              refine ⟨33925989891622780317894997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45234653188830373757193329 33925989891622780317894997)
              ·
                refine ⟨99392548510613614212583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 33925989891622780317894997 99392548510613614212583)
                ·
                  rfl

theorem cell22_2613145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 10].length) (baseStart_2613145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613145 prefixEnd_2613145 := by exact prefixLift 2613145
  have htrace : WordTrace (prefixWord ++ tailWord_2613145) baseStart_2613145 baseEnd_2613145 := by
    simpa [prefixWord, tailWord_2613145, baseEnd_2613145] using wordTrace_append hprefix tailTrace_2613145
  have hstable : (prefixWord ++ tailWord_2613145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613145).length < 2 ^ (prefixWord ++ tailWord_2613145).sum := by decide
  have hdescent : baseEnd_2613145 < baseStart_2613145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613151 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 4]
def baseStart_2613151 : Nat := 118140960795 + 2613151 * 2 ^ 59
def prefixEnd_2613151 : Nat := 4983230072969 + 3 ^ 40 * 2613151 * 2
def baseEnd_2613151 : Nat := 298178330172713504087743

theorem tailTrace_2613151 : CollatzResearch.WordTrace tailWord_2613151 prefixEnd_2613151 298178330172713504087743 := by
  unfold tailWord_2613151
  simp only [CollatzResearch.WordTrace]
  refine ⟨95309446956007692504895307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63539631304005128336596871 95309446956007692504895307)
  ·
    refine ⟨142964170434011538757342961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95309446956007692504895307 142964170434011538757342961)
    ·
      refine ⟨107223127825508654068007221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142964170434011538757342961 107223127825508654068007221)
      ·
        refine ⟨10052168233641436318875677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107223127825508654068007221 10052168233641436318875677)
        ·
          refine ⟨3769563087615538619578379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10052168233641436318875677 3769563087615538619578379)
          ·
            refine ⟨5654344631423307929367569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3769563087615538619578379 5654344631423307929367569)
            ·
              refine ⟨4240758473567480947025677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5654344631423307929367569 4240758473567480947025677)
              ·
                refine ⟨1590284427587805355134629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4240758473567480947025677 1590284427587805355134629)
                ·
                  refine ⟨298178330172713504087743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1590284427587805355134629 298178330172713504087743)
                  ·
                    rfl

theorem cell22_2613151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 4].length) (baseStart_2613151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613151 prefixEnd_2613151 := by exact prefixLift 2613151
  have htrace : WordTrace (prefixWord ++ tailWord_2613151) baseStart_2613151 baseEnd_2613151 := by
    simpa [prefixWord, tailWord_2613151, baseEnd_2613151] using wordTrace_append hprefix tailTrace_2613151
  have hstable : (prefixWord ++ tailWord_2613151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613151).length < 2 ^ (prefixWord ++ tailWord_2613151).sum := by decide
  have hdescent : baseEnd_2613151 < baseStart_2613151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613153 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2613153 : Nat := 118140960795 + 2613153 * 2 ^ 59
def prefixEnd_2613153 : Nat := 4983230072969 + 3 ^ 40 * 2613153 * 2
def baseEnd_2613153 : Nat := 894535675159013173713223

theorem tailTrace_2613153 : CollatzResearch.WordTrace tailWord_2613153 prefixEnd_2613153 894535675159013173713223 := by
  unfold tailWord_2613153
  simp only [CollatzResearch.WordTrace]
  refine ⟨95309519902000446846468113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63539679934666964564312075 95309519902000446846468113)
  ·
    refine ⟨71482139926500335134851085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95309519902000446846468113 71482139926500335134851085)
    ·
      refine ⟨26805802472437625675569157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71482139926500335134851085 26805802472437625675569157)
      ·
        refine ⟨5026087963582054814169217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26805802472437625675569157 5026087963582054814169217)
        ·
          refine ⟨3769565972686541110626913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5026087963582054814169217 3769565972686541110626913)
          ·
            refine ⟨2827174479514905832970185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3769565972686541110626913 2827174479514905832970185)
            ·
              refine ⟨2120380859636179374727639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827174479514905832970185 2120380859636179374727639)
              ·
                refine ⟨3180571289454269062091459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120380859636179374727639 3180571289454269062091459)
                ·
                  refine ⟨4770856934181403593137189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3180571289454269062091459 4770856934181403593137189)
                  ·
                    refine ⟨894535675159013173713223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4770856934181403593137189 894535675159013173713223)
                    ·
                      rfl

theorem cell22_2613153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2613153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613153 prefixEnd_2613153 := by exact prefixLift 2613153
  have htrace : WordTrace (prefixWord ++ tailWord_2613153) baseStart_2613153 baseEnd_2613153 := by
    simpa [prefixWord, tailWord_2613153, baseEnd_2613153] using wordTrace_append hprefix tailTrace_2613153
  have hstable : (prefixWord ++ tailWord_2613153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613153).length < 2 ^ (prefixWord ++ tailWord_2613153).sum := by decide
  have hdescent : baseEnd_2613153 < baseStart_2613153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613194 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_2613194 : Nat := 118140960795 + 2613194 * 2 ^ 59
def prefixEnd_2613194 : Nat := 4983230072969 + 3 ^ 40 * 2613194 * 2
def baseEnd_2613194 : Nat := 894549710296902733438097

theorem tailTrace_2613194 : CollatzResearch.WordTrace tailWord_2613194 prefixEnd_2613194 894549710296902733438097 := by
  unfold tailWord_2613194
  simp only [CollatzResearch.WordTrace]
  refine ⟨23827753823712977712177659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63540676863234607232473757 23827753823712977712177659)
  ·
    refine ⟨35741630735569466568266489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23827753823712977712177659 35741630735569466568266489)
    ·
      refine ⟨26806223051677099926199867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35741630735569466568266489 26806223051677099926199867)
      ·
        refine ⟨40209334577515649889299801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26806223051677099926199867 40209334577515649889299801)
        ·
          refine ⟨30157000933136737416974851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40209334577515649889299801 30157000933136737416974851)
          ·
            refine ⟨45235501399705106125462277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30157000933136737416974851 45235501399705106125462277)
            ·
              refine ⟨8481656512444707398524177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45235501399705106125462277 8481656512444707398524177)
              ·
                refine ⟨6361242384333530548893133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8481656512444707398524177 6361242384333530548893133)
                ·
                  refine ⟨2385465894125073955834925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6361242384333530548893133 2385465894125073955834925)
                  ·
                    refine ⟨894549710296902733438097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385465894125073955834925 894549710296902733438097)
                    ·
                      rfl

theorem cell22_2613194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_2613194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613194 prefixEnd_2613194 := by exact prefixLift 2613194
  have htrace : WordTrace (prefixWord ++ tailWord_2613194) baseStart_2613194 baseEnd_2613194 := by
    simpa [prefixWord, tailWord_2613194, baseEnd_2613194] using wordTrace_append hprefix tailTrace_2613194
  have hstable : (prefixWord ++ tailWord_2613194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613194).length < 2 ^ (prefixWord ++ tailWord_2613194).sum := by decide
  have hdescent : baseEnd_2613194 < baseStart_2613194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613241 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 5]
def baseStart_2613241 : Nat := 118140960795 + 2613241 * 2 ^ 59
def prefixEnd_2613241 : Nat := 4983230072969 + 3 ^ 40 * 2613241 * 2
def baseEnd_2613241 : Nat := 298188599785803425837651

theorem tailTrace_2613241 : CollatzResearch.WordTrace tailWord_2613241 prefixEnd_2613241 298188599785803425837651 := by
  unfold tailWord_2613241
  simp only [CollatzResearch.WordTrace]
  refine ⟨95312729525681637875671577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63541819683787758583781051 95312729525681637875671577)
  ·
    refine ⟨71484547144261228406753683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95312729525681637875671577 71484547144261228406753683)
    ·
      refine ⟨107226820716391842610130525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71484547144261228406753683 107226820716391842610130525)
      ·
        refine ⟨40210057768646940978798947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 107226820716391842610130525 40210057768646940978798947)
        ·
          refine ⟨60315086652970411468198421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40210057768646940978798947 60315086652970411468198421)
          ·
            refine ⟨2827269686857988037571801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60315086652970411468198421 2827269686857988037571801)
            ·
              refine ⟨2120452265143491028178851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827269686857988037571801 2120452265143491028178851)
              ·
                refine ⟨3180678397715236542268277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120452265143491028178851 3180678397715236542268277)
                ·
                  refine ⟨298188599785803425837651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180678397715236542268277 298188599785803425837651)
                  ·
                    rfl

theorem cell22_2613241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 5].length) (baseStart_2613241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613241 prefixEnd_2613241 := by exact prefixLift 2613241
  have htrace : WordTrace (prefixWord ++ tailWord_2613241) baseStart_2613241 baseEnd_2613241 := by
    simpa [prefixWord, tailWord_2613241, baseEnd_2613241] using wordTrace_append hprefix tailTrace_2613241
  have hstable : (prefixWord ++ tailWord_2613241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613241).length < 2 ^ (prefixWord ++ tailWord_2613241).sum := by decide
  have hdescent : baseEnd_2613241 < baseStart_2613241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613267 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_2613267 : Nat := 118140960795 + 2613267 * 2 ^ 59
def prefixEnd_2613267 : Nat := 4983230072969 + 3 ^ 40 * 2613267 * 2
def baseEnd_2613267 : Nat := 894574699688754876362873

theorem tailTrace_2613267 : CollatzResearch.WordTrace tailWord_2613267 prefixEnd_2613267 894574699688754876362873 := by
  unfold tailWord_2613267
  simp only [CollatzResearch.WordTrace]
  refine ⟨95313677823587444316118055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63542451882391629544078703 95313677823587444316118055)
  ·
    refine ⟨142970516735381166474177083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95313677823587444316118055 142970516735381166474177083)
    ·
      refine ⟨214455775103071749711265625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142970516735381166474177083 214455775103071749711265625)
      ·
        refine ⟨160841831327303812283449219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214455775103071749711265625 160841831327303812283449219)
        ·
          refine ⟨241262746990955718425173829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160841831327303812283449219 241262746990955718425173829)
          ·
            refine ⟨45236765060804197204720093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 241262746990955718425173829 45236765060804197204720093)
            ·
              refine ⟨16963786897801573951770035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45236765060804197204720093 16963786897801573951770035)
              ·
                refine ⟨25445680346702360927655053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16963786897801573951770035 25445680346702360927655053)
                ·
                  refine ⟨9542130130013385347870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25445680346702360927655053 9542130130013385347870645)
                  ·
                    refine ⟨894574699688754876362873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9542130130013385347870645 894574699688754876362873)
                    ·
                      rfl

theorem cell22_2613267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_2613267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613267 prefixEnd_2613267 := by exact prefixLift 2613267
  have htrace : WordTrace (prefixWord ++ tailWord_2613267) baseStart_2613267 baseEnd_2613267 := by
    simpa [prefixWord, tailWord_2613267, baseEnd_2613267] using wordTrace_append hprefix tailTrace_2613267
  have hstable : (prefixWord ++ tailWord_2613267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613267).length < 2 ^ (prefixWord ++ tailWord_2613267).sum := by decide
  have hdescent : baseEnd_2613267 < baseStart_2613267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613301 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2613301 : Nat := 118140960795 + 2613301 * 2 ^ 59
def prefixEnd_2613301 : Nat := 4983230072969 + 3 ^ 40 * 2613301 * 2
def baseEnd_2613301 : Nat := 894586338583590121012769

theorem tailTrace_2613301 : CollatzResearch.WordTrace tailWord_2613301 prefixEnd_2613301 894586338583590121012769 := by
  unfold tailWord_2613301
  simp only [CollatzResearch.WordTrace]
  refine ⟨95314917905464268122855757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63543278603642845415237171 95314917905464268122855757)
  ·
    refine ⟨35743094214549100546070909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 95314917905464268122855757 35743094214549100546070909)
    ·
      refine ⟨13403660330455912704776591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35743094214549100546070909 13403660330455912704776591)
      ·
        refine ⟨20105490495683869057164887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13403660330455912704776591 20105490495683869057164887)
        ·
          refine ⟨30158235743525803585747331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20105490495683869057164887 30158235743525803585747331)
          ·
            refine ⟨45237353615288705378620997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30158235743525803585747331 45237353615288705378620997)
            ·
              refine ⟨8482003802866632258491437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45237353615288705378620997 8482003802866632258491437)
              ·
                refine ⟨3180751426074987096934289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8482003802866632258491437 3180751426074987096934289)
                ·
                  refine ⟨2385563569556240322700717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3180751426074987096934289 2385563569556240322700717)
                  ·
                    refine ⟨894586338583590121012769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385563569556240322700717 894586338583590121012769)
                    ·
                      rfl

theorem cell22_2613301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2613301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613301 prefixEnd_2613301 := by exact prefixLift 2613301
  have htrace : WordTrace (prefixWord ++ tailWord_2613301) baseStart_2613301 baseEnd_2613301 := by
    simpa [prefixWord, tailWord_2613301, baseEnd_2613301] using wordTrace_append hprefix tailTrace_2613301
  have hstable : (prefixWord ++ tailWord_2613301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613301).length < 2 ^ (prefixWord ++ tailWord_2613301).sum := by decide
  have hdescent : baseEnd_2613301 < baseStart_2613301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613318 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2613318 : Nat := 118140960795 + 2613318 * 2 ^ 59
def prefixEnd_2613318 : Nat := 4983230072969 + 3 ^ 40 * 2613318 * 2
def baseEnd_2613318 : Nat := 894592158031007743337717

theorem tailTrace_2613318 : CollatzResearch.WordTrace tailWord_2613318 prefixEnd_2613318 894592158031007743337717 := by
  unfold tailWord_2613318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978610560825083750819519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 63543691964268453350816405 2978610560825083750819519)
  ·
    refine ⟨4467915841237625626229279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2978610560825083750819519 4467915841237625626229279)
    ·
      refine ⟨6701873761856438439343919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4467915841237625626229279 6701873761856438439343919)
      ·
        refine ⟨10052810642784657659015879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6701873761856438439343919 10052810642784657659015879)
        ·
          refine ⟨15079215964176986488523819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10052810642784657659015879 15079215964176986488523819)
          ·
            refine ⟨22618823946265479732785729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15079215964176986488523819 22618823946265479732785729)
            ·
              refine ⟨16964117959699109799589297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22618823946265479732785729 16964117959699109799589297)
              ·
                refine ⟨12723088469774332349691973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16964117959699109799589297 12723088469774332349691973)
                ·
                  refine ⟨2385579088082687315567245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12723088469774332349691973 2385579088082687315567245)
                  ·
                    refine ⟨894592158031007743337717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385579088082687315567245 894592158031007743337717)
                    ·
                      rfl

theorem cell22_2613318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2613318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613318 prefixEnd_2613318 := by exact prefixLift 2613318
  have htrace : WordTrace (prefixWord ++ tailWord_2613318) baseStart_2613318 baseEnd_2613318 := by
    simpa [prefixWord, tailWord_2613318, baseEnd_2613318] using wordTrace_append hprefix tailTrace_2613318
  have hstable : (prefixWord ++ tailWord_2613318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613318).length < 2 ^ (prefixWord ++ tailWord_2613318).sum := by decide
  have hdescent : baseEnd_2613318 < baseStart_2613318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613327 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_2613327 : Nat := 118140960795 + 2613327 * 2 ^ 59
def prefixEnd_2613327 : Nat := 4983230072969 + 3 ^ 40 * 2613327 * 2
def baseEnd_2613327 : Nat := 894595238914934719862689

theorem tailTrace_2613327 : CollatzResearch.WordTrace tailWord_2613327 prefixEnd_2613327 894595238914934719862689 := by
  unfold tailWord_2613327
  simp only [CollatzResearch.WordTrace]
  refine ⟨95315866203370074563302235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63543910802246716375534823 95315866203370074563302235)
  ·
    refine ⟨142973799305055111844953353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95315866203370074563302235 142973799305055111844953353)
    ·
      refine ⟨107230349478791333883715015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142973799305055111844953353 107230349478791333883715015)
      ·
        refine ⟨160845524218187000825572523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107230349478791333883715015 160845524218187000825572523)
        ·
          refine ⟨241268286327280501238358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160845524218187000825572523 241268286327280501238358785)
          ·
            refine ⟨180951214745460375928769089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241268286327280501238358785 180951214745460375928769089)
            ·
              refine ⟨135713411059095281946576817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180951214745460375928769089 135713411059095281946576817)
              ·
                refine ⟨101785058294321461459932613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135713411059095281946576817 101785058294321461459932613)
                ·
                  refine ⟨19084698430185274023737365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101785058294321461459932613 19084698430185274023737365)
                  ·
                    refine ⟨894595238914934719862689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19084698430185274023737365 894595238914934719862689)
                    ·
                      rfl

theorem cell22_2613327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_2613327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613327 prefixEnd_2613327 := by exact prefixLift 2613327
  have htrace : WordTrace (prefixWord ++ tailWord_2613327) baseStart_2613327 baseEnd_2613327 := by
    simpa [prefixWord, tailWord_2613327, baseEnd_2613327] using wordTrace_append hprefix tailTrace_2613327
  have hstable : (prefixWord ++ tailWord_2613327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613327).length < 2 ^ (prefixWord ++ tailWord_2613327).sum := by decide
  have hdescent : baseEnd_2613327 < baseStart_2613327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613329 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_2613329 : Nat := 118140960795 + 2613329 * 2 ^ 59
def prefixEnd_2613329 : Nat := 4983230072969 + 3 ^ 40 * 2613329 * 2
def baseEnd_2613329 : Nat := 894595923555807381312683

theorem tailTrace_2613329 : CollatzResearch.WordTrace tailWord_2613329 prefixEnd_2613329 894595923555807381312683 := by
  unfold tailWord_2613329
  simp only [CollatzResearch.WordTrace]
  refine ⟨95315939149362828904875041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63543959432908552603250027 95315939149362828904875041)
  ·
    refine ⟨71486954362022121678656281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95315939149362828904875041 71486954362022121678656281)
    ·
      refine ⟨53615215771516591258992211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71486954362022121678656281 53615215771516591258992211)
      ·
        refine ⟨80422823657274886888488317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53615215771516591258992211 80422823657274886888488317)
        ·
          refine ⟨30158558871478082583183119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80422823657274886888488317 30158558871478082583183119)
          ·
            refine ⟨45237838307217123874774679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30158558871478082583183119 45237838307217123874774679)
            ·
              refine ⟨67856757460825685812162019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45237838307217123874774679 67856757460825685812162019)
              ·
                refine ⟨101785136191238528718243029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67856757460825685812162019 101785136191238528718243029)
                ·
                  refine ⟨2385589129482153016833821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 101785136191238528718243029 2385589129482153016833821)
                  ·
                    refine ⟨894595923555807381312683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385589129482153016833821 894595923555807381312683)
                    ·
                      rfl

theorem cell22_2613329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_2613329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613329 prefixEnd_2613329 := by exact prefixLift 2613329
  have htrace : WordTrace (prefixWord ++ tailWord_2613329) baseStart_2613329 baseEnd_2613329 := by
    simpa [prefixWord, tailWord_2613329, baseEnd_2613329] using wordTrace_append hprefix tailTrace_2613329
  have hstable : (prefixWord ++ tailWord_2613329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613329).length < 2 ^ (prefixWord ++ tailWord_2613329).sum := by decide
  have hdescent : baseEnd_2613329 < baseStart_2613329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613410 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2613410 : Nat := 118140960795 + 2613410 * 2 ^ 59
def prefixEnd_2613410 : Nat := 4983230072969 + 3 ^ 40 * 2613410 * 2
def baseEnd_2613410 : Nat := 298207883837050056679145

theorem tailTrace_2613410 : CollatzResearch.WordTrace tailWord_2613410 prefixEnd_2613410 298207883837050056679145 := by
  unfold tailWord_2613410
  simp only [CollatzResearch.WordTrace]
  refine ⟨23829723365517344934643421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63545928974712919825715789 23829723365517344934643421)
  ·
    refine ⟨8936146262069004350491283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23829723365517344934643421 8936146262069004350491283)
    ·
      refine ⟨13404219393103506525736925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936146262069004350491283 13404219393103506525736925)
      ·
        refine ⟨5026582272413814947151347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13404219393103506525736925 5026582272413814947151347)
        ·
          refine ⟨7539873408620722420727021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026582272413814947151347 7539873408620722420727021)
          ·
            refine ⟨2827452528232770907772633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7539873408620722420727021 2827452528232770907772633)
            ·
              refine ⟨2120589396174578180829475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827452528232770907772633 2120589396174578180829475)
              ·
                refine ⟨3180884094261867271244213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120589396174578180829475 3180884094261867271244213)
                ·
                  refine ⟨298207883837050056679145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3180884094261867271244213 298207883837050056679145)
                  ·
                    rfl

theorem cell22_2613410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2613410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613410 prefixEnd_2613410 := by exact prefixLift 2613410
  have htrace : WordTrace (prefixWord ++ tailWord_2613410) baseStart_2613410 baseEnd_2613410 := by
    simpa [prefixWord, tailWord_2613410, baseEnd_2613410] using wordTrace_append hprefix tailTrace_2613410
  have hstable : (prefixWord ++ tailWord_2613410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613410).length < 2 ^ (prefixWord ++ tailWord_2613410).sum := by decide
  have hdescent : baseEnd_2613410 < baseStart_2613410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613434 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_2613434 : Nat := 118140960795 + 2613434 * 2 ^ 59
def prefixEnd_2613434 : Nat := 4983230072969 + 3 ^ 40 * 2613434 * 2
def baseEnd_2613434 : Nat := 894631867201622107437361

theorem tailTrace_2613434 : CollatzResearch.WordTrace tailWord_2613434 prefixEnd_2613434 894631867201622107437361 := by
  unfold tailWord_2613434
  simp only [CollatzResearch.WordTrace]
  refine ⟨23829942203495607959361839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63546512542654954558298237 23829942203495607959361839)
  ·
    refine ⟨35744913305243411939042759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23829942203495607959361839 35744913305243411939042759)
    ·
      refine ⟨53617369957865117908564139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35744913305243411939042759 53617369957865117908564139)
      ·
        refine ⟨80426054936797676862846209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53617369957865117908564139 80426054936797676862846209)
        ·
          refine ⟨60319541202598257647134657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80426054936797676862846209 60319541202598257647134657)
          ·
            refine ⟨45239655901948693235350993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60319541202598257647134657 45239655901948693235350993)
            ·
              refine ⟨33929741926461519926513245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45239655901948693235350993 33929741926461519926513245)
              ·
                refine ⟨12723653222423069972442467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33929741926461519926513245 12723653222423069972442467)
                ·
                  refine ⟨19085479833634604958663701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12723653222423069972442467 19085479833634604958663701)
                  ·
                    refine ⟨894631867201622107437361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19085479833634604958663701 894631867201622107437361)
                    ·
                      rfl

theorem cell22_2613434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_2613434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613434 prefixEnd_2613434 := by exact prefixLift 2613434
  have htrace : WordTrace (prefixWord ++ tailWord_2613434) baseStart_2613434 baseEnd_2613434 := by
    simpa [prefixWord, tailWord_2613434, baseEnd_2613434] using wordTrace_append hprefix tailTrace_2613434
  have hstable : (prefixWord ++ tailWord_2613434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613434).length < 2 ^ (prefixWord ++ tailWord_2613434).sum := by decide
  have hdescent : baseEnd_2613434 < baseStart_2613434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613481 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_2613481 : Nat := 118140960795 + 2613481 * 2 ^ 59
def prefixEnd_2613481 : Nat := 4983230072969 + 3 ^ 40 * 2613481 * 2
def baseEnd_2613481 : Nat := 894647956262129651512217

theorem tailTrace_2613481 : CollatzResearch.WordTrace tailWord_2613481 prefixEnd_2613481 894647956262129651512217 := by
  unfold tailWord_2613481
  simp only [CollatzResearch.WordTrace]
  refine ⟨95321483044812158864408297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63547655363208105909605531 95321483044812158864408297)
  ·
    refine ⟨71491112283609119148306223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 95321483044812158864408297 71491112283609119148306223)
    ·
      refine ⟨107236668425413678722459335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71491112283609119148306223 107236668425413678722459335)
      ·
        refine ⟨160855002638120518083689003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107236668425413678722459335 160855002638120518083689003)
        ·
          refine ⟨241282503957180777125533505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160855002638120518083689003 241282503957180777125533505)
          ·
            refine ⟨180961877967885582844150129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241282503957180777125533505 180961877967885582844150129)
            ·
              refine ⟨135721408475914187133112597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180961877967885582844150129 135721408475914187133112597)
              ·
                refine ⟨6361941022308477521864653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 135721408475914187133112597 6361941022308477521864653)
                ·
                  refine ⟨2385727883365679070699245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6361941022308477521864653 2385727883365679070699245)
                  ·
                    refine ⟨894647956262129651512217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385727883365679070699245 894647956262129651512217)
                    ·
                      rfl

theorem cell22_2613481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_2613481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613481 prefixEnd_2613481 := by exact prefixLift 2613481
  have htrace : WordTrace (prefixWord ++ tailWord_2613481) baseStart_2613481 baseEnd_2613481 := by
    simpa [prefixWord, tailWord_2613481, baseEnd_2613481] using wordTrace_append hprefix tailTrace_2613481
  have hstable : (prefixWord ++ tailWord_2613481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613481).length < 2 ^ (prefixWord ++ tailWord_2613481).sum := by decide
  have hdescent : baseEnd_2613481 < baseStart_2613481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613485 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_2613485 : Nat := 118140960795 + 2613485 * 2 ^ 59
def prefixEnd_2613485 : Nat := 4983230072969 + 3 ^ 40 * 2613485 * 2
def baseEnd_2613485 : Nat := 894649325543874974412205

theorem tailTrace_2613485 : CollatzResearch.WordTrace tailWord_2613485 prefixEnd_2613485 894649325543874974412205 := by
  unfold tailWord_2613485
  simp only [CollatzResearch.WordTrace]
  refine ⟨95321628936797667547553909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63547752624531778365035939 95321628936797667547553909)
  ·
    refine ⟨8936402712824781332583179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95321628936797667547553909 8936402712824781332583179)
    ·
      refine ⟨13404604069237171998874769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8936402712824781332583179 13404604069237171998874769)
      ·
        refine ⟨10053453051927878999156077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13404604069237171998874769 10053453051927878999156077)
        ·
          refine ⟨3770044894472954624683529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10053453051927878999156077 3770044894472954624683529)
          ·
            refine ⟨2827533670854715968512647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3770044894472954624683529 2827533670854715968512647)
            ·
              refine ⟨4241300506282073952768971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827533670854715968512647 4241300506282073952768971)
              ·
                refine ⟨6361950759423110929153457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241300506282073952768971 6361950759423110929153457)
                ·
                  refine ⟨4771463069567333196865093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6361950759423110929153457 4771463069567333196865093)
                  ·
                    refine ⟨894649325543874974412205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771463069567333196865093 894649325543874974412205)
                    ·
                      rfl

theorem cell22_2613485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_2613485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613485 prefixEnd_2613485 := by exact prefixLift 2613485
  have htrace : WordTrace (prefixWord ++ tailWord_2613485) baseStart_2613485 baseEnd_2613485 := by
    simpa [prefixWord, tailWord_2613485, baseEnd_2613485] using wordTrace_append hprefix tailTrace_2613485
  have hstable : (prefixWord ++ tailWord_2613485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613485).length < 2 ^ (prefixWord ++ tailWord_2613485).sum := by decide
  have hdescent : baseEnd_2613485 < baseStart_2613485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613528 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_2613528 : Nat := 118140960795 + 2613528 * 2 ^ 59
def prefixEnd_2613528 : Nat := 4983230072969 + 3 ^ 40 * 2613528 * 2
def baseEnd_2613528 : Nat := 298221348440879065195691

theorem tailTrace_2613528 : CollatzResearch.WordTrace tailWord_2613528 prefixEnd_2613528 298221348440879065195691 := by
  unfold tailWord_2613528
  simp only [CollatzResearch.WordTrace]
  refine ⟨47661598637820942945684619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63548798183761257260912825 47661598637820942945684619)
  ·
    refine ⟨71492397956731414418526929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47661598637820942945684619 71492397956731414418526929)
    ·
      refine ⟨53619298467548560813895197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71492397956731414418526929 53619298467548560813895197)
      ·
        refine ⟨20107236925330710305210699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53619298467548560813895197 20107236925330710305210699)
        ·
          refine ⟨30160855387996065457816049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107236925330710305210699 30160855387996065457816049)
          ·
            refine ⟨22620641540997049093362037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30160855387996065457816049 22620641540997049093362037)
            ·
              refine ⟨2120685144468473352502691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22620641540997049093362037 2120685144468473352502691)
              ·
                refine ⟨3181027716702710028754037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2120685144468473352502691 3181027716702710028754037)
                ·
                  refine ⟨298221348440879065195691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3181027716702710028754037 298221348440879065195691)
                  ·
                    rfl

theorem cell22_2613528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_2613528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613528 prefixEnd_2613528 := by exact prefixLift 2613528
  have htrace : WordTrace (prefixWord ++ tailWord_2613528) baseStart_2613528 baseEnd_2613528 := by
    simpa [prefixWord, tailWord_2613528, baseEnd_2613528] using wordTrace_append hprefix tailTrace_2613528
  have hstable : (prefixWord ++ tailWord_2613528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613528).length < 2 ^ (prefixWord ++ tailWord_2613528).sum := by decide
  have hdescent : baseEnd_2613528 < baseStart_2613528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613586 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2613586 : Nat := 118140960795 + 2613586 * 2 ^ 59
def prefixEnd_2613586 : Nat := 4983230072969 + 3 ^ 40 * 2613586 * 2
def baseEnd_2613586 : Nat := 894683899907944377636895

theorem tailTrace_2613586 : CollatzResearch.WordTrace tailWord_2613586 prefixEnd_2613586 894683899907944377636895 := by
  unfold tailWord_2613586
  simp only [CollatzResearch.WordTrace]
  refine ⟨23831328177357940449245153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 63550208472954507864653741 23831328177357940449245153)
  ·
    refine ⟨17873496133018455336933865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23831328177357940449245153 17873496133018455336933865)
    ·
      refine ⟨13405122099763841502700399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17873496133018455336933865 13405122099763841502700399)
      ·
        refine ⟨20107683149645762254050599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13405122099763841502700399 20107683149645762254050599)
        ·
          refine ⟨30161524724468643381075899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20107683149645762254050599 30161524724468643381075899)
          ·
            refine ⟨45242287086702965071613849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30161524724468643381075899 45242287086702965071613849)
            ·
              refine ⟨33931715315027223803710387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45242287086702965071613849 33931715315027223803710387)
              ·
                refine ⟨50897572972540835705565581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33931715315027223803710387 50897572972540835705565581)
                ·
                  refine ⟨19086589864702813389587093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50897572972540835705565581 19086589864702813389587093)
                  ·
                    refine ⟨894683899907944377636895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19086589864702813389587093 894683899907944377636895)
                    ·
                      rfl

theorem cell22_2613586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2613586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613586 prefixEnd_2613586 := by exact prefixLift 2613586
  have htrace : WordTrace (prefixWord ++ tailWord_2613586) baseStart_2613586 baseEnd_2613586 := by
    simpa [prefixWord, tailWord_2613586, baseEnd_2613586] using wordTrace_append hprefix tailTrace_2613586
  have hstable : (prefixWord ++ tailWord_2613586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613586).length < 2 ^ (prefixWord ++ tailWord_2613586).sum := by decide
  have hdescent : baseEnd_2613586 < baseStart_2613586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613603 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_2613603 : Nat := 118140960795 + 2613603 * 2 ^ 59
def prefixEnd_2613603 : Nat := 4983230072969 + 3 ^ 40 * 2613603 * 2
def baseEnd_2613603 : Nat := 894689719355361999961843

theorem tailTrace_2613603 : CollatzResearch.WordTrace tailWord_2613603 prefixEnd_2613603 894689719355361999961843 := by
  unfold tailWord_2613603
  simp only [CollatzResearch.WordTrace]
  refine ⟨95325932750370173700349463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63550621833580115800232975 95325932750370173700349463)
  ·
    refine ⟨142988899125555260550524195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95325932750370173700349463 142988899125555260550524195)
    ·
      refine ⟨214483348688332890825786293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142988899125555260550524195 214483348688332890825786293)
      ·
        refine ⟨20107813939531208514917465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 214483348688332890825786293 20107813939531208514917465)
        ·
          refine ⟨15080860454648406386188099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20107813939531208514917465 15080860454648406386188099)
          ·
            refine ⟨22621290681972609579282149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15080860454648406386188099 22621290681972609579282149)
            ·
              refine ⟨4241492002869864296115403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22621290681972609579282149 4241492002869864296115403)
              ·
                refine ⟨6362238004304796444173105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241492002869864296115403 6362238004304796444173105)
                ·
                  refine ⟨4771678503228597333129829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6362238004304796444173105 4771678503228597333129829)
                  ·
                    refine ⟨894689719355361999961843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4771678503228597333129829 894689719355361999961843)
                    ·
                      rfl

theorem cell22_2613603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_2613603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613603 prefixEnd_2613603 := by exact prefixLift 2613603
  have htrace : WordTrace (prefixWord ++ tailWord_2613603) baseStart_2613603 baseEnd_2613603 := by
    simpa [prefixWord, tailWord_2613603, baseEnd_2613603] using wordTrace_append hprefix tailTrace_2613603
  have hstable : (prefixWord ++ tailWord_2613603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613603).length < 2 ^ (prefixWord ++ tailWord_2613603).sum := by decide
  have hdescent : baseEnd_2613603 < baseStart_2613603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613635 : List Nat := [1, 1, 1, 3, 7, 1, 1, 7]
def baseStart_2613635 : Nat := 118140960795 + 2613635 * 2 ^ 59
def prefixEnd_2613635 : Nat := 4983230072969 + 3 ^ 40 * 2613635 * 2
def baseEnd_2613635 : Nat := 99411185956591620351305

theorem tailTrace_2613635 : CollatzResearch.WordTrace tailWord_2613635 prefixEnd_2613635 99411185956591620351305 := by
  unfold tailWord_2613635
  simp only [CollatzResearch.WordTrace]
  refine ⟨95327099886254243165514359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63551399924169495443676239 95327099886254243165514359)
  ·
    refine ⟨142990649829381364748271539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95327099886254243165514359 142990649829381364748271539)
    ·
      refine ⟨214485974744072047122407309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142990649829381364748271539 214485974744072047122407309)
      ·
        refine ⟨80432240529027017670902741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214485974744072047122407309 80432240529027017670902741)
        ·
          refine ⟨1885130637399070726661783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 80432240529027017670902741 1885130637399070726661783)
          ·
            refine ⟨2827695956098606089992675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1885130637399070726661783 2827695956098606089992675)
            ·
              refine ⟨4241543934147909134989013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2827695956098606089992675 4241543934147909134989013)
              ·
                refine ⟨99411185956591620351305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4241543934147909134989013 99411185956591620351305)
                ·
                  rfl

theorem cell22_2613635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 7].length) (baseStart_2613635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613635 prefixEnd_2613635 := by exact prefixLift 2613635
  have htrace : WordTrace (prefixWord ++ tailWord_2613635) baseStart_2613635 baseEnd_2613635 := by
    simpa [prefixWord, tailWord_2613635, baseEnd_2613635] using wordTrace_append hprefix tailTrace_2613635
  have hstable : (prefixWord ++ tailWord_2613635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613635).length < 2 ^ (prefixWord ++ tailWord_2613635).sum := by decide
  have hdescent : baseEnd_2613635 < baseStart_2613635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613654 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_2613654 : Nat := 118140960795 + 2613654 * 2 ^ 59
def prefixEnd_2613654 : Nat := 4983230072969 + 3 ^ 40 * 2613654 * 2
def baseEnd_2613654 : Nat := 894707177697614866936687

theorem tailTrace_2613654 : CollatzResearch.WordTrace tailWord_2613654 prefixEnd_2613654 894707177697614866936687 := by
  unfold tailWord_2613654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5957987054574088088153501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 63551861915456939606970677 5957987054574088088153501)
  ·
    refine ⟨2234245145465283033057563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5957987054574088088153501 2234245145465283033057563)
    ·
      refine ⟨3351367718197924549586345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2234245145465283033057563 3351367718197924549586345)
      ·
        refine ⟨2513525788648443412189759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3351367718197924549586345 2513525788648443412189759)
        ·
          refine ⟨3770288682972665118284639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2513525788648443412189759 3770288682972665118284639)
          ·
            refine ⟨5655433024458997677426959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3770288682972665118284639 5655433024458997677426959)
            ·
              refine ⟨8483149536688496516140439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5655433024458997677426959 8483149536688496516140439)
              ·
                refine ⟨12724724305032744774210659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8483149536688496516140439 12724724305032744774210659)
                ·
                  refine ⟨19087086457549117161315989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12724724305032744774210659 19087086457549117161315989)
                  ·
                    refine ⟨894707177697614866936687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19087086457549117161315989 894707177697614866936687)
                    ·
                      rfl

theorem cell22_2613654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_2613654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613654 prefixEnd_2613654 := by exact prefixLift 2613654
  have htrace : WordTrace (prefixWord ++ tailWord_2613654) baseStart_2613654 baseEnd_2613654 := by
    simpa [prefixWord, tailWord_2613654, baseEnd_2613654] using wordTrace_append hprefix tailTrace_2613654
  have hstable : (prefixWord ++ tailWord_2613654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613654).length < 2 ^ (prefixWord ++ tailWord_2613654).sum := by decide
  have hdescent : baseEnd_2613654 < baseStart_2613654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613667 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 1, 3]
def baseStart_2613667 : Nat := 118140960795 + 2613667 * 2 ^ 59
def prefixEnd_2613667 : Nat := 4983230072969 + 3 ^ 40 * 2613667 * 2
def baseEnd_2613667 : Nat := 894711627863287166361647

theorem tailTrace_2613667 : CollatzResearch.WordTrace tailWord_2613667 prefixEnd_2613667 894711627863287166361647 := by
  unfold tailWord_2613667
  simp only [CollatzResearch.WordTrace]
  refine ⟨95328267022138312630679255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63552178014758875087119503 95328267022138312630679255)
  ·
    refine ⟨142992400533207468946018883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95328267022138312630679255 142992400533207468946018883)
    ·
      refine ⟨214488600799811203419028325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142992400533207468946018883 214488600799811203419028325)
      ·
        refine ⟨40216612649964600641067811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 214488600799811203419028325 40216612649964600641067811)
        ·
          refine ⟨60324918974946900961601717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40216612649964600641067811 60324918974946900961601717)
          ·
            refine ⟨5655461153901271965150161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60324918974946900961601717 5655461153901271965150161)
            ·
              refine ⟨4241595865425953973862621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5655461153901271965150161 4241595865425953973862621)
              ·
                refine ⟨1590598449534732740198483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4241595865425953973862621 1590598449534732740198483)
                ·
                  refine ⟨2385897674302099110297725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1590598449534732740198483 2385897674302099110297725)
                  ·
                    refine ⟨894711627863287166361647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385897674302099110297725 894711627863287166361647)
                    ·
                      rfl

theorem cell22_2613667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 3].length) (baseStart_2613667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613667 prefixEnd_2613667 := by exact prefixLift 2613667
  have htrace : WordTrace (prefixWord ++ tailWord_2613667) baseStart_2613667 baseEnd_2613667 := by
    simpa [prefixWord, tailWord_2613667, baseEnd_2613667] using wordTrace_append hprefix tailTrace_2613667
  have hstable : (prefixWord ++ tailWord_2613667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613667).length < 2 ^ (prefixWord ++ tailWord_2613667).sum := by decide
  have hdescent : baseEnd_2613667 < baseStart_2613667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613740 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_2613740 : Nat := 118140960795 + 2613740 * 2 ^ 59
def prefixEnd_2613740 : Nat := 4983230072969 + 3 ^ 40 * 2613740 * 2
def baseEnd_2613740 : Nat := 894736617255139309286423

theorem tailTrace_2613740 : CollatzResearch.WordTrace tailWord_2613740 prefixEnd_2613740 894736617255139309286423 := by
  unfold tailWord_2613740
  simp only [CollatzResearch.WordTrace]
  refine ⟨47665464775436923049043337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63553953033915897398724449 47665464775436923049043337)
  ·
    refine ⟨35749098581577692286782503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47665464775436923049043337 35749098581577692286782503)
    ·
      refine ⟨53623647872366538430173755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35749098581577692286782503 53623647872366538430173755)
      ·
        refine ⟨80435471808549807645260633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53623647872366538430173755 80435471808549807645260633)
        ·
          refine ⟨60326603856412355733945475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80435471808549807645260633 60326603856412355733945475)
          ·
            refine ⟨90489905784618533600918213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60326603856412355733945475 90489905784618533600918213)
            ·
              refine ⟨16966857334615975050172165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90489905784618533600918213 16966857334615975050172165)
              ·
                refine ⟨3181285750240495321907281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16966857334615975050172165 3181285750240495321907281)
                ·
                  refine ⟨2385964312680371491430461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3181285750240495321907281 2385964312680371491430461)
                  ·
                    refine ⟨894736617255139309286423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2385964312680371491430461 894736617255139309286423)
                    ·
                      rfl

theorem cell22_2613740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_2613740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613740 prefixEnd_2613740 := by exact prefixLift 2613740
  have htrace : WordTrace (prefixWord ++ tailWord_2613740) baseStart_2613740 baseEnd_2613740 := by
    simpa [prefixWord, tailWord_2613740, baseEnd_2613740] using wordTrace_append hprefix tailTrace_2613740
  have hstable : (prefixWord ++ tailWord_2613740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613740).length < 2 ^ (prefixWord ++ tailWord_2613740).sum := by decide
  have hdescent : baseEnd_2613740 < baseStart_2613740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613800 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2613800 : Nat := 118140960795 + 2613800 * 2 ^ 59
def prefixEnd_2613800 : Nat := 4983230072969 + 3 ^ 40 * 2613800 * 2
def baseEnd_2613800 : Nat := 894757156481319152786239

theorem tailTrace_2613800 : CollatzResearch.WordTrace tailWord_2613800 prefixEnd_2613800 894757156481319152786239 := by
  unfold tailWord_2613800
  simp only [CollatzResearch.WordTrace]
  refine ⟨47666558965328238172635427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63555411953770984230180569 47666558965328238172635427)
  ·
    refine ⟨71499838447992357258953141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47666558965328238172635427 71499838447992357258953141)
    ·
      refine ⟨6703109854499283493026857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71499838447992357258953141 6703109854499283493026857)
      ·
        refine ⟨5027332390874462619770143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6703109854499283493026857 5027332390874462619770143)
        ·
          refine ⟨7540998586311693929655215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5027332390874462619770143 7540998586311693929655215)
          ·
            refine ⟨11311497879467540894482823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7540998586311693929655215 11311497879467540894482823)
            ·
              refine ⟨16967246819201311341724235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11311497879467540894482823 16967246819201311341724235)
              ·
                refine ⟨25450870228801967012586353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16967246819201311341724235 25450870228801967012586353)
                ·
                  refine ⟨19088152671601475259439765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25450870228801967012586353 19088152671601475259439765)
                  ·
                    refine ⟨894757156481319152786239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19088152671601475259439765 894757156481319152786239)
                    ·
                      rfl

theorem cell22_2613800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2613800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613800 prefixEnd_2613800 := by exact prefixLift 2613800
  have htrace : WordTrace (prefixWord ++ tailWord_2613800) baseStart_2613800 baseEnd_2613800 := by
    simpa [prefixWord, tailWord_2613800, baseEnd_2613800] using wordTrace_append hprefix tailTrace_2613800
  have hstable : (prefixWord ++ tailWord_2613800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613800).length < 2 ^ (prefixWord ++ tailWord_2613800).sum := by decide
  have hdescent : baseEnd_2613800 < baseStart_2613800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613860 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2613860 : Nat := 118140960795 + 2613860 * 2 ^ 59
def prefixEnd_2613860 : Nat := 4983230072969 + 3 ^ 40 * 2613860 * 2
def baseEnd_2613860 : Nat := 298259231902499665428685

theorem tailTrace_2613860 : CollatzResearch.WordTrace tailWord_2613860 prefixEnd_2613860 298259231902499665428685 := by
  unfold tailWord_2613860
  simp only [CollatzResearch.WordTrace]
  refine ⟨47667653155219553296227517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63556870873626071061636689 47667653155219553296227517)
  ·
    refine ⟨17875369933207332486085319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47667653155219553296227517 17875369933207332486085319)
    ·
      refine ⟨26813054899810998729127979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17875369933207332486085319 26813054899810998729127979)
      ·
        refine ⟨40219582349716498093691969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26813054899810998729127979 40219582349716498093691969)
        ·
          refine ⟨30164686762287373570268977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40219582349716498093691969 30164686762287373570268977)
          ·
            refine ⟨22623515071715530177701733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30164686762287373570268977 22623515071715530177701733)
            ·
              refine ⟨4241909075946661908319075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22623515071715530177701733 4241909075946661908319075)
              ·
                refine ⟨6362863613919992862478613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4241909075946661908319075 6362863613919992862478613)
                ·
                  refine ⟨298259231902499665428685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6362863613919992862478613 298259231902499665428685)
                  ·
                    rfl

theorem cell22_2613860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2613860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613860 prefixEnd_2613860 := by exact prefixLift 2613860
  have htrace : WordTrace (prefixWord ++ tailWord_2613860) baseStart_2613860 baseEnd_2613860 := by
    simpa [prefixWord, tailWord_2613860, baseEnd_2613860] using wordTrace_append hprefix tailTrace_2613860
  have hstable : (prefixWord ++ tailWord_2613860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613860).length < 2 ^ (prefixWord ++ tailWord_2613860).sum := by decide
  have hdescent : baseEnd_2613860 < baseStart_2613860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613892 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_2613892 : Nat := 118140960795 + 2613892 * 2 ^ 59
def prefixEnd_2613892 : Nat := 4983230072969 + 3 ^ 40 * 2613892 * 2
def baseEnd_2613892 : Nat := 894788649961461579485957

theorem tailTrace_2613892 : CollatzResearch.WordTrace tailWord_2613892 prefixEnd_2613892 894788649961461579485957 := by
  unfold tailWord_2613892
  simp only [CollatzResearch.WordTrace]
  refine ⟨47668236723161588028809965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 63557648964215450705079953 47668236723161588028809965)
  ·
    refine ⟨17875588771185595510803737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47668236723161588028809965 17875588771185595510803737)
    ·
      refine ⟨13406691578389196633102803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17875588771185595510803737 13406691578389196633102803)
      ·
        refine ⟨20110037367583794949654205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13406691578389196633102803 20110037367583794949654205)
        ·
          refine ⟨7541264012843923106120327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20110037367583794949654205 7541264012843923106120327)
          ·
            refine ⟨11311896019265884659180491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7541264012843923106120327 11311896019265884659180491)
            ·
              refine ⟨16967844028898826988770737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11311896019265884659180491 16967844028898826988770737)
              ·
                refine ⟨12725883021674120241578053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16967844028898826988770737 12725883021674120241578053)
                ·
                  refine ⟨2386103066563897545295885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12725883021674120241578053 2386103066563897545295885)
                  ·
                    refine ⟨894788649961461579485957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2386103066563897545295885 894788649961461579485957)
                    ·
                      rfl

theorem cell22_2613892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_2613892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613892 prefixEnd_2613892 := by exact prefixLift 2613892
  have htrace : WordTrace (prefixWord ++ tailWord_2613892) baseStart_2613892 baseEnd_2613892 := by
    simpa [prefixWord, tailWord_2613892, baseEnd_2613892] using wordTrace_append hprefix tailTrace_2613892
  have hstable : (prefixWord ++ tailWord_2613892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613892).length < 2 ^ (prefixWord ++ tailWord_2613892).sum := by decide
  have hdescent : baseEnd_2613892 < baseStart_2613892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613903 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_2613903 : Nat := 118140960795 + 2613903 * 2 ^ 59
def prefixEnd_2613903 : Nat := 4983230072969 + 3 ^ 40 * 2613903 * 2
def baseEnd_2613903 : Nat := 894792415486261217460923

theorem tailTrace_2613903 : CollatzResearch.WordTrace tailWord_2613903 prefixEnd_2613903 894792415486261217460923 := by
  unfold tailWord_2613903
  simp only [CollatzResearch.WordTrace]
  refine ⟨95336874649283324936270363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63557916432855549957513575 95336874649283324936270363)
  ·
    refine ⟨143005311973924987404405545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 95336874649283324936270363 143005311973924987404405545)
    ·
      refine ⟨107253983980443740553304159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143005311973924987404405545 107253983980443740553304159)
      ·
        refine ⟨160880975970665610829956239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107253983980443740553304159 160880975970665610829956239)
        ·
          refine ⟨241321463955998416244934359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160880975970665610829956239 241321463955998416244934359)
          ·
            refine ⟨361982195933997624367401539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241321463955998416244934359 361982195933997624367401539)
            ·
              refine ⟨542973293900996436551102309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361982195933997624367401539 542973293900996436551102309)
              ·
                refine ⟨101807492606436831853331683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542973293900996436551102309 101807492606436831853331683)
                ·
                  refine ⟨152711238909655247779997525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101807492606436831853331683 152711238909655247779997525)
                  ·
                    refine ⟨894792415486261217460923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 152711238909655247779997525 894792415486261217460923)
                    ·
                      rfl

theorem cell22_2613903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_2613903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613903 prefixEnd_2613903 := by exact prefixLift 2613903
  have htrace : WordTrace (prefixWord ++ tailWord_2613903) baseStart_2613903 baseEnd_2613903 := by
    simpa [prefixWord, tailWord_2613903, baseEnd_2613903] using wordTrace_append hprefix tailTrace_2613903
  have hstable : (prefixWord ++ tailWord_2613903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613903).length < 2 ^ (prefixWord ++ tailWord_2613903).sum := by decide
  have hdescent : baseEnd_2613903 < baseStart_2613903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2613997 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2613997 : Nat := 118140960795 + 2613997 * 2 ^ 59
def prefixEnd_2613997 : Nat := 4983230072969 + 3 ^ 40 * 2613997 * 2
def baseEnd_2613997 : Nat := 894824593607276305610635

theorem tailTrace_2613997 : CollatzResearch.WordTrace tailWord_2613997 prefixEnd_2613997 894824593607276305610635 := by
  unfold tailWord_2613997
  simp only [CollatzResearch.WordTrace]
  refine ⟨95340303110942778990192245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 63560202073961852660128163 95340303110942778990192245)
  ·
    refine ⟨8938153416650885530330523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 95340303110942778990192245 8938153416650885530330523)
    ·
      refine ⟨13407230124976328295495785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8938153416650885530330523 13407230124976328295495785)
      ·
        refine ⟨10055422593732246221621839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13407230124976328295495785 10055422593732246221621839)
        ·
          refine ⟨15083133890598369332432759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10055422593732246221621839 15083133890598369332432759)
          ·
            refine ⟨22624700835897553998649139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15083133890598369332432759 22624700835897553998649139)
            ·
              refine ⟨33937051253846330997973709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22624700835897553998649139 33937051253846330997973709)
              ·
                refine ⟨12726394220192374124240141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33937051253846330997973709 12726394220192374124240141)
                ·
                  refine ⟨4772397832572140296590053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12726394220192374124240141 4772397832572140296590053)
                  ·
                    refine ⟨894824593607276305610635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4772397832572140296590053 894824593607276305610635)
                    ·
                      rfl

theorem cell22_2613997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2613997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2613997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2613997 prefixEnd_2613997 := by exact prefixLift 2613997
  have htrace : WordTrace (prefixWord ++ tailWord_2613997) baseStart_2613997 baseEnd_2613997 := by
    simpa [prefixWord, tailWord_2613997, baseEnd_2613997] using wordTrace_append hprefix tailTrace_2613997
  have hstable : (prefixWord ++ tailWord_2613997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2613997).length < 2 ^ (prefixWord ++ tailWord_2613997).sum := by decide
  have hdescent : baseEnd_2613997 < baseStart_2613997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2613997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
